(* X86lite Simulator *)

(* See the documentation in the X86lite specification, available on the 
   course web pages, for a detailed explanation of the instruction
   semantics.
*)

open X86

(* simulator machine state -------------------------------------------------- *)

let mem_bot = 0x400000L          (* lowest valid address *)
let mem_top = 0x410000L          (* one past the last byte in memory *)
let mem_size = Int64.to_int (Int64.sub mem_top mem_bot)
let nregs = 17                   (* including Rip *)
let ins_size = 8L                (* assume we have a 8-byte encoding *)
let exit_addr = 0xfdeadL         (* halt when m.regs(%rip) = exit_addr *)

(* Your simulator should raise this exception if it tries to read from or
   store to an address not within the valid address space. *)
exception X86lite_segfault

(* The simulator memory maps addresses to symbolic bytes.  Symbolic
   bytes are either actual data indicated by the Byte constructor or
   'symbolic instructions' that take up eight bytes for the purposes of
   layout.

   The symbolic bytes abstract away from the details of how
   instructions are represented in memory.  Each instruction takes
   exactly eight consecutive bytes, where the first byte InsB0 stores
   the actual instruction, and the next seven bytes are InsFrag
   elements, which aren't valid data.

   For example, the two-instruction sequence:
        at&t syntax             ocaml syntax
      movq %rdi, (%rsp)       Movq,  [~%Rdi; Ind2 Rsp]
      decq %rdi               Decq,  [~%Rdi]

   is represented by the following elements of the mem array (starting
   at address 0x400000):

       0x400000 :  InsB0 (Movq,  [~%Rdi; Ind2 Rsp])
       0x400001 :  InsFrag
       0x400002 :  InsFrag
       0x400003 :  InsFrag
       0x400004 :  InsFrag
       0x400005 :  InsFrag
       0x400006 :  InsFrag
       0x400007 :  InsFrag
       0x400008 :  InsB0 (Decq,  [~%Rdi])
       0x40000A :  InsFrag
       0x40000B :  InsFrag
       0x40000C :  InsFrag
       0x40000D :  InsFrag
       0x40000E :  InsFrag
       0x40000F :  InsFrag
       0x400010 :  InsFrag
*)
type sbyte = InsB0 of ins       (* 1st byte of an instruction *)
           | InsFrag            (* 2nd - 8th bytes of an instruction *)
           | Byte of char       (* non-instruction byte *)

(* memory maps addresses to symbolic bytes *)
type mem = sbyte array

(* Flags for condition codes *)
type flags = { mutable fo : bool
             ; mutable fs : bool
             ; mutable fz : bool
             }

(* Register files *)
type regs = int64 array

(* Complete machine state *)
type mach = { flags : flags
            ; regs : regs
            ; mem : mem
            }

(* simulator helper functions ----------------------------------------------- *)

(* The index of a register in the regs array *)
let rind : reg -> int = function
  | Rip -> 16
  | Rax -> 0  | Rbx -> 1  | Rcx -> 2  | Rdx -> 3
  | Rsi -> 4  | Rdi -> 5  | Rbp -> 6  | Rsp -> 7
  | R08 -> 8  | R09 -> 9  | R10 -> 10 | R11 -> 11
  | R12 -> 12 | R13 -> 13 | R14 -> 14 | R15 -> 15

(* Helper functions for reading/writing sbytes *)

(* Convert an int64 to its sbyte representation *)
let sbytes_of_int64 (i:int64) : sbyte list =
  let open Char in 
  let open Int64 in
  List.map (fun n -> Byte (shift_right i n |> logand 0xffL |> to_int |> chr))
           [0; 8; 16; 24; 32; 40; 48; 56]

(* Convert an sbyte representation to an int64 *)
let int64_of_sbytes (bs:sbyte list) : int64 =
  let open Char in
  let open Int64 in
  let f b i = match b with
    | Byte c -> logor (shift_left i 8) (c |> code |> of_int)
    | _ -> 0L
  in
  List.fold_right f bs 0L

(* Convert a string to its sbyte representation *)
let sbytes_of_string (s:string) : sbyte list =
  let rec loop acc = function
    | i when i < 0 -> acc
    | i -> loop (Byte s.[i]::acc) (pred i)
  in
  loop [Byte '\x00'] @@ String.length s - 1

(* Serialize an instruction to sbytes *)
let sbytes_of_ins (op, args:ins) : sbyte list =
  let check = function
    | Imm (Lbl _) | Ind1 (Lbl _) | Ind3 (Lbl _, _) -> 
      invalid_arg "sbytes_of_ins: tried to serialize a label!"
    | o -> ()
  in
  List.iter check args;
  [InsB0 (op, args); InsFrag; InsFrag; InsFrag;
   InsFrag; InsFrag; InsFrag; InsFrag]

(* Serialize a data element to sbytes *)
let sbytes_of_data : data -> sbyte list = function
  | Quad (Lit i) -> sbytes_of_int64 i
  | Asciz s -> sbytes_of_string s
  | Quad (Lbl _) -> invalid_arg "sbytes_of_data: tried to serialize a label!"


(* It might be useful to toggle printing of intermediate states of your 
   simulator. Our implementation uses this mutable flag to turn on/off
   printing.  For instance, you might write something like:

     [if !debug_simulator then print_endline @@ string_of_ins u; ...]

*)
let debug_simulator = ref false

(* Interpret a condition code with respect to the given flags. *)
(* DONE *)
let interp_cnd {fo; fs; fz} : cnd -> bool = 
  fun x -> match x with
    |Eq -> fz
    |Neq -> not fz
    |Lt -> not (fs == fo)
    |Le -> (not ( fs == fo) )|| fz
    |Gt -> not ((not (fs == fo) )|| fz)
    |Ge -> not (not (fs == fo))
    
    
     

(* Maps an X86lite address into Some OCaml array index,
   or None if the address is not within the legal address space. *)
(* DONE *)
let map_addr (addr:quad) : int option = if (addr < mem_bot) then None else (if (addr >= mem_top) then None else Some (Int64.to_int (Int64.sub addr mem_bot)))

(*Gibt den RIP zurück als quad*)
let get_rip (m:mach) : quad = m.regs.(16)

(*
Nimmt den maschinenstate und
Gibt die Instruction zurück auf die rip zeigt
*)
let fetch_ins (m:mach) : ins = 
  match map_addr (get_rip m) with
    |None -> raise X86lite_segfault
    |Some x -> match m.mem.(x) with
              |InsB0 ins' -> ins'
              |_ -> raise X86lite_segfault

(* 
Nimmt machstate und eine adresse (quad) und gibt den wert dort zurück
*)
let read_quad (m : mach) (addr : quad) : quad =
  let byte k =
    match map_addr (Int64.add addr (Int64.of_int k)) with
    | None -> raise X86lite_segfault
    | Some i -> m.mem.(i)
  in
  int64_of_sbytes (List.init 8 byte)

(*gibt immediate als quad zurück, keine Ahnung was zu tun wenn es ein Label ist*)
let interp_imm : imm -> quad = function
  | Lit i -> i
  | Lbl _ -> failwith "idk??? unresolved label??"

(*gibt den value der in einem Register/mem-addr ist zurück*)
let interp_addr (m : mach) (op : operand) : quad =
  match op with
  | Ind1 d      -> interp_imm d
  | Ind2 r      -> m.regs.(rind r)
  | Ind3 (d, r) -> Int64.add (interp_imm d) m.regs.(rind r)
  | Imm _ | Reg _ -> failwith "interp_addr: kein Speicherort"

(*gibt den value eines Operanden wieder*)
let interp_operand (m:mach) (op:operand) : int64 = 
  match op with
  |Imm x -> interp_imm x
  |Reg x -> m.regs.(rind x)
  |Ind1 _ | Ind2 _ | Ind3 _ -> read_quad m (interp_addr m op)

(*schreibt v (value) in die address, dnake claude*)
let write_quad (m : mach) (addr : quad) (v : quad) : unit =
  List.iteri
    (fun k b ->
       match map_addr (Int64.add addr (Int64.of_int k)) with
       | None   -> raise X86lite_segfault
       | Some i -> m.mem.(i) <- b)
    (sbytes_of_int64 v)

(* 
Nimmt einen machinestate, destination operand and a value
schreibt den value in die destination
*)
let write_operand (m : mach) (dst : operand) (v : quad) : unit =
  match dst with
  | Reg r -> m.regs.(rind r) <- v
  | Ind1 _ | Ind2 _ | Ind3 _ -> write_quad m (interp_addr m dst) v
  | Imm _ -> failwith "write_operand: Immediate kann kein Ziel sein"

(*increase instruction pointer to next instruction*)
let increase_rip (m:mach) : unit = m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) ins_size

(*sets flags for arith instr*)
let set_flag_arith (m:mach) (r:Int64_overflow.t) : unit =
  m.flags.fo <- r.Int64_overflow.overflow;
  m.flags.fs <- Int64.compare r.Int64_overflow.value 0L < 0;
  m.flags.fz <- r.Int64_overflow.value = 0L

(* processes arithmetic instruction and sets flags*)
let proc_arith (m:mach) (dst:operand) (r:Int64_overflow.t) : unit = 
  write_operand m dst (r.Int64_overflow.value);
  set_flag_arith m r;
  increase_rip m


  (*setze für logic ops die flags*)
let set_flags_logic (m:mach) (v:int64) : unit =
  m.flags.fo <- false;
  m.flags.fs <- Int64.compare v 0L < 0;
  m.flags.fz <- v = 0L

  (* Simulates one step of the machine:
    - fetch the instruction at %rip DONe
    - compute the source and/or destination information from the operands
    - simulate the instruction semantics
    - update the registers and/or memory appropriately
    - set the condition flags
*)

let proc_logic (m:mach) (dst:operand) (r:int64) : unit =
    write_operand m dst r; set_flags_logic m r; increase_rip m

let proc_shift (m:mach) (dst:operand) (a:int) (r:int64) (fo:bool) : unit = 
  write_operand m dst r;
  if a <> 0 then begin
    m.flags.fs <- Int64.compare r 0L < 0;
    m.flags.fz <- r = 0L;
    if a = 1 then m.flags.fo <- fo
  end;
  increase_rip m

let step (m:mach) : unit =
  let (op, args) = fetch_ins m in
  let v = interp_operand m in (*v needs a operand and computes its value*) 
  let wr = write_operand m in (*wr needs a destination operand and a value to write there*)
  match op, args with
  (*arith*)
  |Negq, [dst] -> proc_arith m dst (Int64_overflow.neg (v dst))
  |Addq, [src;dst] -> proc_arith m dst (Int64_overflow.add (v dst) (v src))
  |Subq, [src;dst] -> proc_arith m dst (Int64_overflow.sub (v dst) (v src))
  |Imulq, [src;dst] -> proc_arith m dst (Int64_overflow.mul (v dst) (v src))
  |Incq, [src] -> proc_arith m src (Int64_overflow.succ (v src))
  |Decq, [src] -> proc_arith m src (Int64_overflow.pred (v src))

  (*Logic*)
  |Notq, [dst] -> let r = Int64.lognot (v dst) in
                  wr dst r; increase_rip m
  |Andq, [src; dst] -> let r = Int64.logand (v src) (v dst) in proc_logic m dst r
  |Orq, [src;dst] -> let r = Int64.logor (v src) (v dst) in proc_logic m dst r
  |Xorq, [src;dst] -> let r = Int64.logxor (v src) (v dst) in proc_logic m dst r

  (*Bit*)
  |Sarq, [amt;dst] -> let a = Int64.to_int (v amt) and x = v dst in proc_shift m dst a (Int64.shift_right x a) false
  |Shlq, [amt;dst] -> let a = Int64.to_int (v amt) and x = v dst in proc_shift m dst a (Int64.shift_left x a) (Int64.compare (Int64.logxor x (Int64.shift_left x 1)) 0L < 0)
  |Shrq, [amt;dst] -> let a = Int64.to_int (v amt) and x = v dst in proc_shift m dst a (Int64.shift_right_logical x a) (Int64.compare x 0L < 0)
  |Set cc, [dst] -> let b = if interp_cnd m.flags cc then 1L else 0L in (*Claude*)
                    wr dst (Int64.logor (Int64.logand (v dst) (Int64.lognot 0xFFL)) b);
                    increase_rip m
  (*Movmenet - No Flags*)
  |Leaq, [ind;dst] -> wr dst (interp_addr m ind); increase_rip m (*hier interp_addr weil wir die adresse als value haben*)
  |Movq, [src;dst] -> wr dst (v src);increase_rip m
  |Pushq, [src] -> wr (Reg Rsp) (Int64.sub (v (Reg Rsp)) 8L);
                    wr (Ind2 Rsp) (v src);
                    increase_rip m
  |Popq, [dst] -> wr dst (v (Ind2 Rsp)); 
                  wr (Reg Rsp) (Int64.add (v (Reg Rsp)) 8L);
                  increase_rip m

  (*Control Flow*)
  |Cmpq, [src1;src2] -> set_flag_arith m (Int64_overflow.sub (v src2) (v src1));
                        increase_rip m
  |Jmp, [src] -> wr (Reg Rip) (v src)
  |Callq, [src] ->  wr (Reg Rsp) (Int64.sub (v (Reg Rsp)) 8L);
                    wr (Ind2 Rsp) (v (Reg Rip));
                    wr (Reg Rip) (v src)
  |Retq, [] ->  wr (Reg Rip) (v (Ind2 Rsp)); 
                wr (Reg Rsp) (Int64.add (v (Reg Rsp)) 8L)
  |J cc, [src] -> if interp_cnd m.flags cc then wr (Reg Rip) (v src) else increase_rip m
  |_ -> failwith "no operand"
  
  


(* Runs the machine until the rip register reaches a designated
   memory address. Returns the contents of %rax when the 
   machine halts. *)
let run (m:mach) : int64 = 
  while m.regs.(rind Rip) <> exit_addr do step m done;
  m.regs.(rind Rax)

(* assembling and linking --------------------------------------------------- *)

(* A representation of the executable *)
type exec = { entry    : quad              (* address of the entry point *)
            ; text_pos : quad              (* starting address of the code *)
            ; data_pos : quad              (* starting address of the data *)
            ; text_seg : sbyte list        (* contents of the text segment *)
            ; data_seg : sbyte list        (* contents of the data segment *)
            }

(* Assemble should raise this when a label is used but not defined *)
exception Undefined_sym of lbl

(* Assemble should raise this when a label is defined more than once *)
exception Redefined_sym of lbl

(* Convert an X86 program into an object file:
   - separate the text and data segments
   - compute the size of each segment
      Note: the size of an Asciz string section is (1 + the string length)
            due to the null terminator
   - resolve the labels to concrete addresses and 'patch' the instructions to 
     replace Lbl values with the corresponding Imm values.

   - the text segment starts at the lowest address
   - the data segment starts after the text segment

  HINT: List.fold_left and List.fold_right are your friends.
 *)
let assemble (p:prog) : exec =
failwith "assemble unimplemented"

(* Convert an object file into an executable machine state. 
    - allocate the mem array
    - set up the memory state by writing the symbolic bytes to the 
      appropriate locations 
    - create the inital register state
      - initialize rip to the entry point address
      - initializes rsp to the last word in memory 
      - the other registers are initialized to 0
    - the condition code flags start as 'false'

  Hint: The Array.make, Array.blit, and Array.of_list library functions 
  may be of use.
*)
let load {entry; text_pos; data_pos; text_seg; data_seg} : mach = 
failwith "load unimplemented"

type riscv = 
  | Add of string * string * string
  | Addi of string * string * int
  | Sub of string * string * string 
  | Auipc of string * int
  | And of string * string * string
  | Andi of string * string * int
  | Or of string * string * string
  | Ori of string * string * int
  | Xor of string * string * string
  | Xori of string * string * int
  | Lui of string * int 
  | Sll of string * string * string
  | Slli of string * string * int
  | Srl of string * string * string
  | Srli of string * string * int
  | Sra of string * string * string
  | Srai of string * string * int
  | Slt of string * string * string
  | Slti of string * string * int
  | Sltu of string * string * string
  | Sltiu of string * string * int
  | Label of string
  | Lw of string * string * int
  | Sw of string * string * int
  | Sb of string * string * int

(*
  | Jal of string * string (* First argument is the save register, second is the label location *)
  | Jalr of string * string * int (* first argument is save register, second is register for jump location, int is immediate offset *)
  | Beq of string * string * string (* Where the last string is the label location to jump to *)
  | Bne of string * string * string
  | Blt of string * string * string
  | Bge of string * string * string
  | Bltu of string * string * string
  | Bgeu of string * string * string
  | Lb of string * string * int
*)

let rec init_reg_file counter n_regs rf =
  if counter = n_regs then rf
  else
    let () = Hashtbl.add rf ("x" ^ (string_of_int counter)) 0 in 
    init_reg_file (counter + 1) n_regs rf

let reg_file = Hashtbl.create 32 |> init_reg_file 0 32

let ram = Hashtbl.create 1000 

let slt_helper = 
  fun a b -> if a < b then 1 else 0

let sltiu_helper = 
  fun a b -> if b = 1 then (if a = 0 then 1 else 0) else (if abs a < abs b then 1 else 0)

let xori_helper = 
  fun a b -> if b = -1 then lnot a else a lxor b

(* In Little Endian order *)
let rec dec_to_base_2 acc dec = 
  if dec < 0 then failwith "Base 10 number must be non-negative"
  else 
    let dec' = dec / 2 in 
    let rem = dec mod 2 in 
    if dec' = 0 then List.rev (dec :: acc)
    else dec_to_base_2 (rem :: acc) dec'

let rec pad_one_32_helper lst len = 
  if len = 0 then lst 
  else pad_one_32_helper (1 :: lst) (len - 1)

(** Requires: [lst] is in little endian order *)
let pad_one_32 lst = 
  let len = List.length lst in 
  let rem = 32 - len in 
  List.rev (pad_one_32_helper (List.rev lst) rem)

let rec pad_zero_32_helper lst len = 
  if len = 0 then lst 
  else pad_zero_32_helper (0 :: lst) (len - 1)

(** Requires: [lst] is in little endian order *)
let pad_zero_32 lst = 
  let len = List.length lst in 
  let rem = 32 - len in 
  List.rev (pad_zero_32_helper (List.rev lst) rem)

let sign_extend lst = 
  if lst = [] then pad_zero_32 lst 
  else begin 
    let head = List.hd lst in 
    if head = 1 then pad_one_32 lst 
    else pad_zero_32 lst 
  end

(* Little endian constant *)
let c_ONE_BASE_2 = 
  1 |> dec_to_base_2 [] |> pad_zero_32

let invert_base_2 lst = 
  List.map (fun x -> if x = 1 then 0 else 1) lst

(* Both lst1 and lst2 are in little endian order *)
let rec add_base_2_helper lst1 lst2 carry acc = 
  match lst1, lst2 with 
  | [], [] -> List.rev acc 
  | [], _ 
  | _, [] -> failwith "Both lsts must be the same length"
  | h1 :: t1, h2 :: t2 -> 
    let digit = h1 + h2 + carry in 
    if digit > 1 then add_base_2_helper t1 t2 1 (digit :: acc) 
    else add_base_2_helper t1 t2 0 (digit :: acc)

let add_base_2 lst1 lst2 = 
  add_base_2_helper lst1 lst2 0 []

(* n is decimal, and returns little endian list *)
let convert_to_base_2 n = 
  if n >= 0 then dec_to_base_2 [] n 
  else 
    let pos_n = abs n in 
    let pos_base_2 = dec_to_base_2 [] pos_n in 
    let inverted_base_2 = invert_base_2 pos_base_2 in 
    add_base_2 inverted_base_2 c_ONE_BASE_2

(* In little endian order, and returns little endian order *)
let rec take_first_n lst rem_list acc n = 
  if n = 0 then (List.rev acc, rem_list)
  else begin
    match lst with 
    | [] -> failwith "List not long enough to remove n elements"
    | h :: t -> 
      take_first_n t t (h :: acc) (n - 1)
  end

(* Splits into little endian order *)
let split_32_into_4_groups lst = 
  assert (List.length lst = 32);
  let lst1, rem1 = take_first_n lst [] [] 8 in 
  let lst2, rem2 = take_first_n rem1 [] [] 8 in 
  let lst3, rem3 = take_first_n rem2 [] [] 8 in 
  let lst4, rem4 = take_first_n rem3 [] [] 8 in 
  (lst1, lst2, lst3, lst4)

let convert_to_base_10 lst = 
  List.fold_left (fun acc elt -> 2 * acc + elt) 0 (List.rev lst)

(** [dec_to_base_16 dec acc] converts [dec] in base 10 to
    base 16 hexadecimal in list form. 

    Example: 
    0 -> [0] because 0*16^0 = 0
    10 -> [10] because 10*16^0 = 10
    16 -> [1, 0] because 1*16^1 + 0*16^0 = 16
    256 -> [2, 0, 0] because 1*16^2 + 0*16^1 + 0*16^0 = 256

    We then reverse the list so it is in little endian order:
    e.g. 
    [0] -> [0]
    [10] -> [10]
    [2; 3; 5] -> [5; 3; 2]

    Invariant: each element in the returned list is a base 10 number
    between 0 and 15 inclusive of 0 and 15.

    Raises: [Base 10 number must be non-negative]. *)
let rec dec_to_base_16 dec acc = 
  if dec < 0 then failwith "Base 10 number must be non-negative"
  else 
    let dec' = dec / 16 in 
    let rem = dec mod 16 in 
    if dec' = 0 then List.rev (dec :: acc) 
    else dec_to_base_16 dec' (rem :: acc)

let rec eval_table_a expr_lst rf ram pc =
  match expr_lst with 
  | [] -> print_endline "Finished interpretation"; ()

  | Add (rd, rs1, rs2) :: t -> eval_reg_reg rd rs1 rs2 rf ram (+); eval_table_a t rf ram (pc + 4)
  | Addi (rd, rs1, imm) :: t -> eval_reg_imm rd rs1 imm rf ram (+); eval_table_a t rf ram (pc + 4)
  | Sub (rd, rs1, rs2) :: t -> eval_reg_reg rd rs1 rs2 rf ram (-); eval_table_a t rf ram (pc + 4)

  | And (rd, rs1, rs2) :: t -> eval_reg_reg rd rs1 rs2 rf ram (land); eval_table_a t rf ram (pc + 4)
  | Andi (rd, rs1, imm) :: t -> eval_reg_imm rd rs1 imm rf ram (land); eval_table_a t rf ram (pc + 4)
  | Or (rd, rs1, rs2) :: t -> eval_reg_reg rd rs1 rs2 rf ram (lor); eval_table_a t rf ram (pc + 4)
  | Ori (rd, rs1, imm) :: t -> eval_reg_imm rd rs1 imm rf ram (lor); eval_table_a t rf ram (pc + 4)
  | Xor (rd, rs1, rs2) :: t -> eval_reg_reg rd rs1 rs2 rf ram (lxor); eval_table_a t rf ram (pc + 4)
  | Xori (rd, rs1, imm) :: t -> eval_reg_imm rd rs1 imm rf ram (xori_helper); eval_table_a t rf ram (pc + 4)

  | Sll (rd, rs1, rs2) :: t -> eval_reg_reg rd rs1 rs2 rf ram (lsl); eval_table_a t rf ram (pc + 4)
  | Slli (rd, rs1, imm) :: t -> eval_reg_imm rd rs1 imm rf ram (lsl); eval_table_a t rf ram (pc + 4)
  | Srl (rd, rs1, rs2) :: t -> eval_reg_reg rd rs1 rs2 rf ram (lsr); eval_table_a t rf ram (pc + 4)
  | Srli (rd, rs1, imm) :: t -> eval_reg_imm rd rs1 imm rf ram (lsr); eval_table_a t rf ram (pc + 4)
  | Sra (rd, rs1, rs2) :: t -> eval_reg_reg rd rs1 rs2 rf ram (asr); eval_table_a t rf ram (pc + 4)
  | Srai (rd, rs1, imm) :: t -> eval_reg_imm rd rs1 imm rf ram (asr); eval_table_a t rf ram (pc + 4)

  | Lui (rd, imm) :: t -> eval_lui rd imm rf ram; eval_table_a t rf ram (pc + 4)
  | Auipc (rd, imm) :: t -> eval_auipc rd imm pc rf ram; eval_table_a t rf ram (pc + 4)

  | Slt (rd, rs1, rs2) :: t -> eval_reg_reg rd rs1 rs2 rf ram (slt_helper); eval_table_a t rf ram (pc + 4)
  | Slti (rd, rs1, imm) :: t -> eval_reg_imm rd rs1 imm rf ram (slt_helper); eval_table_a t rf ram (pc + 4)
  | Sltu (rd, rs1, rs2) :: t -> eval_sltu rd rs1 rs2 rf ram; eval_table_a t rf ram (pc + 4)
  | Sltiu (rd, rs1, imm) :: t -> eval_reg_imm rd rs1 imm rf ram (sltiu_helper); eval_table_a t rf ram (pc + 4)

  | Label (name) :: t -> eval_table_a t rf ram (pc + 4)

  | _ :: t -> print_endline "Not a Table A operation"; eval t rf ram (pc + 4)

and eval expr_lst rf ram pc = 
  match expr_lst with 
  | [] -> print_endline "Finished interpretation"; ()

  | Add (rd, rs1, rs2) :: t -> eval_reg_reg rd rs1 rs2 rf ram (+); eval t rf ram (pc + 4)
  | Addi (rd, rs1, imm) :: t -> eval_reg_imm rd rs1 imm rf ram (+); eval t rf ram (pc + 4)
  | Sub (rd, rs1, rs2) :: t -> eval_reg_reg rd rs1 rs2 rf ram (-); eval t rf ram (pc + 4)

  | And (rd, rs1, rs2) :: t -> eval_reg_reg rd rs1 rs2 rf ram (land); eval t rf ram (pc + 4)
  | Andi (rd, rs1, imm) :: t -> eval_reg_imm rd rs1 imm rf ram (land); eval t rf ram (pc + 4)
  | Or (rd, rs1, rs2) :: t -> eval_reg_reg rd rs1 rs2 rf ram (lor); eval t rf ram (pc + 4)
  | Ori (rd, rs1, imm) :: t -> eval_reg_imm rd rs1 imm rf ram (lor); eval t rf ram (pc + 4)
  | Xor (rd, rs1, rs2) :: t -> eval_reg_reg rd rs1 rs2 rf ram (lxor); eval t rf ram (pc + 4)
  | Xori (rd, rs1, imm) :: t -> eval_reg_imm rd rs1 imm rf ram (lxor); eval t rf ram (pc + 4)

  | Sll (rd, rs1, rs2) :: t -> eval_reg_reg rd rs1 rs2 rf ram (lsl); eval t rf ram (pc + 4)
  | Slli (rd, rs1, imm) :: t -> eval_reg_imm rd rs1 imm rf ram (lsl); eval t rf ram (pc + 4)
  | Srl (rd, rs1, rs2) :: t -> eval_reg_reg rd rs1 rs2 rf ram (lsr); eval t rf ram (pc + 4)
  | Srli (rd, rs1, imm) :: t -> eval_reg_imm rd rs1 imm rf ram (lsr); eval t rf ram (pc + 4)
  | Sra (rd, rs1, rs2) :: t -> eval_reg_reg rd rs1 rs2 rf ram (asr); eval t rf ram (pc + 4)
  | Srai (rd, rs1, imm) :: t -> eval_reg_imm rd rs1 imm rf ram (asr); eval t rf ram (pc + 4)

  | Lui (rd, imm) :: t -> eval_lui rd imm rf ram; eval t rf ram (pc + 4)
  | Auipc (rd, imm) :: t -> eval_auipc rd imm pc rf ram; eval t rf ram (pc + 4)

  | Slt (rd, rs1, rs2) :: t -> eval_reg_reg rd rs1 rs2 rf ram (slt_helper); eval t rf ram (pc + 4)
  | Slti (rd, rs1, imm) :: t -> eval_reg_imm rd rs1 imm rf ram (slt_helper); eval t rf ram (pc + 4)
  | Sltu (rd, rs1, rs2) :: t -> eval_sltu rd rs1 rs2 rf ram; eval t rf ram (pc + 4)
  | Sltiu (rd, rs1, imm) :: t -> eval_reg_imm rd rs1 imm rf ram (sltiu_helper); eval t rf ram (pc + 4)

  | Label (name) :: t -> eval t rf ram (pc + 4)

  | Lw (rd, rs1, imm) :: t -> eval_lw rd rs1 imm rf ram; eval t rf ram (pc + 4)
  | Sw (rs1, rs2, imm) :: t -> eval_sw rs1 rs2 imm rf ram; eval t rf ram (pc + 4)

  | Sb (rs1, rs2, imm) :: t -> eval_sb rs1 rs2 imm rf ram; eval t rf ram (pc + 4)

and eval_auipc rd imm pc rf ram = 
  let a = imm lsl 12 in 
  let res = a + pc in 
  Hashtbl.add rf rd res

and eval_lui rd imm rf ram = 
  let res = imm lsl 12 in 
  Hashtbl.add rf rd res

and eval_sltu rd rs1 rs2 rf ram = 
  let a = Hashtbl.find rf rs1 in 
  let b = Hashtbl.find rf rs2 in
  let res = if abs a < abs b then 1 else 0 in
  if rs1 = "x0" then begin
    if b <> 0 then Hashtbl.add rf rd 1
    else Hashtbl.add rf rd 0
  end
  else Hashtbl.add rf rd res

and eval_reg_reg rd rs1 rs2 rf ram op = 
  let a = Hashtbl.find rf rs1 in 
  let b = Hashtbl.find rf rs2 in
  let res = op a b in (* No 32 bit rollover *)
  Hashtbl.add rf rd res

and eval_reg_imm rd rs1 imm rf ram op = 
  let a = Hashtbl.find rf rs1 in 
  let res = op a imm in (* No 32 bit rollover *)
  Hashtbl.add rf rd res

and eval_lw rd rs1 imm rf ram = 
  let a = Hashtbl.find rf rs1 in 
  let address = a + imm in 
  if address < 0 then failwith "Memory Fault : Cannot access negative address"
  else match Hashtbl.find_opt ram address with 
    | None -> Hashtbl.add rf rd 0 (* Assume memory id zeroed out, but UB allows me to do anything *)
    | Some lst -> failwith "Unimplemented"

and eval_lb rd rs1 imm rf ram = 
  let a = Hashtbl.find rf rs1 in 
  let address = a + imm in 
  if address < 0 then failwith "Memory Fault : Cannot access negative address"
  else match Hashtbl.find_opt ram address with 
    | None -> Hashtbl.add rf rd 0 (* Assume memory id zeroed out, but UB allows me to do anything *)
    | Some lst -> 
      let extended_list = sign_extend lst in 
      let dec = convert_to_base_10 extended_list in 
      Hashtbl.add rf rd dec

and eval_sw rs1 rs2 imm rf ram = 
  let a = Hashtbl.find rf rs1 in 
  let b = Hashtbl.find rf rs2 in 
  let b_list = convert_to_base_2 b in (* b_list is base 2, little endian first at head *)
  let s1, s2, s3, s4 = split_32_into_4_groups b_list in  
  let address = a + imm in 
  if address < 0 then failwith "Memory Fault : Cannot access negative address"
  else 
    let () = Hashtbl.add ram address s1 in 
    Hashtbl.add ram (address + 1) s2;
    Hashtbl.add ram (address + 2) s3;
    Hashtbl.add ram (address + 3) s4

and eval_sb rs1 rs2 imm rf ram = 
  let a = Hashtbl.find rf rs1 in 
  let b = Hashtbl.find rf rs2 in 
  let b_list = convert_to_base_2 b in (* b_list is base 2, little endian first at head *)
  let s1, _ = take_first_n b_list [] [] 8 in  (* takes low bits of b_list *)
  let address = a + imm in 
  if address < 0 then failwith "Memory Fault : Cannot access negative address"
  else Hashtbl.add ram address s1















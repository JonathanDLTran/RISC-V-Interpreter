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
  | Lb of string * string * int
  | Sb of string * string * int
  | Jal of string * string (* First argument is the save register, second is the label location *)
  | Jalr of string * string * int (* first argument is save register, second is register for jump location, int is immediate offset *)
  | Beq of string * string * string (* Where the last string is the label location to jump to *)
  | Bne of string * string * string
  | Blt of string * string * string
  | Bge of string * string * string
  | Bltu of string * string * string
  | Bgeu of string * string * string

(* ####### INPUT OUTPUT FROM FILE ######### *)

let c_QUIT = "quit"

let rec get_file () = 
  let () = 
    print_endline "Please give the address to the file you want to parse : " in 
  let file_name = read_line () in 
  if String.lowercase_ascii file_name = c_QUIT then exit 0 
  else match open_in file_name with 
    | exception e -> 
      print_endline "The file address you requested does not exist. Try again. ";
      get_file ()
    | ic -> ic

let read_lines_in_file ic = 
  let rec read_lines_helper ic acc = 
    match input_line ic with 
    | exception e -> close_in ic; List.rev acc
    | line -> read_lines_helper ic (line :: acc)
  in read_lines_helper ic []

let main_read_file () = 
  () |> get_file |> read_lines_in_file

(* ########## FRONT END PARSE ######### *)

let c_SPACES_OR_EMPTY = [""; " "; "\n"; "\t"; "\r"]

let c_COMMENT = '#'

let c_SPACE = ' '

let c_COMMA = ','

let c_COLON = ':'

let c_REG_IMM = ["addi"; "andi"; "ori"; "xori"; "slti"; "sltiu"; "slli"; "srai"; "srli"]

let c_REG_REG = ["add"; "sub"; "and"; "or"; "xor"; "slt"; "sltu"; "srl"; "sll"; "sra"]

let c_BRANCH = ["beq"; "bne"; "bge"; "bgeu"; "blt"; "bltu"]

let rec init_regs counter n_regs acc =
  if counter = n_regs then acc
  else
    init_regs (counter + 1) n_regs (("x" ^ (string_of_int counter)) :: acc)

let c_REGISTERS = 
  init_regs 0 32 []

let remove_comments str = 
  match String.index str c_COMMENT with 
  | exception e -> str 
  | i -> begin (* i is an index of #, that could be at 0 *)
      String.sub str 0 (i - 1) (* i - 1 to avoid # symbol at i *)
    end

let replace_commas str = 
  String.map (fun c -> if c = c_COMMA then c_SPACE else c) str

let clean_strings str_lst = 
  str_lst 
  |> List.map remove_comments (* all comments gone *)
  |> List.map (String.lowercase_ascii) (* all to lowercase *)
  |> List.map (String.trim) (* remove spaces in each string *)
  |> List.filter (fun s -> List.mem s c_SPACES_OR_EMPTY) (* any emoty string or spaces only string removed *)
  |> List.map (String.split_on_char c_SPACE) (* each remianing string is turned into a list with subelements now *)
  |> List.map (fun lst -> List.map replace_commas lst) (* turn commas into spaces *)
  |> List.map (fun lst -> List.map String.trim lst) (* remove spaces where commas were *)

let check_imm h imm = 
  match int_of_string imm with 
  | exception e -> failwith ("Parse Error : Immediate not an integer : " ^ imm)
  | i -> begin 
      if h = "slli" || h = "srli" || h = "srai" then begin
        if i > 31 || i < 0 
        then 
          failwith ("Immediate Error : Shift immediates must be between 0 and 31 : " ^ string_of_int i)
        else i
      end
      else if h = "addi" || h = "andi" || h = "ori" || h = "xori" || h = "slti" || h = "sltiu" then begin
        if i >= 1024 || i < -1024 
        then failwith ("Immediate Error : Reg Imm immediates must be between -1024 and 1023 : " ^ string_of_int i)
        else i
      end
      else if h = "auipc" || h = "lui" then begin
        if i > 1048575 || i < -1048576 
        then failwith ("Immediate Error : AUIPC/LUI immediates must be between -1048576 and 1048575 : " ^ string_of_int i)
        else i
      end
      else i (* for JALR immediate *)
    end

let check_reg reg = 
  if List.mem reg c_REGISTERS then reg 
  else failwith ("Parse Error : Register not recognized : " ^ reg)

let choose_op_reg_imm h rd rs1 imm = 
  if h = "addi" then Addi (rd, rs1, imm)
  else if h = "andi" then Andi (rd, rs1, imm)
  else if h = "ori" then Ori (rd, rs1, imm)
  else if h = "xori" then Xori (rd, rs1, imm)
  else if h = "slti" then Slti (rd, rs1, imm)
  else if h = "sltiu" then Sltiu (rd, rs1, imm)
  else if h = "slli" then Slli (rd, rs1, imm)
  else if h = "srli" then Srli (rd, rs1, imm)
  else if h = "srai" then Srai (rd, rs1, imm)
  else failwith ("Opcode Error : " ^ h)

let match_reg_imm h t = 
  match t with 
  | [] -> failwith "Parse Error : No args specified"
  | rd :: rs1 :: imm :: [] -> 
    let rd' = check_reg rd in 
    let rs1' = check_reg rs1 in 
    let imm' = check_imm h imm in 
    choose_op_reg_imm h rd' rs1' imm'
  | rd :: rs1 :: imm :: t -> failwith "Parse Error : Too many args"
  | _ -> failwith "Parse Error : Too few args"

let choose_op_reg_reg h rd rs1 rs2 = 
  if h = "add" then Add (rd, rs1, rs2)
  else if h = "and" then And (rd, rs1, rs2)
  else if h = "or" then Or (rd, rs1, rs2)
  else if h = "xor" then Xor (rd, rs1, rs2)
  else if h = "slt" then Slt (rd, rs1, rs2)
  else if h = "sltu" then Sltu (rd, rs1, rs2)
  else if h = "sll" then Sll (rd, rs1, rs2)
  else if h = "srl" then Srl (rd, rs1, rs2)
  else if h = "sra" then Sra (rd, rs1, rs2)
  else if h = "sub" then Sub (rd, rs1, rs2)
  else failwith ("Opcode Error : " ^ h)

let match_reg_reg h t = 
  match t with 
  | [] -> failwith "Parse Error : No args specified"
  | rd :: rs1 :: rs2 :: [] ->
    let rd' = check_reg rd in 
    let rs1' = check_reg rs1 in 
    let rs2' = check_reg rs2 in 
    choose_op_reg_reg h rd' rs1' rs2'
  | rd :: rs1 :: imm :: t -> failwith "Parse Error : Too many args"
  | _ -> failwith "Parse Error : Too few args"

let match_label h = 
  if String.get h (String.length h - 1) = c_COLON(* last character of label must be colon *)
  then begin
    (* must remove colon so that jumps and branches can work by comparing strings directly *)
    let removed_colon_str = String.sub h 0 (String.length h - 1) in 
    Label (removed_colon_str)
  end
  else failwith ("Parse Error : label must end in colon : " ^ h)

let match_auipc h1 h2 h3 = 
  let rd' = check_reg h2 in 
  let imm' = check_imm h1 h3 in 
  Auipc (rd', imm')

let match_lui h1 h2 h3 = 
  let rd' = check_reg h2 in 
  let imm' = check_imm h1 h3 in 
  Lui (rd', imm')

let check_label label = 
  if String.contains label c_COLON then failwith ("Parse Error : Label cannot have colon : " ^ label)
  else label

let choose_op_branch h rs1 rs2 label = 
  if h = "beq" then Beq (rs1, rs2, label)
  else if h = "bne" then Bne (rs1, rs2, label)
  else if h = "bge" then Bge (rs1, rs2, label)
  else if h = "bgeu" then Bgeu (rs1, rs2, label)
  else if h = "blt" then Blt (rs1, rs2, label)
  else if h = "bltu" then Bltu (rs1, rs2, label)
  else failwith ("Opcode Error : " ^ h)

let match_branch h t = 
  match t with 
  | [] -> failwith "Parse Error : No args specified"
  | rs1 :: rs2 :: label :: [] ->
    let rs1' = check_reg rs1 in 
    let rs2' = check_reg rs2 in 
    let label' = check_label label in
    choose_op_branch h rs1' rs2' label'
  | rd :: rs1 :: imm :: t -> failwith "Parse Error : Too many args"
  | _ -> failwith "Parse Error : Too few args"

let match_jal h1 h2 h3 = 
  let rd' = check_reg h2 in 
  let label' = check_label h3 in 
  Jal (rd', label')

let convert_string_lst_to_riscv str_lst = 
  match str_lst with 
  | [] -> failwith "Parse Error : No op or args specified"
  | h :: [] -> match_label h
  | h1 :: h2 :: h3 :: [] -> begin
      if h1 = "auipc" then match_auipc h1 h2 h3
      else if h1 = "lui" then match_lui h1 h2 h3
      else if h1 = "jal" then match_jal h1 h2 h3
      else failwith ("Parse Error : Unsupported Op " ^ h1)
    end
  | h :: t -> begin 
      if List.mem h c_REG_IMM then match_reg_imm h t
      else if List.mem h c_REG_REG then match_reg_reg h t
      else if List.mem h c_BRANCH then match_branch h t
      else failwith ("Parse Error : Unsupported Op " ^ h)
    end

let rec parse acc cleaned_str_lst  = 
  match cleaned_str_lst with 
  | [] -> List.rev acc 
  | inner_str_lst :: t -> begin
      parse (convert_string_lst_to_riscv inner_str_lst :: acc) t
    end 

let main_parse str_lst = 
  str_lst 
  |> clean_strings
  |> parse []

(* ######### BACK END EVALUATION ############# *)

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

let beq = 
  fun a b -> a = b 

let bne = 
  fun a b -> a <> b

let bge = 
  fun a b -> a >= b

let bgeu = 
  fun a b -> abs a >= abs b

let blt = 
  fun a b -> a < b 

let bltu = 
  fun a b -> abs a < abs b

(* In Little Endian order *)
let rec dec_to_base_2 acc dec = 
  if dec < 0 then failwith "Base 10 number must be non-negative"
  else 
    let dec' = dec / 2 in 
    let rem = dec mod 2 in 
    if dec' = 0 then List.rev (dec :: acc)
    else dec_to_base_2 (rem :: acc) dec'

let rec pad_two_32_helper lst len = 
  if len = 0 then lst 
  else pad_two_32_helper (1 :: lst) (len - 1)

(** Requires: [lst] is in little endian order *)
let pad_two_32 lst = 
  let len = List.length lst in 
  let rem = 32 - len in 
  List.rev (pad_two_32_helper (List.rev lst) rem)

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

let c_2_TO_32 = 
  let twos_list = pad_two_32 [] in 
  List.fold_left ( * ) 1 twos_list

(* takes in Little endian, returns base 10 *)
(* raises non empty argument with AssertionError *)
let convert_to_base_10 lst = 
  assert (lst <> []);
  if lst |> List.rev |> List.hd = 1 then 
    let rev_tail = lst |> List.rev |> List.tl in 
    let positive_part = 
      List.fold_left (fun acc elt -> 2 * acc + elt) 0 rev_tail in 
    let negative_part = -1 * c_2_TO_32 in 
    positive_part + negative_part (* 2's complement negative *)
  else
    List.fold_left (fun acc elt -> 2 * acc + elt) 0 (List.rev lst)

let c_ZERO_BASE_2 = [0; 0; 0; 0; 0; 0; 0; 0]

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

let search_address ram address = 
  match Hashtbl.find_opt ram address with 
  | None -> c_ZERO_BASE_2
  | Some lst -> lst

let rec add_pc_to_instruction instr_list pc acc = 
  match instr_list with 
  | [] -> List.rev acc 
  | h :: t ->
    add_pc_to_instruction t (pc + 4) ((pc, h) :: acc)

let remove_pc_from_instruction pc_instr_list = 
  List.map (fun (_, expr) -> expr) pc_instr_list

let rec jump_to_label instr_list label_name = 
  match instr_list with 
  | [] -> failwith "The label you requested is not in the series of instructions you gave. The Jump failed. "
  | (_, h) :: t -> begin 
      match h with 
      | Label name -> begin
          if name = label_name then instr_list
          else jump_to_label t label_name
        end
      | _ -> jump_to_label t label_name
    end 

let rec get_label_pc instr_list label_name = 
  match instr_list with 
  | [] -> failwith "The label you requested is not in the series of instructions you gave. Could not get PC. "
  | (pc, h) :: t -> begin
      match h with 
      | Label name -> begin 
          if name = label_name then pc 
          else get_label_pc t label_name
        end
      | _ -> get_label_pc t label_name
    end

let rec jump_to_pc instr_list pc = 
  match instr_list with 
  | [] -> failwith "The pc number you requested is not in the series of instructions you gave. Possibly, your PC was halfword aligned but not word aligned. The Jump failed. "
  | (num, _) :: t -> begin 
      if num = pc then instr_list 
      else jump_to_pc t pc
    end

let print_registers rf = 
  Hashtbl.iter (fun k v -> (k ^ " : " ^ string_of_int v) |> print_endline; print_newline ()) rf

let mem_to_dec lst = 
  lst |> sign_extend |> convert_to_base_10

let print_memory ram = 
  Hashtbl.iter (fun k v -> (k ^ " : " ^ string_of_int (mem_to_dec v)) |> print_endline; print_newline ()) ram

let rec eval_table_a expr_lst rf ram pc instr_lst =
  match expr_lst with 
  | [] -> print_endline "Finished interpretation"; ()

  | Add (rd, rs1, rs2) :: t -> eval_reg_reg rd rs1 rs2 rf ram (+); eval_table_a t rf ram (pc + 4) instr_lst
  | Addi (rd, rs1, imm) :: t -> eval_reg_imm rd rs1 imm rf ram (+); eval_table_a t rf ram (pc + 4) instr_lst
  | Sub (rd, rs1, rs2) :: t -> eval_reg_reg rd rs1 rs2 rf ram (-); eval_table_a t rf ram (pc + 4) instr_lst

  | And (rd, rs1, rs2) :: t -> eval_reg_reg rd rs1 rs2 rf ram (land); eval_table_a t rf ram (pc + 4) instr_lst
  | Andi (rd, rs1, imm) :: t -> eval_reg_imm rd rs1 imm rf ram (land); eval_table_a t rf ram (pc + 4) instr_lst
  | Or (rd, rs1, rs2) :: t -> eval_reg_reg rd rs1 rs2 rf ram (lor); eval_table_a t rf ram (pc + 4) instr_lst
  | Ori (rd, rs1, imm) :: t -> eval_reg_imm rd rs1 imm rf ram (lor); eval_table_a t rf ram (pc + 4) instr_lst
  | Xor (rd, rs1, rs2) :: t -> eval_reg_reg rd rs1 rs2 rf ram (lxor); eval_table_a t rf ram (pc + 4) instr_lst
  | Xori (rd, rs1, imm) :: t -> eval_reg_imm rd rs1 imm rf ram (xori_helper); eval_table_a t rf ram (pc + 4) instr_lst

  | Sll (rd, rs1, rs2) :: t -> eval_reg_reg rd rs1 rs2 rf ram (lsl); eval_table_a t rf ram (pc + 4) instr_lst
  | Slli (rd, rs1, imm) :: t -> eval_reg_imm rd rs1 imm rf ram (lsl); eval_table_a t rf ram (pc + 4) instr_lst
  | Srl (rd, rs1, rs2) :: t -> eval_reg_reg rd rs1 rs2 rf ram (lsr); eval_table_a t rf ram (pc + 4) instr_lst
  | Srli (rd, rs1, imm) :: t -> eval_reg_imm rd rs1 imm rf ram (lsr); eval_table_a t rf ram (pc + 4) instr_lst
  | Sra (rd, rs1, rs2) :: t -> eval_reg_reg rd rs1 rs2 rf ram (asr); eval_table_a t rf ram (pc + 4) instr_lst
  | Srai (rd, rs1, imm) :: t -> eval_reg_imm rd rs1 imm rf ram (asr); eval_table_a t rf ram (pc + 4) instr_lst

  | Lui (rd, imm) :: t -> eval_lui rd imm rf ram; eval_table_a t rf ram (pc + 4) instr_lst
  | Auipc (rd, imm) :: t -> eval_auipc rd imm pc rf ram; eval_table_a t rf ram (pc + 4) instr_lst

  | Slt (rd, rs1, rs2) :: t -> eval_reg_reg rd rs1 rs2 rf ram (slt_helper); eval_table_a t rf ram (pc + 4) instr_lst
  | Slti (rd, rs1, imm) :: t -> eval_reg_imm rd rs1 imm rf ram (slt_helper); eval_table_a t rf ram (pc + 4) instr_lst
  | Sltu (rd, rs1, rs2) :: t -> eval_sltu rd rs1 rs2 rf ram; eval_table_a t rf ram (pc + 4) instr_lst
  | Sltiu (rd, rs1, imm) :: t -> eval_reg_imm rd rs1 imm rf ram (sltiu_helper); eval_table_a t rf ram (pc + 4) instr_lst

  | Label (name) :: t -> eval_table_a t rf ram (pc + 4) instr_lst

  | _ :: t -> print_endline "Not a Table A operation : Will Not Be Executed"; eval t rf ram (pc + 4) instr_lst

and eval expr_lst rf ram pc instr_lst = 
  match expr_lst with 
  | [] -> print_endline "Finished interpretation"; ()

  | Add (rd, rs1, rs2) :: t -> eval_reg_reg rd rs1 rs2 rf ram (+); eval t rf ram (pc + 4) instr_lst
  | Addi (rd, rs1, imm) :: t -> eval_reg_imm rd rs1 imm rf ram (+); eval t rf ram (pc + 4) instr_lst
  | Sub (rd, rs1, rs2) :: t -> eval_reg_reg rd rs1 rs2 rf ram (-); eval t rf ram (pc + 4) instr_lst

  | And (rd, rs1, rs2) :: t -> eval_reg_reg rd rs1 rs2 rf ram (land); eval t rf ram (pc + 4) instr_lst
  | Andi (rd, rs1, imm) :: t -> eval_reg_imm rd rs1 imm rf ram (land); eval t rf ram (pc + 4) instr_lst
  | Or (rd, rs1, rs2) :: t -> eval_reg_reg rd rs1 rs2 rf ram (lor); eval t rf ram (pc + 4) instr_lst
  | Ori (rd, rs1, imm) :: t -> eval_reg_imm rd rs1 imm rf ram (lor); eval t rf ram (pc + 4) instr_lst
  | Xor (rd, rs1, rs2) :: t -> eval_reg_reg rd rs1 rs2 rf ram (lxor); eval t rf ram (pc + 4) instr_lst
  | Xori (rd, rs1, imm) :: t -> eval_reg_imm rd rs1 imm rf ram (lxor); eval t rf ram (pc + 4) instr_lst

  | Sll (rd, rs1, rs2) :: t -> eval_reg_reg rd rs1 rs2 rf ram (lsl); eval t rf ram (pc + 4) instr_lst
  | Slli (rd, rs1, imm) :: t -> eval_reg_imm rd rs1 imm rf ram (lsl); eval t rf ram (pc + 4) instr_lst
  | Srl (rd, rs1, rs2) :: t -> eval_reg_reg rd rs1 rs2 rf ram (lsr); eval t rf ram (pc + 4) instr_lst
  | Srli (rd, rs1, imm) :: t -> eval_reg_imm rd rs1 imm rf ram (lsr); eval t rf ram (pc + 4) instr_lst
  | Sra (rd, rs1, rs2) :: t -> eval_reg_reg rd rs1 rs2 rf ram (asr); eval t rf ram (pc + 4) instr_lst
  | Srai (rd, rs1, imm) :: t -> eval_reg_imm rd rs1 imm rf ram (asr); eval t rf ram (pc + 4) instr_lst

  | Lui (rd, imm) :: t -> eval_lui rd imm rf ram; eval t rf ram (pc + 4) instr_lst
  | Auipc (rd, imm) :: t -> eval_auipc rd imm pc rf ram; eval t rf ram (pc + 4) instr_lst

  | Slt (rd, rs1, rs2) :: t -> eval_reg_reg rd rs1 rs2 rf ram (slt_helper); eval t rf ram (pc + 4) instr_lst
  | Slti (rd, rs1, imm) :: t -> eval_reg_imm rd rs1 imm rf ram (slt_helper); eval t rf ram (pc + 4) instr_lst
  | Sltu (rd, rs1, rs2) :: t -> eval_sltu rd rs1 rs2 rf ram; eval t rf ram (pc + 4) instr_lst
  | Sltiu (rd, rs1, imm) :: t -> eval_reg_imm rd rs1 imm rf ram (sltiu_helper); eval t rf ram (pc + 4) instr_lst

  | Label (name) :: t -> eval t rf ram (pc + 4) instr_lst

  | Lw (rd, rs1, imm) :: t -> eval_lw rd rs1 imm rf ram; eval t rf ram (pc + 4) instr_lst
  | Sw (rs1, rs2, imm) :: t -> eval_sw rs1 rs2 imm rf ram; eval t rf ram (pc + 4) instr_lst

  | Lb (rd, rs1, imm) :: t -> eval_lb rd rs1 imm rf ram; eval t rf ram (pc + 4) instr_lst
  | Sb (rs1, rs2, imm) :: t -> eval_sb rs1 rs2 imm rf ram; eval t rf ram (pc + 4) instr_lst

  | Jal (rd, label) :: t -> eval_jal rd label rf ram pc instr_lst
  | Jalr (rd, rs1, imm) :: t -> eval_jalr rd rs1 imm rf ram pc instr_lst

  | Beq (rs1, rs2, name) :: t -> eval_branch rs1 rs2 name t rf ram pc instr_lst beq
  | Bne (rs1, rs2, name) :: t -> eval_branch rs1 rs2 name t rf ram pc instr_lst bne
  | Blt (rs1, rs2, name) :: t -> eval_branch rs1 rs2 name t rf ram pc instr_lst blt
  | Bge (rs1, rs2, name) :: t -> eval_branch rs1 rs2 name t rf ram pc instr_lst bge
  | Bltu (rs1, rs2, name) :: t -> eval_branch rs1 rs2 name t rf ram pc instr_lst bltu
  | Bgeu (rs1, rs2, name) :: t -> eval_branch rs1 rs2 name t rf ram pc instr_lst bgeu

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
  else begin
    let s1 = search_address ram address in 
    let s2 = search_address ram (address + 1) in 
    let s3 = search_address ram (address + 2) in 
    let s4 = search_address ram (address + 3) in 
    let list_32 = s1 @ s2 @ s3 @ s4 in 
    let dec = convert_to_base_10 list_32 in 
    Hashtbl.add rf rd dec
  end

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

and eval_jal rd label rf ram pc instr_lst = 
  let () = Hashtbl.add rf rd (pc + 4) in 
  let expr_lst' = 
    label |> jump_to_label instr_lst |> remove_pc_from_instruction in 
  let pc' = 
    label |> get_label_pc instr_lst in 
  eval expr_lst' rf ram pc' instr_lst

and eval_jalr rd rs1 imm rf ram pc instr_lst = 
  let () = Hashtbl.add rf rd (pc + 4) in 
  let a = Hashtbl.find rf rs1 in 
  let res = a + imm in 
  let half_word_pc = (res / 2) * 2 in (* integer divide removes remainder part, then mult by 2 *)
  let expr_lst' = half_word_pc |> jump_to_pc instr_lst |> remove_pc_from_instruction in 
  let pc' = 
    half_word_pc in 
  eval expr_lst' rf ram pc' instr_lst

and eval_branch rs1 rs2 label expr_lst rf ram pc instr_lst op = 
  let a = Hashtbl.find rf rs1 in 
  let b = Hashtbl.find rf rs2 in 
  if op a b then begin
    let expr_lst' = 
      label |> jump_to_label instr_lst |> remove_pc_from_instruction in 
    let pc' = 
      label |> get_label_pc instr_lst in 
    eval expr_lst' rf ram pc' instr_lst
  end
  else begin
    eval expr_lst rf ram (pc + 4) instr_lst
  end

let main_eval expr_lst = 
  let () = print_endline "Do you want only Table A instructions to be executed?" in 
  let res = () |> read_line |> String.lowercase_ascii |> String.trim in 
  let table_a_only = res = "yes" || res = "true" in
  let instr_lst = add_pc_to_instruction expr_lst 0 [] in
  let pc = 0 in 
  if table_a_only then eval_table_a expr_lst reg_file ram pc instr_lst 
  else eval expr_lst reg_file ram pc instr_lst

(* ######### MAIN PROGRAM ######### *)
let main = 
  ()
  |> main_read_file
  |> main_parse
  |> main_eval










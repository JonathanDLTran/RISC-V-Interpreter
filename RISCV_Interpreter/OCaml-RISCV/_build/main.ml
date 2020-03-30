type riscv = 
  | Add of string * string * string
  | Addi of string * string * int
  | Sub of string * string * string 
  | Auipc of string * string * int
  | And of string * string * string
  | Andi of string * string * int
  | Or of string * string * string
  | Ori of string * string * int
  | Xor of string * string * string
  | Xori of string * string * int
  | Slt of string * string * string
  | Slti of string * string * int
  | Sltu of string * string * string
  | Sltiu of string * string * int
  | Sll of string * string * string
  | Slli of string * string * int
  | Srl of string * string * string
  | Srli of string * string * int
  | Sra of string * string * string
  | Srai of string * string * int
  | Lui of string * int
  | Jal of string * string (* First argument is the save register, second is the label location *)
  | Jalr of string * string * int (* first argument is save register, second is register for jump location, int is immediate offset *)
  | Beq of string * string * string (* Where the last string is the label location to jump to *)
  | Bne of string * string * string
  | Blt of string * string * string
  | Bge of string * string * string
  | Bltu of string * string * string
  | Bgeu of string * string * string
  | Lw of string * string * int
  | Lb of string * string * int
  | Sw of string * string * int
  | Sb of string * string * int
  | Label of string


let reg = Hashtbl.create 10000

let () = Hashtbl.add reg 2 3
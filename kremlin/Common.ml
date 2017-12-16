type calling_convention =
  | StdCall
  | CDecl
  | FastCall
  [@@deriving show { with_path = false }]

type lifetime =
  | Eternal
  | Stack
  [@@deriving show { with_path = false }]

type flag =
  | Private
  | NoExtract
  | CInline
  | Substitute
  | GcType
  | Comment of string
  [@@deriving show { with_path = false }]

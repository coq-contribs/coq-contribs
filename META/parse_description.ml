
(* description.ml *)

(* A record type corresponding to a description file *)

type author =
    { author : string;
      email : string;
      homepage : string;
      institution : string;
      address : string
    }

type description =
    { name  : string;
      title : string;
      authors : author list;
      date : string list;
      description : string;
      url : string;
      keywords : string list;
      categories : string list;
      require : string list;
      license : string
    }

(* Transforming association list into a record *)

let split_words = Str.split (Str.regexp "[ \t\n]+")

let first_word s = match split_words s with f::_ -> f | _ -> ""

let split_group = Str.split (Str.regexp ",[ \t\n]*")

let standardize_typography s =
  (* ensure at most one space after a period *)
  Str.global_replace (Str.regexp "\\. +") ". " s 

let rec get_optional acc fl = function
  | (f,_ as x)::l when List.mem f fl -> get_optional (x::acc) fl l
  | l -> (List.rev acc,l)

let get_field_group f =
  List.fold_left (fun acc (f',s) -> if f=f' then List.flatten (List.map split_group s) @ acc else acc) []

let get_field_line f l =
  String.concat " " (List.fold_left (fun acc (f',s) -> if f=f' then s @ acc else acc) [] l)

let get_field_block f l =
  String.concat "\n" (List.fold_left (fun acc (f',s) -> if f=f' then List.map standardize_typography s @ acc else acc) [] l)

let rec get_fields acc f optf = function
  | [] -> List.rev acc
  | (f',s)::l when f=f' -> 
      let fl,l = get_optional [] optf l in
      let os = List.map (fun x -> get_field_line x fl) optf in
      let s = String.concat " " s in
      let acc = if s="" && List.for_all ((=) "") os then acc else (s,os)::acc in
      get_fields acc f optf l
  | _::l -> get_fields acc f optf l

let exclude_none = function
  | ["None"|"none"] -> []
  | l -> l

let complete_institution = function
  | [] -> []
  | l ->
    let l = List.rev l in
    let { institution = i; address = d } = List.hd l in
    let (_,_,l) = 
      List.fold_left (fun (i,d,acc) a ->
	let { institution = i'; address = d' } = a in
	if i'="" && d' = "" then (i,d, { a with institution=i; address=d }::acc)
	else (i',d',a :: acc)) (i,d,[List.hd l]) (List.tl l) in
    l

let description_of_raw l =
  let get_field_group f = get_field_group f l in
  let get_field_block f = get_field_block f l in
  let get_field_line f = get_field_line f l in
  let get_fields1 f1 = List.map fst (get_fields [] f1 [] l) in
  let authors =
    List.map (fun (s,l) ->
      { author = s;
        email = List.nth l 0;
	homepage = List.nth l 1;
	institution = List.nth l 2;
	address = List.nth l 3
      })
      (get_fields [] "Author" ["Email";"Homepage";"Institution";"Address"] l)
  in
  { name  = first_word (get_field_line "Name");
    title = get_field_line "Title";
    authors = complete_institution authors;
    date = get_fields1 "Date";
    description = get_field_block "Description";
    url = get_field_line "Url";
    keywords = get_field_group "Keywords";
    categories = get_fields1 "Category";
    require = exclude_none (get_field_group "Require");
    license = get_field_block "License";
  }


(* Reading description file *)

(* An identifier followed by ":", possibly preceded by spaces *)
let is_field = Str.regexp "^\\([A-Za-z_]*\\)[ \t]*:[ \t]*"

let is_blank c = (c = ' ' || c = '\t')

let strip_trailing_white line =
  let j = ref (String.length line - 1) in
  while !j >= 0 && is_blank line.[!j] do decr j done;
  if !j <> String.length line - 1 then String.sub line 0 (!j + 1)
  else line

let strip_white line =
  let i = ref 0 in
  while String.length line > !i && is_blank line.[!i] do incr i done;
  let j = ref (String.length line - 1) in
  while !j >= 0 && is_blank line.[!j] do decr j done;
  if !i <> 0 || !j <> String.length line - 1 then String.sub line !i (!j + 1 - !i)
  else line

let rec drop_trailing_empty_lines = function
  | "" :: l -> drop_trailing_empty_lines l
  | l -> l

let unindent = function
  | [] -> []
  | line :: rest as block ->
    let rec aux n =
      if
        String.length line > n &&
        let c = line.[n] in
        is_blank c &&
        List.for_all (fun line -> String.length line <= n || line.[n] = c) rest
      then
        (* We found a common blank prefix *)
        aux (n+1)
      else
        if n = 0 then block else
          List.map (fun line ->
              if String.length line > n then String.sub line n (String.length line - n)
              else "") block
    in aux 0

let push_field_content fieldcontents acc =
  match fieldcontents with
  | Some (field,head,rest) ->
    (* We drop trailing empty lines *)
    let rest = List.rev (drop_trailing_empty_lines rest) in
    (* We globally unindent if any global indent *)
    let rest = unindent rest in
    (* We add the heading line *)
    (field,if head="" then rest else head::rest)::acc
  | None ->
    (* begin of file *)
    acc

let read_description chan =
  let rec read_fields fieldcontents acc =
    try
      let s = input_line chan in
      if Str.string_match is_field s 0 then
        (* Pushing the content of the field *)
        let acc = push_field_content fieldcontents acc in
        (* Initiating reading of the new field *)
	let field = Str.matched_group 1 s in
	let content = Str.string_after s (Str.match_end()) in
	read_fields (Some (field,strip_white content,[])) acc
      else
        match fieldcontents with
        | Some (field,head,contents) ->
          (* field spans over several lines, we preserve the space layout (but trailing spaces) *)
          read_fields (Some (field,head,strip_trailing_white s::contents)) acc
        | None -> (* begin of file *)
          if strip_white s = "" then
            (* skipping empty line at the beginning *)
            read_fields None acc
          else
            failwith "File not starting with a field"
    with End_of_file ->
      List.rev (push_field_content fieldcontents acc)
  in
    description_of_raw (read_fields None [])

let read_all_descriptions directory =
  let dir = Unix.opendir directory in
  let rec read acc =
     try
       let f = Unix.readdir dir in
	 if Filename.check_suffix f ".description" then
           let chan = open_in (Filename.concat directory f) in
	   let d = read_description chan in
           close_in chan;
	   read (d::acc)
	 else
	   read acc
     with End_of_file -> Unix.closedir dir; acc
  in
    read []

(* sorting *)

let sort_descriptions l =
  List.sort (fun d1 d2 -> Pervasives.compare d1.name d2.name) l

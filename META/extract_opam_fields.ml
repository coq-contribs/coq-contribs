open Parse_description

(* exporting *)

let quote s = "\"" ^ s ^ "\""
let surround s = "(" ^ s ^ ")"
let anglebracket s = "<" ^ s ^ ">"
let squarebracket s = "[" ^ s ^ "]"

let make_author a =
  let author_fields = 
    (if a.author = "" then [] else [a.author])@
(*    (if a.institution = "" then [] else [surround a.institution])@ *)
    (if a.email = "" then [] else [anglebracket a.email])@
    (if a.homepage = "" then [] else [squarebracket a.homepage]) in
  quote (String.concat " " author_fields)
                  
let description_to_opam_fields f f' d =
  let keywords = List.map (fun s -> quote ("keyword: " ^ s)) d.keywords in
  let categories = List.map (fun s -> quote ("category: " ^ s)) d.categories in
  let date = List.map (fun s -> quote ("date: " ^ s)) d.date in
  let authors = String.concat " " (List.map make_author d.authors) in
  Printf.fprintf f "name=%s\n" d.name;
  Printf.fprintf f "tags=%s\n" (String.concat " " (keywords@categories@date));
  Printf.fprintf f "authors=%s\n" authors;
  Printf.fprintf f "license=%s\n" d.license;
  Printf.fprintf f' "<<%s>>" d.title;
  if d.description <> "" then Printf.fprintf f' "@%s@\n@\n@" d.description

let is_uppercase c = 'Z' >= c && c >= 'A'
let lowercase c = if is_uppercase c then Char.chr (Char.code c + 32) else c

let lower name =
  (* This is a heuristic: CoRN -> corn; MapleMode -> maple-mode *)
  let b = Buffer.create (String.length name) in
  for i = 0 to String.length name - 1 do
    let c = name.[i] in
    if
      is_uppercase c && i > 0 &&
      not (is_uppercase name.[i-1]) &&
      i < String.length name - 1 && not (is_uppercase name.[i+1])
    then
      Buffer.add_char b '-';
    Buffer.add_char b (lowercase c)
  done;
  Buffer.contents b

let adjust_license fields license =
  if fields.license = "" then { fields with license }
  else if Str.string_match (Str.regexp_string fields.license) license 0 then
    fields
  else
    failwith ("Mismatch between license in description file ("^fields.license^") and expected license ("^license^")")

let adjust_name fields installdir =
  if installdir <> "" then begin
      if installdir <> fields.name then
        Printf.printf "Warning: installation dir (%s) differs from name (%s); using the former.\n" installdir fields.name;
      { fields with name = installdir }
    end
  else
    fields

let drop_period s =
  if s.[String.length s - 1] = '.' then String.sub s 0 (String.length s - 1) else s

let description_to_opam_files opam descr packagename d maj med =
  let keywords = List.map (fun s -> quote ("keyword: " ^ s)) d.keywords in
  let categories = List.map (fun s -> quote ("category: " ^ s)) d.categories in
  let date = List.map (fun s -> quote ("date: " ^ s)) d.date in
  Printf.fprintf opam "opam-version: \"1.2\"\n";
  Printf.fprintf opam "maintainer: \"Hugo.Herbelin@inria.fr\"\n";
  Printf.fprintf opam "homepage: \"https://github.com/coq-contribs/%s\"\n" packagename;
  Printf.fprintf opam "license: \"%s\"\n" (if d.license = "" then "Unknown" else d.license);
  Printf.fprintf opam "build: [make \"-j%%{jobs}%%\"]\n";
  Printf.fprintf opam "install: [make \"install\"]\n";
  Printf.fprintf opam "remove: [\"rm\" \"-R\" \"%%{lib}%%/coq/user-contrib/%s\"]\n" d.name;
  Printf.fprintf opam "depends: [\n";
  Printf.fprintf opam "  \"coq\" {>= \"%d.%d\" & < \"%d.%d~\"}\n" maj med maj (med+1);
  List.iter (fun s -> Printf.fprintf opam "  \"coq-%s\" {>= \"%d.%d\" & < \"%d.%d~\"}\n" (lower s) maj med maj (med+1)) d.require;
  Printf.fprintf opam "]\n";
  Printf.fprintf opam "tags: [ %s ]\n" (String.concat " " (keywords@categories@date));
  Printf.fprintf opam "authors: [ %s ]\n" (String.concat " " (List.map make_author d.authors));
  Printf.fprintf opam "bug-reports: \"https://github.com/coq-contribs/%s/issues\"\n" packagename;
  Printf.fprintf opam "dev-repo: \"https://github.com/coq-contribs/%s.git\"\n" packagename;
  Printf.fprintf descr "%s.\n" (drop_period d.title);
  if d.url <> "" then Printf.fprintf descr "\n%s\n" d.url;
  if d.description <> "" then Printf.fprintf descr "\n%s\n" d.description
  
let _ =
  if Array.length Sys.argv = 1 then
    description_to_opam_fields stdout stderr (read_description stdin)
  else if Array.length Sys.argv = 6 || Array.length Sys.argv = 7 then
    let chan = open_in Sys.argv.(1) in
    let opam = open_out "opam" in
    let descr = open_out "descr" in
    let packagename = Sys.argv.(2) in
    let major = int_of_string (Sys.argv.(3)) in
    let median = int_of_string (Sys.argv.(4)) in
    let fields = read_description chan in
    let fields = adjust_name fields Sys.argv.(5) in
    let fields = if Array.length Sys.argv = 7 then adjust_license fields Sys.argv.(6) else fields in
    description_to_opam_files opam descr packagename fields major median;
    close_in chan;
    close_out opam;
    close_out descr
  else begin
    Printf.eprintf "Usage: %s [description-file contribname major-number minor-number installdir [license]]\n" Sys.argv.(0);
    Printf.eprintf "\n";
    Printf.eprintf "If arguments are given, generates opam and descr files in current directory from description file\n";
  end

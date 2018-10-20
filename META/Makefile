all: extract-opam-description-fields

extract-opam-description-fields: parse_description.ml extract_opam_fields.ml
	ocamlopt -o $@ unix.cmxa str.cmxa parse_description.ml extract_opam_fields.ml

clean:
	-rm *.o *.cm{i,x} extract-opam-description-fields

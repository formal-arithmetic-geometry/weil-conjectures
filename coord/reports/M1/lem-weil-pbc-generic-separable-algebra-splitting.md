1. Files written:
   - `dag/nodes/sec-smooth-purity/lem-weil-pbc-generic-separable-algebra-splitting.json` (item, split)
   - `dag/nodes/sec-smooth-purity/lem-weil-pbc-finite-algebra-reduction-product-fields.json` (statement-only, Mathlib no match)
   - `citations.json`
2. Attachments: none.
3. WANTED: none.
4. No source or statement error was found. The source declaration search in `~/weil-conjectures-slopmaster2/WeilConjectures` found no declaration tagged `(blueprint: lem-weil-pbc-generic-separable-algebra-splitting)` and no sorry-free declaration with the item's statement. Whole-DAG searches found no duplicate of the new Artinian reduction statement; the existing residue-field splitting node and finite-spectrum node were reused.
5. Nothing remains unfinished.

## Not duplicates

`lem-weil-pbc-finite-algebra-reduction-product-fields` vs `lem-weil-pbc-separable-split-purely-inseparable-residue-fields`: the former decomposes one finite algebra's reduction over its original field; the latter chooses a finite separable base extension for a finite list of field extensions and controls all residue fields after tensoring.

`lem-weil-pbc-finite-algebra-reduction-product-fields` vs `lem-weil-pbc-product-ideal-closed-subscheme-union`: the new statement decomposes the reduction of a finite-dimensional algebra into finite fields; the existing node identifies a closed subscheme defined by a product ideal.
`lem-weil-pbc-finite-algebra-reduction-product-fields` vs `lem-weil-pbc-reduced-induced-closed-subscheme`: the new statement is an Artinian algebra decomposition; the existing node concerns reducedness of an induced closed subscheme.
`lem-weil-pbc-finite-algebra-reduction-product-fields` vs `lem-weil-pbc-zero-locus-eq-iff-radical-eq`: the new statement gives a product-of-fields structure; the existing node is an equality criterion for zero loci and radicals.
`lem-weil-pbc-finite-algebra-reduction-product-fields` vs `lem-weil-pbc-zero-locus-ideal-intersection`: the new statement gives field factors of a reduction; the existing node identifies an intersection of ideals from a zero locus.
`lem-weil-pbc-finite-algebra-reduction-product-fields` vs `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact`: the new statement is an algebra decomposition; the existing node is a quasi-compactness/unit-ideal result for basic opens.
`lem-weil-pbc-finite-algebra-reduction-product-fields` vs `lem-weil-pbc-span-pow-eq-top`: the new statement concerns Artinian reductions; the existing node concerns powers of an ideal whose span is top.
`lem-weil-pbc-finite-algebra-reduction-product-fields` vs `lem-weil-pbc-proper-ideal-contained-in-maximal`: the new statement gives finite field factors; the existing node only places a proper ideal inside a maximal ideal.
`lem-weil-pbc-finite-algebra-reduction-product-fields` vs `lem-weil-pbc-etale-localize-upstairs`: the new statement is a product decomposition of a finite algebra; the existing node localizes an etale morphism upstairs.
`lem-weil-pbc-finite-algebra-reduction-product-fields` vs `lem-weil-pbc-separate-image-closed-from-closed`: the new statement is ring-theoretic; the existing node separates a closed image from a closed subset topologically.
`lem-weil-pbc-finite-algebra-reduction-product-fields` vs `lem-weil-pbc-spec-localization-away-basic-open`: the new statement decomposes a reduction; the existing node identifies a basic open with a localization spectrum.
`lem-weil-pbc-finite-algebra-reduction-product-fields` vs `lem-weil-pbc-prime-contains-minimal-prime`: the new statement gives all field factors of an Artinian reduction; the existing node only asserts existence of a minimal prime inside a prime.
`lem-weil-pbc-finite-algebra-reduction-product-fields` vs `lem-weil-pbc-minimal-prime-over-proper-ideal`: the new statement is a finite product decomposition; the existing node asserts existence of a minimal prime over a proper ideal.

## Review by M1

I read the item's blueprint source at the finite-algebra calculation in `lem-weil-pbc-finite-pushforward-generic-constructible.md`, and read the full statements of every cited DAG node. The new node records the standard Artinian fact from Algebra Lemmas 00KH and 00E0. Step 1 uses exactly that decomposition and the elementary facts that a nilpotent ideal stays nilpotent after tensoring and that reduction commutes with finite products. Step 2 uses the existing node's precise hypothesis (a finite list of finite field extensions) and its conclusion (finite separable base field, finite purely inseparable residue fields). Step 3 checks the cited finite-spectrum node supplies finiteness, maximality, and nilradical intersection; the Chinese remainder identification is then the stated elementary ring argument. Step 4 only reassembles the finite products and retains the separability and purely-inseparability hypotheses. I checked the zero-algebra case and the one-factor case while reviewing the indexing. The four Mathlib searches for the item and the four searches for the new node were run with the launcher search tool and recorded verbatim, including LeanSearch unavailability.

## Second reading by M1

- Step 1: checked against Algebra Tags 00KH and 00E0 and the reduction definition; verdict correct after writing out nilpotence under tensor and componentwise nilpotence for products.
- Step 2: checked against More Morphisms Tag 02LM, proof lines 12060-12079; verdict correct.
- Step 3: checked against Algebra Tags 00E0 and 00DT and the existing finite-spectrum node; verdict correct after explicit citation of the existing CRT node.
- Step 4: checked against steps 1-3 and the item statement; verdict correct and elementary reassembly.
- New node `lem-weil-pbc-finite-algebra-reduction-product-fields`: checked on the zero algebra and one-factor field cases and against Tags 00KH and 00E0; verdict self-contained statement-only node, no duplicate found.
- Item statement: checked against the blueprint generic-fibre calculation and Tag 02LM; verdict hypotheses and conclusion agree.

Changes made: corrected `created.item`; expanded Step 1's tensor/reduction justification; cited `lem-pc-crt-ideal-quotient-product` in Step 3 and added its verbatim quote.

## Worker report

Files written: dag/nodes/sec-trace-formula/lem-trf-smooth-generic-rank-reduction.json — statement split into nine proof steps, using existing nodes only; the item is not a Mathlib leaf. Supporting sandbox files are citations.json and searches.jsonl. No new nodes, no Mathlib leaves, no unit record changes, and no Lean files.

Attachments: none. Searches for the blueprint tag, generic basis/rank and flattening in lean/WeilConjectures found no declaration stating the full item. Generic-rank and coherent integral generic-free declarations do not construct this admissible blowup or cover its universal exactness and every-fibre support clauses.

WANTED: none. The required Stacks sources are present.

The imported statement is retained. Its proof was empty. I removed no statement hypothesis or conclusion. The support convention in the item gives the empty set dimension -1; the general dimension definition uses minus infinity. The last proof step explicitly treats empty support separately, rather than identifying these conventions.

The main-20261015 proof of lem-trf-local-term-locality now follows contracting correspondences, whereas this item's recorded ancestry comes from the historical semistable-alteration/flattening expansion. I read that current proof and retained the assigned item's existing Stacks 0815 route; I changed neither the chapter nor the unit. The old finite-type quasi-coherent module is not assumed finitely presented away from U.

Nothing remains unfinished in this stage-1 split. Dry-run and delivery results are recorded below after execution.

## Not duplicates

No new nodes were created. Searches of the DAG and whole blueprint for generic free/basis, rank reduction and Tags 0811/0815 found the already existing lem-trf-generic-free-blowup and lem-trf-free-subtraction-flatness and related local variants. I cite those existing results. In particular I did not create a node duplicating the preliminary generic-free blowup, its local algebra criterion, or a separate node for the elementary proper-closed-subset dimension argument.

## Review by Q106

I read flat.tex Tag 0811 (lemma-flatten-module-pre), including all its hypotheses and proof; Tag 0815 (theorem-flatten-module), especially its third proof paragraph; and Tag 05I3 (lemma-induction-step), including the existence argument and the flat-cokernel equivalence. I also read properties.tex Tags 01PB/01PC for affine finite modules, modules.tex Tag 0H96 for finite-presentation cokernels, morphisms.tex Tags 01VB/01VF for smooth base change/flatness, the fppf-open proof, and Tag 056J for support. All are used through the existing DAG statements, not by a bare source citation. No new node needs a separate source review. I read every cited node's statement, and citations.json copies those statements verbatim so the exact interface is available step by step.

Step 1 uses lem-pc-smooth-flat for flatness and local finite presentation, lem-weil-pbc-lfp-affine-opens-finite-presentation for the finite-presentation ring-map condition, and lem-trf-generic-free-blowup for precisely the admissible blowup and surjective locally-free open. Affineness of both original schemes is supplied by the item. Flatness over U supplies flatness at its fibre generic points, so no hypothesis of 0811 is omitted.

Step 2 uses lem-trf-generic-rank-admissible-invariance for the affine flat finitely presented family, geometrically integral fibres, finite-type quasi-coherent transform and qcqs base. It uses lem-trf-module-admissible-blowup-calculus for agreement over U, lemma-nagata-admissible-blowup-over-open for the base isomorphism there, and lem-sbc-smooth-relative-dimension-permanence for the unchanged n. I checked that the invariance lemma alone asserts freeness at generic points rather than arbitrary flatness over the whole preserved open: the latter comes from agreement with the original module and the base isomorphism.

Step 3 uses the affine-open basis, the affine finite-type module criterion, stalk localization of a quasi-coherent module, and the affine tilde–global-sections adjunction. A finite list of global generators spans the generic residue vector space, so a basis can be selected from it without lifting fractions. The resulting map is defined on the whole affine source. Freeness is already known on V; the determinant of its square matrix becomes a unit at the chosen generic point, and its invertibility open gives an actual isomorphism. Thus no openness of the flat locus for a merely finite-type module is smuggled into the argument.

Step 4 uses smooth flatness/local finite presentation and the flat-lfp open-map theorem to get an open image containing the chosen base point. The affine-open basis gives a base chart contained in that image, and quasi-compactness from Step 2 selects finitely many charts. Step 5 uses the affine-intersection criterion on the quasi-separated modified base to prove U_a is quasi-compact. It does not assume arbitrary intersections of affine opens are affine.

Step 6 uses the flat affine criterion, finite-presentation affine criterion, finite generation of section modules, and the stalk localization theorem to verify every hypothesis of lem-trf-free-subtraction-flatness. Every fibre has a nonempty W_a-fibre; integrality puts its generic point there. On W_a the module is free and the family is flat, so the required generic-stalk relative flatness holds. The cited subtraction node states both universal injectivity and the flatness equivalence at every stalk, which are exactly the assertions taken from it.

Step 7 uses the full quasi-coherent cokernel-image statement, not just a definition of cokernel: it gives the quotient of affine section modules. Finite generation descends by taking images of generators. The affine sheaf/module adjunction and tilde pullback theorem identify arbitrary affine base change with scalar extension; universal injectivity is tested with the underlying base algebra as module. Localization exactness then proves sheaf exactness at every stalk. I added these comparison/exactness citations in my self-review rather than leaving the affine-to-sheaf identification implicit.

Step 8 uses the same subtraction node's stalkwise flatness equivalence, and the finite-type-source/finitely-presented-target cokernel theorem. Its hypotheses hold only on X_{U_a}, which is all the conclusion requests. Step 9 uses the support-pullback node for finite type and closed support on the actual fibre and the definitions of smooth relative dimension and Krull dimension. Because the support is proper closed in an irreducible fibre, appending the whole fibre to any chain increases its length by one. This writes out the strict dimension drop without a hidden dimension lemma.

I checked the B–E return checklist against the final split: every non-elementary external assertion has a node whose statement supplies it; quotes are literal; uses and proof_deps agree; no new statement-only placeholder restates the item; no new node can be a duplicate or an unsearched Mathlib leaf. All steps are shorter than 2000 characters. The explicit matrix, scalar-extension and chain arguments are elementary assembly from the stated interfaces, not omitted standard lemmas. The report declares the generic tools from other units in split_report.tool_uses, without writing maintainer-owned top-level tool_uses.

Small cases: if the modified base is empty, the empty finite affine cover suffices. For rank zero the free source is zero and the locally-free open has zero target, so the isomorphism condition and universal injection remain valid. If U is empty the finite-presentation/flatness assertions on it are vacuous, and the preliminary blowup lemma permits that case. If n=0 any nonempty support would yield a chain of length one in an integral zero-dimensional fibre, contradiction; hence each cokernel fibre is zero as required. The proof never uses reducedness or Noetherianity of the arbitrary base.

## Validation

The first server dry run returned one B2 wording diagnostic in Step 9 (the phrase referring to the item's convention). I replaced that phrase with the explicit assignment of dimension -1 to empty support. The next deliver.py --no-push invocation exited successfully: OK (not pushed), commit 64bfb73b20e, server preflight passed, including the required DAG and split checks. No repository check or compiler was run on this machine. A final dry run after this report update precedes direct delivery.

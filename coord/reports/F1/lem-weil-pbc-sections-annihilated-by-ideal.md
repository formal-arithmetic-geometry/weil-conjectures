# lem-weil-pbc-sections-annihilated-by-ideal

## Files

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-sections-annihilated-by-ideal.json`: split the existing 01PO statement into five proof steps; no new nodes.

## Source and statement

Read `/tmp/stacks-project/properties.tex` at `lemma-sections-annihilated-by-ideal` (Tag 01PO, lines 3754-3795) and `definition-subsheaf-sections-annihilated-by-ideal` (Tag 01PP, lines 3797-3805); checked the tags in `/tmp/stacks-project/tags/tags`. The item has exactly the source hypotheses: a scheme, a finite-type quasi-coherent ideal, and a quasi-coherent module. Its clauses (1)-(3) match 01PO; the formula in its statement expands the source's notation `I s = 0` to all restrictions. No statement change was needed. The source omits the proof of (3), so step 5 writes its finite-generator localization calculation. In the source's proof of (1), `f^m x in M'` is read as the numerator calculation `f^m y in M'` for `x=y/f^n`.

## Dependencies and split

Step 1 verifies closure under restrictions, module operations, and gluing from the sheaf-module definition. Step 2 uses the affine tilde/global-sections equivalence and the finite-type-on-affines node to identify `F'(U)` with `Ann_M(I)` and describes principal-open sections. Step 3 clears one common power of `f` for finitely many ideal generators and establishes `Ann_M(I)_f = Ann_{M_f}(I_f)`. Step 4 identifies the sheaf on a principal-open basis with the tilde sheaf of `Ann_M(I)`, proving quasi-coherence. Step 5 uses the existing tilde-stalk and open-stalk localization nodes, plus exactness of stalks for inclusion, and clears one common denominator outside the prime to establish (3). Every cited statement was checked for the clause used; `proof_deps` is their union. No existing node is being used for material available only in its proof.

The whole-blueprint searches `blueprint_refs.py search 01PO`, `search sections annihilated ideal`, and `search annihilated` found no blueprint node with this statement (`same_as=[]`). A DAG search for `01PO` and `lemma-sections-annihilated-by-ideal` found only this item and its citer. `blueprint_refs.py ancestor` gives `thm-weil-pbc-finite-etale-lifting`; its recorded step 7 is the essential-surjectivity part of the 0GS2 route, with the item reached through the `via` chain. In that chain the immediate use is step 2 of `lem-weil-pbc-coherent-generic-point-ideal-inclusion`, which needs the annihilator subsheaf to be quasi-coherent and to have its expected stalk. The `split_report.blueprint` names both places. The item is an existing node; no new blueprint `from` metadata was needed.

The existing item has three Mathlib search kinds recorded (LeanSearch, LeanFinder, source grep), with no match for the full sheaf statement. I also inspected pinned Mathlib v4.33.1 in `/tmp/mathlib-f1/Mathlib/Algebra/Category/ModuleCat/Sheaf/` and `Mathlib/AlgebraicGeometry/Modules/`: quasi-coherence and tilde constructions exist, but no annihilator subsheaf theorem. No child node or Mathlib leaf was created. In the slopmaster2 checkout `/home/ubuntu/weil-src-slopmaster2` at `71d63dcf`, searches by the node id, the 01PO tag, the natural-language terms `annihilated`, `ideal` and `sections`, and `dag/lean_names_upstream.json` found no declaration stating this item. Thus the B10 exact-match rule does not close it; its audit remains `none`.

## Checks

- B1-B10: no new node; the existing statement is self-contained, uses one TeX escape layer, names 01PO/01PP by tag and label, has `same_as=[]`, and no exact slopmaster2 declaration was found.
- C1-C8: each nontrivial step cites existing public statements; the local computations are written out, no new cross-unit proof tool was introduced, and `review_split.py` found no route error.
- D1-D5: the split proves all three clauses rather than restating them in another node. The source's omitted stalk argument is explicit.
- E1-E7: finite generation is used precisely in steps 3 and 5. For `I=0`, the empty generator family gives exponent/denominator 1 and `F'=F`; for `I=O_X`, one generator 1 gives `F'=0`; for nilpotent `f`, the fraction test still uses the localization equality criterion; for an empty scheme the affine-local and stalk claims are vacuous. No Noetherian, quasi-compact, or finite-presentation hypothesis was added.
- `python3 tools/review_split.py lem-weil-pbc-sections-annihilated-by-ideal`: PASS, zero new nodes.
- `python3 tools/check_dag.py --cycles`: zero cycles and self-loops; exit 1 for seven pre-existing unreached nodes unrelated to this item (`constructible-finite-pushforward-approximation`, `constructible-finite-pushforward-noetherian`, `constructible-approximation`, `finite-cover-killing`, `finite-stage-killing`, `prime-torsion-devissage`, `pushout-monicity`).
- `git diff --check`: PASS.

## Review by F1

I read Stacks Properties 01PO (`lemma-sections-annihilated-by-ideal`, `properties.tex` lines 3754-3795) and its 01PP definition. The item's scheme, quasi-coherent ideal and module, finite-type ideal, and three conclusions agree hypothesis by hypothesis; its restriction-wise annihilation formula makes the source's `I s = 0` precise. There are no new nodes. I checked the worker's whole-blueprint search, its `same_as=[]`, the recorded ancestor step 7 and via chain, and its slopmaster2 exact-declaration search (B1-B10).

Step 1 proves the subsheaf condition from the public sheaf-module definition. Step 2 uses the affine tilde/Gamma equivalence, the finite-type affine criterion, and tilde sections to identify the global annihilator and its principal-open sections. Step 3 spells out the finite-generator localization calculation using the module-localization definition; the common power of f is chosen after checking each generator. Step 4 compares the resulting sheaves on the principal-open basis and uses the public quasi-coherence statement for a tilde module. Step 5 applies the cited tilde-stalk and affine-open localization statements and clause (1) of module-stalk exactness to identify the inclusion as a submodule, then repeats the finite clearing calculation outside the prime. These cited statements provide the non-elementary inputs; no proof of a cited node is imported (C1-C8, D1-D5).

I tested I=0, I=O_X, empty X, and denominators that kill a numerator without being injective; the calculations still give the stated equalities. Step 5 uses only finite generation, not a Noetherian assumption. The printed source's `f^m x in M'` is a notation slip in its fraction argument; the split correctly clears the numerator. I found no correction to send back. `review_split.py` passes, and the cycle check has no cycle; its seven reachability warnings concern other nodes (E1-E7, A, F).

1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-derived-acyclic-resolution.json`: item split; no new nodes.
- `citations.json`: citation for step 2.

2. Attachments: none. No sorry-free declaration in the Lean source states this finite augmented-resolution statement exactly. The broader declarations `CategoryTheory.Functor.rightDerivedObjIsoOfResolution` and `CategoryTheory.Functor.nonempty_rightDerivedObjIso_homology_of_acyclic` concern formal cochain-complex resolutions and do not match the item's wording exactly.

3. WANTED: none.

4. What was checked: the item source is Stacks Project Derived Categories, Proposition 13.16.8 (Tag 05TA). I read the existing node `lemma-weil-pbc-leray-acyclicity`; its clause 2 explicitly states that an augmented resolution by $v$-acyclic objects has cohomology canonically isomorphic to $R^qv(F)$, including the comparison map to an injective resolution. Step 1 checks that the finite exact augmented complex can be extended by zero terms, preserving exactness and acyclicity. Step 2 applies precisely that cited statement and identifies the resulting infinite-complex cohomology with the finite displayed complex because all later terms are zero. The cited node therefore says exactly what step 2 takes from it. The existing lemma is in another unit and is declared as a tool use because it is a generic criterion not supplied by this unit's route; no duplicate child node was created. Small cases checked conceptually: $n=0$ gives $v(M)\\cong R^0v(M)$, and appending zero terms does not change any cohomology group.

## Review by J1

I checked the item against Tag 05TA and the source's bounded-below acyclic-resolution formulation. I opened the full statement of `lemma-weil-pbc-leray-acyclicity` and verified that its clause 2 includes the exactness, bounded-below condition, termwise $v$-acyclicity, canonical comparison map, and conclusion used in step 2. Step 1 is elementary padding by zero objects; step 2 is the only non-elementary inference and cites that node verbatim in `citations.json`. The hypotheses on abelian categories, enough injectives, left exact additivity, and acyclicity are already introduced in the item and match the cited criterion. I searched the DAG and blueprint for Tag 05TA and acyclic-resolution language before deciding that the existing general criterion makes a new node a duplicate. Mathlib searches were run with LeanFinder, Loogle, grep, and LeanSearch; only generic `rightDerived` declarations appeared, with no Mathlib acyclic-resolution criterion (LeanSearch was unavailable). No statement or proof correction was needed beyond making the finite-to-bounded-below padding explicit.

## Second reading by J1

- Item statement: checked against Stacks Tag 05TA, Proposition 13.16.8, hypothesis by hypothesis; zero-padding makes the finite complex bounded below and termwise acyclic.
- New nodes: none; the cited existing Leray acyclicity node states the comparison used by step 2.
- Step 1: checked against the bounded-below construction in Tag 05TA; appending zero objects preserves exactness and acyclicity, so the elementary marking is appropriate.
- Step 2: checked against clause 2 of `lemma-weil-pbc-leray-acyclicity`; its hypotheses match the padded resolution, and zero terms after degree $n$ identify the finite and infinite cohomology complexes.
- Existing-node search: searched the DAG for Tag 05TA and acyclic-resolution terminology; the imported Leray criterion is the general node, so no duplicate child is needed.
- Mathlib search: reran LeanFinder, Loogle, and grep through `msearch.py`; only generic `rightDerived` declarations were found, with no exact finite acyclic-resolution theorem. LeanSearch was unavailable.
- Small cases: checked $n=0$, the zero object, and the zero functor; these give the expected degree-zero comparison and vanishing higher cohomology.
- Changes: no mathematical correction was needed; the fresh search records and this second-reading section were added, and the split metadata was checked for correct item attribution.

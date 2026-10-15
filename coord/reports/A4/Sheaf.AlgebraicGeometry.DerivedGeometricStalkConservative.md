## What changed

Proved `AlgebraicGeometry.Scheme.isIso_iff_isIso_geometricStalk_homologyMap` in
`Sheaf.AlgebraicGeometry.DerivedGeometricStalkConservative` without changing its signature.
The forward direction uses preservation of isomorphisms by cohomology and stalk functors.
The reverse direction applies Mathlib `DerivedCategory.Plus.isIso_iff`, then the proved
`Scheme.isIso_of_isIso_sheafFiber_map` to each cohomology map. Its stalk family is universe
lifted, so `Point.uliftSheafFiberIso` and `NatIso.isIso_map_iff` transfer the hypothesis at
`AlgebraicClosure (T.residueField s)` and `T.algClosurePoint s` to exactly that family.

Replaced the private proof import of `Mathlib.Algebra.Homology.DerivedCategory.Fractions`
with `Mathlib.Algebra.Homology.DerivedCategory.Plus` and removed the private proof import
of `WeilConjectures.AlgebraicGeometry.EtaleSheaves`. Retained both public imports.
Updated only `proof`, `proof_deps`, and `proof_origin` of the existing DAG node to describe
this route. The existing Mathlib leaf `lem-weil-pbc-derived-plus-iso-on-cohomology` supplies
the cohomology criterion. The unit record has no realizations attached to this auxiliary
node; its statement and steps are unchanged.

The final module compiled cleanly through `lcompile.py` in 1.8 seconds. A separate
`#print axioms` check reported exactly `propext`, `Classical.choice`, and `Quot.sound`.
Searches ran through
`msearch.py` with LeanFinder (related localization criteria), Loogle (the exact
`DerivedCategory.Plus.isIso_iff`), and grep; local source inspection confirmed the criterion
at Mathlib `DerivedCategory/Plus.lean:214` and the stalk-universe isomorphism at the
library `Sites/Point/Basic.lean:85`.

## Proved and sorry left

Closed the only hole:
`AlgebraicGeometry.Scheme.isIso_iff_isIso_geometricStalk_homologyMap`
(node `lem-weil-pbc-derived-stalk-conservative`). One of one holes proved.
No holes remain in the item, no holes added, and no intermediate statements split off.

## No longer needed

Removed proof imports:
- `Mathlib.Algebra.Homology.DerivedCategory.Fractions`.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`.

Removed direct proof dependencies from this node:
- `lem-pc-quasi-isomorphisms-multiplicative-system`: Mathlib's exact cohomology criterion
  replaces writing the localization/roof argument here.
- `def-weil-abstract-derived-category`: used indirectly inside the Mathlib criterion,
  rather than as a direct proof dependency.
- `def-weil-pbc-derived-categories`: remains a statement dependency and its module stays
  publicly imported; no direct proof dependency is needed.
- `def-weil-pbc-etale-sheaves`: the cohomology maps already have the right sheaf category;
  no theorem from its module is used by this proof.

No modules are withdrawn. These are removed direct edges, not a claim that any module
becomes globally unreachable. Stalk exactness was already absent from the original proof
dependencies and is not needed: the hypothesis takes stalks of cohomology sheaves directly.

## Where the brief, the DAG or earlier work was wrong

The old plan elaborates a roof argument which Mathlib already packages in the exact
bounded below criterion, recorded in an existing DAG leaf. The conservativity declaration
uses universe-lifted geometric points, whereas the item uses ordinary points; the existing
proved stalk-universe comparison closes that interface gap. No mathematical statement or
definition was corrected. The referenced literature files are not populated in this local
clone; the unit route was read from `dag/units/sk-prop-cd.json`, and the proof and signatures
were checked against the supplied node and actual Mathlib/library source files.

## Second reading by A4

1. **Unchanged interface — PASS.** Compared the complete delivered module and node with
   the repository versions using `diff -u`. Independently checked that the existing
   theorem signature is byte for byte identical and both public imports are unchanged.
   There are no changed definitions, new declarations, change records, or forced
   adaptations. Only the proof and private imports change in Lean.
2. **Proof and axioms — PASS.** Recompiled the delivered file through `lcompile.py` with
   no errors or warnings (1.8 seconds). Compiled the scratch copy containing the same
   proof and `#print axioms`: exactly `propext`, `Classical.choice`, `Quot.sound`.
   Inspected the proof and scanned for `sorry`, `axiom`, `unsafe`, `opaque`,
   `implemented_by`, `extern`, and explicit `sorryAx`: none occur. No data is chosen
   from an unproved existence theorem. The algebraic closure and its geometric point
   are the existing concrete library constructions.
3. **Split statements — PASS, none.** No statements or nodes were split off and no
   holes were added. The one original hole is closed. Checked that the hypothesis
   supplies exactly the stalk maps needed at every algebraic-closure residue-field
   point, with the coefficient universe handled by the existing natural isomorphism.
   The argument also covers the empty scheme (the conservative family is empty),
   identity and zero-object maps, and every integer degree without boundedness or
   nonemptiness assumptions added to the signature.
4. **Route, searches, and pruning — PASS.** Read Mathlib `Plus.isIso_iff`, library
   `Scheme.isIso_of_isIso_sheafFiber_map`, and `Point.uliftSheafFiberIso` at their
   definitions. Searched local sources with the alternative terms `sheafFiber_map`,
   `homologyFunctor_map`, and `uliftSheafFiberIso`, and ran an additional `msearch.py`
   grep query. Inspected the upstream `Sites/DerivedStalk.lean` criterion
   `isIso_iff_isIso_sheafFiber_map_homologyFunctor_map_plus`: its hypothesis concerns
   the lifted residue-field family, so it still requires this proof's universe
   comparison. The current proof already combines its two elementary steps using
   the exact existing Mathlib criterion and conservative-family theorem; no rewrite
   or additional import is warranted. Both private imports supply declarations used
   in the proof and are private as required. `## No longer needed` names both removed
   imports and all four removed old direct proof dependencies. No global module
   pruning is claimed. Read `dag/units/sk-prop-cd.json`: this auxiliary node does not
   realize a unit statement or step; no unit route or realization is changed.
5. **DAG agreement — PASS.** Checked the existing cohomology-criterion Mathlib leaf,
   the stalk-conservativity node and its Lean attachment, and the geometric-stalk
   definition node. The delivered node changes exactly `proof`, `proof_deps`, and
   `proof_origin`; its statement and Lean record are unchanged. Its three steps
   describe the actual criterion, stalk transport, and functorial preservation
   argument. Independently verified that `proof_deps` is the union of their `uses`.
   There are no new-node metadata obligations.

Second reading changed only this report by adding the independent review. The Lean proof
and DAG changes are retained as written. Outcome: one of one original holes proved,
zero holes added, zero split-off statements, and no globally withdrawn modules.

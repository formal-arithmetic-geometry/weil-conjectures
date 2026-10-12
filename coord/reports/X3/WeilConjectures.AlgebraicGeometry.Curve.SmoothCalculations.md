## What changed

Proved C₄, C₅ and C₆ in
`WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations`, keeping every existing
signature and visibility unchanged. Four proved private helpers handle finite coefficient
biproducts, finiteness transport, the Artin-Schreier kernel, and standard base change.
C₄ uses proper/affine cohomology and handles dimension zero separately. C₅ uses the
Artin-Schreier triangle, surjectivity in degree zero, and finite Frobenius fixed points.
C₆ uses the existing prime-injective comparison and a restriction-square transport,
rather than rebuilding the Kummer argument.

Added the fully proved module
`Sheaf.AlgebraicGeometry.Curve.ArtinSchreierProperDegreeZero`, imported privately by
the item. Updated the proof routes of nodes `lem-sc-c4`, `lem-sc-c5`, and `lem-sc-c6`.
No definitions, target statements, unit records, or other existing modules changed.
Both delivered Lean files compile cleanly with lcompile --all.

## Proved and sorry left

Closed three of the six original holes:

- `AlgebraicGeometry.IsCurve.finite_sheafH_constantModSheaf_of_ne_zero`
  (`lem-sc-c4`).
- `AlgebraicGeometry.IsCurve.finite_sheafH_constantModSheaf_of_isProper`
  (`lem-sc-c5`).
- `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_constantModSheaf_of_ne_zero`
  (`lem-sc-c6`).

The three untouched holes are:

- `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_constantModSheaf_of_isProper`
  (`lem-sc-c7`).
- `AlgebraicGeometry.IsCurve.assertions_constantModSheaf_of_ne_zero`
  (`lemma-weil-pbc-smooth-curve-kummer-localization`).
- `AlgebraicGeometry.IsCurve.assertions_constantModSheaf_of_charP`
  (`lemma-weil-pbc-smooth-curve-artin-schreier`).

Added zero holes and split off zero unproved statements. The new theorem
`AlgebraicGeometry.epi_etaleCohomology_artinSchreier_zero_of_isProper`
(`lem-sc-artin-schreier-proper-degree-zero`) and all four private helpers are proved.
The closed upper statements still depend on existing named, unproved theory, as
intended by stage 3; this is not an axiom-free completion of their dependency closure.

## No longer needed

Removed these original private proof imports:

- `WeilConjectures.AlgebraicGeometry.Curve.Affine`
- `WeilConjectures.AlgebraicGeometry.Curve.Compactification`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`
- `Sheaf.AlgebraicGeometry.ArtinSchreier`
- `Sheaf.AlgebraicGeometry.BaseChangeCurve`
- `Sheaf.AlgebraicGeometry.Curve.ConstantInvariance`
- `Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension`
- `Sheaf.AlgebraicGeometry.EtaleSheaves`
- `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`
- `WeilConjectures.AlgebraicGeometry.Curve.SerreDuality`
- `WeilConjectures.AlgebraicGeometry.Sites.Gm`
- `WeilConjectures.AlgebraicGeometry.Sites.Kummer`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension`

The first three imports are redundant: their declarations remain available through
retained public import chains and are still used by the proofs. The other removed
imports are not needed directly by the completed proofs. Modules still reachable
through retained imports are not claimed globally pruned. The plans of untouched
holes remain unchanged; a later proof may need to restore some imports.

A source-import reachability comparison from `lean/TargetsCheck.lean`, against
this repository snapshot with and without the delivered sources, removes exactly
`Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension`. No other library module
is claimed pruned; the new degree-zero module becomes reachable. This source check
is not a substitute for the maintainer's pinned-baseline sorry ledger.

The replaced proofs no longer cite these original DAG dependencies directly.
The affine Picard/unit estimates remain packaged in thm-sc-affine-cohomology;
removing their direct edges does not prune them transitively:

- `lem-sc-c4`: `def-weil-pbc-etale-sheaves`, `def-weil-pbc-eight-curve-assertions`, `lem-sc-compactification`, `lem-sc-affine-open-proper`, `lem-sc-pic-affine`, `lem-sc-affine-unit-quotient`.
- `lem-sc-c5`: `thm-sc-proper-cohomology`, `lem-sc-cohomological-dimension`, `lem-sc-artin-schreier-dimension`.
- `lem-sc-c6`: `thm-sc-constant-invariance`, `def-sc-field-extension`, `def-weil-pbc-eight-curve-assertions`.

## Where the brief, the DAG or earlier work was wrong

The Lean C₄/C₅ statements concern arbitrary finite Λ/(r), whereas the planned
arguments are expressed for prime-field coefficients. The proved finite-biproduct
helper supplies this necessary transfer without a new hole. Also IsCurve permits
dimension zero, so its vanishing case is included explicitly rather than applying
a dimension-one curve theorem there. C₆ admits the shorter existing
prime-injective cohomology comparison. The unit's eight-assertion route stays intact:
only the proofs below C₄, C₅ and C₆ were replaced. No disputed statement or forced
adaptation was necessary.

## New nodes

`lem-sc-artin-schreier-proper-degree-zero` corresponds to the proved new module
`lean/Sheaf/AlgebraicGeometry/Curve/ArtinSchreierProperDegreeZero.lean`.
It isolates the global-functions part of Artin-Schreier on a proper smooth
connected curve. Global functions are k; algebraic closedness makes x^p-x
surjective, and the natural degree-zero and Ext/derived identifications transport
this to the stated cohomology endomorphism. No new sorry or change record.

## Second reading by X3

1. **Existing interface — pass.** Read the full diff against the repository module.
   Every existing declaration signature and visibility is byte-for-byte unchanged;
   the public imports, shared variable binders, definitions and previously completed
   proofs are unchanged. The only original theorem bodies replaced are C₄, C₅ and C₆.
   The new module has a proved theorem, with no new definition or change record.
2. **Proof checking — pass.** Both files compile cleanly through lcompile. Exactly
   the three original named holes listed above remain; no new hole, hollow definition,
   forbidden declaration or foreign implementation is present. Scratch-copy
   `#print axioms` checks cover all four private helpers, C₄/C₅/C₆ and the new public
   theorem. The two coefficient helpers use only `propext`, `Classical.choice` and
   `Quot.sound`; the other checked proofs additionally use `sorryAx` through existing
   open dependencies, with no other axiom. This is three direct holes closed, not
   an axiom-free completion of the import closure.
3. **New statement — pass.** There is no split-off unproved statement. The new
   degree-zero lemma is strictly the global-functions input to C₅: the structural
   map k → Γ(C,O_C) is surjective because C is proper, connected and reduced;
   smoothness supplies reducedness. The field Artin–Schreier map is onto in prime
   characteristic, and H.equiv₀ plus the natural Ext/derived comparison transport
   that exact endomorphism. Naturality of a is an unused but valid hypothesis;
   it is supplied by the existing sequence. Checked p = 2, genus zero, zero target
   section, and arbitrary natural section coordinates. An empty C cannot satisfy
   IsConnectedCurve. The coefficient helper also handles Λ/(r) = 0 via an empty
   basis. Fresh LeanFinder and rg searches of both source roots find no duplicate
   degree-zero theorem; Loogle could not resolve the upstream H.equiv₀ identifier; the existing degree-one epi theorem has
   a different conclusion. The already-used field and global-functions facts are
   reused, not restated.
4. **Route and pruning — pass after repair.** C₄ splits off dimension zero before
   using the proper/affine dimension-one computation. C₅ uses the actual
   Artin–Schreier triangle, its degree-zero epimorphism, and a semilinear finite
   fixed-point kernel; C₆ proves the standard comparison first and transports
   it to the precise arbitrary cartesian square. No upper claim is delegated to
   a renamed copy. The `sk-thm-p1` realized eight-assertion nodes and the
   `sk-thm-curveestimate` proper-cohomology statement remain used and unchanged.
   Compared every old proof_deps list with the delivered list: every removed
   direct edge is accounted for under No longer needed. The source-import closure
   check finds the single removed module recorded there; no larger pruning is
   claimed. Removed twelve redundant private imports after checking their
   retained public import chains and compiling the cumulative removal. Kept
   the right-derived triangulated import: removing it loses the additive and
   shift-compatible instances needed by C₅.
5. **DAG — pass.** Read the four delivered nodes and all three replaced proof
   routes. Existing node changes are confined to proof, proof_deps and
   proof_origin; their statements are unchanged. Each proof_deps list is the
   union of the uses in its steps. The new node records its source, full
   statement, proof steps, searches, creation, blueprint ancestry, chapter,
   unit and matching Lean declaration. No unit record changes.

Second reading changed only import pruning and this report. Removed the redundant
original private imports Affine, Compactification and TopologicalInvariance, and
removed nine newly added Mathlib imports (Basis.VectorSpace, Module.ZMod,
Grp.Biproducts, ModuleCat.Colimits, Preserves.Shapes.Biproducts, Grp.Zero,
AlgClosed.Basic, GroupTheory.Index and DerivedCategory.SingleTriangle).
The geometric declarations are still used through retained public import chains;
these removals do not claim that the corresponding modules leave target reachability.
No theorem body, signature, new statement or DAG proof route required repair.

## What changed
Proved `H.baseChangeLinear_mayerVietoris` from a geometric Ext presentation. The proof constructs all six linear maps, proves their injectivity and exactness with Mathlib, and computes all three comparison squares using exact-functor preservation of Ext composition and the short exact sequence class. Added `CohomologyMayerVietorisExtPresentation` for the remaining geometric identifications.

## Proved and sorry left
Closed the original hole `AlgebraicGeometry.Scheme.Modules.H.baseChangeLinear_mayerVietoris` (1 of 1 original sorries), conditional on the geometric presentation below. This is a decomposition: one hole closed, one hole added, net zero holes closed; it is not a completed axiom-free proof of the item.
One new sorry: `AlgebraicGeometry.Scheme.Modules.H.exists_mayerVietoris_extPresentation`, node `lem-pc-cohomology-mayer-vietoris-ext-presentation`.

## No longer needed
Removed proof import `Sheaf.Topology.ModuleMayerVietoris`, node `lem-sc-mayer-vietoris-ringed-space`. Its derived-module-cohomology sequence is replaced by Mathlib's contravariant Ext exact sequence, the cohomology theory used by the comparison definition. Its proof-only dependencies `InjectiveRestrictionSurjective`, `RestrictInjectiveResolution`, and `RingedSpaceModuleCohomology` are not used by this argument; their relevance elsewhere is unchanged.


Modules reached by the removed import but absent from the new module's source import closure:

- `Sheaf.AlgebraicGeometry.InjectiveRestrictionSurjective`
- `Sheaf.CategoryTheory.Abelian.RightDerived.InjectivelyExactSquare`
- `Sheaf.CategoryTheory.Abelian.RightDerived.InjectivelyExactSquareBoundaryExact`
- `Sheaf.CategoryTheory.Abelian.RightDerived.InjectivelyExactSquareBoundaryNaturality`
- `Sheaf.Paper.DerivedHomMayerVietoris`
- `Sheaf.Topology.ModuleMayerVietoris`
- `Sheaf.Topology.OpenModuleCohomology`
- `Sheaf.Topology.RingedSpaceModuleCohomology`
- `Sheaf.Topology.RingedSpaceModuleEnoughInjectives`
- `WeilConjectures.FromJoel.Algebra.Homology.Double`
- `WeilConjectures.FromJoel.Algebra.Homology.DoubleHomology`
- `WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso`
- `WeilConjectures.FromJoel.CategoryTheory.Limits.ExactFunctor`
- `WeilConjectures.FromJoel.CategoryTheory.Localization.LocalizerMorphism`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure`
- `WeilConjectures.Mathlib.Algebra.Homology.ExactSequence`
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory`
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Plus`
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Shift`
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence`
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors`
- `WeilConjectures.Mathlib.Algebra.Homology.SingleHomology`
- `WeilConjectures.Mathlib.Algebra.Homology.SpectralObject.Basic`
- `WeilConjectures.Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly`
- `WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift`
- `WeilConjectures.Mathlib.CategoryTheory.Triangulated.SpectralObject`
- `WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.ETrunc`
- `WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject`

Node records for those modules (pruned from this item's argument, not necessarily from every target):

- `def-sc-open-module-cohomology`
- `def-sc-ringed-space-module-cohomology`
- `def-sc-sheaf-cohomology-functor`
- `def-weil-pbc-derived-inverse-image`
- `lem-sc-derived-hom-mayer-vietoris`
- `lem-sc-injectively-exact-square-boundary-exact`
- `lem-sc-injectively-exact-square-boundary-naturality`
- `lem-sc-injectively-exact-square-resolution-short-exact`
- `lem-sc-mayer-vietoris-ringed-space`
- `lem-sc-ringed-space-injective-restriction-surjective`
- `lem-sc-ringed-space-module-sheaves-enough-injectives`
- `lem-weil-pbc-exact-functor-bounded-below`

## Where the brief, the DAG or earlier work was wrong
The ringed-space Mayer--Vietoris declaration uses right-derived module sections, while `HOver` uses Ext in abelian sheaves. It does not expose a comparison between them or inverse-image naturality. The new geometric presentation states the missing identifications without moving row exactness or the boundary-square proof into the sorry. No existing signature or definition changed.
The new presentation has been checked on empty/repeated opens, the zero module and the zero ring. The short exact sequence convention uses inclusion and minus inclusion; exact inverse image retains these signs.

## New nodes
`lem-pc-cohomology-mayer-vietoris-ext-presentation`: presents the original and base-changed graded cohomology groups as Ext from a short exact complex and its inverse image, with scalar and vertical-comparison identifications. It asserts no horizontal maps or exactness; those and the three squares are proved in the original module. The full source-based proof is in its docstring. No change records are needed.

## Second reading by N1
1. Compared both delivered modules with the repository. The Ext-presentation module is
   new; the existing public theorem signature is byte-for-byte identical, with no
   hypothesis, conclusion, definition or existing public import changed. Restored the
   original theorem docstring whitespace. The only new definitions are a data-bearing
   presentation structure and a private linear-map transport; neither is hollow.
2. Compiled both modules in dependency order using lcompile.py. The item's proof and
   all private helpers have no sorry; the only new sorry is the complete proof of
   H.exists_mayerVietoris_extPresentation. No forbidden declarations or kernel bypasses
   occur. Checked the named theorem axioms in a scratch probe; the delivery tool also
   probes every generated declaration. Only the three standard axioms and sorryAx
   from the recorded geometric hole are permitted.
3. Read the geometric presentation statement and its full docstring proof against
   FlatCohomologyComparison, Stacks 01EB, 01F7 and 02KH, and Mathlib's free-sheaf
   MayerVietorisSquare.shortComplex_shortExact. The statement is true: exact open
   restriction with exact extension by zero gives the Ext identifications; inverse
   image preserves free sheaves on opens and the coefficient adjunction gives the
   displayed vertical maps. For an empty open its free sheaf and cohomology vanish;
   for repeated opens (necessarily both X) the sequence is the split diagonal/sum
   sequence with one minus sign. Zero coefficients give zero Ext groups; a zero
   base ring forces an empty scheme. No flatness assumption enters. Independent
   leanfinder, loogle and grep searches used free-sheaf/restriction/Ext terminology;
   Mathlib has the abstract exact sequence and object cohomology, but no theorem
   identifying all these scheme/module base-change terms and scalars. The geometric
   identification remains substantial work, so it was not closed in this reading.
   It is strictly a part of the argument: no horizontal maps, row exactness or
   boundary squares are asserted. The item proves those by Ext transport, rather
   than applying a renamed copy of its own conclusion.
4. Checked extTransport's scalar law by Ext associativity, transported exactness,
   initial injectivity from the epi, and all three naturality squares, including
   preservation of extClass. This is the direct abstract Ext route. Removed the
   redundant public ExactSequences import from the new module: it is already
   provided by FlatCohomologyComparison and only the main proof needs its results.
   The old proof_deps has exactly one removed node, lem-sc-mayer-vietoris-ringed-space,
   already listed under No longer needed. The unit sk-thm-picard-rr has empty realized
   statement and step arrays, and no protected realization is bypassed. The two-open
   Mayer--Vietoris step remains implemented through the free-sheaf sequence.
5. Compared the two node files with the Lean: proof steps, proof_deps and proof_origin
   describe the actual geometric-presentation/Ext route. The new node has its source,
   searches, creation record, blueprint provenance, chapter/unit and verbatim Lean
   statement, and records both new public declarations. Existing statement fields
   are unchanged. Verdict: passes as a decomposition with pruning, not a net closure.

Second-reading changes: removed one redundant public import, restored existing
 docstring whitespace, and corrected the progress accounting to one hole closed and
 one added. No mathematical statement or proof body was changed.

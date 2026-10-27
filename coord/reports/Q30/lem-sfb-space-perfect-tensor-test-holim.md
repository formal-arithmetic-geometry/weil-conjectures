## Worker report

The item is stated by
`AlgebraicGeometry.AlgebraicSpace.perfectTensorTest_preserves_products_holim`
in `Sheaf.AlgebraicGeometry.SpacePerfectTensorTestHolim`. Its two helper definitions
give the actual tensor-test functor and its projection-induced product comparison.
Every theorem proof is `sorry`; definition data are actual functor compositions,
limit lifts, or Mathlib's induced full-subcategory structure.

The inherited BLOCKED ending was a stage-1 gate refusing to re-split Q129's accepted
split. The stage-2 handoff paragraph of coord/brief-stage2.md explicitly distinguishes
that situation. The current item has no lean record, is in the stage-2 queue, and
its accepted statement, proof and proof dependencies are preserved. There is no
released repair note for this item.

Clause-by-clause rendering:

- The size convention is expressed by explicit `u w`. Schemes, the ring, ring
  sections and module sections use `u`; `HasDerivedCategory.{w} X.SmallModules`
  retains the independent localization morphism universe. The original etale site
  with larger object universe is replaced only by the already recorded equivalent
  small affine model, with unchanged section universe and structure rings.
- The commutative ring is `(A : Type u) [CommRing A]`. An arbitrary scheme base S
  is allowed. The affine target is `(Y : Over S)` with
  `(e : Y.left ≅ Spec (.of A))`; `(f : X ⟶ schemeSpace Y)` is the given map.
  This affine presentation neither assumes properness nor finite type, nor
  restricts the base scheme. In particular take S = Spec A and Y its identity
  over-object to recover any algebraic space over Spec A.
- The given space is `(X : AlgebraicSpace S)`. `hqc` is compactness of its existing
  point space. `hqs : X.IsAbsolutelyQuasiSeparated` is exactly quasi-compactness
  of the absolute diagonal, expressed by the recorded equivalent affine-pair
  test, including when S itself is not quasi-separated.
- `X.DerivedModules` is the unbounded derived category of the recorded equivalent
  small ringed model. `X.DerivedQCoh` is its existing full subcategory of objects
  whose transported cohomology sheaves satisfy Mathlib's `IsQuasicoherent`.
  It is not the derived category of the abelian category QCoh.
- `E : X.DerivedModules` has hypothesis
  `SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u,u,u,w}
  X.smallStructureSheaf E`. Its definition uses local bounded complexes of
  degreewise finite-free retracts; local bounds and ranks can vary.
- `perfectTensorTest` is the full inclusion followed by
  `Prod.sectL X.DerivedModules E`, then
  `X.derivedDualityModel.closed.tensor`, then `affineDerivedSections A Y e X f`.
  The tensor is the existing closed derived tensor normalized on K-flat
  representatives. The last functor is the K-injective right derived functor of
  Hom(O,-), with A-action obtained from Gamma-Spec and each actual chart map f.
  Its target is the derived category of ordinary A-modules, not abelian groups
  or an arbitrary replacement coefficient ring.
- Exactness is the first two conjuncts: additivity and existence of a natural
  isomorphism T(F[1]) = T(F)[1] under which every distinguished triangle maps to
  a distinguished triangle. This is the ordinary exact-functor formulation for
  triangulated categories, written directly so the shift witness is concluded
  rather than assumed of T.
- The next conjunct quantifies over every `I : Type u` and family F in D_QCoh.
  It concludes existence of both products. For every choice of product fans P,Q,
  the comparison is an isomorphism. `perfectTensorTestProductComparison` is
  literally `hQ.lift (Fan.mk _ (fun i ↦ T.map (P.proj i)))`, so its components
  are T of the source projections. This includes countable products by reindexing
  a countable family with ULift of the natural numbers if u is nonzero; products
  are invariant under that index equivalence. The tower clause itself uses ℕ
  directly. Empty index sets are included.
- The final conjunct quantifies over a tower `(F,t)` in that same full subcategory,
  arbitrary product fans P,Q with their limit proofs, and their endomorphisms s,s'.
  The displayed projection equations uniquely specify 1-shift on each product;
  s and s' are not arbitrary transition maps. The hypotheses `hK` and `hR` say
  that the triangles `(p,s,delta)` and `(p',s',delta')` are distinguished. These
  are exactly the definition of `IsDerivedLimitTriangle`, expressed with
  arbitrary specified products instead of Mathlib's globally chosen product.
  Thus they cover every choice of the two defining Roos triangles. No agreement
  of the source product with the ambient derived product is assumed.
- The conclusion gives an isomorphism `phi : T(K) ≅ R` in D(A), with
  `phi.hom ≫ p' = T.map p ≫ comparison`. This is exactly compatibility of the
  arrows to the products under the projection-induced comparison. No unique or
  functorial cone comparison is claimed. A strict tower of complexes is evaluated
  by localization to obtain this tower of derived objects. Conversely countable
  derived towers can be represented by strict complexes using K-injective
  representatives and chain maps; hence the intrinsic tower formulation does
  not impose a stronger geometric assertion.

The existing dependency declarations were read in their source modules:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Spec`,
  `Spec.map`, and `Scheme.ΓSpecIso`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`,
  `structureSheaf` and `Modules`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`, transparently
  Mathlib's sheaf-of-modules category, with its inherited abelian structure.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory` and the cohomology functors.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and
  the slice sheafification instances; the underlying quasi-coherence predicate
  is Mathlib's existing `SheafOfModules.IsQuasicoherent`.
- `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`:
  `IsPerfectOnRingedSiteOfUniverses` and its local strictly perfect predicate.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients` and its resolution predicate.
  `RingedSiteDualityModel.models` pins the used tensor to these K-flat models.
- `Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses`:
  `ringedSiteZerothHypercohomologyOfUniverses` is H0 of RΓ. It is imported as the
  recorded dependency, while the full A-valued RΓ needed here is the landed
  `affineDerivedSections`, not a replacement definition of that H0 functor.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`:
  `CategoryTheory.IsDerivedLimitTriangle` and `IsDerivedLimit`.
- Added existing definition dependencies:
  `def-sfb-space-derived-module-calculus` supplies `DerivedQCoh`,
  `derivedQCohProperty` and `derivedDualityModel` in
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`;
  `def-sfb-space-affine-global-sections` supplies `affineDerivedSections` in
  `Sheaf.AlgebraicGeometry.SpaceAffineGlobalSections`;
  `def-sfb-space-absolute-quasi-separated` supplies `IsAbsolutelyQuasiSeparated`
  in `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`.
  These are already landed with lean records and are added under the express
  authorization to cite landed definition nodes.
- Available proof-only dependencies are imported without public visibility:
  `SpacePerfectUniformTor` and `RingedSiteKInjectiveResolutionsOfUniverses`.
  The remaining proof nodes have no recorded modules yet; no duplicate theorem
  is introduced for them, and their imports can be attached when stated.

Edge cases checked: A = 0; X empty; E = 0; empty and singleton product families;
unbounded input complexes; arbitrary local ranks and perfectness intervals;
arbitrary localization universe w; non-Noetherian A; non-quasi-separated auxiliary
base S; zero transitions; identity transitions; any selected source or target
derived limit. No finite type, properness, flatness, separation or boundedness
hypothesis beyond the node is imposed. Products remain intrinsic to D_QCoh.

Searches for the item used msearch.py LeanFinder on the full tensor-test statement,
LeanSearch on derived global sections tensor perfect commuting with products and
homotopy inverse limits, Loogle on `"PreservesLimits", "tensor"`, and Mathlib grep
`perfect|Perfect|homotopyLimit|homotopy.*limit` in Algebra/Homology. Results were
ordinary flat-tensor finite-limit facts, scheme-limit facts, and unrelated
homotopy-category facts, not this assertion. Project rg searches for
`tensor.*[Gg]lobal`, `[Tt]ensor.*[Tt]est`, `perfectTensor`, `PerfectTensor` and the
item id found no exact theorem in WeilConjectures or Sheaf. They did find the
existing calculus, normalized tensor and canonical A-valued sections reused here.
The new node records its additional targeted searches with their tool output.

No STATEMENT-DISPUTED issue or statement correction is required. The source
0CX6 paragraph explicitly states exactness and product/derived-limit preservation
of global derived Hom; 08JJ makes the translation to the perfect tensor test.

## New nodes

`def-sfb-space-qcoh-derived-triangulation` supplies the inherited triangulation on
the already existing D_QCoh full subcategory. Its module is
`Sheaf.AlgebraicGeometry.AlgebraicSpaceQCohTriangulated`. The closure obligation
`derivedQCohProperty_isTriangulated` is a named theorem, with a complete proof in
its docstring; `qcohDerivedTriangulation` uses the actual Mathlib induced structure.
No category, shift, or distinguished-triangle data are chosen by a mere existence
theorem. Source: spaces-perfect.tex, definition-derived-quasi-coherent and the
paragraph immediately following it, and derived.tex Tag 06UP. Mathlib already
supplies the general full-subcategory construction, which this module reuses,
but no existing general algebraic-space quasi-coherent closure instance was found.
The landed perfect-localizing-generation theorem has qcqs hypotheses and states
closure properties; it is not an inherited triangulation interface for all spaces.
The DAG and blueprint searches found no definition node for this structure.

## Second reading by Q30

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Worker report

The delivery states `AlgebraicGeometry.ProEtale.spEtaleMate_transpose` in
`Sheaf.Paper.SpDirectImageEtaleMate`. Its sole postponed proof is this theorem,
whose docstring carries all four proof steps and their dependencies. All eight
supporting definitions/abbreviations have actual data. No theorem is proved,
no definition contains `sorry`, and no statement correction or dependency
repair is needed.

The signature renders every hypothesis as follows:

- The prime ell is `(ℓ : ℕ)` with `_hℓ : ℓ.Prime`. The characteristic is
  `(p : ℕ)`, `(k : Type u) [Field k] [CharP k p]`, `_hp : 0 < p`, and
  `_hne : p ≠ ℓ`. The implication from positive field characteristic to primality
  needs no additional assumption.
- The separated finite-type k-schemes are `X Y : Scheme.{u}`, their `Over`
  instances over `Spec (.of k)`, and `IsSeparated`, `LocallyOfFiniteType`, and
  `QuasiCompact` instances on both structural morphisms. The last two together
  mean finite type. The map is `(f : X ⟶ Y)` with `[f.IsOver (Spec (.of k))]`
  and `[IsProper f]`. Properness supplies exactly the qcqs instances needed by
  the normalized comparison. The setting node's chosen compactifications and
  condensed coefficients are not used in this ordinary-coefficient assertion.
- `A B : Type (u + 1)` with `CommRing` and `Finite` instances are the finite
  commutative coefficient rings, with `(a : A →+* B)`. The hypotheses
  `_hA : ∃ n : ℕ, (ℓ : A) ^ n = 0` and the corresponding `_hB` are exactly
  annihilation by powers of ell; no flatness, nontriviality or projective
  dimension is assumed.
- `spEtaleCoefficient a Y` is B_Y[0]: take B as a B-module, restrict scalars
  along a by `ModuleCat.restrictScalars`, apply the constant sheaf functor on
  Y's small etale site, and then `DerivedCategory.singleFunctor _ 0`.
  This uses the actual homomorphism, not an arbitrary A-module structure.
- `K` is in `DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat A))` and
  `hK : ∃ n : ℤ, K.IsGE n` says precisely K lies in D+. The object
  `spEtaleTensorObject a f K` is H, using the recorded etale derived tensor
  with the derived inverse image of B_Y[0]. Exact inverse image of constant
  sheaves gives B_X[0], the identification stipulated in the node.
  `hH : ∃ n : ℤ, (spEtaleTensorObject a f K).IsGE n` is the separately required
  D+ hypothesis on H. No D+ hypothesis is imposed on the tensor on Y.
- All categories are ordinary, uncompleted fixed-ring module-sheaf categories.
  `comparisonUpperStar ... .mapDerivedCategory` is nu-star and its value on K
  is N. The fixed-ring encoding is canonically equivalent to modules over the
  ring sheaves of `def-weil-pbc-proetale-modules`, by the recorded
  `finiteCoefficientEtaleRealization` and `finiteCoefficientRealization`
  equivalences; it is not the condensed or completed coefficient encoding.
- `spDirectImageComparisonIso A f K hK` is beta_K and its value at H is beta_H.
  It includes **the recorded** `fixedComparisonDirectImageMatePlus` from D+
  using `Functor.rightDerivedFunctorPlusCompatibility` on both direct images
  and `Functor.mapDerivedCategoryPlusCompatibility` on both comparison
  pullbacks. Its sole invertibility input is the recorded
  `isIso_fixedComparisonDirectImageMatePlus`. This keeps the specified counit
  normalization and does not choose some endpoint isomorphism.
- `spEtaleProjection a f K` is exactly the recorded
  `Etale.rightDerivedLowerStarProjectionMap`, evaluated at K and B_Y[0]. Its
  target is the H just defined. The derived adjunctions and the tensor maps
  are the recorded ordinary ones.
- `spEtaleMateTargetIso` first applies the published canonical tensor
  comparison for nu_X, and then tensors the inverse of the published ordinary
  pullback square with the identity of N. Thus it identifies nu_X-star H with
  N tensor p-star nu_Y-star B_Y. Constants identify the latter coefficient
  with B_X, exactly as fixed in the node. The source is presented similarly
  with nu_Y-star B_Y = B_Y; no arbitrary coefficient identification is supplied.
- `spEtaleMate` is the stated t in Lean's left-to-right composition order:
  tensor beta_K.inv with the identity; undo the tensor comparison for nu_Y;
  apply nu_Y-star to pi_K; apply beta_H.hom; and push forward the target tensor
  identification. Its source and target are named `spEtaleMateSource` and
  `spEtaleMateTarget` only to avoid repeating these endpoint expressions.
- The first conjunct of `spEtaleMate_transpose` applies the inverse of
  `leftDerivedUpperStarTensorIso` to the adjoint transpose
  `(derivedUpperStarLowerStarAdjunction ...).homEquiv.symm (spEtaleMate ...)`.
  It asserts equality with `derivedTensor.map` of the pro-etale counit,
  evaluated at the pullback coefficient. This is precisely epsilon_N^p tensor
  the identity after the stipulated pullback-tensor identification.
- The second conjunct is
  `IsIso (spEtaleProjection a f K) → IsIso (spEtaleMate a f K hK hH)`.
  It asserts only the conditional invertibility in the node.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `FiniteCoefficientModules`,
  `FiniteCoefficientEtaleDerivedCategory`, the two realization functors and
  their equivalence statements, and `finiteCoefficientDerivedComparison`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and its recorded
  `AlgebraicGeometry.Etale.DerivedCategoryModule` / derived-category interface;
  `DerivedCategory`, `DerivedCategory.Plus`, `IsGE`, and `singleFunctor`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`: ordinary intrinsic
  ring pullback and adjunction, and their constant-section normalization.
  The statement uses their fixed-ring sheaf presentation through the published
  `upperStar`, `lowerStar` and `derivedUpperStarLowerStarAdjunction` APIs.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`: `Etale.derivedTensor`;
  `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`:
  `Etale.rightDerivedLowerStarProjectionMap` and its transpose formula.
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`:
  `fixedComparisonPullbackPlus`, `fixedComparisonDirectImageMatePlus`,
  `isIso_fixedComparisonDirectImageMatePlus`, and the recorded counit equation.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`.
  Its canonical comparison specializes to the published
  `derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso` and
  `leftDerivedUpperStarTensorIso` used in the statement. These existing maps
  retain the K-flat representative normalization; no tensor is redefined.
- The existing node `def-weil-boundary-exceptional-comparison-data` is added
  to `stmt_deps` solely because its published module
  `Sheaf.Paper.BoundaryExceptionalComparisonData` already supplies
  `BoundaryComparison.pullbackSquare`, the canonical ambient inverse-image
  square, constructed by exact-functor descent from the ordinary square. Only
  this general helper is used; none of its exceptional-image objects or
  properties is assumed. It has no dependency path back to this item.
- Proof imports retain `Sheaf.Paper.RingedExchangeTensorCoherence`
  (`SheafOfModules.ringedExchangeTensorCoherence`),
  `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`, and
  `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`. The site-comparison
  morphism is publicly imported through the recorded comparison modules.
- The closed upstream setting declarations
  `HasCompactification.of_isOver` and
  `ProEtale.CondensedRing.compactificationOverField` were read. They confirm
  the separated finite-type k-scheme convention, but compactification is not
  an object used by this node, so its data is not inserted into the signature.

Source verification: read the current blueprint direct-image proof Step 1
and its remaining Steps 2-4, and Stacks `sites-cohomology.tex`, the projection
formula map and `remark-compatible-with-diagram` (0E48). The latter explicitly
allows any commutative ringed square, with no cartesianness. The comparison
maps used here are exactly its tensor, exchange and pullback-square arrows.
The theorem docstring records the node's four proof steps: identify normalized
exchange; apply ringed exchange/tensor coherence; cancel beta_K and transpose;
reverse the composite if pi_K is invertible.

Edge cases checked before writing: empty schemes and the zero ring/module are
included; the constant sheaf and pullback construction give the unique zero
objects in the empty case. Exponent n=0 in an annihilation hypothesis allows
exactly the zero coefficient ring. The identity map and the identity coefficient
homomorphism use their actual normalized comparison maps. Disconnected schemes
are covered by the constant **sheaf**, rather than an unsheafified constant
presheaf. K is not required to be bounded above or constructible. For
A=Z/ell^2 and B=K=F_ell in degree zero, H can be unbounded below: this fails the
explicit hH assumption, and no unsupported assertion that H is always D+ is
made. The Y-side tensor can be unbounded and is never packed into D+.

Searches made on 2026-10-18:

- `msearch.py leanfinder`, query “Adjoint transpose of etale projection after
  pro-etale comparison is the counit tensor identity”: eight results, including
  GammaSpec counit declarations, `Condensed.profiniteSolidCounit` and etale
  Kahler-differential comparisons. No match for this statement.
- `msearch.py loogle`, query
  `CategoryTheory.mateEquiv, CategoryTheory.Adjunction.counit`: four generic
  mate-equivalence identities (`mateEquiv_counit`, its symmetric variant,
  `mateEquiv_apply` and its inverse variant); no site/tensor specialization.
- `msearch.py grep`, query `projection.*comparison|mateEquiv_counit` in
  `CategoryTheory`: four results in Mathlib's generic mates and monoidal closed
  functor modules; no normalized etale/pro-etale projection comparison.
- `rg` for the node ID, and for
  `etale.*[Mm]ate.*[Ii]so|directImage.*[Ee]tale.*[Mm]ate`, in both upstream
  `WeilConjectures` and project `lean/Sheaf`: no exact statement. The upstream
  name index has no occurrence of the item ID. Existing scalar-mate and
  boundary-comparison material was read, but concerns different statements.
- Focused source searches found the published D+ inclusion compatibilities,
  the tensor/pullback comparisons and the existing ambient pullback square.
  All are reused. No new independent mathematical notion is introduced.

The first import probe exposed duplicate declarations from the old scalar-mate
module's mixed original/finite-coefficient import families. It was removed;
the final module uses the finite-coefficient family consistently and transports
the recorded D+ comparison itself. An initial elaboration error required
`[Finite A]` on the target-identification helper to derive the existing
Noetherian flat-preservation instance. The signature uses the standard pair
`LocallyOfFiniteType` and `QuasiCompact` for finite type. These are implementation
repairs, not new hypotheses on the item.

Validation: the full statement and all eight helpers compiled without errors
or warnings through `scompile.py`, both as a sandbox file and under its actual
module name (8.5 s and 17.6 s respectively). The final explicit dependency imports
are checked again by the required delivery dry run. No `#check` probes remain.
No STATEMENT-DISPUTED flag or node fault remains.

## Second reading by Q03

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

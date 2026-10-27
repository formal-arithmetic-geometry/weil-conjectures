## Worker report

The module `Sheaf.TraceFormula.AffineSectionIdealTwistH1Vanishing` states
`AlgebraicGeometry.Scheme.Modules.exists_ideal_tensorPow_h1_isZero_of_affine_nonvanishing`.
Its sole proof is `sorry`; there are no new definitions. The node changes only in `lean`.
The six proof steps in the declaration docstring follow the node and Stacks Project,
`literature/stacks-project/varieties.tex`, Tag 0B5X, lemma-ample-curve, third proof
paragraph (lines 10038–10066), which I opened and read.

Hypothesis and conclusion correspondence:

- The field k is `{k : Type u} [Field k]`.
- The scheme C over k is `{C : Scheme.{u}} [C.Over (Spec (.of k))]`.
- Integrality and properness are `[IsIntegral C]` and
  `[IsProper (C ↘ Spec (.of k))]`. No smoothness, normality, algebraic closure,
  geometric integrality, or rational-point assumption is imposed.
- Topological Krull dimension one is
  `hdim : topologicalKrullDim C = (1 : WithBot ℕ∞)`.
- The invertible module is `(N : C.Modules) [N.IsInvertible]`.
- The integer n at least one is `(n : ℕ) (hn : 1 ≤ n)`. Natural exponents encode
  exactly the nonnegative integers; the bound excludes zero.
- The global section is
  `(s : (N.tensorPow n).val.presheaf.obj (op ⊤))`, and nonzero is `hs : s ≠ 0`.
- The nonvanishing open C_s is represented by `(U : C.Opens)` and the exact set
  equality `hU : (U : Set C) = nonvanishingLocus (N.tensorPow n) s`.
  The already recorded locus is a set; representing it by an open with this equality
  uses the same interface as `exists_tensorPowSection_cohomology_eq_zero`.
  Affineness is `hAffine : IsAffineOpen U`. The equality determines U uniquely.
- Every quasi-coherent ideal is an arbitrary `(I : C.IdealSheafData)` with
  `hI : I.toModules.IsQuasicoherent`. IdealSheafData supplies affine-local ideals
  with localization compatibility; `I.toModules` is the canonical kernel subsheaf
  of O_C, with its canonical monic inclusion, not an arbitrary module or map.
  This is also the interface of the existing sibling
  `AlgebraicGeometry.idealTwistVanishing_implies_isAmple`.
- The conclusion is `∃ E : ℕ, 1 ≤ E ∧ IsZero (...)`. Thus E is positive and may
  depend on I, as in the node. The module inside the cohomology functor is exactly
  `I.toModules ⊗ N.tensorPow (E * n)`; the exponent order is E times n.
- H^1 is `(RingedSpace.moduleCohomology C.toRingedSpace 1).obj`, the right
  derived global-sections functor on O_C-modules. Its value is a ModuleCat object,
  so categorical `IsZero` expresses the entire cohomology module being zero.

Recorded statement dependencies used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs.
- `def-pc-integral-scheme`: `AlgebraicGeometry.IsIntegral`,
  Mathlib.AlgebraicGeometry.Properties.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsProper`,
  Mathlib.AlgebraicGeometry.Morphisms.Proper.
- `def-kun-topological-krull-dimension`: `topologicalKrullDim`,
  Mathlib.Topology.KrullDimension.
- `def-sc-invertible-module`: `AlgebraicGeometry.Scheme.Modules.IsInvertible`,
  WeilConjectures.AlgebraicGeometry.Modules.Invertible; that module also supplies
  the actual recursive `tensorPow` and the scheme-module tensor product.
- `def-weil-pbc-ample-invertible-module`:
  `AlgebraicGeometry.Scheme.Modules.nonvanishingLocus`,
  WeilConjectures.AlgebraicGeometry.Ample. Ampleness is not assumed here.
- `pqf-def-coherent`: Sheaf.AlgebraicGeometry.CoherentFiniteType publicly exposes
  the recorded `SheafOfModules.IsQuasicoherent`; its conjunction with finite type
  is not an added hypothesis.
- `pqf-def-cohomology`: WeilConjectures.AlgebraicGeometry.PQFCohomology exposes
  `AlgebraicGeometry.RingedSpace.moduleCohomology`, defined in
  WeilConjectures.Topology.RingedSpaceModuleCohomology.
- `def-pur-sheaf-tensor-product`:
  Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses, recorded monoidal
  sheaf tensor interface. The tensor notation here uses the established scheme
  monoidal structure, with no replacement construction.

The canonical ideal-module bridge is imported from
WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module:
`AlgebraicGeometry.Scheme.IdealSheafData.toModules` and `toModulesι`.
I read its construction and affine-section characterization. This reuses an
existing notion and requires no new helper node or dependency repair.

Already stated proof dependencies are imported without `public`:
WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
(`isCoherent_kernel_cokernel_biprod_and_submodule`), Mathlib.AlgebraicGeometry.Noetherian
(`IsLocallyNoetherian.quasiSeparatedSpace`),
Sheaf.AlgebraicGeometry.CoherentZeroDimensionalSupport
(`coherent_zero_dimensional_support`),
Sheaf.AlgebraicGeometry.SectionAffineOpenKillsCohomology
(`exists_tensorPowSection_cohomology_eq_zero`), and
WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
(`isFinitePresentation_higherDirectImage`). Their modules/signatures were read.
`lem-trf-proper-field-invertible-coherent` has no Lean record or Mathlib match in
this checkout, so there is no module to import for that proof-only dependency.
It is not needed to type the statement.

Edge cases checked before writing: I = 0 gives zero cohomology and allows E = 1;
if H^1(I) is already zero, the empty basis in the source argument again allows
E = 1. The bound n ≥ 1 and hs exclude zero exponent and zero section. No positive
lower bound on the vanishing order at any individual point is assumed. Empty C
is excluded by integrality, consistently with dimension one. The statement allows
singular integral curves, non-geometrically-integral curves, and every characteristic.
The exponent is En, not an arbitrary unrelated exponent or a uniform exponent for all
ideals. On P^1, positive-degree line bundles and ideal O(-d) have eventual vanishing;
negative-degree bundles cannot supply the required nonzero section. This is consistent
with the hypothesis and not an extra positivity assumption.

Searches for an exact existing statement (2026-10-24):

- `msearch.py ... leanfinder`: “For an invertible module L on a proper integral curve,
  nonzero section with affine nonvanishing locus implies some positive power L tensor I
  has vanishing H1 for any ideal sheaf I”. Eight hits, headed by
  `exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen` and its
  quasi-compact variant: localization of structure-sheaf sections, not ideal-twist H1
  vanishing. An earlier equivalent plain-language query gave the same kind of hits.
- `msearch.py ... loogle`:
  `AlgebraicGeometry.Scheme.Modules.tensorPow, AlgebraicGeometry.RingedSpace.moduleCohomology`.
  Zero hits; the remote index reports tensorPow as unknown (a project declaration).
  The local project sources supply these actual declarations, as read above.
- `msearch.py ... grep 'ideal.*twist|tensorPow' AlgebraicGeometry`: zero Mathlib hits.
- `rg` in lean/WeilConjectures and lean/Sheaf for
  `ideal.*twist|ideal_twist|affineSection.*[Vv]an|affine_section.*[Vv]an`:
  related disjoint-ideal twists and the converse ampleness criterion, but no exact
  statement. ProperIntegralCurveAmpleDegree's proof docstring contains this argument;
  its theorem instead states the degree/ampleness equivalence.
- The exact node-id search in lean/WeilConjectures returned no declaration.
- The IdealSheafData bridge was found by project `rg` for ideal-module interfaces.
  It was reused, not copied.

Validation: the prescribed scompile.py server compile passed for both sandbox and
library module names, taking approximately two seconds each, with no compiler messages.
No statement correction, disputed statement, new node, or dependency module is needed.

## Second reading by Q60

I reread the node statement alongside the final Lean signature after compilation.
The field/scheme/proper/integral/dimension hypotheses and N, n, s match separately.
The open equality is exact, and the affine hypothesis is on that same open.
The ideal binder uses the existing actual ideal subsheaf and explicitly retains
quasi-coherence. The quantifier order lets E depend on the ideal, while 1 ≤ E
retains the positive-exponent clause. The tensor exponent is E * n and cohomology
is the recorded module-sheaf H^1. There is no smoothness or stronger ideal-finiteness
hypothesis. No mismatch was found and no statement change was made. This is a
second pass by this worker; the dispatcher's required independent maintainer review
remains separate, and no other agent was started.

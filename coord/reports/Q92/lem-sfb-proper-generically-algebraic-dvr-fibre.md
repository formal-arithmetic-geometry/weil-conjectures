## Worker report

The module `Sheaf.AlgebraicGeometry.Morphisms.ProperGenericAlgebraicityDvrFibre` states
`AlgebraicGeometry.proper_generic_algebraicity_dvr_fibre`, with `sorry` as its only proof.
No definitions, helper axioms, new nodes, or dependency repairs are introduced. The node
is changed only in `lean`.

Source read: `literature/stacks-project/varieties.tex`, lines 3187–3320, especially
Tag 0AB6 (`lemma-quasi-finite-in-codim-1`), hypothesis (1), Tag 0AB7
(`lemma-finite-in-codim-1`), its first three proof sentences, and Tag 0BFP
(`lemma-modification-normal-iso-over-codimension-1`), clause (2). These explicitly
allow algebraic generic residue extensions and do not require global Noetherianness
for the finite-discrete-fibre argument. DVR properties use the node's cited Algebra
Tag 00PD. The five proof steps from the accepted node are included in the docstring.

Hypothesis and conclusion correspondence:

- Schemes Y and X: `{Y X : Scheme.{u}}`; the universe `u` is explicitly declared.
- Morphism f:Y→X: `(f : Y ⟶ X)`; properness: `[IsProper f]`.
- Point x∈X: `(x : X)`. The ring R=O(X,x) is always the actual
  `X.presheaf.stalk x`, rather than a separately chosen ring or isomorphism.
- R is a DVR: `[IsDomain (X.presheaf.stalk x)]` and
  `[IsDiscreteValuationRing (X.presheaf.stalk x)]`. Mathlib's DVR class takes its
  domain instance as a parameter, so both binders together express precisely the
  node's DVR assumption. They impose no extra condition.
- Dimension one: `(hdim : ringKrullDim (X.presheaf.stalk x) = 1)`.
- Every irreducible component: `∀ (T : Set Y), T ∈ irreducibleComponents Y →`.
- Every generic point of that component: `∀ (η : Y), IsGenericPoint η T →`.
- Algebraic extension κ(fη)⊆κ(η):
  `@Algebra.IsAlgebraic (X.residueField (f η)) (Y.residueField η) _ _
  (f.residueFieldMap η).hom.toAlgebra`. This is algebraicity for the canonical
  induced homomorphism, not an arbitrary algebra structure. Mathlib defines it
  elementwise by a nonzero annihilating polynomial.
- R is Noetherian: the first conjunct `IsNoetherianRing (X.presheaf.stalk x)`.
- R is normal: the next conjunct explicitly quantifies over every prime ideal p
  and asserts `IsDomain (Localization.AtPrime p) ∧
  IsIntegrallyClosed (Localization.AtPrime p)`, exactly the inline normal-ring
  definition recorded by def-weil-pbc-normal-ring. No conclusion is replaced by a
  normal-scheme assertion or by an unspecified notion of normality.
- Quasi-finite at every point above x: `∀ y : Y, f y = x →
  Scheme.Hom.IsQuasiFiniteAtPoint f y`, the recorded Stacks finite-type-inclusive
  predicate, not Mathlib's bare stalkwise `QuasiFiniteAt`.
- The actual scheme fibre is `f.fiber x = pullback f (X.fromSpecResidueField x)`.
  Its underlying space is finite: `Finite (f.fiber x)`; discrete:
  `DiscreteTopology (f.fiber x)`.
- Identified with f⁻¹({x}): `∃ e : f.fiber x ≃ₜ (f ⁻¹' {x}),
  ∀ z : f.fiber x, (e z).val = f.fiberι x z`. This asserts a homeomorphism onto
  the subspace, compatible with the first projection, rather than an arbitrary
  bijection. The existing `f.fiberHomeo x` provides exactly this identification.

Recorded dependency declarations read and used:

- def-pc-scheme: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and `AlgebraicGeometry.Scheme.Hom`.
- def-weil-proper-morphism: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper`, extending `IsSeparated`, `UniversallyClosed`,
  and `LocallyOfFiniteType`; universal closedness supplies quasi-compactness.
- def-sc-discrete-valuation-ring (mathlib_match):
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`, `IsDiscreteValuationRing`.
- def-weil-pbc-krull-dimension-ring: `Mathlib.RingTheory.KrullDimension.Basic`,
  `ringKrullDim`.
- def-sc-generic-point: `Mathlib.Topology.Sober`, `IsGenericPoint`.
- def-weil-residue-field: `Mathlib.AlgebraicGeometry.ResidueField`,
  `AlgebraicGeometry.Scheme.residueField` and `Scheme.Hom.residueFieldMap`.
- def-weil-pbc-noetherian-ring: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`.
- def-weil-pbc-normal-ring: `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`,
  `IsIntegrallyClosed`; `IsDomain` and `Localization.AtPrime` (the latter in
  `Mathlib.RingTheory.Localization.AtPrime.Basic`), in the exact recorded inline form.
- pqf-def-quasifinite:
  `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`,
  `AlgebraicGeometry.Scheme.Hom.IsQuasiFiniteAtPoint`.
- def-pc-scheme-fibre: `Mathlib.AlgebraicGeometry.Fiber`,
  `Scheme.Hom.fiber`, `fiberι`, `fiberToSpecResidueField`, and `fiberHomeo`.
- def-weil-irreducible-components (mathlib_match):
  `Mathlib.Topology.Irreducible`, `irreducibleComponents`.

Proof dependencies are imported without `public` when needed only for the future
proof: `PrincipalIdealRing.isNoetherianRing` and
`UniqueFactorizationMonoid.instIsIntegrallyClosed` from PrincipalIdealDomain and
Polynomial.RationalRoot; `LocallyOfFiniteType` from Morphisms.FiniteType;
`AlgebraicGeometry.quasiFiniteAtPoint_of_generic_algebraic_of_local_dim_le_one`
from `Sheaf.AlgebraicGeometry.Morphisms.GenericAlgebraicityQuasiFiniteDimensionOne`;
`Scheme.Hom.quasiFiniteAtPoint_isolated_in_fiber` from
`WeilConjectures.AlgebraicGeometry.QuasiFiniteAtPointIsolated`.
The base-change clause (b) of lem-weil-pbc-proper-fp-permanence is in the already
publicly imported `Mathlib.AlgebraicGeometry.Morphisms.Proper`; the affine spectrum
is in the imported `Mathlib.AlgebraicGeometry.Scheme`. No import cycle is introduced.

Edge cases checked before writing:

- Empty Y or an empty fibre: no nonempty or surjectivity hypothesis is imposed;
  the universal point/generic hypotheses are vacuous where appropriate, and an
  empty fibre is finite and discrete. The canonical homeomorphism also covers it.
- Components mapping to x itself: the generic hypothesis does not assume dominance
  or discard vertical components; the dimension-one prerequisite covers them.
- Reducible or nonreduced Y: all component generic points are quantified, and
  no irreducibility or reducedness hypothesis is introduced.
- Noetherianness is only asserted for the stalk, not assumed globally or locally
  for X or Y. There is no birationality assumption.
- A field or the zero ring cannot satisfy the dimension-one DVR binders. They are
  already excluded by the node's assumptions, not excluded by an additional binder.
- No restriction on characteristic, residue-field perfection, or separability.
- `set_option autoImplicit false` and `universe u` make all binders explicit;
  the residue-field algebra structure is the specified canonical one.

Searches actually run (msearch.py, group Q92, this item):

- LeanFinder: “A proper morphism with algebraic residue field extensions at every
  component generic point has finite discrete fibre over a DVR stalk”. Eight hits:
  finite-morphism fibre instances, `Scheme.Hom.discrete_fiber`,
  `finite_appTop_of_universallyClosed`, preimmersion/residue-field facts, and the
  Jacobson fibre instance. None has the hypotheses and combined conclusion here.
- Loogle: `AlgebraicGeometry.IsProper, IsDiscreteValuationRing`: zero hits.
- Mathlib grep: `quasiFinite.*dimension|dimension.*quasiFinite|discrete_fiber|finite_preimage_singleton`,
  subdirectory AlgebraicGeometry: ten hits. These concern finite or locally
  quasi-finite morphisms, or finite-near results with an already finite fibre;
  none proves the requested statement from generic algebraicity and a DVR stalk.
- LeanSearch: “A proper generically algebraic morphism has finite discrete fibre
  over a discrete valuation stalk”. Eight hits on proper morphisms, finite
  morphism fibres and the valuative criterion; no exact match.
- Local rg in both `lean/WeilConjectures` and `lean/Sheaf` for
  `proper.*(dvr|Dvr)|generic.*algebraic|algebraic.*generic` and the item id:
  found the prerequisite GenericAlgebraicityQuasiFiniteDimensionOne, its affine
  model, and the downstream NormalModificationCodimensionOne; no existing theorem
  states this node. Searched the chosen declaration and module names in those
  directories and `dag/lean_names_upstream.json`: no collision.

There is no STATEMENT-DISPUTED finding and no statement correction. The supplied
single-file server compiler checked both sandbox and final module contexts cleanly.

## Second reading by Q92

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Worker report

States `AlgebraicGeometry.exists_genericBasis_baseOpen_universalInjectivity` in
`Sheaf.RingTheory.GenericBasisBaseOpenUniversalInjectivity`. The only proof is `sorry`;
there are no new definitions, helper theorems, new nodes, or changes to the accepted split.
The inherited BLOCKED ending concerned a stage-1 delivery, not this stage-2 task:
coord/brief-stage2.md §0 explicitly permits this handoff. The reviewed node still has
no Lean record, so this delivery supplies one.

Source read: literature/stacks-project/flat.tex, lemma-induction-step-fp (Tag 05IA),
the full statement and proof of (1) implies (2), lines 3140–3240. Its special case q=p
and global R-flatness gives exactly this item. No statement correction is needed.

Hypothesis and conclusion correspondence:

- Commutative rings and their homomorphism: `(R B : Type u) [CommRing R]
  [CommRing B] [Algebra R B]`, with map `algebraMap R B`. Sharing a universe
  does not require equal carriers or cardinalities: choose an ambient universe
  containing both rings. The module has its own independent universe v.
- Flat map: `[Module.Flat R B]`, equivalently `RingHom.Flat (algebraMap R B)`.
- Finite presentation of the algebra: `[Algebra.FinitePresentation R B]`.
- Every fibre remains a nonzero integral domain after every extension of its
  residue field: `[GeometricallyIntegral (Spec.map (CommRingCat.ofHom
  (algebraMap R B)))]`. This class quantifies over all field-valued base changes;
  on affine schemes the pullback is the spectrum of the fibre algebra after
  extension. `IsIntegral` of that affine scheme is exactly `IsDomain` of that
  ring, including nonzeroness. Conversely every map R→K into a field factors
  through the residue field of its kernel, so this adds no extra hypothesis.
- B-module M and its restricted R-action: `[AddCommGroup M] [Module B M]
  [Module R M] [IsScalarTower R B M]`. The tower is compatibility of the stated
  restricted action, not an additional mathematical hypothesis.
- M finitely presented over B and flat over R: `[Module.FinitePresentation B M]`
  and `[Module.Flat R M]`; no finite generation over R is imposed.
- Prime r: `(r : Ideal R) [r.IsPrime]`.
- The extension p=rB is prime: `(p : Ideal B) [p.IsPrime]` and
  `hp : p = Ideal.map (algebraMap R B) r`.
- Contraction to r: `hcontract : Ideal.comap (algebraMap R B) p = r`.
- Nonnegative rank and specified B-linear map: `(a : ℕ)` and
  `(α : (Fin a → B) →ₗ[B] M)`. A finite product is the same finite direct sum.
- The specified map becomes an isomorphism over κ(p):
  `hα : Function.Bijective (α.baseChange p.ResidueField)`. This is the actual
  scalar extension of α, not an unrelated isomorphism of the two spaces.
  Tensor symmetry identifies its left-tensor convention with the node's
  M⊗κ(p) convention. Finite free base change identifies its source with κ(p)^a.
- The output is `∃ f : R, f ∉ r ∧ ...`, retaining that same f in every map.
- For every R_f-module L: `∀ (L : Type (max u v w)) [AddCommGroup L]
  [Module (Localization.Away f) L], ...`. The independent w allows arbitrarily
  large testing modules, and the max includes the ring and module universes.
- The injective map is
  `((LocalizedModule.map (Submonoid.powers f) (α.restrictScalars R)).lTensor L)`.
  LocalizedModule.map is linear over `Localization (Submonoid.powers f)`,
  definitionally `Localization.Away f`. Its fraction formula sends m/f^n to
  α(m)/f^n; lTensor sends l⊗z to l⊗α_f(z). The localized source is
  `(B^a)_f`, canonically `B_f^a`. Localizing a B-module at powers of f through
  the R-action is exactly localizing at powers of its image in B: the quotient
  relation and scalar operations are the same. No arbitrary comparison map
  or assumption of universal injectivity is supplied.

Dependency declarations read and used:

- Mathlib.RingTheory.RingHom.Flat: `RingHom.Flat`,
  `RingHom.flat_algebraMap_iff`; Mathlib.RingTheory.Flat.Basic: `Module.Flat`.
- Mathlib.RingTheory.FinitePresentation: `Algebra.FinitePresentation`.
- Mathlib.AlgebraicGeometry.Geometrically.Integral:
  `AlgebraicGeometry.GeometricallyIntegral`; Mathlib.AlgebraicGeometry.Properties:
  `AlgebraicGeometry.IsIntegral` (transitively imported). These implement both
  geometric-integrality and integral-scheme statement dependencies.
- Mathlib.Algebra.Module.FinitePresentation: `Module.FinitePresentation`.
- Mathlib.Algebra.Module.LocalizedModule.Basic: `LocalizedModule`, `mk`, `mk_eq`;
  Mathlib.RingTheory.Localization.Module: `LocalizedModule.map`, `map_mk`.
- Mathlib.AlgebraicGeometry.ResidueField: `Scheme.residueField` and
  `Spec.residueFieldIso`, which identifies the scheme residue field at an affine
  point with the ring `Ideal.ResidueField` used here. This is the same residue
  field, not a replacement definition. Mathlib's ring implementation is used
  directly as is usual in the existing local-generic-basis statement.
- Mathlib.LinearAlgebra.TensorProduct.Defs and .Map: `TensorProduct`,
  `LinearMap.lTensor`, `LinearMap.baseChange`.
- Proof imports: WeilConjectures.RingTheory.Flat.LocalizationPreservesFlatness,
  `Module.Flat.localizedModule_of_algebra`; Mathlib.RingTheory.Flat.Localization,
  `Module.flat_iff_of_isLocalization`.
- The remaining proof dependency
  `lem-sfb-local-flat-generic-basis-universal-injectivity` has neither a Lean
  record nor a Mathlib match in the current node. It is named in the complete
  proof docstring, but there is no module to import. It is not needed to type
  this statement, so it is not duplicated or added as a statement dependency.

Edge cases checked before writing: a=0 is allowed (`Fin 0 → B` is the zero
module); then every localized/tensored map out of it is injective. M=0 is
allowed and the residue-basis hypothesis forces a=0. A field base is allowed
and f can be nonzero; no local-ring hypothesis is added. R=0 or B=0 cannot
have the prime r or p required by the node. No noetherianity or positivity is
imposed. Nonzero geometric fibres are required by IsIntegral, including over
all field extensions. No disputed statement or node fault was found.

Searches actually run using batch2/msearch.py with Q95 and this item:

- LeanFinder: “A generic fibre basis of a relatively flat finitely presented
  module becomes universally injective after shrinking the base”: eight hits,
  including Module.flat_of_isLocalized_span, faithfully flat descent, and
  Algebra.FormallyUnramified.flat_of_restrictScalars; no exact statement.
- Loogle: `Module.Flat, LinearMap.lTensor`: twelve hits; flat-module preservation
  and flat-cokernel exact-sequence statements, not this base-open assertion.
- grep in Mathlib/RingTheory: `universally.*inject|generic.*basis|geometrically.*integral`:
  zero hits.
- LeanSearch: “A generic fibre basis becomes universally injective on a base
  open”: eight hits, chiefly scheme topological universal injectivity; none
  expresses tensor injectivity of this module map.
- rg of lean/WeilConjectures and lean/Sheaf by the exact node id: only the
  consumer's proof docstring, no declaration. rg of both roots for
  `generic.*basis|basis.*generic|genericBasis|generic_basis`: the local 05I3
  theorem and FreeSubtractionFlatness; neither gives a base-open theorem at
  one specified prime. The former assumes a local base; the latter needs
  generic-basis/flatness hypotheses at every base prime. Neither is a one-line
  specialization yielding the present assertion. Additional RingTheory grep
  found localization preservation and the stalk criterion, likewise not this
  base-open existence statement.

Validation: scompile.py compiled this delivery as both sandbox and library
module, exit 0, with no errors or warnings. No direct compiler or global build
was run. The source clone was read only; files were written only in the assigned
sandbox. The prescribed wrappers perform delivery bookkeeping.

## Second reading by Q95

The dispatcher forbids starting other agents. This is a separate second reading
by the same worker; the maintainer's independent review remains necessary.
Reopened the node and module and checked every binder and conclusion against
the correspondence above. In particular: geometric integrality includes
nonempty fibres, p is explicitly the extended ideal and contracts to r,
the map over κ(p) is the scalar extension of the specified α, and tensoring
in the conclusion is over R_f with no flatness requirement on L. Localization
of the finite free source is canonically the finite free localized module,
including rank zero. Test universes are max u v w, not an independent universe
below R. All variables and universes are explicit; autoImplicit is false.
No mismatch was found, no statement changes or private definitions were made.

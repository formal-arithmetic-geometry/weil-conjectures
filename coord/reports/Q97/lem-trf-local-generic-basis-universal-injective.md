## Worker report

Repair of return H3 on immutable head `53591ecc6125`. The retained packet first
passed `deliver2.py --no-push` (dry-run commit `c4755b59a4`), confirming that the
mechanical gates alone did not detect the mathematical interface faults. This
packet changes the signature and supplies the missing transport and primality
statements; it does not merely re-push that head.

`Sheaf.TraceFormula.LocalGenericBasisUniversalInjective` states
`RingHom.local_generic_basis_universal_injective`. Its hypotheses and conclusions
match the node as follows:

- `(R,m)` is `[CommRing R] [IsLocalRing R]`, with `m` the canonical
  `IsLocalRing.maximalIdeal R`. `[CommRing S] [Algebra R S]` specifies `R → S`.
- Flatness and finite presentation are `hflat : RingHom.Flat (algebraMap R S)`
  and `hfp : RingHom.FinitePresentation (algebraMap R S)`.
- Geometrically integral fibres are `hgeom`: for every prime `p`, field `K`,
  residue-field embedding `ι : p.asIdeal.ResidueField →+* K`, and compatible
  `R`-algebra structure, `K ⊗[R] S` is a domain. The equality in `hgeom` only
  identifies the canonical composite `R → κ(p) → K`; it is not an extra
  restriction on the extension. Tensor associativity gives the canonical
  identification with `K ⊗[κ(p)] p.asIdeal.Fiber S`, sending
  `a ⊗ (b ⊗ s)` to `(a * ι b) ⊗ s`, with inverse `a ⊗ s ↦ a ⊗ (1 ⊗ s)`.
  This is the affine formulation of the recorded `GeometricallyIntegral`
  notion (Stacks 05DX and 020H; affine tensor pullback and Spec of a domain).
- The test universe is `max u v w`, with `w` independent of the ring and
  module universes. The accompanying theorem
  `RingHom.geometricFibres_domain_baseChange` gives precisely the domain
  condition for **any** `K : Type z`, including the identity extension in the
  smaller residue-field universe. Its proof docstring describes the canonical
  shrink/lift transport through finitely generated subfields and the injective
  tensor scalar-extension map. Thus the testing-universe encoding is equivalent
  to geometric integrality for arbitrary field extensions, rather than an
  unbridged size restriction. Taking `w = 0` suffices; larger `w` works as well.
- The node's derived prime `ξ = mS` is the actual ideal
  `Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)`.
  `RingHom.maximalIdeal_map_isPrime_of_geometricFibres hgeom` derives its
  primality from the closed fibre, with no prime-ideal instance hypothesis.
  This proof is explicitly supplied to `Ideal.ResidueField`, so `κ(ξ)` is the
  canonical residue field of exactly that ideal, not an arbitrary field.
- `r : ℕ`, `N : Type t`, `[AddCommGroup N] [Module S N] [Module.Finite S N]`
  render the finite module and rank. `[Module R N] [IsScalarTower R S N]`
  identify its restricted scalar action. This structure always exists as
  `Module.compHom N (algebraMap R S)` and is unique under the tower equation;
  no extra property of the S-module is required.
- `q : PrimeSpectrum S` and `hq` say that `q` lies over the maximal ideal.
  `hNq` is flatness of `LocalizedModule q.asIdeal.primeCompl N` over `R`,
  with its explicitly specified canonical `Module.compHom` action.
- `α : (Fin r → S) →ₗ[S] N` renders the map from the finite free module.
  `hα` is bijectivity of its canonical tensor map with `κ(ξ)` over `S`,
  equivalently the specified residue-field linear isomorphism. Tensor symmetry
  identifies the order of the tensor factors with the node's notation.
- The first conclusion quantifies over every `L : Type z` with its `R`-module
  structure and asserts injectivity of `LinearMap.lTensor L
  (α.restrictScalars R)`. The independent universe `z` excludes no module.
- The second conclusion is `Module.Flat R` for
  `LocalizedModule q.asIdeal.primeCompl (N ⧸ LinearMap.range α)`, the localization
  at `q` of the canonical cokernel quotient, again with `Module.compHom`.

The two helper statements render the geometric-integrality and derived-primality
clauses of this same node, and are listed in `lean.declarations`. Every proof is
`sorry`; each declaration has its source, blueprint id, and full natural-language
proof. No definition has postponed data. The natural-language node and all its
non-`lean` fields are unchanged; no statement correction is needed.

Dependency declarations read and used: `RingHom.Flat` / `Module.Flat`
(`Mathlib.RingTheory.RingHom.Flat`); `RingHom.FinitePresentation`
(`Mathlib.RingTheory.RingHom.FinitePresentation`); `Module.Finite`
(`Mathlib.RingTheory.Finiteness.Defs`); `Ideal.ResidueField` and `Ideal.Fiber`
(`Mathlib.RingTheory.LocalRing.ResidueField.Ideal` / `.Fiber`);
`PrimeSpectrum`, `AlgebraicGeometry.Spec`, `Spec.residueFieldIso`, and
`GeometricallyIntegral` from the recorded affine-spectrum, residue-field, and
geometric-property Mathlib interfaces; `LocalizedModule`
(`Mathlib.Algebra.Module.LocalizedModule.Basic`).

The now-recorded proof dependencies are imported without `public`:
`Algebra.projective_of_geometricallyIntegral_fibres`
(`Sheaf.RingTheory.AffineGeometricallyIntegralProjective`),
`Module.universallyInjective_of_residueField_injective`
(`Sheaf.RingTheory.LocalUniversalInjectiveResidue`),
`LinearMap.universally_injective_localizedModule_map`
(`Sheaf.RingTheory.UniversalInjectiveLocalization`), and
`Module.flat_of_universally_exact` (`Sheaf.TraceFormula.LocalUIFlatCokernel`).
Their signatures and proof docstrings were read; the main docstring explains
all three DAG proof steps, including the reduction map through `κ(ξ)`.

Edge cases checked: `r = 0`; `N = 0` (the basis hypothesis forces the appropriate
zero rank); a field base; `q = ξ` and `q` strictly containing `ξ`; unequal ring
universes; module universes independent of both rings; small and large extension
fields; identity residue-field extensions. A zero algebra cannot satisfy geometric
integrality over the nonzero local base. The quotient/localization constructions
also cover a zero cokernel. `scratchpad/Interface.lean` checks the actual imported
interface with independent `u,v,w,z`, an arbitrary extension, the identity extension,
and derived primality. It is a compilation check, not a delivered module.

Searches retained from the initial packet: LeanFinder and LeanSearch queries for
local flat finitely presented geometrically integral generic-basis universal
injectivity returned general flat/tensor lemmas only; Loogle query
`Module.Projective, Module.Flat, Coker, Function.Injective` gave no exact match;
grep for universal injectivity and flat cokernels found only unrelated scheme
morphism and descent material. Repair searches through `msearch.py`:
LeanFinder `geometrically integral tensor fibre domain arbitrary field extension
universe transport` returned 8 results, including geometrically reduced and
integral-extension tensor lemmas but no matching transport; Loogle
`Ideal.ResidueField, IsDomain, TensorProduct` returned 0; grep
`geometricFibres_domain_baseChange|maximalIdeal_map_isPrime_of_geometricFibres`
returned 0. Direct `rg` in upstream `WeilConjectures` and shared `lean/Sheaf`
found none of the main or new helper names. The exact item-id upstream search
also found none. Existing projectivity is reused, not duplicated.

## Second reading by Q97

I reopened the node, current dependency records, Stacks `flat.tex`
`lemma-induction-step` (05I3), `algebra.tex` `definition-geometrically-integral`
(05DX), and the final module for this self-check. No other agent was started,
as required by this repair brief; the maintainer supplies the independent review.

The previous signature had two mismatches: an independent prime-ideal instance,
and a fixed-universe field quantifier with no formal transport. The first is
removed and replaced by a named derived proof passed explicitly to
`@Ideal.ResidueField S`. The second has the transport theorem described above,
whose conclusion permits arbitrary extension-field universe `z`. I checked the
compatible ring-map equality and the identity-extension case, including when the
residue field is in a smaller universe than either ring.

Localness, flatness, finite presentation, all geometrically integral fibres,
finite generation of `N`, the point-over-`m` equality, localized flatness, the
specified linear map, and its generic-fibre isomorphism are all present. The two
conclusion clauses are universal injectivity over `R` and localized cokernel
flatness over `R`. The prime ideal, residue field, tensor map, and restricted
scalar structures are canonical. The module retains independent ring, coefficient
module, extension-field, and tensor-testing universes. The signature recorded in
the node is extracted verbatim from the final file.

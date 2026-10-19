## Worker report

`Sheaf.Paper.FiniteConstantH1Pi1` states equation (3.1) as an abelian-group
isomorphism, its pointed-automorphism naturality, and the specified Weil
inverse-conjugation formula. The theorem's sole proof is `sorry`. The constant
coefficient pullback and all integer Frobenius powers contain actual data.
The node statement and all existing dependency records are unchanged.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The globally fixed finite field and its chosen algebraic closure are
  `D : WeilConjectures.FiniteFieldDatum`; neither the field nor its closure is
  replaced by a fixed canonical model.
- A scheme over that finite field is `U₀ : Over (Spec (.of D.k₀))`.
  `LocallyOfFiniteType U₀.hom` and `QuasiCompact U₀.hom` together express finite
  type; `IsSeparated U₀.hom` expresses separatedness;
  `GeometricallyConnected U₀.hom` expresses geometric connectedness.
- `U = U₀ × k` is exactly the dependency's `(D.geometricFiber U₀).left`.
  The point is `s : Spec (.of Ω) ⟶ U`, with `Field Ω` and `IsAlgClosed Ω`,
  exactly as `def-weil-geometric-point` defines a geometric point.
- `M : Type (u + 1)` with `AddCommGroup M` and `Finite M` is a finite abelian
  coefficient group; `TopologicalSpace M` and `DiscreteTopology M` specify its
  unique discrete topology. There is no coefficient-prime restriction.
- The fundamental group is an arbitrary model `G` with the recorded
  `IsFundamentalGroup (fiber s) G` interface, its compact topological group
  structure and natural actions on the geometric fibres. This is the project's
  convention, identified with the automorphism group of the fibre functor.
- The left side is `Sheaf.H ((constantSheaf U.smallEtaleTopology
  AddCommGrpCat).obj (AddCommGrpCat.of M)) 1`, using the existing Ext model of
  etale cohomology explicitly permitted in the cohomology node's `lean.note`.
  Its identification with derived-global-sections cohomology is the general
  model-comparison bridge identified by that dependency record for stage 3,
  not an added hypothesis of this theorem.
- The right side is `Additive (G →ₜ* Multiplicative M)`. `Multiplicative` and
  `Additive` only change notation; the group law on characters is pointwise.
  `≃+` makes the assertion an isomorphism of abelian groups, not just a set
  bijection. The first conjunct identifies its underlying map with the actual
  upstream canonical torsor/monodromy comparison
  `EtaleTorsor.sheafHEquivContinuousMonoidHom M s G`.
- For every scheme automorphism `a` fixing the geometric point (`ha`), the
  second conjunct is the pullback naturality square evaluated at arbitrary
  `c` and `g`. The fundamental-group map is the existing
  `fundamentalGroupMap` from the canonical `pullbackFiberIso`, followed only by
  the equality identification coming from `ha`. It is not an arbitrary map.
- For every model `G₀` of the arithmetic fundamental group and every element
  `w` of the dependency's actual `weilGroup`, the last conjunct takes the
  integer from the actual `weilGroupDeg`. The cohomology map is pullback by
  the actual morphism `id × Spec(geometricFrobenius ^ deg(w))`.
  The inclusion of the geometric group is the existing `fundamentalGroupMap`
  for `pullback.fst`. The equality naming `h` means exactly
  `h = w⁻¹ g w` under this inclusion; the conclusion reads
  `e(w^* c)(g) = e(c)(h)`. This formulation avoids making an arbitrary choice
  of a conjugation lift in `G`. Existence and uniqueness of `h` are the
  geometric kernel identification, not extra hypotheses on the geometry.

Helpers owned by this node: `finiteConstantH1Pullback` is exactly
`Sheaf.H.map` of the canonical `upperStarConstantSheafIso`, composed with
`Etale.cohomologyMap`; `finiteConstantFrobeniusPower` is a pullback map using the
specified field automorphism raised to an arbitrary integer. The two named
connectedness instances apply Mathlib's
`GeometricallyConnected.connectedSpace_of_subsingleton` to the model and the
base-changed structure morphism. They introduce no mathematical assumption.

Dependency declarations read and used:

- `def-wf-weil-group`: module
  `WeilConjectures.AlgebraicGeometry.FundamentalGroup.WeilGroup`,
  `Scheme.FiniteEtale.constantCover`, `constantCoverAction`,
  `arithmeticFrobenius`, `geometricFrobenius`, `weilGroup`, `weilGroupDeg`.
- `def-weil-pbc-etale-cohomology`: module
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`,
  `Etale.rightDerivedGlobalSections` and `Etale.cohomology`, together with the
  recorded Ext-model convention `CategoryTheory.Sheaf.H`.
- `def-weil-finite-field-fiber`: `Sheaf.Paper.FiniteFieldFiber`,
  `WeilConjectures.FiniteFieldDatum` and its `geometricFiber`.
- `def-galois-fibre-functor`: module
  `WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale`,
  `Scheme.FiniteEtale.fiber`; the abstract fundamental-group-model interface
  uses this same fibre functor.
- Proof imports: `Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence`
  and `Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence` supply the
  recorded finite-etale/FLC and fibre equivalences. The upstream torsor module
  supplies the canonical torsor class/character comparisons; its imports give
  `CategoryTheory.Sheaf.Torsor` and the torsor/H1 classification. The Weil-group
  module imports the recorded exact-sequence module. The two currently unstated
  proof nodes `cor-galois-abelian-h1` and `lem-wf-finite-etale-weil-transport`
  have no module to import; their roles remain in the theorem's seven-step
  proof docstring. No missing notion is needed to type the present statement.

Edge cases checked before and while writing: the empty scheme is excluded
already by geometric connectedness and a geometric point. The trivial finite
abelian group is admitted. Arbitrary finite coefficient groups in characteristic
p are admitted (this is the etale H1/torsor classification, not Kummer theory).
Degree zero gives an inner conjugation and thus the identity on abelian
characters; negative degrees are included by `n : ℤ`. The identity pointed
automorphism uses the canonical pullback map. The arithmetic inclusion is the
canonical geometric-fibre projection, and all lifts of each degree are
quantified, so changing the auxiliary lift cannot change the asserted map.

Searches made (2026-10-17 UTC):

- `msearch.py ... leansearch`: “First etale cohomology of a finite constant
  abelian sheaf is the continuous characters of the etale fundamental group”.
  Eight hits including `CategoryTheory.Sheaf.H`, abstract Galois-category
  instances and abstract group-cohomology H1 results. No complete comparison
  with the stated two naturalities.
- `msearch.py ... leanfinder`: “First etale cohomology of a finite constant
  abelian sheaf is continuous characters of the fundamental group naturally
  for Weil descent”. Eight hits including `IsFundamentalGroup`, continuous
  group cohomology and abstract group-cohomology H1 results; no exact match.
- `msearch.py ... loogle`: `ContinuousMonoidHom, CategoryTheory.Sheaf.H`:
  zero hits.
- `msearch.py ... grep`: `etale.*fundamental|H1IsoOfIsTrivial|torsor.*cohomology`:
  five hits in Mathlib's abstract group-cohomology low-degree file; not etale
  cohomology or Weil descent.
- `rg` searches in upstream `WeilConjectures` and in this project's `lean/Sheaf`
  for the node id, finite constant H1/characters, and candidate new names.
  Upstream `FundamentalGroup.Torsor.sheafHEquivContinuousMonoidHom` gives the
  canonical set bijection, reused here. `FundamentalGroup.Frobenius.monodromy_mapIso`
  gives a conditional fibre-transport formula for torsors with arbitrary
  `σ`, not the full cohomological theorem for actual Weil elements. The
  rank-one `RealSheaves.FundamentalGroup` file only cites these facts in its
  proof of the vanishing theorem. No exact existing full statement or name
  collision was found.

No statement correction, new node, dependency replacement, or statement dispute.
Validation: `scompile.py Q50 lem-wf-finite-constant-h1-pi1` completed successfully
for both the sandbox module and the intended library module, with no errors or
warnings. The displayed elapsed times include server slot acquisition; the
wrapper retained its standard 60-second limit for each Lean process. The
delivery dry run is run separately through `deliver2.py --no-push`.

## Second reading by Q50

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Reviewer fix (maintainer review, 2026-10-18)

H4: the helper `AlgebraicGeometry.finiteConstantFrobeniusPower` (`id × Spec(φ_q⁻¹ ^ n)` on
`(D.geometricFiber U₀).left`) re-defined a landed notion: the geometric Frobenius automorphism
`WeilConjectures.FiniteFieldDatum.geometricFrobenius D U₀ : Aut (D.geometricFiber U₀).left`
of `def-weil-frobenius-detailed` (`Sheaf.AlgebraicGeometry.FrobeniusDetailed`, the same
`id × Spec(γ)`, `γ = φ_q⁻¹`, on the same chosen geometric fibre). The helper is removed and the
Weil clause pulls back along `(D.geometricFrobenius U₀ ^ deg(w) : Aut _).hom`, the same morphism
for every integer degree. The import `WeilConjectures.Mathlib.FieldTheory.Finite.Basic` (now
unused) is replaced by `Sheaf.AlgebraicGeometry.FrobeniusDetailed`. Nothing else changed; the
fixed module compiles clean through `tools/nt_compile.py` (30 s).

## Worker report

The module `Sheaf.AlgebraicGeometry.GenericNilpotentAffinePreparation` states
`AlgebraicGeometry.exists_generic_nilpotent_affine_preparation`. Its sole theorem has
proof `sorry`. There are no new definitions, dependency repairs, new nodes, or statement
corrections. Only the item's `lean` record changes.

Source read: `literature/stacks-project/more-morphisms.tex`, Tag 0575,
`lemma-nonreduced-in-neighbourhood`, lines 7108–7134: reduction of the base, identification
of fibres, affine integral base, nonzero nilpotent generic section, and two shrinkings.
The node's expanded proof supplies the localization and arbitrary-principal-restriction
details. The full seven-step proof is in the theorem docstring, naming its DAG dependencies.

Hypotheses and clauses, in their statement order:

| Node text | Lean rendering |
| --- | --- |
| Schemes and their morphism `f : X → T` | `{X T : Scheme.{u}} (f : X ⟶ T)` |
| Finite type | `[LocallyOfFiniteType f] [QuasiCompact f]`, exactly the recorded conjunction |
| Irreducible base | `[IrreducibleSpace T]`, including nonemptiness |
| Generic point ξ | `(ξ : T) (hξ : IsGenericPoint ξ (Set.univ : Set T))` |
| Nonreduced scheme-theoretic generic fibre | `hgeneric : ¬ IsReduced (f.fiber ξ)` |
| Reduction `T'`, canonical map `i` | `T.nilradical.subscheme`, `T.nilradical.subschemeι` |
| `X' = X ×_T T'` with projection `p` | `pullback f T.nilradical.subschemeι`, `pullback.snd f T.nilradical.subschemeι` |
| Integral `T'` | First conjunct `IsIntegral T.nilradical.subscheme` |
| Homeomorphism on underlying spaces | `IsHomeomorph T.nilradical.subschemeι` |
| Finite type projection | `LocallyOfFiniteType p ∧ QuasiCompact p` |
| For every `t'`, the canonical residue-field map is invertible | `∀ t', IsIso (T.nilradical.subschemeι.residueFieldMap t') ∧ ...` |
| Canonical fibre isomorphism over the identified fields | `∃ e : p.fiber t' ≅ f.fiber (i t'), ...`, with the first equation fixing its map to `X` and the second its map to `Spec κ(i t')`, using precisely `Spec.map (i.residueFieldMap t')` |
| Generic point ξ' of the reduction corresponding to ξ | `∃ ξ', IsGenericPoint ξ' Set.univ ∧ i ξ' = ξ ∧ ...` |
| Nonempty affine base neighbourhood `V = Spec A` | `A : CommRingCat.{u}`, `j : Spec A ⟶ T'`, `IsOpenImmersion j ∧ ξ' ∈ Set.range j`; this identifies `Spec A` with its open image and proves it is nonempty |
| Affine open `U = Spec B` in `X' ×_{T'} V` | `B : CommAlgCat.{u} A`, `k : Spec (.of B) ⟶ pullback p j`, `IsOpenImmersion k` |
| The A-algebra structure is the chart's structure map | `k ≫ pullback.snd p j = Spec.map (CommRingCat.ofHom (algebraMap A B))` |
| A is a domain; B is finite type over A | `IsDomain A` and `(algebraMap A B).FiniteType` |
| Fraction field K, identified with κ(ξ') | `K : CommAlgCat.{u} A`, `IsFractionRing A K`, and `eK : CommRingCat.of K ≅ T'.residueField ξ'` |
| This is the canonical generic-field identification | `Spec.map eK.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ j = T'.fromSpecResidueField ξ'`; it fixes the A-structure, not merely an abstract ring isomorphism |
| K is the localization at the zero prime | For a domain, `IsFractionRing A K` is `IsLocalization (nonZeroDivisors A) K`; these denominators are exactly the complement of `(0)`. This uses the existing fraction-ring notion rather than defining a second field |
| Nilpotent section, positive exponent, generically nonzero | `∃ (b : B) (n : ℕ), 1 ≤ n ∧ b ^ n = 0 ∧ b ⊗ₜ[A] (1 : K) ≠ 0` |
| Every principal restriction `V_a = D(a) = Spec A_a` | `∀ a : A`, followed by equality between the range of `Spec.map (algebraMap A (Localization.Away a))` and `↑(PrimeSpectrum.basicOpen a)` |
| `U ×_V V_a = Spec B_a` | The `IsPullback` square has apex `Spec (.of (Localization.Away (algebraMap A B a)))`, its canonical map to `Spec B`, and its map to `Spec A_a` given by `ka ≫ pullback.snd ...` |
| This is an affine open of `X' ×_{T'} V_a` | `ka` has that exact target and `IsOpenImmersion ka` |
| Compatibility with structure maps | The cartesian square fixes both projections to `U` and `V_a`; the final equation fixes the map to `X'` as the localization map followed by `k` and the original projection |

Here `p`, `i`, `T'`, `V`, `U`, and `V_a` in the table are explanatory names only. The
Lean signature contains their full expressions, with no local notation, private helper,
`let`, hidden `show`, or auto-bound implicit. All schemes and chart rings are in the
same arbitrary universe `u`; coordinate rings of affine opens and their residue fields
are available there. `CommAlgCat` carries actual algebra data, linked to the scheme
maps by equations. These are existential witnesses in the conclusion, not added
hypotheses. The isomorphism `eK` also implies that K is a field, without choosing a
second Field structure incompatible with its bundled commutative ring.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.Topology.Irreducible`: `IsIrreducible`, `IrreducibleSpace` (the node
  `def-weil-irreducible-components` also records `irreducibleComponents`);
  `Mathlib.Topology.Sober`: `IsGenericPoint`.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`,
  `fiberToSpecResidueField`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`, `IsIntegral`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`: `Scheme.nilradical`;
  `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`: `Scheme.IdealSheafData.subscheme`,
  `subschemeι`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the recorded
  scheme-base-change convention is `Limits.pullback`, with `pullback.snd` to the
  new base; its principal declaration `Scheme.Modules.moduleBaseChange` is for
  modules only and is not substituted for scheme base change.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`; the final cartesian square uses Mathlib `IsPullback`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`, `Scheme.fromSpecResidueField`.
- `Mathlib.RingTheory.FiniteType`: the recorded `RingHom.FiniteType`, applied to
  the actual algebra map `A →+* B`.
- `Mathlib.LinearAlgebra.TensorProduct.Tower`: recorded tensor-product and
  base-change convention; `TensorProduct` and its pure tensor `TensorProduct.mk`
  implement exactly `b ⊗ 1` in the factor order in the node.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime` and
  `IsLocalization.AtPrime`; the zero-prime localization here is expressed by
  the equivalent existing `IsFractionRing` in `Mathlib.RingTheory.Localization.FractionRing`.
- `Mathlib.GroupTheory.MonoidLocalization.Away`: `Localization.Away`, with its
  commutative-ring structure and algebra map from
  `Mathlib.RingTheory.Localization.Away.Basic`.

All recorded proof modules are imported, including the reduction universal
homeomorphism, closed-immersion residue-field isomorphism, and affine-chart
base-change interface. The Mathlib proof leaves use the corresponding public
statement imports or explicit proof imports `AffineScheme`, `Pullbacks`,
`PullbackCarrier`, `FunctionField`, `LocalProperties.Reduced`,
`Localization.BaseChange`, and `Localization.Defs`.

Searches actually run for this item:

- `msearch.py ... leanfinder`, query: “A finite type scheme morphism with
  nonreduced generic fibre admits a generically nonzero nilpotent section on an
  affine chart over its reduced integral base”. Eight hits, including
  `isReduced_of_isIntegral`, `IsReduced`,
  `exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen`,
  `Scheme.isNilpotent_of_isNilpotent_cover`, and local reducedness criteria.
  None states the preparation, canonical fibre identifications, or localization
  compatibility together.
- `msearch.py ... loogle`, query:
  `AlgebraicGeometry.IsReduced, AlgebraicGeometry.Scheme.Hom.fiber`.
  One hit: `AlgebraicGeometry.instIsReducedFiberOfGeometricallyReduced`, a different
  implication with geometrically reduced hypothesis.
- `msearch.py ... grep`, query:
  `nonreduced|nonReduced|nilpotent.*generic|generic.*nilpotent`, directory
  `AlgebraicGeometry`: zero hits.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`,
  query `generic.*[Nn]ilpotent|[Nn]ilpotent.*generic|nilpotent_affine_preparation`.
  Hits include `GenericTensorNilpotenceAnnihilator`, `GenericTensorNilpotenceDescent`,
  `GenericProductKernelBound`, and `NonreducedFibreOpen`; their conclusions concern
  nilpotence descent, annihilators, or the eventual open nonreduced locus, not this
  affine preparation. Read `GenericTensorNilpotenceDescent.lean` and
  `NonreducedFibreOpen.lean`; neither has this statement.
- `grep -rn 'lem-trf-generic-nilpotent-affine-preparation' lean/WeilConjectures`:
  zero hits. No existing exact declaration was found.

Edge cases checked before and after writing:

- Empty T is excluded by the given irreducibility and generic point; no extra
  nonemptiness hypothesis is introduced. An empty generic fibre is reduced, so
  cannot satisfy `hgeneric`.
- `n = 0` is explicitly excluded by the node's `1 ≤ n`. `n = 1` would force
  `b = 0` and contradict the asserted nonzero generic tensor. No unnecessary
  `n ≥ 2` condition was added.
- The base ring cannot be zero because `IsDomain A` includes nontriviality.
  The source chart cannot have zero generic ring because its pure tensor is nonzero.
  No Nontrivial assumption was added to arbitrary localizations.
- The clause quantifies over every a, including zero: `Localization.Away 0`
  is the zero ring and its spectrum is empty. Its canonical map is still an open
  immersion and the displayed square is still cartesian. No Field/domain instance
  is requested for localized rings in this clause. At a = 1 it recovers the chart.
- No characteristic restriction, Noetherian hypothesis, separatedness condition,
  finite-presentation assumption, or geometric reducedness replaces the node's data.
- The two fibre equations rule out a merely abstract fibre isomorphism. The
  generic-field equation likewise fixes the coefficient identification. The final
  cartesian square and source-projection equation rule out an arbitrary affine
  open unrelated to the localized original chart.

Validation: prescribed `scompile.py` accepted both the sandbox and library module,
with no errors or unexpected warnings. A first compile exposed a header comment
syntax mistake, which was repaired; a second exposed the need for an explicit
open-to-set coercion on `PrimeSpectrum.basicOpen`, also repaired. No mathematical
statement changed. The final delivery dry run rechecks the completed packet.

## Second reading by Q82

This is the in-session clause audit, with the node and final module reopened;
no additional agent was started, as required by the dispatcher's explicit instruction.
The independent maintainer review follows delivery.

The antecedent is exactly finite type, irreducible base, specified generic point,
and nonreduced ordinary generic fibre. The first four conclusions concern the
specified nilradical reduction and its base-changed projection. For every reduced-base
point the residue-field isomorphism uses `i.residueFieldMap`, and both equations
characterize the fibre isomorphism. In the existential preparation, the two open
immersions are the affine base and source charts; `ξ' ∈ Set.range j` provides both
generic containment and nonemptiness. The chart equation fixes the A-algebra, while
`IsFractionRing` and the equation using `eK` fix the generic coefficient field. The
nilpotence exponent and nonzero pure tensor match the two algebraic conditions.
For each a the principal range is D(a), `ka` is an open immersion into the stated
base-changed source, and `IsPullback` plus the final equation gives exactly both
projection compatibilities. The zero-localization case remains present. No
mathematical mismatch or statement correction was found. The only changes during
elaboration were the header syntax and explicit coercion recorded above.

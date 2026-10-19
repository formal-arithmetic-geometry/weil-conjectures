## Worker report

Item: `lem-trf-artin-join-theorem-6-3`.

The module `Sheaf.AlgebraicGeometry.ArtinJoinTheorem63` states
`artin_join_theorem_6_3` with proof `sorry`. It introduces no definitions and no
additional DAG nodes. The explicit rings `H₁` and `H₂`, with
`Algebra.IsHenselizationAtPrime' A pᵢ Hᵢ`, render the two ordinary henselizations
`A^h_{pᵢ}` in the item statement. The assumptions `[Algebra A Hᵢ]` and the two
`IsScalarTower A Hᵢ Dᵢ` instances express the canonical A-actions through these
henselizations, while `[Algebra.IsIntegral Hᵢ Dᵢ]` renders integrality over
`A^h_{pᵢ}`. The target tensor product is `TensorProduct A D₁ D₂`.

Hypothesis and conclusion correspondence:

- `A : Type u` with `[CommRing A]` is the commutative base ring.
- `p₁ p₂ : Ideal A` with prime instances are the two prime ideals.
- `H₁ H₂` with commutative-ring, localization-algebra and henselian-local instances,
  together with `hH₁` and `hH₂`, are the universal henselizations of the two prime
  localizations. The universal property is the recorded dependency
  `Algebra.IsHenselizationAtPrime'`.
- `D₁ D₂` with commutative-ring, `Hᵢ`-algebra, A-algebra, scalar-tower and local-ring
  instances are the local integral algebras in the node. The two
  `Algebra.IsIntegral Hᵢ Dᵢ` instances say elementwise that every element satisfies a
  monic equation over the corresponding henselization.
- The first conjunct quantifies every `x : PrimeSpectrum E` and provides
  `HenselianLocalRing (AlgebraicGeometry.componentRing E x)`, exactly the
  quasi-acyclic assertion that every component ring is henselian local.
- For each component, `hC` supplies its henselian-local structure and `C` abbreviates
  `AlgebraicGeometry.componentRing E x`. The canonical maps `f₁` and `f₂` are the
  quotient map by `componentIdeal E x` composed with the left and right tensor
  inclusions. These are the maps `Dᵢ → C` in the node.
- If both `f₁` and `f₂` are not `IsLocalHom`, the first clause states
  `IsSepClosed (C ⧸ IsLocalRing.maximalIdeal C)`, i.e. the residue field is separably
  closed. The field structure is installed by `Ideal.Quotient.field`.
- If `f₁` is local, the second clause states `RingHom.IsIntegral f₁` and supplies the
  induced quotient map `g : D₁/m_{D₁} →+* C/m_C`; its displayed composition equation
  identifies this with the canonical residue map, and `Algebra.IsAlgebraic` states that
  the residue extension is algebraic. The `f₂` clause is identical with indices swapped.
- `IsLocalHom` is the Mathlib predicate that the inverse image of the target maximal
  ideal is the source maximal ideal, matching the final sentence of the item.

Dependency declarations used:

- `Sheaf.RingTheory.GeneralizedHenselizationAtPrime`,
  `Algebra.IsHenselizationAtPrime'` (repaired dependency record).
- `Mathlib.RingTheory.Localization.AtPrime.Basic`,
  `Localization.AtPrime`.
- `Sheaf.TraceFormula.AffineEtaleCoverComponentCriterion`,
  `AlgebraicGeometry.componentIdeal`, `componentRing`, and `componentSpectrumMap`.
- `WeilConjectures.Mathlib.RingTheory.Henselian`, `HenselianLocalRing` and
  `IsStrictlyHenselianLocalRing`.
- `Mathlib.FieldTheory.IsSepClosed`, `IsSepClosed`.
- `Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs`, `RingHom.IsIntegral` and
  `Algebra.IsAlgebraic`.
- Proof-plan imports are present for the stated dependencies:
  `Sheaf.RingTheory.HenselizationsCommonNormalCover`,
  `Sheaf.TraceFormula.NormalTensorComponentJoinModel`,
  `Sheaf.TraceFormula.ArtinEmbeddedHenselJoin`,
  `Sheaf.TraceFormula.IndEtaleLocalHenselianIntegral`, and
  `Sheaf.RingTheory.IntegralComponentHenselianPermanence`.
  The four generic integral lemmas in `proof_deps` are Mathlib leaves and have no
  project module to import; `lem-trf-nonlocal-join-internal-normalization` has no
  recorded Lean declaration and is therefore not imported.

Edge cases checked: `p₁ = p₂`; zero or nonreduced A; the zero tensor product (the
component quantifiers are vacuous); components with either local map or with both maps
nonlocal; and arbitrary residue characteristics. No Noetherian, finite-generation,
domain or separability hypothesis was added. All universes and variables are explicit.

Searches made: the node's recorded `leanfinder`, `leansearch`, `loogle`, and `grep`
queries were rerun with `msearch.py` for Artin tensor joins, henselian local rings,
component rings, and quasi-acyclicity. Mathlib hits were only generic henselian,
integrality, localization, and residue-field declarations; no declaration states this
join theorem. `rg` over `WeilConjectures/` and `lean/Sheaf/` found only the separate
Artin tensor-residue theorem and component-ring constructions. No existing declaration
has this theorem's hypotheses and conclusions.

No `STATEMENT-DISPUTED` flag or node fault was found. The only postponed proof is the
named theorem `artin_join_theorem_6_3` itself.

## Second reading by Q108

I reread the target node and the final signature line by line. `Hᵢ` plus
`IsHenselizationAtPrime'` supplies exactly the node's notation `A^h_{pᵢ}`; `Dᵢ` are
local commutative algebras integral over those rings; and the tensor product is over A.
For every component, the quotient by the component ideal is used, and its induced maps
from both factors are the canonical tensor inclusions. The three alternatives preserve
both nonlocal hypotheses, each local hypothesis, integrality of the corresponding map,
and the algebraic/separably-closed residue conclusion. The universal residue map is
written by its quotient composition equation. The explicit `hC` is the local-ring
structure guaranteed by quasi-acyclicity and introduces no mathematical assumption.
No clause, edge case, or source hypothesis is dropped, and every proof remains `sorry`.

## Reviewer fix (NT-cc stage-2 second reader, 2026-10-18)

- H3 (hypothesis missing, statement false as delivered): the delivered signature had both
  `[Algebra (Localization.AtPrime pᵢ) Hᵢ]` and an independent `[Algebra A Hᵢ]` with no
  compatibility, so the `A`-action on `Hᵢ`, hence on `Dᵢ` and on `E = D₁ ⊗_A D₂`, need not be
  the node's `A → A_{pᵢ} → A^h_{pᵢ}`. Counterexample to the delivered statement: `A = ℚ[X]`,
  `p₁ = p₂ = ⊥`, `Hᵢ = Dᵢ = Localization.AtPrime ⊥ = ℚ(X)` (a field, its own henselization),
  `A` acting through `X ↦ 0`; then `E ≅ ℚ(X) ⊗_ℚ ℚ(X)`, a connected domain that is not local,
  so its only component ring is not henselian local. Added
  `[IsScalarTower A (Localization.AtPrime p₁) H₁] [IsScalarTower A (Localization.AtPrime p₂) H₂]`,
  exactly as in the dependency `normalTensorComponentJoinModel` the proof uses.
- Universes: `Hᵢ : Type vᵢ`, `Dᵢ : Type wᵢ` independent of `A : Type u` (the recorded
  `Algebra.IsHenselizationAtPrime'` is universe polymorphic for this purpose); the citer
  `artin_henselian_tensor_residue_dichotomy` (all in `Type u`) is a specialization.
- H8: the statement docstring now carries the node's nine proof steps.
- Compile: `nt_compile.py` on the fixed module, clean (no error, autoImplicit false).

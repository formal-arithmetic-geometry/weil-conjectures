## Worker report

The module `Sheaf.FieldTheory.SylowConstantsFieldDegree` states
`FieldExtension.sylow_fixedField_degree`. Its sole theorem has proof `sorry`;
there are no new definitions, helper theorems, new nodes, dependency repairs,
or statement corrections. The node copy changes only `lean`.

Source checked: ILO, Travaux de Gabber, Expose X, 2.3 Step 2, printed p.151,
diagram (2.c), specifically the sentences that S1/G1 over S is radicial,
S1/L over S1/G1 has degree prime to ell, S' = S1/L has degree prime to ell
over S, and S1 over S' is Galois. The node already correctly refines the
last phrase to the image of L when the constants action is ineffective.
The complete five-step proof from the DAG is transcribed in the theorem
docstring, with its five proof dependencies named.

Every hypothesis and clause is represented as follows:

| Node text | Lean rendering |
| --- | --- |
| Fields e and K | `(e : Type u) (K : Type v) [Field e] [Field K]` |
| Extension K/e | `[Algebra e K]`, whose structure map is `algebraMap e K` |
| Finite field extension | `[FiniteDimensional e K]` |
| Prime ell | `(ℓ : ℕ) (hℓ : Nat.Prime ℓ)` |
| ell differs from the characteristic | `(hchar : ℓ ≠ ringChar e)` |
| Finite group G | `(G : Type w) [Group G] [Finite G]` |
| Action by e-automorphisms | `(ρ : G →* (K ≃ₐ[e] K))` |
| E = K^G | `IntermediateField.fixedField ρ.range` |
| E/e purely inseparable | `(hinsep : IsPurelyInseparable e (IntermediateField.fixedField ρ.range))` |
| Subgroup L of G | `(L : Subgroup G)` |
| L has ell-power order | `(hpower : ∃ n : ℕ, Nat.card L = ℓ ^ n)` |
| L has index prime to ell | `(hindex : ¬ ℓ ∣ L.index)` |
| F = K^L | `IntermediateField.fixedField (L.map ρ)` throughout the conclusion |
| F/e finite | `Module.Finite e (IntermediateField.fixedField (L.map ρ))` |
| Degree F/e prime to ell | `¬ ℓ ∣ Module.finrank e (IntermediateField.fixedField (L.map ρ))` |
| K/F finite | `Module.Finite (IntermediateField.fixedField (L.map ρ)) K` |
| K/F Galois | `IsGalois (IntermediateField.fixedField (L.map ρ)) K` |
| Full automorphism group exactly the image of L, as actual automorphisms | Equality of `Set.range (fun σ : K ≃ₐ[IntermediateField.fixedField (L.map ρ)] K ↦ (σ : K → K))` with `Set.range (fun g : L ↦ (ρ g : K → K))` |
| Actions need not be faithful | No injectivity or `FaithfulSMul` hypothesis; `ρ.range` and `L.map ρ` take effective images |

The last equality uses all F-algebra automorphisms of K, rather than merely
those e-automorphisms already known to come from L. Its two inclusions assert
that every F-automorphism is induced by L and every image of L fixes F.
The equality identifies the underlying functions, so it identifies actual
automorphisms and their composition, not merely abstract isomorphism types.
`IntermediateField.mem_fixedField_iff` makes the fixed-field expressions
exactly the fixed-element equations in the node, including ineffective actions.

Dependency interfaces read and used:

- `def-weil-field`: Mathlib `Field` in `Mathlib.Algebra.Field.Defs`.
- `def-pc-field-extension`: `Algebra` in `Mathlib.Algebra.Algebra.Defs`.
- `def-sfb-finite-infinite-set`: `Set.Finite` in `Mathlib.Data.Finite.Defs`.
  `[Finite G]` is the corresponding underlying-type finiteness; `Set.Finite`
  is by definition finiteness of a subtype. No cardinal bound is substituted.
- `def-pc-field-tower`: public import `Sheaf.FieldTheory.FieldTower`.
  Its `FieldExtension.degree` is the natural-valued `Module.finrank` when
  `Module.Finite`, and infinity otherwise. The finite degree here is therefore
  directly `Module.finrank`; `Module.Finite` and `IsPurelyInseparable` are the
  Mathlib notions explicitly identified by that module. There is no second
  definition of degree or of pure inseparability.
- `Mathlib.FieldTheory.Galois.Basic`: `IntermediateField.fixedField`,
  `IntermediateField.mem_fixedField_iff`, and `IsGalois`. `IsGalois` has exactly
  normal and separable fields; separability includes algebraicity in Mathlib.
  The `IsPurelyInseparable` docstring in
  `Mathlib.FieldTheory.PurelyInseparable.Basic` was read; over fields it has
  exactly the characteristic-power meaning and the characteristic-zero
  surjectivity specialization recorded by the dependency node.
- Proof imports follow the recorded nodes: `IsGalois.of_fixed_field`,
  `IsGalois.mem_range_algebraMap_iff_fixed` and `IsGalois.card_aut_eq_finrank`
  from `Mathlib.FieldTheory.Galois.Basic`; `FixedPoints.finrank_eq_card` and
  the fixed-field finite-dimensional instance from `Mathlib.FieldTheory.Fixed`;
  `Module.finrank_mul_finrank` from `Mathlib.LinearAlgebra.Dimension.Free`;
  `Subgroup.index_map_dvd` and `Subgroup.card_mul_index` from
  `Mathlib.GroupTheory.Index`; and `IsPurelyInseparable.exists_pth_root_tower`
  from `WeilConjectures.FieldTheory.PurelyInseparablePthRootTower`.
  Full signatures and surrounding hypotheses/docstrings were checked.
  The source of the last theorem, including its characteristic and universe
  binders and its empty-tower and final-step clauses, was read in full.

Edge cases checked before writing:

- Characteristic zero: pure inseparability identifies E with the base; the
  inseparable factor has degree one. No positive-characteristic assumption
  appears in the theorem.
- Positive characteristic p different from ell: the inseparable factor is a
  power of p, including exponent zero, hence prime to ell.
- Trivial action of any finite G: E = F = K, K/e is finite purely inseparable,
  and K/F has only the identity automorphism. The function-set equality works
  even when L is nontrivial and its entire action is ineffective.
- L is trivial: F = K, and the prime-to-ell index condition gives the required
  prime-to-ell degree by the same effective-image argument.
- L = G: F = E and the index is one; the extension over the purely inseparable
  constants has the image of G as its full Galois group.
- Degree one and the empty purely inseparable tower are included. Fields are
  nontrivial by `Field`, as in the node. Universes u, v, w are independent and
  explicit; no constraint identifies the group universe with a field universe.
- The ell-power-order hypothesis is retained even though the accepted DAG
  proof needs only the prime-to-ell index. No faithful-action assumption was
  inferred from it, and no assertion incorrectly sets `[K:F] = |L|`.

Searches for an existing full statement:

1. `msearch.py ... leanfinder` with the query "For a finite field extension with
   a finite possibly nonfaithful group of base field automorphisms, a Sylow
   subgroup fixed field has degree coprime to the Sylow prime if the total
   fixed field is purely inseparable": eight hits, including
   `FixedPoints.isSeparable`, `IsGalois.of_fixed_field`,
   `IsGaloisGroup.fixedPoints`, and
   `IntermediateField.finrank_fixedField_eq_card`. None gives the full
   conclusion over a purely inseparable fixed base with a prime-to-ell index.
2. `msearch.py ... loogle "IntermediateField.fixedField, IsPurelyInseparable"`:
   zero hits.
3. `msearch.py ... grep "sylow|coprime.*finrank|finrank.*coprime" FieldTheory`:
   three hits, all linear-disjointness documentation/theorems; no match.
4. `rg` of `lean/WeilConjectures` and `lean/Sheaf` for Sylow/constants/fixed-field
   pure-inseparability terms: existing Sylow module filtrations and normal
   extension fixed-field pure-inseparability results, but no theorem with
   this statement. `grep -rn` for the item id in `lean/WeilConjectures` found
   nothing. No declaration-name clash for `sylow_fixedField_degree` in either
   project tree, Mathlib, or `dag/lean_names_upstream.json`.

Validation: `scompile.py Q124 lem-sfb-sylow-constants-field-degree` compiled
both sandbox and library module views cleanly (1.2 seconds each); no errors
or warnings. The only postponed proof is the named item theorem. No node
fault or disputed statement was found.

## Second reading by Q124

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

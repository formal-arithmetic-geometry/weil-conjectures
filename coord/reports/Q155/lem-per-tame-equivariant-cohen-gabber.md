## Worker report

The module `Sheaf.RingTheory.TameEquivariantCohenGabber` states
`IsLocalRing.tame_equivariant_cohen_gabber` with one `sorry`.
`IsLocalRing.IsTameEquivariantCohenGabberPresentation` is a transparent predicate
bundling the clauses of this theorem's own promised presentation, with real data
and no proof holes. It introduces no replacement for any standard notion.
The node's statement, dependencies, and proof are unchanged.

I read ILO Exposé IV 2.1.1–2.1.4 and 2.1.12, and 2.2.2–2.2.6
(printed pp.50, 52–55). The source states the finite generically étale equivariant
map with residue section and fixed variables. The equidimensional case also has
the injective torsion-free normalization of IV 2.1.1. The proof docstring records
all seven steps of the DAG node, including the Frobenius argument for perfect
constants. I also read the current blueprint's ancestor proof,
`sec-deligne-laumon-a1/sk-p-dl-a1-perverse/lem-per-artin-gabber-affine-curve.proof.md`.
This item is an auxiliary node, not that blueprint unit's statement.

Every hypothesis is rendered as follows:

| Node hypothesis | Lean rendering |
| --- | --- |
| Commutative local ring C with maximal ideal n | `(C : Type u) [CommRing C] [IsLocalRing C]`, with `IsLocalRing.maximalIdeal C` |
| Reduced | `[IsReduced C]` |
| Noetherian | `[IsNoetherianRing C]` |
| Complete and separated for n | `[IsAdicComplete (maximalIdeal C) C]` |
| Characteristic p > 0, p prime | `(p : ℕ) [Fact p.Prime] [CharP C p]` |
| Dimension e ≥ 1 | `(e : ℕ) (he : 1 ≤ e) (hdim : ringKrullDim C = (e : WithBot ℕ∞))` |
| Equidimensional: dim(C/q) = e for each minimal prime | `hequidim : ∀ q : Ideal C, IsMinimalPrime q → ringKrullDim (C ⧸ q) = (e : WithBot ℕ∞)` |
| k = C/n | Mathlib's `IsLocalRing.ResidueField C`, defined as this quotient, and `residue C` |
| Finite group acting by local ring automorphisms | `(H : Type v) [Group H] [Finite H] (ρ : H →* RingAut C)`; ring automorphisms of a local ring preserve units, hence its maximal ideal |
| Group order invertible in k | `htame : IsUnit (Nat.card H : ResidueField C)` |
| Optional specified subfield k₀ ⊆ C | `(K₀ : Type w) [Field K₀] (constants : Option (K₀ →+* C))`; a unital field-to-nonzero-ring map is injective |
| Its perfection means bijective p-th power | `hperfect`, conditional on `constants = some ι`, is `Function.Bijective (fun a : K₀ ↦ a ^ p)` |
| Its H-stability | `hstable`, conditional on `some ι`, says `∀ h a, ∃ b, ρ h (ι a) = ι b`; inverses in H give equality, rather than only forward invariance, of the image |

The theorem quantifies over independent universes for C, H and K₀. There is no
cardinality restriction on the acting group beyond finiteness and no faithfulness
assumption. Choosing `none` imposes no perfection or stability requirement.

Every conclusion clause is expanded in the presentation predicate:

| Node conclusion | Lean rendering |
| --- | --- |
| A field section s : k ↪ C | Existential `s : ResidueField C →+* C`; `(residue C).comp s = RingHom.id (ResidueField C)`; injectivity follows already from this identity (also from the field source) |
| H-equivariance of s with the residue action | `∀ h a, ρ h (s a) = s (ResidueField.mapEquiv (ρ h) a)` |
| e chosen parameters in n | Existential `x : Fin e → C`, with `∀ i, x i ∈ maximalIdeal C` |
| Parameters fixed by H | `∀ h i, ρ h (x i) = x i` |
| The continuous evaluation map from k[[T₁,...,Tₑ]] | Existential `f : MvPowerSeries (Fin e) (ResidueField C) →+* C`, its values on `MvPowerSeries.C` and `MvPowerSeries.X`, and `∀ r, ∃ N, (variableIdeal ^ N).map f ≤ maximalIdeal C ^ r` |
| Coefficient map s and Tᵢ ↦ xᵢ | `∀ a, f (MvPowerSeries.C a) = s a` and `∀ i, f (MvPowerSeries.X i) = x i` |
| Injective and local | `Function.Injective f ∧ IsLocalHom f` |
| Module-finite | `Module.Finite (MvPowerSeries (Fin e) (ResidueField C)) C` using exactly `f.toAlgebra` |
| Torsion-free | `Module.IsTorsionFree (MvPowerSeries (Fin e) (ResidueField C)) C` for the same algebra structure |
| Identity on residue fields | `∀ F, residue C (f F) = MvPowerSeries.constantCoeff F`; the power-series residue field is canonically k by the constant coefficient map |
| Radical of parameter ideal is n | `(Ideal.span (Set.range x)).radical = maximalIdeal C` |
| H acts on coefficients by the residue action, fixes variables; evaluation equivariant | `∀ h F, ρ h (f F) = f (MvPowerSeries.map (ResidueField.mapEquiv (ρ h)).toRingHom F)`; `MvPowerSeries.map` acts coefficientwise and fixes all variables |
| K = Frac(k[[T]]) | `FractionRing (MvPowerSeries (Fin e) (ResidueField C))` throughout the final conjunct |
| The generic algebra is a finite product of fields | Existential `n : ℕ`, `L : Fin n → Type u`, field and K-algebra structures on each `L i`, and `Nonempty ((K ⊗[R] C) ≃ₐ[K] (∀ i : Fin n, L i))` |
| Each factor finite and separable over K | `∀ i, Module.Finite K (L i) ∧ Algebra.IsSeparable K (L i)` |
| Respect the specified perfect field after residue identification | Outside the predicate: `∀ ι, constants = some ι → ∀ a, s (residue C (ι a)) = ι a` |

The predicate's definitional `letI := f.toAlgebra` supplies the actual scalar
structure associated with the displayed map, not an extra assumption or a
choice. Its unfolding is an ordinary definition-body let. There are no lets in
the theorem signature. The tensor product is written `K ⊗[R] C`, the canonical
left K-algebra version of the node's `C ⊗[R] K`, as permitted by the recorded
base-change node. The displayed algebra equivalence, rather than only a ring
equivalence, preserves the generic field's scalar structure.

The evaluation map is not arbitrary. For finite variable sets the constant
and variable clauses determine its polynomial values. A series differs from
its degree-N truncation by the N-th power of the variable ideal. Continuity
therefore determines the value of the full series in the separated target.
This agrees with the existing universal-property interface
`MvPowerSeries.exists_ringHom_of_isAdicComplete` in
`WeilConjectures.RingTheory.PowerSeriesUniversalPropertyComplete`, whose full
signature and docstring I read. I do not redefine or choose a second evaluation
construction. Its interface even proves uniqueness without an extra continuity
hypothesis because the variable ideal is finitely generated.

The eight statement dependencies use the following recorded declarations
(signatures and docstrings read in their source files):

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`.
- `def-weil-pbc-adically-complete-ring`: `Mathlib.RingTheory.AdicCompletion.Basic`, `IsAdicComplete`.
- `def-weil-pbc-krull-dimension-ring`: `Mathlib.RingTheory.KrullDimension.Basic`, `ringKrullDim`.
- `def-weil-pbc-multivariate-power-series`: `Mathlib.RingTheory.MvPowerSeries.Basic`, `MvPowerSeries` (publicly supplied by the imported `Inverse` module).
- `def-weil-finitely-generated-module`: `Mathlib.RingTheory.Finiteness.Defs`, `Module.Finite`.
- `def-weil-module-base-change`: `Mathlib.LinearAlgebra.TensorProduct.Tower`, `TensorProduct` and its canonical base-change module structure, with algebra multiplication from `Mathlib.RingTheory.TensorProduct.Basic`. The node explicitly permits the left-factor scalar convention.
- `def-pc-field-extension`: `Mathlib.Algebra.Algebra.Defs`, `Algebra`.
- `def-weil-pbc-separable-algebraic-extension`: `Mathlib.FieldTheory.Separable`, `Algebra.IsSeparable`, which includes algebraicity.

The other standard constructions are also reused directly: `RingAut`, `ResidueField`,
`residue`, `ResidueField.mapEquiv`, `IsMinimalPrime`, `FractionRing`, `Ideal.radical`,
and `Module.IsTorsionFree`. No dependency repair or new independent definition node
is required.

Proof-dependency imports are included for all available recorded modules and
Mathlib matches. The following proof-only dependencies have no available module
and are therefore not imported: `lem-per-tame-fixed-ring-generic-components` and
`lem-per-parameter-ideal-formal-normalization` have no Lean record;
`lem-per-coefficient-field-generic-differential-basis` and
`lem-per-finite-formal-map-differential-cokernel` have records noting that their
modules were deleted on 2026-10-20. I confirmed the latter two modules are absent
locally and `scompile.py --source` returns `Module source unavailable` for each.
None defines an object used to type the present statement. Their node IDs and
full mathematical uses remain in the theorem's proof docstring.

Edge cases checked before and after writing:

- `e = 0` is excluded by the source's explicit `e ≥ 1`; no additional bound on e is imposed.
- The zero ring is excluded by `IsLocalRing`, as required by a local ring with a residue field. No domain assumption is made on C.
- For C = k[[t]] and trivial H, choose the coefficient section and x = t: the normalization is the identity and the generic product has one factor.
- For C = k[[t]] with t ↦ ζt of order m prime to p, x = t^m is fixed and the fraction extension is finite separable. This tests the need for tame order rather than trivial action on the tangent space.
- For C = k[[x,y]]/(xy) with the order-two swap in odd characteristic, the fixed parameter x+y gives two generic field factors. Thus reducible reduced equidimensional rings are covered. In characteristic two the swap fails the tame-order hypothesis.
- The action on k need not be trivial: coefficient automorphisms of k acting on k[[t]] and fixing t fit the residue-equivariance formula. The optional perfect subfield may also carry a nontrivial H-action.
- `none` leaves all three conditional clauses vacuous and allows imperfect residue fields. `some ι` encodes its actual inclusion and the exact residue-identification compatibility, rather than requiring a chosen equality with a separate residue subfield.
- Empty generic products are syntactically allowed, but cannot witness the conclusion for an injective map into nonzero C. Finite products need no artificial nonempty index hypothesis.
- The factor fields can be taken in `Type u`: the generic algebra is in that universe, and its factor fields are quotients of it. The unrelated universes v and w impose no extra size equality.

Searches made (all by the prescribed msearch wrapper, with raw logs in the sandbox):

- LeanFinder: `Tame equivariant Cohen Gabber theorem reduced complete Noetherian local ring finite group invariant formal parameters`. Eight hits: arithmetic Frobenius existence/construction, `Ideal.Quotient.finite_of_isInvariant`, `HenselianLocalRing`, BDeRham constructions and `PowerSeries.exists_isWeierstrassFactorization`. None states the theorem.
- Loogle: `MvPowerSeries, IsAdicComplete`. One hit, `MvPowerSeries.instIsAdicCompleteSpanRangeXOfFinite`; useful completeness infrastructure, no equivariant normalization result.
- LeanSearch: `Finite separable generic fiber of formal power series normalization of reduced equidimensional complete local ring`. Eight hits concerning formal étaleness of separable field extensions, separable elements and polynomials, and inseparability degree. None constructs this normalization.
- Mathlib grep: `Cohen.Gabber|equivariant.*[Cc]ohen|[Cc]ohen.*equivariant`. No hits.
- Project/upstream `rg` with the same expression, `Cohen.Gabber|tameEquivariant|tame_equivariant|FormalNormalization|formalNormalization`, and exact proposed declaration names found no matching statement. The exact node-ID grep in `lean/WeilConjectures` also returned no hit.
- Further source searches for formal evaluation, residue automorphisms, finite separable generic products and torsion-free modules led to the standard interfaces used above. The formal-local-presentation structure found in the project concerns a surjection onto a completion, not this finite injective equivariant normalization, and was not duplicated.

Validation: the prescribed server compiler accepted the module in both sandbox
and library contexts (1.6 s and 1.5 s), with no errors or non-sorry warnings.
A final dry run and delivery follow. No statement correction or disputed
mathematical clause was found.

## Second reading by Q155

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

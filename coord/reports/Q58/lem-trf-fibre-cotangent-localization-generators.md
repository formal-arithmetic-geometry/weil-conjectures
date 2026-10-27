## Worker report

States `KaehlerDifferential.FibreLocalization.comparison` in
`Sheaf.RingTheory.FibreCotangentLocalizationGenerators`. Its only postponed proof is
`comparison := by sorry`. The helper declarations named in `lean.declarations` provide
concrete canonical maps, aliases of the existing Mathlib objects, and the unfolded
comparison specification. No new DAG nodes, dependency repairs, or statement corrections.

### Hypotheses and clauses

| Node text | Lean rendering |
| --- | --- |
| Homomorphism of commutative rings R to A | Independent universes `R : Type u`, `A : Type v`, `[CommRing R]`, `[CommRing A]`, `[Algebra R A]`. Any specified ring map is represented by its `RingHom.toAlgebra`; no injectivity, flatness, finiteness, or characteristic condition is assumed. |
| Prime q and contracted p | `(q : Ideal A) [q.IsPrime]`; `basePrime q` is `q.comap (algebraMap R A)`. Its prime instance is Mathlib's comap instance. |
| k = kappa(p) and F = k tensor_R A | `(basePrime q).ResidueField` and the alias `fibre q := (basePrime q).Fiber A`, exactly the recorded `Ideal.Fiber` orientation. |
| The map F to kappa(q), c tensor a to c-bar times a-bar | `residueMap q` is `Algebra.TensorProduct.lift` of the canonical `Ideal.ResidueField.mapₐ` and `IsScalarTower.toAlgHom R A q.ResidueField`. The definition of the lift gives precisely this pure-tensor formula. |
| Q is the kernel and L = kappa(Q) | `fibrePoint q` bundles `RingHom.ker (residueMap q).toRingHom` with Mathlib's `RingHom.ker_isPrime`; `fibreField q` is its `asIdeal.ResidueField`. |
| M = Omega A/R and N = Omega F/k | `KaehlerDifferential R A` and `KaehlerDifferential (basePrime q).ResidueField (fibre q)`, as expanded in `ComparisonAlong`. |
| The A-module structure on F | `fibreAlgebra q` is only an alias of `Algebra.TensorProduct.rightAlgebra`, the canonical inclusion `a` to `1 tensor a`. |
| Differential base-change beta : N isomorphic to F tensor_A M | `beta q` is the inverse of the existing `KaehlerDifferential.tensorKaehlerEquiv R k A F`, so it is the specified canonical F-linear equivalence. No arbitrary equivalence is assumed or chosen. |
| Induced map A_q to L | The conclusion existentially provides `ρ : Localization.AtPrime q →+* fibreField q` and requires its value on every `a/1` to be the image under A to F to L. This is the localization universal-property characterization of the induced map, and determines it uniquely. |
| Localized module M_q and tensor products | `LocalizedModule q.primeCompl M`, `Mq ⊗[Aq] L`, and `N ⊗[F] L`; all are the dependency declarations, with `LocalizedModule.mk` as the fraction constructor. |
| Canonical L-linear theta | `ComparisonAlong q ρ` is a fully defined proposition asserting an `L`-linear equivalence. Its L-actions are fixed by transporting the standard left-factor actions through `TensorProduct.comm` with `AddEquiv.module`. These are the right-factor actions on the node's tensor orientation; no arbitrary module structure is quantified over. The two pure-tensor formulas determine theta. |
| Value on (omega/a) tensor z for a outside q | First conjunct of `ComparisonAlong`: `ha : a ∉ q`, fraction `LocalizedModule.mk ω ⟨a, ha⟩`, image `(beta q).symm (1 ⊗ₜ[A] ω) ⊗ₜ[F] (z / a-bar)`, with a-bar the composite A to F to L. |
| Inverse on beta inverse(b tensor omega) tensor z | Second conjunct: `θ.symm ((beta q).symm (b ⊗ₜ[A] ω) ⊗ₜ[F] z)` equals `LocalizedModule.mk ω 1 ⊗ₜ[Aq] (algebraMap F L b * z)`. |
| Any r >= 0 generators m_1,...,m_r of M_q | `∀ (r : ℕ) (m : Fin r → Mq), Submodule.span Aq (Set.range m) = ⊤ → ...`. Naturals include zero, and no independence is required. |
| Their images span N tensor_F L | `Submodule.span L (Set.range (fun i : Fin r ↦ θ (m i ⊗ₜ[Aq] 1))) = ⊤`. |
| Finite-dimensional dimension <= r | `FiniteDimensional L (N ⊗[F] L) ∧ Module.finrank L (N ⊗[F] L) ≤ r`. Including finite dimensionality ensures `finrank` is the dimension defined by the dependency, rather than its infinite-rank default value. |

The module and theorem docstrings name the source and blueprint id. The theorem docstring
contains all six DAG proof steps: denominators and induced ring map; differential base
change; localization cancellation; the second tensor cancellation and inverse formulas;
spanning; independent-subfamily dimension bound. All definitions contain real data and no
postponed proofs. The proposition `ComparisonAlong` merely packages this node's conclusion.

### Dependency declarations and sources read

- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime` in
  `Mathlib.RingTheory.Localization.AtPrime.Basic`; `Ideal.ResidueField` in
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`; `Ideal.Fiber` in
  `Mathlib.RingTheory.LocalRing.ResidueField.Fiber`. Their source signatures and
  residue-field/fibre docstrings were read. `residueMap` also uses the existing
  `Ideal.ResidueField.mapₐ`, whose source specifies the canonical embedding from
  a contracted prime's residue field.
- `def-weil-pbc-kahler-differentials`: `KaehlerDifferential`, its derivation `D`,
  and `linearMapEquivDerivation` in `Mathlib.RingTheory.Kaehler.Basic`. Read the
  concrete cotangent construction and the complete universal-property signature.
- `def-weil-pbc-module-tensor-product`: its status is Mathlib and its `mathlib_match`
  records `TensorProduct`, `TensorProduct.mk`, `lift`, `ext'`, and `LinearMap.rTensor`.
  Read the quotient/balancing construction and pure-tensor universal property in
  `Mathlib.LinearAlgebra.TensorProduct.Defs` and `.Basic`. No Lean record repair is needed.
- `def-weil-pbc-module-localization`: `LocalizedModule`, `LocalizedModule.mk` and
  `mkLinearMap` in `Mathlib.Algebra.Module.LocalizedModule.Basic`. Read the fraction
  relation and localized module construction.
- `def-weil-vector-space-dimension`: `Module.finrank` in
  `Mathlib.LinearAlgebra.Dimension.Finrank`; its source docstring explicitly identifies
  this with dimension when finite dimensionality is established.
- Existing proof dependency `lem-weil-pbc-kahler-differentials-base-change` is a
  Mathlib leaf: read both `tensorKaehlerEquivBase` and `tensorKaehlerEquiv` and their
  complete types/docstrings in `Mathlib.RingTheory.Kaehler.TensorProduct`; the latter
  gives the required F-linear scalar-extension form and is directly used by `beta`.
- Existing proof dependency `lem-weil-pbc-ring-localization-universal-property` is
  `IsLocalization.lift` / `ringHom_ext` in `Mathlib.RingTheory.Localization.Defs`.
  Read the lift and uniqueness signatures. `ρ` is specified by exactly that uniqueness
  condition; the existence proof is part of this item's sorry.
- The two linear-algebra proof leaves record `exists_linearIndependent'` in
  `Mathlib.LinearAlgebra.LinearIndependent.Lemmas` and `finrank_span_eq_card` in
  `Mathlib.LinearAlgebra.Dimension.Constructions`; both signatures were read, and
  both modules are plain proof imports.

Read Stacks `algebra.tex`, label `lemma-differentials-base-change` (00RV), and
`morphisms.tex`, label `lemma-smooth-at-point` (01V9), especially its displayed
comparison in (4) and the subsequent base-change discussion. The source uses no
finite presentation hypothesis for the algebraic comparison itself; the surrounding
smoothness criterion's finite-presentation and flatness hypotheses are not added here.
The example `Sheaf.CategoryTheory.CompactObject` is currently withdrawn; its node points
to the existing upstream declaration. This delivery follows the current module-mode
public-import and expose-section conventions from the stage-2 brief.

### Edge cases

Checked the empty generating family `r = 0`: the premise says `Mq = 0`, the image
range is empty and the conclusion explicitly gives finite dimensionality and dimension
zero. A zero differential module and the identity ring map are included. Prime ideals
need not be maximal, rings need not be domains and the fibre may have zero divisors.
For instance Z[i] at (1+i) has a nonreduced fibre over F2; all tensor and denominator
formulas still make sense, with only elements outside q inverted. A polynomial ring
over a field at (t) gives the usual one-dimensional differential fibre. Different
universes for R and A are allowed, with the fibre and its residue field in their maximum.
No zero-ring or characteristic exclusion is introduced; existence of q imposes exactly
its usual prime-ideal condition. No statement dispute or mathematical node fault found.

### Searches

All msearch calls used group Q58 and this item; their actual digests are in
`searches.jsonl` in the sandbox.

- LeanFinder: `fibre cotangent localization generators Kahler differentials beta isomorphism`:
  eight hits on localized cotangent presentations and standard smooth cotangent bases,
  including `Algebra.Generators.cotangentCompLocalizationAwayEquiv`; none states the
  whole comparison, both fraction formulas, and the generator implication.
- Loogle: `KaehlerDifferential.tensorKaehlerEquiv, LocalizedModule, Module.finrank`:
  no hits for that combined query.
- LeanSearch: `Localizing Kahler differentials at a prime and tensoring with residue field of the fibre gives an isomorphism and a finite generator dimension bound`:
  eight hits, including `KaehlerDifferential.isLocalizedModule_map`,
  `KaehlerDifferential.tensorKaehlerEquivBase`, and `Module.rankAtStalk_eq`.
  These are ingredients; none is an exact declaration of this node.
- msearch grep: `tensorKaehlerEquiv|finrank_le_of_span_eq_top` under `RingTheory/Kaehler`:
  five hits in `TensorProduct.lean`; the full canonical differential equivalence was read
  and reused. The earlier grep using `Mathlib/RingTheory` as its subdirectory returned
  zero hits because that supplied prefix was redundant; the corrected search above is
  the substantive grep search.
- Read-only rg on both project roots for the item id, `FibreLocalization`,
  `ComparisonAlong`, `fibreCotangentLocalizationGenerators`, the differential comparison
  names and the upstream-name index: no existing declaration of this item or collision
  with the new names. Related `SmoothAtPointDifferentialCriterion` uses the comparison
  only in its proof docstring and does not state the present standalone algebraic fact.

### Validation

The completed module compiled cleanly through the prescribed `scompile.py`, in both
sandbox and library module contexts, with no error or non-sorry warning. Final delivery
preflight and per-file compilation are run with `deliver2.py --no-push` before the push.

## Second reading by Q58

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

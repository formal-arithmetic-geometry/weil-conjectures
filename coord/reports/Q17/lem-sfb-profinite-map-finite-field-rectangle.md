## Worker report

The module `Sheaf.NumberTheory.Padics.ProfiniteMapFiniteFieldRectangle` states
`Padic.exists_finiteIntermediateField_coset_rectangle` with a single `sorry` proof.
It defines no new notion. The item is unchanged except for its `lean` record.

The source is the agent arithmetic expansion of paragraph (3) in the current
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`.
I read that current paragraph, Stacks `topology.tex`,
`lemma-baire-category-locally-compact` (Tag 0CQN), and Stanford Weil II seminar
L19, Proposition 1.1.9, page 3. The last source concerns representations and
supplies background for the countable-field argument; it is not claimed to state
this arbitrary-map rectangle assertion.

Hypothesis and conclusion correspondence:

| Node text | Lean rendering |
| --- | --- |
| A prime ℓ | `(ℓ : ℕ) [Fact ℓ.Prime]` |
| An algebraic closure Ω/ℚ_ℓ | `(Ω : Type u) [NormedField Ω] [NormedAlgebra (Padic ℓ) Ω] [IsAlgClosure (Padic ℓ) Ω]` |
| Extended norm topology | The topology of `NormedField Ω`; the normed algebra structure makes the field embedding isometric, hence its norm extends the p-adic norm. No completeness instance on Ω is assumed. |
| A finite intermediate field E | `(E : IntermediateField (Padic ℓ) Ω) [FiniteDimensional (Padic ℓ) E]` |
| G is a compact Hausdorff topological group | `(G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]` |
| Open subgroups form an identity neighbourhood basis | `hG : ∀ U ∈ nhds (1 : G), ∃ H : OpenSubgroup G, (H : Set G) ⊆ U`. Every open subgroup is itself an identity neighbourhood, so this is precisely the stated basis condition. |
| Integers m ≥ 1 and d ≥ 0 | `(m : ℕ) (hm : 1 ≤ m) (d : ℕ)` |
| Product topologies on G^m and Ω^d | The Pi topologies on `Fin m → G` and `Fin d → Ω` |
| Every continuous f | `(f : (Fin m → G) → (Fin d → Ω)) (hf : Continuous f)` |
| A finite intermediate extension E ⊆ F ⊆ Ω | `∃ F : IntermediateField (Padic ℓ) Ω, E ≤ F ∧ FiniteDimensional (Padic ℓ) F ∧ ...` |
| An open subgroup and m centres | `∃ (H : OpenSubgroup G) (a : Fin m → G), ...` |
| For all h_i in H the image lies in F^d | `∀ h : Fin m → H, ∀ r : Fin d, f (fun i ↦ (h i : G) * a i) r ∈ F` |
| No normality, equivariance, cocycle, completeness, or finite-generation hypothesis | The displayed binders contain none of these conditions. `f` is an arbitrary function with its sole continuity hypothesis. |

The separate universes `u v` cover arbitrary sizes of the algebraic closure and
group. Every universe and variable is explicit; `autoImplicit` is disabled.
Membership in F is taken in Ω through the standard `IntermediateField` carrier,
so the conclusion uses the original function and canonical subfield inclusion.
Finite-dimensionality over ℚ_ℓ also says F/E is finite since E ≤ F and E/ℚ_ℓ
is finite; no extra extension structure or embedding is chosen.

Dependency declarations read and used:

- `def-weil-algebraic-closure`: the recorded Mathlib match is `AlgebraicClosure`,
  and its `how` explicitly identifies the arbitrary-closure predicate
  `IsAlgClosure` in `Mathlib.FieldTheory.IsAlgClosed.Basic`. This is the predicate
  used in the signature, publicly imported through
  `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`.
- `def-weil-l-adic-coefficient-extension`: public import
  `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, whose recorded theorem
  is `Padic.finite_coefficientExtensionRing`. I read its full signature and
  docstring and the imported `CoefficientExtension` constructions, including
  `Padic.coefficientExtensionDegree` and `coefficientExtensionAbsoluteValue`.
  As in that interface, finite extension means `FiniteDimensional (Padic ℓ) E`.
  No coefficient quotient or uniformizer is used in this node's statement.
- Proof dependency `lem-sfb-algcl-countable-closed-finite-cover`: plain import
  `Sheaf.NumberTheory.Padics.CountableClosedFiniteCover`, with the full statement
  `Padic.exists_monotone_closed_finiteIntermediateField_cover` read. Its closure
  and normed-algebra hypotheses agree exactly with this statement.
- Proof dependency `lem-sfb-baire-closed-cover-interior`: Mathlib's
  `nonempty_interior_of_iUnion_of_closed` from `Mathlib.Topology.Baire.Lemmas`,
  together with `BaireSpace.of_t2Space_locallyCompactSpace` from
  `Mathlib.Topology.Baire.LocallyCompactRegular`; both are plain imports.
- Proof dependency `lem-weil-pbc-tychonoff-product-quasi-compact`: `Pi.compactSpace`
  from `Mathlib.Topology.Compactness.Compact`, a plain import.
- Mathlib's `OpenSubgroup` from `Mathlib.Topology.Algebra.OpenSubgroup` is publicly
  imported for the signature. Its defining structure was read; it imposes
  openness and the subgroup laws, with no normality requirement.

The theorem docstring gives all three DAG proof steps: the finite-coordinate
closed cover (including d = 0), Baire nonempty interior on the compact Hausdorff
product, and the finite intersection of open subgroups inside right-translated
coordinate neighbourhoods. No proof was supplied at this stage.

Edge cases checked before writing: d = 0 has an empty coordinate condition and
one can take F = E, H = G, and identity centres. For the trivial group all
coordinates of its unique image generate a finite extension together with E,
since Ω/ℚ_ℓ is algebraic. For a constant map the same construction works for
every G. The case m = 1 uses one ordinary coset. The domain group is always
nonempty by its identity, so no nonempty assumption is added. The value m = 0
is outside the node's scope and is explicitly excluded by hm. Characteristic
and the prime ℓ = 2 require no restriction. Noncommutative groups are allowed:
the formula is exactly `h i * a i`, not the reverse order. There is no
metrizability or countable-basis assumption on G, and no completeness of Ω.

Searches run on 2026-10-24 with the prescribed `msearch.py Q17
lem-sfb-profinite-map-finite-field-rectangle` wrapper:

- LeanFinder query: `A continuous map from a finite power of a profinite group into the normed algebraic closure of a p adic field maps some open coset rectangle into a finite intermediate field`.
  Eight hits, led by `InfiniteGalois.proj`, its compatibility lemmas,
  `IntermediateField.fixingSubgroup_isOpen`, and `cyclotomicCharacter.continuous`.
  These concern Galois actions and the Krull topology, not arbitrary norm-continuous
  maps; no exact match.
- Loogle query: `OpenSubgroup, IntermediateField, Continuous`.
  Service returned OK, zero hits.
- LeanSearch query: `A continuous profinite group function has values in a finite extension on an open subgroup coset rectangle`.
  Eight hits: profinite group morphism and topology facts, cyclotomic continuity,
  and finiteness of an open subgroup quotient. None asserts this rectangle lemma.
- Mathlib grep query:
  `(IntermediateField|PadicAlgCl).*(rectangle|coset)|(rectangle|coset).*(IntermediateField|PadicAlgCl)`.
  Service returned OK, zero hits.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the node id and proposed declaration name:
  zero matches. `grep -rn` of the item id in `lean/WeilConjectures` likewise
  returned no match.
- Project `rg` for finite-field/coset rectangle phrases found
  `Sheaf.RepresentationTheory.CochainClosedRectangleCertificates` and a
  proof-docstring mention in `PrimeToEllCochainFiniteQuotientDescent`.
  I read `ContinuousCohomology.exists_cochain_closed_rectangle_certificates`:
  it has metrizable parameter and group hypotheses, a normal-subgroup basis,
  and concerns parameterized cochain differences with closed certificates.
  It is not this arbitrary finite-power map statement and cannot supply its
  full generality. A separate `rg` for `rectangle|coset` in both p-adic source
  directories found integer coset-basis and profinite-tower facts only.

No node fault, correction, new definition, dependency repair, or
STATEMENT-DISPUTED issue was found. The example Sheaf CompactObject module is
withdrawn; I read its node's currently recorded upstream module
`WeilConjectures.CategoryTheory.CompactObject` for the active conventions.

Validation: prescribed `scompile.py` passed both sandbox and library module-mode
checks (3.1 s and 2.5 s), with no compiler errors or warnings. All Lean lines
are at most 100 characters.

## Second reading by Q17

This dispatcher assignment explicitly forbids starting another agent; this is a
separate self-review, not a claim of review by a second worker. The maintainer's
independent delivery review remains to follow. I reopened the node and module
and checked every row above against the actual signature: the algebraic closure
and extended norm agree with the finite-cover dependency; the subgroup-basis
binder is the node's definition of profinite, without metrizability or normality;
`hm` preserves the positive-power scope; the coordinate type is `Fin d`, including
zero; E ≤ F and finite-dimensionality are both asserted; centres are existential
after F and H; all tuples in H are universally quantified; multiplication is in
the required order; and the final universal coordinate membership is exactly
membership in F^d. There is no extra closedness or global finite-image conclusion.
The actual imports cover both statement dependencies and every recorded proof
dependency. No mismatch was found and no statement was changed in this reading.

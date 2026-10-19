## Worker report

The delivery states `IsDiscreteValuationRing.finite_normalization_tame_inertia` in
`Sheaf.FieldTheory.FiniteDVRTameInertia`, with one `sorry` and no definitions or
additional nodes. The source is Stacks More on Algebra, Remark 09E8
(`remark-finite-separable-extension`) and Lemma 09EE (`lemma-galois-inertia`),
including `equation-inertia-character`. I read both source passages in
`literature/stacks-project/more-algebra.tex`. The current reviewed ten-step DAG
proof is preserved and is written out in the theorem docstring, including the
imperfect-residue-field order calculation and the explicit Cauchy argument.

The preceding worker's diagnosis concerned splitting an already reviewed DAG
node. This is a stage-2 statement task: the current node is split and reviewed
and has no Lean record. No new split was attempted. There is no item-specific
maintenance repair note in the shared repository.

Every hypothesis is rendered as follows:

| Node hypothesis or object | Lean rendering |
| --- | --- |
| An arbitrary DVR A | `(A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]` |
| K its fraction field | `(K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]` |
| Finite Galois extension L/K, finite, normal and separable | `(L : Type w) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]`; `IsGalois` contains `Algebra.IsSeparable` and `Normal` |
| The specified A-algebra structure on L through K | `[Algebra A L] [IsScalarTower A K L]`; this records the composition of the two given field/ring maps |
| Residue characteristic p > 0 | `(p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]`; a positive characteristic of a field is prime |
| B is the integral closure in L | The actual type `integralClosure A L`, with no copy or arbitrary normalization model |
| Every maximal ideal of B | `∀ (𝔫 : Ideal (integralClosure A L)) [𝔫.IsMaximal]` in the conclusion |

Every conclusion and construction is rendered as follows. In this explanation
only, C denotes `Localization.AtPrime 𝔫`, E denotes `𝔫.ResidueField`,
D denotes `MulAction.stabilizer Gal(L/K) 𝔫`, and I denotes `𝔫.inertia D`.
The Lean signature uses the complete expressions and has no local notation,
`let`, hidden `show`, or auto-bound variables.

| Node clause | Lean rendering |
| --- | --- |
| B is a finite A-module | `Module.Finite A (integralClosure A L)` |
| C is a DVR | The existential proof `hC : IsDiscreteValuationRing (Localization.AtPrime 𝔫)`; this is a conclusion, not an extra hypothesis |
| C has fraction field L | `∃ j : C →+* L`, the equations `j (algebraMap B C b) = (b : L)` for every b, and `@IsFractionRing C _ L _ j.toAlgebra` |
| The residue field is κ(𝔫) | `𝔫.ResidueField` is definitionally `IsLocalRing.ResidueField C` by the dependency's Mathlib declaration |
| κ(𝔫) is finite over the residue field of A | `∃ ρ : IsLocalRing.ResidueField A →+* E`, its equation on every residue of a in A, and `Module.Finite` for the scalar action of `ρ.toAlgebra.toModule` |
| D stabilizes 𝔫 | Mathlib's `MulAction.stabilizer Gal(L/K) 𝔫`, for the canonical action on the integral closure and its ideals |
| I acts trivially on κ(𝔫) | Mathlib's `𝔫.inertia D`; its condition is `∀ b : B, σ • b - b ∈ 𝔫`, exactly triviality on B/𝔫, hence on E since 𝔫 is maximal |
| e is the ramification index v_C(π_A) | `∃ e : ℕ`, with `@addVal C _ _ hC (algebraMap A C π) = (e : ℕ∞)` for every `π : A` satisfying `Irreducible π`; this is independent of the base uniformizer |
| χ is a homomorphism I → μ_e(E) | `∃ χ : I →* rootsOfUnity e E`; `rootsOfUnity` is Mathlib's subgroup of units satisfying the e-th-power equation |
| χ(σ) is the residue of σ(t)/t | For every local uniformizer t and every σ in I, there is `a : Cˣ` with `j a = σ.1.1 (j t) / j t` and the field value of `χ σ` equal to `IsLocalRing.residue C a` |
| Independence of t | The *same* homomorphism χ satisfies that formula for **every** `t : C` with `Irreducible t`, not just a chosen t |
| P = ker χ is normal in D | `(χ.ker.map I.subtype).Normal`; the subtype hom embeds I in D, so this is normality in D rather than just in I |
| P is a finite p-group | `Finite χ.ker ∧ (∃ a : ℕ, Nat.card χ.ker = p ^ a)` |
| n is the largest divisor of e prime to p | The expression `e / p ^ e.factorization p`, exactly Mathlib's global notation `ordCompl[p] e`; see Factorization/Defs and `Nat.dvd_ordCompl_of_dvd_not_dvd` |
| μ_e(E) = μ_n(E) | Equality of the two `rootsOfUnity` subgroups of Eˣ |
| μ_n(E) is cyclic of order n | `IsCyclic (rootsOfUnity n E)` and `Nat.card (rootsOfUnity n E) = n` |
| χ induces I/P ≅ μ_n(E) | `∃ θ : (I ⧸ χ.ker) ≃* rootsOfUnity n E`, with `(θ (QuotientGroup.mk σ) : Eˣ) = (χ σ : Eˣ)` for every σ; this records the induced map, not an unrelated abstract equivalence |

The existential maps are not arbitrary choices: j is fixed on B and thus on
its localization, and ρ is fixed on every residue of A, which surjects onto
A's residue field. Their equations characterize the canonical maps uniquely.
The unit a is uniquely determined by its value under j, since the fraction-ring
map is injective. Giving the formula in L avoids inventing a second localization
action. In a DVR `Irreducible t` means exactly that t generates the maximal ideal
(`IsDiscreteValuationRing.irreducible_iff_uniformizer`), so no uniformizer is
lost. All three ring/field universes u, v, w are independent.

Statement-dependency declarations read and used:

- `def-sc-discrete-valuation-ring` is a Mathlib leaf without a Lean record;
  its `mathlib_match` is `IsDiscreteValuationRing` in
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`. I read the full class,
  its nonfield condition, and `irreducible_iff_uniformizer`.
- `def-weil-pbc-integral-closure`: `integralClosure` in
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`; its carrier is exactly
  the set of elements integral over A.
- `def-pc-field-extension`: `Algebra` in `Mathlib.Algebra.Algebra.Defs`;
  field structures and the algebra map give the stated field inclusion.
- `def-weil-pbc-separable-algebraic-extension`: `Algebra.IsSeparable` in
  `Mathlib.FieldTheory.Separable`; the same recorded class is supplied by
  `IsGalois`, whose full definition was also read.
- `def-weil-finitely-generated-module`: `Module.Finite` in
  `Mathlib.RingTheory.Finiteness.Defs`.
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime` in
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, and the recorded
  `Ideal.ResidueField` in `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`.
  The dependency's fibre-ring clause is irrelevant to this item.

All statement dependencies are used through those recorded declarations or
Mathlib matches. No dependency module is needed. The module imports the stated
proof dependencies: the Mathlib DVR dimension theorem, the PID and finite
normalization/Dedekind-localization results, the fraction-field results, Cauchy's
theorem, roots of unity, and
`Sheaf.AlgebraicGeometry.IntegralClosureDedekindSurjectiveFibres`
(`AlgebraicGeometry.integralClosure_isDedekind_surjective_finite_fibres`).
The independent proof-only node `lem-exc-dvr-inertia-order-prime-part` currently
has neither a Lean record nor a Mathlib match; its import is therefore omitted.
It is not needed to type the statement and was not stated in this delivery.

Edge cases checked before writing: L = K gives e = n = 1, trivial character
and quotient, and kernel order p^0 = 1. A totally wild extension with e a
p-power gives n = 1 and the trivial roots group; a tame extension gives P = 1
and a cyclic quotient of order e. Imperfect residue fields are allowed: no
residue separability or perfectness is assumed, and there is no assertion
|I| = e (in particular the Stacks example following 09EE with e = 1 and
nontrivial wild inertia remains included). Nonhenselian DVRs and all maximal
ideals of the normalization are covered. A field or zero ring is not a DVR;
p = 0 and p = 1 are excluded exactly by positive field characteristic.
No statement correction or disputed statement was necessary.

Searches made with the prescribed tools (actual wrapper records are retained
in `searches.jsonl` in the sandbox):

- `msearch.py ... leanfinder "Finite Galois extension of discrete valuation rings tame inertia character kernel p group and roots of unity quotient"`:
  eight hits, including `ValuationSubring.inertiaSubgroup`,
  `ValuationSubring.decompositionSubgroup`,
  `Ideal.card_inertia_eq_ramificationIdxIn`, and inertia-degree identities;
  none states the character or its p-group kernel and induced isomorphism.
- `msearch.py ... loogle "Ideal.inertia, rootsOfUnity"`: zero hits.
- `msearch.py ... leansearch "Finite Galois DVR extension tame inertia character wild inertia is a p group"`:
  eight hits, again inertia-subgroup and ramification-degree statements;
  the inertia-order results require extra residue separability and do not
  supply this theorem.
- `msearch.py ... grep "tame|wild|inertiaSubgroup" RingTheory/Valuation`:
  one hit, `Mathlib/RingTheory/Valuation/RamificationGroup.lean` defining
  `ValuationSubring.inertiaSubgroup`; no tame character.
- `rg` in the upstream `WeilConjectures` source, its Mathlib additions, and
  shared `lean/Sheaf` for tame/wild inertia and character vocabulary found
  the related henselian tame-sequence statement and Abhyankar material, not
  this finite normalization/character statement. The exact blueprint-id
  grep in upstream `WeilConjectures` had no hits.
- The proposed declaration and module names were searched in Mathlib,
  upstream `WeilConjectures`, shared `lean/Sheaf`, and
  `dag/lean_names_upstream.json`; no collision was found.

Validation: `scompile.py Q57 lem-exc-finite-dvr-tame-inertia` compiled the
module cleanly (sandbox 3.5 seconds, module 4.1 seconds). The first compile
identified that `ordCompl` is notation rather than a declaration named
`Nat.ordCompl`; the signature now uses its exact defining natural-number
expression. Every variable and universe is explicit, all lines are at most
100 characters, and the sole proof is `by sorry`. The node copy differs only
in `lean`, with its exact source signature and the current UTC date.


## Second reading by Q57

I independently read the current node, its ten proof steps, the complete delivered
Lean module, and Stacks `more-algebra.tex` Remark 09E8
(`remark-finite-separable-extension`, lines 33006 onward), the definition of
D and I (`definition-decomposition-inertia`), Lemma 09EE
(`lemma-galois-inertia`, lines 33251 onward), and
`equation-inertia-character`, including the proof and the imperfect-residue
example following it. These passages assume an arbitrary DVR and a finite
Galois extension; they do not assume henselianity, excellence, completeness,
perfect residue field, or residue separability. The node restricts to positive
residue characteristic, as does the Lean. No statement correction is needed.

My object/hypothesis/conclusion checklist follows. In this report only, write
B = `integralClosure A L`, C = `Localization.AtPrime 𝔫`,
E = `𝔫.ResidueField`, D = `MulAction.stabilizer Gal(L/K) 𝔫`,
and I = `𝔫.inertia D`. These are explanatory abbreviations, not declarations.

| Node item | Exact Lean rendering or clause | Verdict |
| --- | --- | --- |
| A is a DVR | `(A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]` | Exact; Mathlib's class is a local PID with nonzero maximal ideal. |
| K is its fraction field | `(K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]` | Exact. |
| Finite normal separable L/K | `(L : Type w) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]` | Exact; `IsGalois` supplies normality and separability. |
| The inclusion A into L through K | `[Algebra A L] [IsScalarTower A K L]` | Compatibility data for the stated inclusion, no extra mathematical hypothesis. |
| Positive residue characteristic p | `(p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]` | Exact; every positive field characteristic is prime. |
| B is the normalization in L | The actual type `integralClosure A L` | Exact, not an arbitrary integral algebra. |
| B is finite over A | `Module.Finite A (integralClosure A L)` | Exact. |
| Every maximal ideal of B | `∀ (𝔫 : Ideal (integralClosure A L)) [𝔫.IsMaximal]` | Exact universal quantification after finiteness. |
| C is a DVR | `∃ hC : IsDiscreteValuationRing (Localization.AtPrime 𝔫)` | Exact conclusion, not a hypothesis. |
| C has fraction field L | `∃ j : C →+* L`, its equation on every `b : B`, and `@IsFractionRing C _ L _ j.toAlgebra` | Exact canonical inclusion, characterized on the localization generators. |
| Residue field is κ(𝔫) | `𝔫.ResidueField` | Definitionally `IsLocalRing.ResidueField C`. |
| E is finite over the residue field of A | `∃ ρ : IsLocalRing.ResidueField A →+* E`, its equation on all `a : A`, and `@Module.Finite ... ρ.toAlgebra.toModule` | Exact; surjectivity of the base residue map determines ρ uniquely. |
| D stabilizes 𝔫 | `MulAction.stabilizer Gal(L/K) 𝔫` | Exact canonical action by automorphisms of L restricted to B and then mapped on ideals. |
| I acts trivially on κ(𝔫) | `𝔫.inertia D` | Exact: its definition is `∀ b : B, σ • b - b ∈ 𝔫`; for maximal 𝔫 this is trivial action on the residue field. |
| e is v_C(π_A) | `∃ e : ℕ`, followed by the `@addVal C _ _ hC` equation for every irreducible base π | Exact normalized valuation; `Irreducible π` is equivalent to generating the maximal ideal. |
| χ is a homomorphism into μ_e(E) | `∃ χ : I →* rootsOfUnity e E` | Exact; `rootsOfUnity` consists of units whose e-th power is one. |
| χ(σ) is the residue of σ(t)/t | For every irreducible `t : C` and `σ : I`, `∃ a : Cˣ`, `j a = σ.1.1 (j t) / j t`, and the equality of χ's value with `IsLocalRing.residue C a` | Exact, computing the ratio in L through the characterized embedding j. |
| Independence of t | The same χ satisfies the formula for every irreducible t | Exact; this also characterizes χ uniquely since a DVR has a uniformizer. |
| P = ker χ is normal in D | `(χ.ker.map I.subtype).Normal` | Exact normality in D, not merely in I. |
| P is a finite p-group | `Finite χ.ker ∧ (∃ a : ℕ, Nat.card χ.ker = p ^ a)` | Exact, including the trivial group. |
| n is the largest divisor of e prime to p | `e / p ^ e.factorization p` everywhere n occurs | Exact prime-to-p part for the necessarily positive ramification index. |
| μ_e(E) = μ_n(E) | Equality of the two `rootsOfUnity` subgroups of `Eˣ` | Exact equality, not an abstract isomorphism. |
| This group is cyclic of order n | `IsCyclic (rootsOfUnity ... E)` and its `Nat.card` equation | Both clauses present exactly. |
| χ induces I/P ≅ μ_n(E) | `∃ θ : (I ⧸ χ.ker) ≃* rootsOfUnity ... E` with the equation on every `QuotientGroup.mk σ` | Exact induced isomorphism; the representative equation ties θ to χ. |

I opened all six statement-dependency node records and their actual Mathlib
signatures. In particular, `integralClosure` has carrier `{x | IsIntegral A x}`;
`Algebra` is a ring map with its induced scalar action; `Algebra.IsSeparable`
means every minimal polynomial is separable and implies algebraicity;
`Module.Finite` means the top submodule is finitely generated;
`Localization.AtPrime` localizes at the prime complement; and
`Ideal.ResidueField` is exactly the residue field of that localization.
No recorded dependency is replaced by a private notion. I also read
`integralClosure`'s `MulSemiringAction` instance, `Ideal.pointwiseDistribMulAction`,
`Ideal.inertia` and its underlying `AddSubgroup.inertia`: the two nested
subgroup coercions `σ.1.1` in the formula give precisely the original field
automorphism. The maps j and ρ have real mathematical characterizations,
not arbitrary-map hypotheses or choices from a bare existence theorem.
There are no definitions, new nodes, or dependency modules in this delivery.
The proof-only imports match the recorded dependencies; the unstated
`lem-exc-dvr-inertia-order-prime-part` still has no module to import.
I opened the imported integral-closure/Dedekind theorem as well.

Edge cases: the identity extension has e = n = 1, trivial χ and kernel of
order p^0. For a p-power ramification index, n = 1 and the tame quotient is
trivial. An imperfect residue field, inseparable residue extension, and the
example after 09EE with e = 1 but nontrivial wild inertia are all allowed:
there is no hypothesis of separable residues and no claim that |I| = e.
Nonhenselian rings and every maximal ideal of B are covered. The zero ring
and fields are excluded by the DVR notion itself, as in the node; p = 0 and
p = 1 are excluded by positive residue characteristic. Although the Lean
existential uses `e : ℕ`, e = 0 cannot satisfy its valuation equation: B is
integral over A, so a maximal ideal contracts to the maximal ideal of A;
the canonical map into C is local and injective, and a base uniformizer has
positive finite valuation. Thus neither the e = 0 nor the empty-uniformizer
case weakens the conclusion. There is no varying index set or empty scheme
in this statement. The independently bound universes u, v, w allow all ring
and field sizes covered by the node.

Independent duplicate searches (with different vocabulary from the worker):

- `msearch.py ... leanfinder "wild ramification subgroup is a p-group quotient inertia roots of unity uniformizer"` returned eight hits. I opened `ValuationSubring.inertiaSubgroup`; it defines the subgroup for a valuation subring but gives none of the character, kernel, or quotient assertions. The other hits concern inertia degrees.
- `msearch.py ... loogle "rootsOfUnity, IsPGroup"` returned no hits.
- `msearch.py ... leansearch "The kernel of the inertia character on the cotangent space of a discrete valuation ring has prime power order"` returned eight hits: inertia definitions, cotangent constructions, and the inertia-order theorem requiring separable residues; none is this theorem.
- `msearch.py ... grep "rootsOfUnity|IsPGroup" RingTheory/Valuation` returned no hits.
- Independent `rg` searches for `tame.*(character|inertia)`, `wild.*(group|inertia)`, `inertia.*(uniformizer|rootsOfUnity)`, and `ramification.character` in upstream `WeilConjectures`, Mathlib FieldTheory/RingTheory, and shared `lean/Sheaf` found the henselian tame-sequence consumer and a Frobenius comment, not this assertion. The exact node id and proposed name have no upstream/name-index collision.

No mathematical or Lean mismatch was found, so I preserved the module and
node copy verbatim and added only this independent review. The theorem's
source/blueprint docstring includes all ten proof steps, including the
imperfect-residue order computation, conjugation normality, telescoping,
Cauchy's theorem, Frobenius root equality, and the final image cardinality
comparison. Its only proof is `by sorry`; there are no hollow definitions,
local notation declarations, private copies, or unbound variables/universes.
The node copy changes only `lean`, and `lean.statement` was checked verbatim
against the complete signature. All Lean lines satisfy the 100-column limit.

Validation: the prescribed `scompile.py Q57 lem-exc-finite-dvr-tame-inertia`
with the sandbox module's absolute path passed cleanly (sandbox 2.4 seconds,
module 4.1 seconds), with no errors or warnings. An initial invocation with
a repository-relative path failed to locate the sandbox file; rerunning with
the absolute path resolved it without changing any source.

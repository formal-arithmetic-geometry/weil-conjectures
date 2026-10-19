## Worker report

`lean/Sheaf/FieldTheory/HenselianDVRTameSequence.lean` states
`IsDiscreteValuationRing.exists_tame_galois_sequence`, with one postponed proof
and no new definitions. The node is unchanged except for its `lean` record.
The theorem docstring contains all six proof steps, including the scaled tame
characters, their inverse limit, explicit cofinal coordinate identification,
and the compatible-root/Chinese remainder product identification.

Hypothesis and clause correspondence:

- A commutative excellent DVR is `(R : Type u) [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R] (hR : IsExcellent R)`. The nonfield condition is
  part of Mathlib's DVR class, rather than an omitted hypothesis.
- Henselianity is `[HenselianLocalRing R]`. We do not replace algebraic
  closedness of the residue field by the weaker separable closedness.
- The residue field k is `IsLocalRing.ResidueField R`, so no arbitrary field
  or unspecified identification with a residue field is introduced.
- Characteristic p > 0 is `(p : ℕ) [Fact p.Prime]
  [CharP (IsLocalRing.ResidueField R) p]`. Positive characteristic of a field
  is prime, so the prime binder is equivalent to the stated assumption.
- Algebraically closed k is `[IsAlgClosed (IsLocalRing.ResidueField R)]`.
- F = Frac(R) is any `(F : Type v) [Field F] [Algebra R F]
  [IsFractionRing R F]`.
- A chosen separable closure is `(Fsep : Type w) [Field Fsep] [Algebra F Fsep]
  [IsSepClosure F Fsep]`. The group is `Gal(Fsep/F)`, the existing automorphism
  group with Mathlib's Krull topology. `IsSepClosure.isGalois` and the compactness
  and total separation instances make it profinite without extra hypotheses.
- Existence of closed normal P is `∃ (P : Subgroup (Gal(Fsep/F))) (_ : P.Normal),
  IsClosed (P : Set (Gal(Fsep/F))) ∧ ...`. Existentially binding the normality
  instance makes the quotient's group structure available in the rest of the
  expression; it is a conclusion, not an assumption on R or G.
- The displayed product is
  `Multiplicative (∀ r : {r : Nat.Primes // (r : ℕ) ≠ p},
    @PadicInt r.1 (Fact.mk r.1.2))`.
  `Multiplicative` uses the ADDITIVE operation of the existing PadicInt rings.
  Its topology is unchanged (`Mathlib.Topology.Constructions`, lines 85–86),
  and the dependent function space has its product topology. The explicit
  prime Fact introduces no assumption. `PadicInt` is the already recorded
  r-adic integer type from def-weil-l-adic-numbers; its standard p-adic topology
  is the inverse-limit topology, since congruences modulo r^n are precisely
  p-adic neighborhoods. `PadicInt.toZModPow`, `ker_toZModPow`, `lift_spec`, and
  `lift_unique` in `Mathlib.NumberTheory.Padics.RingHoms` give the usual residue
  maps and projective-limit description. No competing completion is defined.
- The homomorphism is existential `θ : Gal(Fsep/F) →* ...`, with explicit
  `Continuous θ`, `Function.Surjective θ`, and `θ.ker = P`.
- The induced topological isomorphism is an existential
  `e : (Gal(Fsep/F) ⧸ P) ≃ₜ* ...` with
  `∀ g, e (QuotientGroup.mk' P g) = θ g`. This last equality ensures that the
  equivalence is induced by this very θ. The quotient topology comes from
  `QuotientGroup.instTopologicalSpace`, and P carries its subtype topology.
- Every finite continuous quotient is quantified as `(Q : Type z) [Group Q]
  [TopologicalSpace Q] [DiscreteTopology Q] [Finite Q] (f : P →* Q)` with
  `Continuous f → Function.Surjective f → ∃ n : ℕ, Nat.card Q = p ^ n`.
  The universe z is independent, so all finite quotient groups are allowed.
- Noncanonicity is retained by existentially quantifying θ and e. No canonical
  choice, primitive-root family, or trivialization is imposed as a hypothesis;
  the docstring explains the permitted choices in the proof.

Statement dependencies, exact interfaces read and used:

- def-exc-excellent-ring: `IsExcellent`, with its complete definition in
  `Sheaf.RingTheory.ExcellentRing` (quasi-excellent and universally catenary).
- def-sc-discrete-valuation-ring: `IsDiscreteValuationRing` in
  `Mathlib.RingTheory.DiscreteValuationRing.Basic` (extends local PID, with
  nonzero maximal ideal, on an integral domain). Its uniformizer convention
  was read but no uniformizer is needed to state this conclusion.
- def-weil-pbc-henselian-terminology: `HenselianLocalRing` in
  `Mathlib.RingTheory.Henselian`, publicly available through the recorded
  `WeilConjectures.Mathlib.RingTheory.Henselian` module. Its recorded
  `IsStrictlyHenselianLocalRing` class was also read; the theorem needs only
  henselianity together with the separately stated algebraic closedness.
- def-weil-l-adic-numbers: `PadicInt` in
  `Mathlib.NumberTheory.Padics.PadicIntegers`, explicitly named in the node's
  mathlib_match; its data are the norm-at-most-one subtype of `Padic`.
- def-weil-algebraic-closure: `IsAlgClosed` in
  `Mathlib.FieldTheory.IsAlgClosed.Basic`, explicitly named in mathlib_match.
  Only algebraic closedness of the residue field is needed here.
- def-pd-separable-closure: `IsSepClosure` from the recorded module
  `WeilConjectures.Mathlib.FieldTheory.IsSepClosed`. Its recorded theorem
  `IsSepClosure.exists_intermediateField_mem` and its full docstring were read:
  every element lies in a finite separable intermediate field. The module
  explains that the notion itself is Mathlib's `IsSepClosure`, used here.

Proof dependencies with declarations are imported non-publicly:

- `Sheaf.RingTheory.FiniteOverHenselianLocalProduct`, theorem
  `HenselianLocalRing.finite_over_henselian_exists_algEquiv_pi`.
- `Mathlib.FieldTheory.Galois.Profinite`, declaration
  `InfiniteGalois.continuousMulEquivToLimit` for
  lem-exc-galois-krull-finite-limit; the lattice and bottom instances were read
  in `Mathlib.FieldTheory.Galois.GaloisClosure`.

The other five proof prerequisites have no recorded Lean declaration at the
snapshot read. They are cited in the proof docstring and not re-stated. None is
needed to elaborate this theorem's statement. There are no new nodes or
statement corrections, and no statement dispute.

Edge checks: p = 2 is allowed, while p = 0 and p = 1 are excluded by the source's
positive field characteristic; mixed and equal characteristic fraction fields
are both allowed. The target includes every prime other than p, with no finite
support restriction or exclusion of another prime. The product is a dependent
function space, so empty-product conventions are the usual ones (the actual
prime-to-p index is nonempty). The subgroup P may be trivial. The finite
quotient condition includes the trivial group with n = 0 and imposes no
nontriviality requirement. Ring, fraction field, separable closure and finite
quotient groups have independent explicit universes u, v, w, z.

Sources opened: the complete statement and proof of Stacks Tag 0BUB at
`literature/stacks-project/pione.tex:3344`, and the complete current blueprint
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-prop-a1-kummer/lem-exc-dvr-galois.proof.md`. The henselian/algebraically closed
residue specialization makes D = I = G; the full product after a choice of
compatible roots is exactly the tame limit used there.

Searches made in this work (in addition to reviewing the node's recorded searches):

- `msearch.py ... leanfinder`: “The absolute Galois group of the fraction field
  of an excellent henselian discrete valuation ring with algebraically closed
  residue field of characteristic p admits a continuous surjection to the
  product of additive r-adic integers for r different from p with closed normal
  pro-p kernel”. Result: eight hits including absolute Galois group definitions,
  `IsFractionRing.stabilizerHom_surjective`, a Fontaine theta theorem,
  `InfiniteGalois.algEquivToLimit_continuous`, `krullTopology`, and a cyclotomic
  character. None is this tame sequence theorem.
- `msearch.py ... loogle "IsDiscreteValuationRing, IsSepClosure"`: zero hits.
- `msearch.py ... grep "wild.*inertia|tame.*inertia|tame.*sequence|henselian.*galois"
  FieldTheory`: zero hits in that Mathlib subdirectory.
- `msearch.py ... leansearch`: “The tame quotient of the absolute Galois group
  of a strictly henselian discretely valued field is the product of prime to
  residue characteristic adic integers”. Eight hits: absolute Galois group
  definitions/abelianization, finite normal quotient equivalences, Krull
  topology/total separation, adic completion integers, and profinite Galois
  packaging. None supplies the claimed wild kernel and full tame product.
- `rg` of upstream `WeilConjectures` and side `lean/Sheaf` for the same concepts:
  one upstream docstring mentions a tame inertia ell-part in a Frobenius proof;
  side `RepresentationTheory/DvrGalois.lean` cites this very node as a proof
  prerequisite and states a cohomology result, not the sequence. Both were
  inspected. Searching the item id in upstream found no hits.
- The full Mathlib ramification-group source was read: it defines decomposition
  and inertia subgroups only, and has no wild/tame structure theorem.
- Name checks in upstream sources, Mathlib, side Lean, and
  `dag/lean_names_upstream.json` found no existing
  `IsDiscreteValuationRing.exists_tame_galois_sequence`.

Validation: `scompile.py NQ lem-exc-henselian-dvr-tame-sequence
lean/Sheaf/FieldTheory/HenselianDVRTameSequence.lean` compiled the final statement
both as sandbox and library module, with no errors or warnings. The UTC date in
the node is obtained from `date -u +%F`.
## Second reading by NQ

I independently read the node statement, Stacks Tag 0BUB at
`literature/stacks-project/pione.tex:3344`, the blueprint proof, all six recorded
statement dependencies, and the module
`Sheaf/FieldTheory/HenselianDVRTameSequence.lean`. The node's list and the Lean
rendering agree item by item:

- The base object is a commutative ring `R : Type u` with `[IsDomain R]`,
  `[IsDiscreteValuationRing R]`, and the node's excellent hypothesis. The Lean
  binders are `R`, the two algebraic instances, and `(hR : IsExcellent R)`;
  Mathlib's DVR class includes the nonfield condition, so no source hypothesis
  is omitted or strengthened.
- Henselianity is `[HenselianLocalRing R]`. The residue field is exactly
  `IsLocalRing.ResidueField R`, and its algebraic closedness is
  `[IsAlgClosed (IsLocalRing.ResidueField R)]`.
- Positive residue characteristic is represented by `(p : ℕ)` with
  `[Fact p.Prime]` and `[CharP (IsLocalRing.ResidueField R) p]`. Thus `p > 0`
  and the prime-to-`p` indexing in the conclusion are explicit.
- `F` is the fraction field through `(F : Type v)`, `[Field F]`,
  `[Algebra R F]`, and `[IsFractionRing R F]`; `Fsep` is a chosen separable
  closure through `(Fsep : Type w)`, `[Field Fsep]`, `[Algebra F Fsep]`, and
  `[IsSepClosure F Fsep]`. `Gal(Fsep/F)` supplies the absolute Galois group
  with its existing Krull topology.
- The first existential introduces a subgroup `P : Subgroup (Gal(Fsep/F))`,
  a proof of `P.Normal`, and `IsClosed (P : Set (Gal(Fsep/F)))`, exactly the
  closed normal subgroup in the node.
- The map is the existential
  `θ : Gal(Fsep/F) →* Multiplicative (∀ r : {r : Nat.Primes // (r : ℕ) ≠ p},
  PadicInt r.1)`, with `Continuous θ`, surjectivity, and `θ.ker = P`.
  `Multiplicative` is the standard group encoding of the additive product of
  the `PadicInt` groups; it does not change the underlying product or topology.
  `PadicInt` is the recorded Mathlib realization of the `r`-adic integers and
  carries their inverse-limit topology.
- The quotient clause is the existential topological-group equivalence
  `e : (Gal(Fsep/F) ⧸ P) ≃ₜ* Multiplicative (...)`, together with
  `∀ g, e (QuotientGroup.mk' P g) = θ g`; hence the equivalence is induced by
  this `θ`, rather than an unrelated isomorphism.
- The final clause quantifies arbitrary universes `z`, finite groups `Q` with
  a discrete topology, and a homomorphism `f : P →* Q`; under continuity and
  surjectivity it concludes `∃ n : ℕ, Nat.card Q = p ^ n`. This is exactly the
  node's assertion that every finite continuous quotient of `P` has
  `p`-power order.

The edge cases are covered: `p = 2` and mixed or equal characteristic are
allowed; `p = 0` and `p = 1` are excluded by `Fact p.Prime`; the prime index set
has the usual dependent product convention; `P` may be trivial; the trivial
finite quotient is admitted with `n = 0`; and the universes of `R`, `F`,
`Fsep`, and `Q` are independent. No empty scheme or nonzero-object assumption
is introduced.

For the one-definition-per-notion check I searched Mathlib's valuation,
ramification, absolute-Galois, and Padic files, the upstream
`WeilConjectures/` tree, and this side `lean/Sheaf` tree with `rg`; I also ran
LeanFinder/Loogle searches for tame inertia, wild inertia, and the henselian
DVR Galois quotient. The only relevant matches were the existing
`ValuationSubring.inertiaSubgroup`, `InfiniteGalois` Krull-topology declarations,
and `PadicInt`; none states this theorem. I found no duplicate declaration or
repair note for this item.

No mismatch was found, so no Lean file, statement, dependency record, or node
statement was changed. The node copy's `lean.statement` remains verbatim equal
to the theorem signature. The required compile command succeeded for the
module with only the permitted postponed proof (`sorry`) and no other warning.

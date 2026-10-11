## Worker report

The module `Sheaf.RingTheory.HenselianLocalRootLifting` states
`IsLocalRing.idempotent_lifting_iff_monic_simple_root_lifting`, with one `sorry` and no
new definitions or extra hypotheses. The node is unchanged except for its `lean` record.

Hypothesis and clause correspondence:
- A local ring `(R,m,κ)` is `(R : Type u) [CommRing R] [IsLocalRing R]`, with
  `IsLocalRing.maximalIdeal R` and `IsLocalRing.ResidueField R`. The latter is exactly
  the quotient by the maximal ideal, and `residue R` is its quotient homomorphism.
- “The following are equivalent” is `↔`.
- Condition (i), every finite R-algebra B, is
  `∀ (B : Type (max u v)) [CommRing B] [Algebra R B] [Module.Finite R B]`.
  Finiteness means module-finiteness, as in Stacks. Using `max u v` prevents a test-algebra
  universe smaller than R from making the condition vacuous; v is explicitly declared.
  Finite algebras in smaller universes can be lifted to this universe without changing the
  property; arbitrary larger universes are covered by v.
- The quotient B/mB is `B ⧸ (maximalIdeal R).map (algebraMap R B)`.
  Extension of the ideal by `Ideal.map` is exactly mB.
- Every idempotent in that quotient is `∀ e₀, IsIdempotentElem e₀ → ...`.
- Unique lifting is `∃! e : B, IsIdempotentElem e ∧ Ideal.Quotient.mk (...) e = e₀`.
  The uniqueness concerns the element among idempotent lifts, not proof witnesses.
- Condition (ii), every monic polynomial, is `∀ f : Polynomial R, f.Monic → ...`.
- Every a₀ in κ is `∀ a₀ : ResidueField R`.
- Reduced f vanishes at a₀ is `Polynomial.aeval a₀ f = 0`.
  The canonical R-algebra structure on κ uses `residue R`, so aeval is evaluation after
  reducing coefficients. The nonzero reduced derivative is
  `Polynomial.aeval a₀ f.derivative ≠ 0`. Reduction commutes with differentiation.
- A lifted root a is `∃ a : R, f.IsRoot a ∧ residue R a = a₀`.
  `Polynomial.IsRoot` means `f.eval a = 0`. No root uniqueness is added to condition (ii).

Dependency declarations: `def-weil-pbc-henselian-terminology` records
`Sheaf.RingTheory.HenselianTerminology`, including the existing Mathlib declarations
`HenselianRing` and `HenselianLocalRing`. I opened that module and the full signatures and
source docstrings of both classes and `HenselianLocalRing.TFAE` in
`Mathlib.RingTheory.Henselian`, as well as the upstream module
`WeilConjectures.Mathlib.RingTheory.Henselian`. Its record explicitly says that citers
stating the idempotent condition state it inline; this theorem follows that instruction
and imports the recorded module. Using `HenselianLocalRing R` as condition (i) alone
would hide the comparison the node intends. Condition (ii) is verbatim the mathematical
condition numbered 2 in `HenselianLocalRing.TFAE`, using that existing root API.
`IsStrictlyHenselianLocalRing` is irrelevant here. No dependency replacement is needed.
Additional Mathlib notions are `Module.Finite` (`Mathlib.RingTheory.Finiteness.Defs`),
`IsIdempotentElem` (`Mathlib.RingTheory.Idempotents`), polynomial evaluation, derivative,
ideal extension and quotient. There is no private copy of any notion.

Sources checked: the repository lacks the untracked Stacks TeX files; I read the local
copies `/home/ubuntu/c1-stacks-review/algebra.tex` at definition-henselian and
lemma-characterize-henselian (Tags 04GF and 04GG), and
`/home/ubuntu/c1-stacks-review/more-algebra.tex` at definition-henselian-pair and
lemma-characterize-henselian-pair (Tags 09XE and 09XI). The former gives exactly the monic
simple-root condition; the latter gives exactly bijectivity on idempotents of finite
algebras. The complete five-step DAG proof is carried in the theorem docstring, including
uniqueness via d³=d, the rank-one factor of R[T]/(f), étale retractions, splitting finite
algebras, and componentwise zero/one lifts.

Edge cases checked: zero B is admitted (no Nontrivial or IsLocalRing B hypothesis), and
its sole idempotent has a unique lift; empty products in the proof give precisely this B.
The zero base ring is excluded by the existing local-ring notion, consistently with the
source's field κ. Fields are included with maximal ideal zero. The monic constant
polynomial 1 has no residue root, so its implication is vacuous; the zero polynomial is
not monic in a nonzero local ring. Linear monic polynomials are covered; no degree or
characteristic restriction is imposed. Repeated roots are excluded exactly by the
nonzero derivative condition. No Noetherian hypothesis is introduced.

Searches performed using `/home/ubuntu/weil-launcher/msearch.py J1
lem-weil-pbc-henselian-local-root-lifting`:
- `leanfinder`: “a local ring has unique idempotent lifts in every finite algebra if and
  only if simple roots of monic polynomials lift from its residue field”. Eight hits:
  `HenselianLocalRing.TFAE`, `HenselianLocalRing`, its root-lifting field, unramified
  results, and standard étale lifting results. None states the idempotent equivalence.
- `loogle`: `HenselianLocalRing, IsIdempotentElem`. Zero hits.
- `grep`: `henselian.*idempotent|idempotent.*henselian`, in RingTheory. Zero hits.
- `leansearch`: “henselian local ring finite algebra unique idempotent lifting equivalent
  simple root lifting”. Unavailable: Internal Server Error; recorded as unavailable.
- `rg -n 'henselian.*idempotent|idempotent.*henselian|lem-weil-pbc-henselian-local-root-lifting'`
  over upstream WeilConjectures and project lean/Sheaf: upstream
  `Scheme.bijective_appTop_idempotent_of_henselianRing` concerns proper schemes; project
  terminology and zero-dimensional results mention idempotent lifting but do not state
  this equivalence. No upstream declaration is tagged with this item.
- Name collision search `henselianLocalRing_iff.*idempotent|idempotent_lifting_iff` over
  `dag/lean_names_upstream.json`, all Mathlib, upstream WeilConjectures and lean/Sheaf:
  no hits. The chosen full theorem name is new.

Validation: server `scompile.py` compiled the module in 1.4 seconds, exit code 0,
with no errors or warnings. No statement dispute, correction, new node, or dependency
module is needed. The delivery dry run is the final validation; the second reader will
perform the independent reading and delivery.

## Second reading by J1

I independently read the node statement, its source places (Stacks Algebra Tags 04GF,
04GG and More on Algebra Tags 09XE, 09XI), the dependency node
`def-weil-pbc-henselian-terminology`, and
`Sheaf/RingTheory/HenselianLocalRootLifting.lean`.

The node introduces a commutative local ring `(R, m, κ)`.  Lean renders this as
`(R : Type u) [CommRing R] [IsLocalRing R]`, with `m` rendered by
`maximalIdeal R` and `κ` by `ResidueField R`; the canonical quotient map is
`residue R`.  The conclusion is an equivalence (`↔`) with exactly two clauses.
Clause (i), for every finite `R`-algebra, is rendered by
`∀ (B : Type (max u v)) [CommRing B] [Algebra R B] [Module.Finite R B]` and
then quantifies every `e₀` in
`B ⧸ (maximalIdeal R).map (algebraMap R B)`.  Its idempotence is
`IsIdempotentElem e₀`, and its unique lift is
`∃! e : B, IsIdempotentElem e ∧ Ideal.Quotient.mk (...) e = e₀`.
Thus uniqueness is among idempotent elements and the reduction equation is explicit.
Clause (ii) quantifies `f : Polynomial R` with `f.Monic`, then
`a₀ : ResidueField R`, and uses
`Polynomial.aeval a₀ f = 0` and
`Polynomial.aeval a₀ f.derivative ≠ 0`, followed by
`∃ a : R, f.IsRoot a ∧ residue R a = a₀`.  This is exactly vanishing of the
reduced polynomial, nonvanishing of the reduced derivative, and a root reducing to
`a₀`; no root uniqueness is added.  The universe `max u v` is explicit and no
Noetherian, finiteness beyond module-finiteness, characteristic, or separability
hypothesis is present.

Verdict: every object, hypothesis, quantifier, and conclusion clause matches the node
and the Stacks statements.  The source's local-ring zero/one argument and finite
algebra formulation include the zero algebra; fields and degree-zero/linear monic
polynomials are included, with the constant-one implication vacuous and repeated
roots excluded by the derivative condition.  No mismatch was found and no Lean or
node change was required.

I searched Mathlib, the source repository, and project modules (including LeanSearch,
LeanFinder/Loogle, and ripgrep searches for henselian idempotent lifting).  The only
near match is `HenselianLocalRing.TFAE`, whose simple-root condition is clause (ii)
and which does not state the idempotent equivalence.  The dependency's recorded
`HenselianRing`, `HenselianLocalRing`, and `IsStrictlyHenselianLocalRing` declarations
were inspected; the theorem correctly spells out the idempotent condition inline and
introduces no private notion.  The module compiles cleanly with `scompile.py`; its
only proof placeholder is the theorem's permitted `sorry`.

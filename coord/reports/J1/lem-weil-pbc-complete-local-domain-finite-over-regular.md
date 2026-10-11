## Worker report

The module `Sheaf/RingTheory/CompleteLocalDomainFiniteOverRegular.lean` states the complete-local-domain finite-over-regular-power-series lemma. Its hypotheses are a commutative ring `R`, local-ring, Noetherian, domain, and adic-completeness instances. It existentially supplies a subring `R₀` and an explicit `IsRegularLocalRing R₀` witness; a `let` binding exposes its local-ring instance for the remaining clauses.

The first conclusion clause is `IsAdicComplete (IsLocalRing.maximalIdeal R₀) R₀`. The second is `Module.Finite R₀ R`. The third states the maximal ideal equality with the ideal comap along `R₀.subtype`, rendering `m₀ = m ∩ R₀`. The fourth supplies a residue-field ring equivalence and the equation showing it is induced by the inclusion. The final disjunction gives either a field `k` and an isomorphism
`R₀ ≃+* MvPowerSeries (Fin d) k`, or a commutative ring `Λ`, a natural number
`p` and `IsCohenRing p Λ` together with `R₀ ≃+* MvPowerSeries (Fin d) Λ`.
`IsCohenRing` is the existing landed definition, whose clauses are primality of p,
a domain and discrete valuation ring structure, maximal ideal `(p)`, and `(p)`-adic
completeness. Thus it includes exactly the node's local PID, nonfield, and completeness
clauses. Coefficient rings live in `Type u`, the same universe as R; they may be chosen
as subrings of R, so no ring-size case is excluded. The variable count d ranges over ℕ.

Dependencies used are Mathlib declarations: `IsNoetherianRing` from `Mathlib.RingTheory.Noetherian.Defs`, `IsAdicComplete` from `Mathlib.RingTheory.AdicCompletion.Basic`, `IsRegularLocalRing` from `Mathlib.RingTheory.RegularLocalRing.Defs`, and `MvPowerSeries` from `Mathlib.RingTheory.MvPowerSeries.Basic`. The original four dependencies are Mathlib leaves. The already landed node `def-weil-pbc-cohen-ring` was added to `stmt_deps` and its declaration `IsCohenRing` imported from `Sheaf.RingTheory.CohenRing`; no new node or dependency module is needed.

Edge cases checked: the field case permits `d = 0`, so the power-series ring is the coefficient field; the Cohen-ring disjunct explicitly excludes fields and requires a prime generator; and the residue equivalence is stated separately from the power-series disjunction. The statement compiles with the expected single `sorry` warning using `scompile.py`.

Searches performed with `msearch.py`: LeanFinder query “A Noetherian complete local
domain is finite over a regular power series subring” returned the power-series
Noetherian instances, `PowerSeries.fg_iff_of_isPrime`, a local-completeness criterion,
and DVR equivalences, with no match for this existence theorem. Loogle query
`IsAdicComplete, IsRegularLocalRing` returned zero hits. Grep query
`Cohen|coefficient ring|finite_over_regular` in Mathlib RingTheory returned seven
unrelated coefficient-ring uses and the Cohen bibliography entry. LeanSearch query
“A complete Noetherian local domain is finite over a regular power series subring”
was also run; its recorded result is in `searches.jsonl`. `rg` searches of
`WeilConjectures` and `lean/Sheaf` found no existing theorem for the item; they did
find the landed `IsCohenRing` definition, which is used. The original node's historical
searches were read, not rerun under their original query strings.

Source checked directly: [Stacks 032D](https://stacks.math.columbia.edu/tag/032D)
and [Stacks 0327](https://stacks.math.columbia.edu/tag/0327). The literature checkout
is absent on this machine, so these official pages supplied the source statement and
proof. No statement correction or dispute is needed. The complete eight-step DAG
proof is included in the theorem docstring for stage 3.

## Earlier second reading (a previous round; superseded)

Pending the independent second reader; the stage-2 worker dry run records the module and node as ready for review.

## Second reading by J1

Independent second reader: opened the sandbox node and module together, the five
statement dependency nodes, the recorded Mathlib definitions, and the landed
`Sheaf.RingTheory.CohenRing` definition. The original node has no
`statement_change`; no correction of the node is needed. There are no new nodes
or dependency modules in this delivery. The added dependency
`def-weil-pbc-cohen-ring` already exists and states exactly the Cohen-ring notion
needed here, so adding it to `stmt_deps` follows brief-stage2 section 5.

Source: read Stacks `algebra.tex` directly, obtained from
https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex
and saved only in the sandbox scratchpad. Read section
`section-cohen-structure-theorem` from line 44780, its definition of complete
local ring (44786), coefficient rings and the characteristic cases, Definition
0327 (44872), and Lemma 032D and its entire proof (45065--45121).
Also checked the official pages https://stacks.math.columbia.edu/tag/032D and
https://stacks.math.columbia.edu/tag/0327. There are no additional standing
hypotheses in this section; completeness includes separatedness. The node's
maximal-ideal intersection clause is supplied by the source's local inclusion
and residue map, as its proof explains.

Objects, hypotheses, and conclusions, matched individually:

- Object: commutative ring R, with its unique maximal ideal m. Lean:
  `(R : Type u) [CommRing R] [IsLocalRing R]` and
  `IsLocalRing.maximalIdeal R`. PASS; no field or algebra-over-a-base assumption.
- Hypothesis: R is Noetherian. Lean: `[IsNoetherianRing R]`. PASS;
  `Mathlib.RingTheory.Noetherian.Defs` defines this as `IsNoetherian R R`,
  whose field says that every submodule (here ideal) is finitely generated.
- Hypothesis: R is an integral domain. Lean: `[IsDomain R]`. PASS;
  this includes nontriviality, as does the source's domain hypothesis.
- Hypothesis: R is m-adically complete. Lean:
  `[IsAdicComplete (IsLocalRing.maximalIdeal R) R]`. PASS;
  the recorded dependency is Mathlib's complete-and-Hausdorff predicate,
  equivalent to bijectivity of the completion map. No mere surjectivity is used.
- Object in the conclusion: a subring R0 of R. Lean:
  `∃ (R₀ : Subring R)`. PASS; this is a unital subring of the same R,
  with its inherited commutative-ring structure and inclusion `R₀.subtype`.
- Conclusion (1a): R0 is regular local. Lean:
  `∃ hreg : IsRegularLocalRing R₀`, followed by
  `let _ := hreg.toIsLocalRing`. PASS; the dependency node's local-ring
  notion is exactly Mathlib's class, extending local and Noetherian with
  maximal-ideal generator number equal to Krull dimension. Its equality
  formulation is equivalent to generation by dim R0 elements, as checked
  in `IsRegularLocalRing.of_spanFinrank_maximalIdeal_le`. No scheme notion
  or global regular-ring predicate is substituted. The let binds the
  returned structure, not an extra hypothesis on R0.
- Conclusion (1b): R0 is complete for its maximal ideal. Lean:
  `IsAdicComplete (IsLocalRing.maximalIdeal R₀) R₀`. PASS.
- Conclusion (1c): m0 is m intersect R0. Lean:
  `IsLocalRing.maximalIdeal R₀ =
  Ideal.comap R₀.subtype (IsLocalRing.maximalIdeal R)`. PASS;
  comap is exactly intersection interpreted as an ideal of R0.
- Conclusion (2a): R is a finitely generated R0-module. Lean:
  `Module.Finite R₀ R`. PASS; no freely selected module instance is
  quantified or assumed. Mathlib's subring scalar action is inherited
  from multiplication in R (`Subring.smul_def`), so this is finiteness
  for the inclusion, rather than for an unrelated action.
- Conclusion (2b): inclusion induces an isomorphism of residue fields.
  Lean: existential ring equivalence `e` between the two maximal-ideal
  quotients and `∀ x : R₀, e (Ideal.Quotient.mk ... x) =
  Ideal.Quotient.mk ... (R₀.subtype x)`. PASS; the equation fixes the
  equivalence to the inclusion-induced map, so this is stronger than
  a bare existence of unrelated isomorphic fields and exactly the node.
  Both quotients are the residue fields of the given local rings.
- Conclusion (3a): field power-series alternative. Lean:
  `∃ (k : Type u), ∃ h : Field k, ∃ d : ℕ, let _ := h;
  Nonempty (R₀ ≃+* MvPowerSeries (Fin d) k)` (the semicolon here is
  explanatory punctuation). PASS; `MvPowerSeries` is the dependency's
  coefficient family `(Fin d →₀ ℕ) → k`, with coefficientwise sums
  and Cauchy products, not polynomials or a single-variable restriction.
- Conclusion (3b): Cohen-ring power-series alternative. Lean:
  `∃ (Λ : Type u), ∃ h : CommRing Λ, ∃ d : ℕ, let _ := h;
  ∃ p : ℕ, IsCohenRing p Λ ∧
  Nonempty (R₀ ≃+* MvPowerSeries (Fin d) Λ)`. PASS;
  `IsCohenRing` requires prime p, a domain and DVR structure,
  maximal ideal equal to `Ideal.span {(p : Λ)}`, and completeness
  for that ideal. Read its body, not just its name, and read
  `IsDiscreteValuationRing` in Mathlib: it extends local and principal
  ideal ring, with nonzero maximal ideal. Along with the domain this
  is precisely the local PID which is not a field in the node.
- Quantifiers: one subring and one regular-local witness precede all
  clauses; a residue equivalence for that subring precedes the disjunction.
  The field or Cohen-ring witnesses belong to their respective branches.
  PASS; no coefficient ring, dimension, finiteness, or residue equivalence
  is assumed in the hypotheses.

Edge cases: `Fin 0` is permitted, so zero-variable power series give the
coefficient ring in either branch. A field R with m = 0 is covered (R0 = R,
field branch, d = 0); a Cohen ring itself is covered by the second branch
with d = 0. The zero ring is excluded by the source's domain hypothesis and
Lean's `IsDomain`, not by an added condition. Equal characteristic zero,
equal positive characteristic, and mixed characteristic are all allowed;
no p is fixed in the hypotheses. The Cohen branch excludes the field
case through the DVR predicate and requires a prime, nonzero uniformizer.
There are no scheme, empty-scheme, or independent index-family objects in
this node. Universe u is explicitly bound and arbitrary. Requiring the
existential coefficient rings to lie in `Type u` loses no case: the source
chooses a coefficient subring of R, which lies in that universe. The only
index set is finite `Fin d`, including the empty set for d = 0. All names
and universes in the signature are bound; `autoImplicit` is disabled.

Independent duplicate searches (queries differ from the first worker's):

- LeanFinder via `msearch.py`: "A complete local integral domain contains a
  regular local subring over which it is module finite". Eight hits:
  locality from adic completeness and DVR characterizations/localizations,
  with no existence theorem for a finite regular power-series subring.
- Loogle via `msearch.py`: `Subring, IsRegularLocalRing`. Zero hits.
- Grep via `msearch.py`: `regular subring|regular.*complete.*local.*domain|Cohen structure`.
  Zero hits.
- LeanSearch via `msearch.py`: "Noetherian complete local domain contains a
  module finite regular power series subring". Service unavailable
  (Internal Server Error), recorded as unavailable, not as a no-match verdict.
- Direct `rg` across all Mathlib, `WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for `regular subring`, `complete.local.domain`,
  `finite_over_regular`, and `cohen structure`: no matching declaration.
  Project mentions of this lemma are proof outlines in `NagataOfCompleteLocal`
  and `CompleteLocalGRing`, not a duplicate declaration. Broader Cohen and
  regular/subring searches found the landed Cohen-ring and coefficient-ring
  modules, which are related different notions; the required Cohen-ring
  definition is reused rather than copied. The exact full theorem name
  does not already occur in Mathlib or the source library.

Mismatch found and repaired: H8 documentation defect. The original proof
outline stripped TeX backslashes, leaving unreadable expressions such as
`$Lambdacapmathfrak m$`. Replaced only the eight proof paragraphs with the
node's eight proof-step texts verbatim, rewrapped to at most 100 columns.
The source places, dependency references, and complete logical proof are
now readable. Did not rewrite the correct signature or other documentation.
No mathematical mismatch, hollow definition, additional proof, or dispute
was found. The sole theorem proof remains `sorry`. Asserted that
`lean.statement` is verbatim the module signature and that all lines meet
the width convention. `scompile.py` compiled the repaired single module
cleanly on the server in 1.7 seconds, with no warnings or errors.

## Worker report

Stage 2, direct delivery by Q121. The prior session left only brief markers in
both item sandboxes: no module, node copy, report or compile/delivery process
survived. The current live item has the accepted O2 stage-1 split and no Lean
record. This delivery changes only its `lean` record and introduces one module,
`Sheaf.RingTheory.TruncatedPolynomialSectionsSmooth`, containing the theorem
`Algebra.exists_smooth_away_of_truncated_polynomial_sections`. Its whole proof is
`sorry`, as required for stage 2. No new DAG nodes or dependency modules are needed.
The natural-language statement and accepted proof are unchanged.

I read Stacks Algebra Tag 02HT, label `lemma-smooth-test-artinian`, especially
(4) implies (1), the definition of B'_N and B_N, the splitting equation, and the
following conormal/Artin--Rees argument. This is the exact conclusion needed by
`lem-sfb-smooth-fixed-residue-artinian-test`: a smooth principal neighbourhood,
not a smoothness assumption on the entire prime localization.

Hypotheses and conclusion matched against the node:

- R and A are arbitrary commutative rings in independent universes u and v,
  with `[Algebra R A]` and `[IsNoetherianRing R]`. No domain, nontriviality,
  characteristic, locality of A, or independent finite-presentation assumption
  has been added. A prime q already rules out the zero algebra.
- The finite number of variables is `d : ℕ`, including zero. The polynomial
  algebra is the recorded `MvPolynomial (Fin d) R`. The map α is an R-algebra
  map and `hα` says precisely that it is surjective.
- The prime is `(q : Ideal A) [q.IsPrime]`. Its inverse image Q is written
  `q.comap α.toRingHom`; the comap instance supplies primality without another
  hypothesis. C is exactly `Localization.AtPrime Q`, while S is exactly
  `Localization.AtPrime q`.
- The canonical induced p is Mathlib's `Localization.localAlgHom Q q α rfl`.
  I read its definition in Localization/AtPrime/Basic.lean:305-311: its
  underlying ring map is `Localization.localRingHom`, so it sends a fraction
  a/s to α(a)/α(s). Its surjectivity follows from hα and is not an extra
  hypothesis. `J` and `hJ` are an explicit ideal name and its defining equality
  with `RingHom.ker p.toRingHom`; this is a universally quantified alias for
  the unique kernel, not a restriction or a second notion.
- `IsLocalRing.maximalIdeal C` is the ideal QC. The source declaration
  `Localization.AtPrime.map_eq_maximalIdeal` identifies these two descriptions.
  The expression with `^ N` therefore uses the node's precise m^N.
- `hsections` quantifies over every N with `1 ≤ N`, in exactly the source's
  range. For each N it supplies an R-algebra map σ from C/(J + m^N) to
  C/(J^2 + m^N). Here ideal sum is the lattice join `⊔`.
  The canonical map in the opposite direction is `Ideal.Quotient.factorₐ R`
  for J^2 ≤ J joined with the identity inclusion of m^N. The equation
  `(factorₐ ...).comp σ = AlgHom.id R _` is exactly a right inverse.
  There is no compatibility assumption between different N.
- The conclusion `∃ g ∉ q, Algebra.Smooth R (Localization.Away g)` supplies
  every part of the desired principal neighbourhood. The R-algebra structure
  is the canonical tower R -> A -> A_g. I read `Algebra.Smooth` in
  Smooth/Basic.lean:540: it is formal smoothness plus finite presentation,
  as in the recorded definition dependency and its cotangent criterion.

The four statement dependency declarations are used without redefining them:
`Mathlib.RingTheory.Noetherian.Defs` / `IsNoetherianRing`,
`Mathlib.Algebra.MvPolynomial.Basic` / `MvPolynomial`,
`Mathlib.RingTheory.Localization.AtPrime.Basic` / `Localization.AtPrime`, and
`Mathlib.RingTheory.Smooth.Basic` / `Algebra.Smooth`. They and the quotient
operations needed by the statement are public imports. Proof-only imports
include all currently stated dependencies: finite type/presentation,
Noetherian localization, polynomial/localized differentials, Artin--Rees,
`Algebra.FormallySmoothAdic`, the closed upstream
`Algebra.truncated_section_conormal_residue_kernel`, tensor base change, the
local Jacobian criterion, and the prime-neighbourhood criterion. The six
accepted proof steps and their dependency ids are reproduced in the docstring.
There are no local notations, auxiliary definitions, hidden let binders or
new postponed helper claims.

Edge cases checked: d = 0 remains `Fin 0` and introduces no nonempty-variable
assumption; J = 0 makes the truncated maps identities; N = 1 is included.
For A = k[t]/(t^2) at (t), the N = 3 truncation would require lifting the class
of t to an element of k[t]/(t^3) whose square is zero and whose reduction is t,
which is impossible, so the hypothesis does not spuriously force this singular
algebra to be smooth. R = 0 admits no such prime q, as expected. Independent
universes cover all coefficient and algebra sizes with no test-ring universe
restriction.

Searches for an existing statement were actually run with msearch.py and
recorded in searches.jsonl (the stage-2 sandbox selected by the dispatcher):

- LeanSearch: `Sections of all truncated square zero localized polynomial presentations imply smoothness near a prime ideal`.
  Eight hits, including Algebra.IsSmoothAt, Algebra.smoothLocus,
  Algebra.Smooth.of_isLocalization_Away, and RingHom.Smooth.holdsForLocalizationAway.
  These either define the local property or smoothness of a localization of
  the coefficient ring; none deduces the claim from the given sections.
- LeanFinder: `Sections of every quotient C/(J squared plus maximal ideal power N) onto C/(J plus maximal ideal power N) imply smoothness of a finitely generated algebra`.
  Eight hits: smooth_iff, Smooth, standard smoothness, smooth-locus facts.
  None includes the truncated-section hypothesis or the conormal argument.
- LeanFinder, second phrasing: `A finitely generated algebra over a Noetherian ring is smooth at a prime if every truncated conormal square zero quotient splits as an algebra map`.
  Eight hits, including Algebra.IsSmoothAt.exists_notMem_smooth. I read its
  source in Smooth/Locus.lean:150-157: it requires formal smoothness at q;
  deriving that hypothesis is the substance of this item, so this is not an
  existing statement or a one-line specialization.
- Source grep through msearch.py, RingTheory:
  `truncat.*[Ss]mooth|[Ss]mooth.*truncat|section.*maximalIdeal` returned no hits.
- I also searched WeilConjectures, Sheaf and dag/lean_names_upstream.json by the
  item id, the new declaration name, truncated sections and smoothness. The
  existing truncated-section and residue-kernel declarations give earlier
  steps, not this item's conclusion; the consumer's docstring only references
  this item. No existing declaration states it exactly.

Validation: the authorized batch2/scompile.py wrapper compiled this single module
on the server in module mode, first as sandbox and then under its actual module
name. Both passed with no diagnostics (13.1 s and 5.6 s). All Lean lines are at
most 100 characters. The sole JSON change is `lean`, whose signature is copied
verbatim from the theorem keyword through the conclusion before `:=`.

## Review by Q121

I reread the source and node against the compiled file. The only naming binder,
J = ker(p), is fixed by an equality with the canonical localized map, so the
statement is not about an arbitrary surjection or arbitrary ideal. I checked
the direction of σ and its composition equation: reversing this equation would
weaken the assumption to a retraction rather than the required section, and the
file uses the correct direction. The source takes m to be QC; the local-ring
maximal ideal is that extension, not q in the target. The conclusion uses
Smooth of A_g, avoiding the different formal-smoothness-at-q interface. The
Noetherian assumption stays on R and d = 0 is allowed.

For the proof docstring, step 1 carries exactly the finite-presentation and
Noetherian inputs, step 2 the polynomial lifting and finite-free differential
argument, step 3 the Artin--Rees bound, step 4 the closed residue-kernel comparison
and explicit tensor quotient maps, step 5 the local Jacobian criterion, and
step 6 the neighbourhood theorem. All are proof imports, while the four recorded
notions used in the signature are public. No proof or DAG route was changed.

## Second reading by Q121

No second reading by a worker: this is a direct delivery. The maintainer's
independent review is the independent reading; the preceding section is the
author's own check and does not claim to be an independent review.

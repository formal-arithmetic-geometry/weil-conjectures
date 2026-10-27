## Worker report

The module `Sheaf.RingTheory.CompleteModelFaceQuotients` states the whole node as
`ToricMonoid.complete_model_face_quotients`, with one `sorry` and no other postponed
proof. Its docstring carries all seven proof steps, distinguishing agent algebra
from the source's model notation. I opened ILO PDF page 76 (printed p. 70), Exposé VI
1.6(i)--(ii): it gives the equal-characteristic model and the Cohen hypersurface
with equation congruent to p modulo chart monomials and variables. The source does
not assert this face lemma; the node correctly attributes its refinement to agents.
No statement correction or dependency repair is needed.

Hypotheses and objects:

- `P : Type u`, `[AddCommMonoid P]`, and `hfs :
  AlgebraicGeometry.IsFineSaturatedMonoid (Multiplicative P)` give exactly finite
  generation, injectivity into the group completion, and saturation. The additive
  type tag preserves the monoid and its canonical group completion.
- `hsharp` says `a + b = 0 → a = 0 ∧ b = 0`, equivalently that zero is the only
  additive unit. No cancellation or torsion-free hypothesis is added separately.
- `n : ℕ` permits zero variables; `S : AddSubmonoid P` and `hface` express precisely
  the stipulated face condition, including zero in S.
- `L : Type v`, `[CommRing L]`, `[IsLocalRing L]`, and
  `IsField L ∨ ∃ p : ℕ, IsCohenRing p L` encode precisely the two coefficient cases.
  `IsField` is the structure-free field predicate on the already specified ring;
  all fields occur, with their local-ring structure. Universes u and v are independent.
- `ToricMonoid.Complete L P n` and `Complete L S n` are the dependency's original
  adic completions, not new rings of coefficient families. Its `monomial`,
  `completionIdeal`, and `completedChartIdeal` are used without a private copy.

Conclusions, clause by clause:

- The first conjunct is `IsFineSaturatedMonoid (Multiplicative S)` and the second
  is sharpness of S. Thus S is finitely generated, integral, saturated and sharp.
- For every generator list `g : Fin s → P` with closure top, the closure of
  `Set.range g ∩ (S : Set P)` equals S. This is exactly generation by its subset
  lying in S, including the empty list.
- Existential `ρ : Complete L P n →ₐ[L] Complete L S n` is an L-algebra map;
  `Function.Surjective ρ` asserts surjectivity. The coefficient maps `cP,cS` are
  linear equivalences onto all families at `(q,e)`, where `e : Fin n →₀ ℕ` is the
  exponent vector. `cS (ρ b) q e = cP b q.val e` says precisely that ρ retains the
  face coefficients.
- The helper `IsModelCoefficientDescription` pins these coefficient equivalences
  to the original completion. For each x,q,e,k it requires a truncation N such that
  EVERY polynomial representative of x modulo the Nth completion-ideal power has
  its (q,e)-coefficient congruent to `c x q e` modulo the kth coefficient maximal-
  ideal power. Completeness gives existence and separatedness gives uniqueness.
  For k=0 the condition is automatic, while all positive k enforce the actual
  coefficients. These are auxiliary descriptions of the objects already in the
  node, not arbitrary maps substituted for a canonical construction. This avoids
  adding an independent coefficient-theorem prerequisite to stmt_deps.
- `faceMonomialIdeal` is literally the ideal span of `monomial L P n q` for q
  outside S. `RingHom.ker ρ.toRingHom = faceMonomialIdeal ...` and the next
  universally quantified generator-list equality give both displayed kernel
  presentations, including when no generator is outside S.
- In the field case E is an L-algebra equivalence from the quotient by J_S to the
  actual face completion. Its equality on every quotient representative identifies
  it with the induced ρ. The surviving-monomial equation is explicit. The algebra
  equivalence preserves all constants by its type. `IsDomain`, `IsIntegrallyClosed`,
  primality of J_S and the iff for monomial membership give the remaining field
  conclusions. `IsDomain` includes nontriviality.
- For every Cohen prime p and every θ satisfying the original chart-ideal condition,
  `ρ θ` is θ_S. The first conjunct asserts the required chart-ideal condition on
  `ρ θ - p`. `hypersurfaceFaceIdeal` is exactly the ideal image of J_S under the
  canonical quotient map modulo θ. E has exactly the iterated-quotient source and
  the face hypersurface target. Its representative equation identifies the induced
  quotient map; its monomial equation and L-algebra type preserve the specified
  monomials and constants. The next two conjuncts say the face hypersurface is a
  nonzero normal domain. The last two assert primality of the image ideal and
  membership of the image of z^q iff q is outside S. The left displayed quotients
  are consequently nonzero normal domains as well, via E.

Dependency declarations read and used:

- `Sheaf.RingTheory.CompleteToricModel`: `ToricMonoid.PolynomialRing`,
  `completionIdeal`, `Complete`, `monomial`, `completedChartIdeal`; I read their
  complete signatures and docstrings, including their definitions by the already
  published AddMonoidAlgebra completed-local-model interface.
- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`: its imported
  `AlgebraicGeometry.IsFineSaturatedMonoid`, whose complete definition I read in
  `Sheaf.AlgebraicGeometry.LogRegularPair` (canonical group completion, not an
  arbitrary embedding). The log-scheme declarations themselves are not involved.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`, its
  canonical ring/algebra maps and `AdicCompletion.evalₐ`; the latter's signature
  and docstring give the actual quotient by `I ^ N` used in the helper condition.
- `WeilConjectures.RingTheory.CohenRing`: `IsCohenRing`, including primality, domain,
  DVR, maximal ideal equal to span p, and completeness; read verbatim.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed` and
  `IsDomain` implement exactly the recorded normal-domain convention.
- Plain proof imports: `Sheaf.TraceFormula.SharpFsOrthantEmbedding`,
  `Sheaf.RingTheory.LogRegularSaturationNormality`,
  `Mathlib.RingTheory.PrincipalIdealDomain` and
  `Mathlib.RingTheory.Polynomial.RationalRoot`. The completed coefficient nonvanishing
  proof dependency currently has no recorded Lean declaration; it is therefore not
  imported, and its pending proof is named in the theorem's proof plan. It is not
  needed as an extra assumption of this statement.

Edge checks: S=P gives the zero outside-monomial ideal and an identity coefficient
restriction; S={0} keeps exactly the formal-variable coefficients. For P={0}, S=P
and rank zero are allowed. For n=0 the exponent type has its sole zero element.
The empty generator list can generate only the zero monoid, and both spans are zero.
For S={0}, n=0, the Cohen quotient is C/(p), a nonzero residue field; θ=p is allowed.
For P=ℕ² and an axis face, the ideal is the omitted coordinate monomial. For θ=p-z
with that coordinate removed, θ_S=p, as required; when retained, the corresponding
monomial remains nonzero modulo p-z. No nonempty generator list, positive dimension,
perfect residue field, or coefficient/monoid universe equality has been imposed.

Searches (2026-10-24):

- msearch.py LeanFinder: “Projection of a completed monoid algebra onto a face
  retains coefficients, with kernel generated by the monomials outside the face”.
  Eight hits, principally `AddMonoidAlgebra.modOf` and grading lemmas; none states
  the completed face quotient theorem or supplies its coefficient description.
- msearch.py Loogle: `AdicCompletion.map, AddMonoidAlgebra,
  Ideal.quotientKerEquivOfSurjective`. Zero hits, with the last name unknown.
- msearch.py LeanSearch: “completed monoid algebra coefficient description face
  quotient”. Eight hits on ordinary MonoidAlgebra, coefficients and domain-reindexing
  maps; no completed-face statement.
- msearch.py grep: `face.*([Qq]uotient|[Pp]rojection)|([Cc]omplet.*[Ff]ace)` in
  Mathlib RingTheory; zero hits.
- rg searches in the source `lean/WeilConjectures`, project `lean/Sheaf/RingTheory`
  and `lean/Sheaf/TraceFormula` found face-strata and facet-valuation consumers, the
  orthant support projection, and the actual model definitions, but no face-quotient
  theorem or coefficient accessor. Searching the exact blueprint id under
  `lean/WeilConjectures` found none. The existing support projection is for a
  lattice-supported subring of ambient power series, not restriction to a face.
- Full-name rg across Mathlib, WeilConjectures, Sheaf and `dag/lean_names_upstream.json`
  found no `IsModelCoefficientDescription`, `faceMonomialIdeal`,
  `hypersurfaceFaceIdeal` or `complete_model_face_quotients` before this delivery.

Validation: scompile.py compiled the sandbox and library forms cleanly, 4.5 s and
5.5 s respectively. Every theorem proof is exactly `by sorry`; every helper has
real definitional data. No new independent definition nodes, no dependency node
changes, no statement dispute, and no statement changes.

## Second reading by Q22

I reread the node alongside the final file after compilation; no other agent was
started, as the dispatcher brief prohibits delegation. The maintainer's independent
reading remains the review step. This rereading checked the two coefficient cases
share a projection before θ is quantified; θ_S is literally ρ θ; the face quotient
uses the image of J_S, rather than its preimage; the kernel includes exactly outside
monomials; the generator condition uses every original list; and both surviving
monomial equations use q.val in P and q in S. The family descriptions are tied to
ALL deep polynomial representatives (not an unconstrained equivalence). The algebra
equivalences preserve constants even when the coefficient-to-hypersurface map is
not injective. I checked conjunction scope: domain, normality, primality and the iff
all lie inside the appropriate field/Cohen implication; every p and admissible θ
are included. The comparison requires no choices of generators or orthant embedding
in the hypotheses. No mismatch found and no mathematical change was made.

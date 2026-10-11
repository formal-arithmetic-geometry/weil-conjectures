## Worker report

The module `lean/Sheaf/RingTheory/PopescuResolveSeparable.lean` states
`Algebra.canBePopescuResolved_of_regularLocalRing_separable`, with its only proof `sorry`.
The node is unchanged except for its `lean` record. No new notion, dependency module,
statement correction, or disputed statement is needed.

Source read: Stacks Smoothing Ring Maps, Lemma 07FE, `lemma-resolve-special`,
Section 07FB. The repository lacks `literature/stacks-project/smoothing.tex` on this
machine; the available copy `/home/ubuntu/c1-stacks-review/smoothing.tex`, lines
2351–2432, contains that lemma and its proof. The statement agrees with the node.
The declaration docstring reproduces all twelve DAG proof steps, including the
finite-generator exponent correction, the dimension-zero case, the change back
from the polynomial base to k, and the minimality check after quotienting.

Clause-by-clause rendering:

- The field k is `{k : Type u} [Field k]`.
- The k-algebra A is `{A : Type v} [CommRing A] [Algebra k A]`;
  finite presentation is `[FinitePresentation k A]`.
- The commutative k-algebra Λ is `{Λ : Type w} [CommRing Λ] [Algebra k Λ]`.
- The k-algebra homomorphism α is `(α : A →ₐ[k] Λ)`.
- The prime ideal q is `(q : PrimeSpectrum Λ)`, whose `asIdeal` has its prime instance.
- The auxiliary ideal h_A is the existing `popescuIdeal α`, definitionally
  `(Ideal.map α.toRingHom (singularIdeal k A)).radical`. Thus the ideal extension
  and its radical are taken with the given α, not an unrelated map.
- Hypothesis (1) is `[IsNoetherianRing Λ]`.
- Hypothesis (2) is
  `(hminimal : q.asIdeal ∈ (popescuIdeal α).minimalPrimes)`.
  Mathlib's `Ideal.minimalPrimes` is the set of ideals p satisfying
  `Minimal (fun p ↦ p.IsPrime ∧ popescuIdeal α ≤ p) p`.
  This includes containment and minimality among precisely the primes containing h_A.
- Hypothesis (3) is `[IsRegularLocalRing (Localization.AtPrime q.asIdeal)]`,
  including locality, Noetherianity, and the maximal-ideal generator/dimension equality.
- Hypothesis (4) is `(hsep : IsSeparableExtension k q.asIdeal.ResidueField)`.
  `Ideal.ResidueField` is the residue field of `Localization.AtPrime q.asIdeal`;
  its k-algebra structure is inferred from the canonical Λ-algebra structures
  and the given `Algebra k Λ`, through the scalar tower. There is no extra choice
  of a k-action. `IsSeparableExtension` is the recorded definition for potentially
  transcendental extensions, not just Mathlib's separable algebraic extension predicate.
- The conclusion is `CanBePopescuResolved α q`, exactly the existence of an
  intermediate finitely presented k-algebra B, maps β and γ with γ.comp β = α,
  h_A ≤ h_B and h_B not contained in q, using the dependency's definition.

Dependency declarations read and used:

- `Sheaf.RingTheory.PopescuResolution`: `Algebra.popescuIdeal`,
  `Algebra.CanBePopescuResolved`, with `Algebra.IsPopescuResolution` read in full.
- `Sheaf.FieldTheory.SeparableExtension`: `Algebra.IsSeparableExtension`,
  with `Algebra.IsSeparablyGenerated` read in full.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (available through imports).
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`
  (available through the regular-local-ring and residue-field imports).
- `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`: `Ideal.ResidueField`.
- `Mathlib.RingTheory.RegularLocalRing.Defs`: `IsRegularLocalRing`.
- Mathlib's `Ideal.minimalPrimes` / `Ideal.IsMinimalPrime` in
  `Mathlib.RingTheory.Ideal.MinimalPrime.Basic`, available through the regular-ring import.

Edge cases checked before writing:

- Dimension zero is allowed: no positive-dimension binder was introduced; the DAG's
  step 2 gives the field/localization case separately.
- Characteristic zero and positive characteristic are both allowed. The separability
  hypothesis remains meaningful for imperfect fields and transcendental residue fields.
- The zero target ring has no prime spectrum points, so the premise cannot be
  instantiated; no artificial nonzero-ring assumption is needed.
- If h_A is the unit ideal (e.g. A is smooth), there is no prime containing it;
  minimal-prime membership correctly excludes that premise.
- If the singular ideal has no generators (zero ideal), no nonempty-generator
  hypothesis is imposed; the DAG proof handles r = 0.
- The three carrier universes u, v, w are independent and explicitly bound. The
  intermediate algebra universe is that of the dependency definition, `max u v`;
  finitely presented k-algebras have representatives there. No dimension/index
  universe restriction or algebraicity/finite-extension assumption is imposed.

Searches made (2026-10-11):

- `msearch.py ... leanfinder "Popescu resolution of finitely presented algebra at a
  regular prime with separable residue field"`: eight related smoothness, residue-field,
  and finite-presentation results; none states this resolution theorem.
- `msearch.py ... loogle "Algebra.CanBePopescuResolved, IsRegularLocalRing,
  Ideal.ResidueField"`: no hits, unknown identifier `Algebra.CanBePopescuResolved`.
- `msearch.py ... grep "Popescu|popescu|resolve.*separable" RingTheory`: no hits.
- `msearch.py ... leansearch "Popescu local resolution regular local ring separable
  residue field"`: service unavailable, Internal Server Error. The other searches
  and direct source inspection cover the search despite that service failure.
- `rg -n 'popescu|Popescu|resolve.*separable|CanBePopescuResolved|IsSeparableExtension'`
  over `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`: only the
  recorded definitions, separability applications, and unrelated Gabriel–Popescu material.
- `grep -rn 'lem-weil-pbc-popescu-resolve-separable' WeilConjectures`: no upstream declaration.
- Exact proposed declaration-name search across Mathlib, WeilConjectures, lean/Sheaf,
  and dag/lean_names_upstream.json: no collision.

Validation: `scompile.py G1 lem-weil-pbc-popescu-resolve-separable` on the delivered
module succeeded in 1.7 seconds, with no errors or warnings. The second reading is
reserved for the independent second worker; no second-reading section is asserted here.

## Second reading by G1

Independent reading of the sandbox node and Lean module against Stacks
`smoothing.tex`, Lemma 07FE (`lemma-resolve-special`), lines 2351–2432,
and its inherited Situation 07F7, lines 2078–2094. I opened the available
source copy `/home/ubuntu/c1-stacks-review/smoothing.tex`; the repository's
literature copy is absent. Situation 07F7 requires a Noetherian base ring,
an algebra map, a prime, and finite presentation of A over the base.
Here the base is a field, so its Noetherian instance is automatic and does
not strengthen the statement. No section-wide extra assumption was found.

Objects, hypotheses, and conclusion, listed from the node before comparison:

- Base field k: `{k : Type u} [Field k]`. Exact.
- Finitely presented commutative k-algebra A: `{A : Type v} [CommRing A]
  [Algebra k A] [FinitePresentation k A]`. Exact; finite presentation is
  inherited from Situation 07F7, not an added assumption.
- Commutative k-algebra Λ: `{Λ : Type w} [CommRing Λ] [Algebra k Λ]`.
  Exact; Λ need not be a field, local, or finitely generated over k.
- Given k-algebra map α: `(α : A →ₐ[k] Λ)`. Exact, with the prescribed
  scalar actions on both rings.
- Prime ideal q of Λ: `(q : PrimeSpectrum Λ)`. Exact: `q.asIdeal` carries
  primality and imposes no maximality assumption.
- Auxiliary ideal h_A = sqrt(H_{A/k} Λ), extended along α:
  `popescuIdeal α`. I opened `Algebra.popescuIdeal` and the underlying
  `Algebra.singularIdeal`; this is literally
  `(Ideal.map α.toRingHom (singularIdeal k A)).radical`. Exact.
- Hypothesis (1), Λ Noetherian: `[IsNoetherianRing Λ]`. I opened the
  recorded Mathlib abbreviation and `isNoetherianRing_iff_ideal_fg`:
  every ideal is finitely generated. Exact.
- Hypothesis (2), q minimal among primes containing h_A:
  `(hminimal : q.asIdeal ∈ (popescuIdeal α).minimalPrimes)`.
  I opened `Ideal.minimalPrimes` and `Ideal.IsMinimalPrime`: the latter
  is `Minimal (fun p ↦ p.IsPrime ∧ popescuIdeal α ≤ p) q.asIdeal`.
  It includes both containment and minimality in the correct set. Exact.
- Hypothesis (3), Λ_q regular local:
  `[IsRegularLocalRing (Localization.AtPrime q.asIdeal)]`.
  I opened the recorded Mathlib declarations: localization is at the
  complement of q, and regular locality includes locality, Noetherianity,
  and equality of maximal-ideal spanFinrank with Krull dimension. The
  generator-bound formulation in the node is equivalent by the adjacent
  `IsRegularLocalRing.of_spanFinrank_maximalIdeal_le`. Exact; regularity
  of all of Λ is not required.
- Hypothesis (4), κ(q)/k separable via the given k-action:
  `(hsep : IsSeparableExtension k q.asIdeal.ResidueField)`.
  I opened `Ideal.ResidueField`, `Algebra.IsSeparableExtension`, and
  `Algebra.IsSeparablyGenerated`, and compared the latter two with
  Stacks Algebra 030O, `/home/ubuntu/c1-stacks-review/algebra.tex`,
  lines 9915–9927. The residue field is the quotient of Λ_q by its
  maximal ideal, with the canonical scalar tower from k through Λ.
  Separability quantifies over every finitely generated intermediate
  field and asks for a transcendence basis with separable algebraic
  extension above its generated field. Mathlib's `Algebra.IsSeparable`
  in that last clause implies algebraicity, as its declaration explains.
  Exact; no algebraicity of κ(q)/k or finite-extension hypothesis is added.
- Conclusion, the local problem can be resolved:
  `CanBePopescuResolved α q`. I opened both this definition and
  `IsPopescuResolution`. After all the displayed hypotheses, it asserts
  existence of a commutative k-algebra B, β : A →ₐ[k] B, and γ : B →ₐ[k] Λ,
  with `FinitePresentation k B`, `γ.comp β = α`,
  `popescuIdeal α ≤ popescuIdeal γ`, and
  `¬ popescuIdeal γ ≤ q.asIdeal`. These are all the factorization,
  finite-presentation, inclusion, and noncontainment clauses in the
  definition following Situation 07F7, in the right quantifier order.
  Exact; it does not replace the conclusion by an unrelated smooth map.

Every recorded statement dependency was opened, including the local-ring
clause of `def-weil-regular-scheme`, rather than using its similarly named
regular-ring clause. The delivered module uses the recorded notions directly.
No new definition nodes or dependency modules are present or needed.
There is no `statement_change`, and the node differs from the base only in
`lean`; no source correction or citer verdicts need review.

Edge cases: dimension zero is included without an artificial positive-dimension
binder. Both characteristics and imperfect fields are allowed; transcendental
separable residue extensions are included. The zero target ring has no prime
and hence no instance of the premises. If A is the zero ring, a unital map
into a ring with a prime cannot exist, which correctly excludes that case.
When h_A is the unit ideal there is no prime over it. Empty lists of singular
ideal generators, including H = 0, are not excluded. There is no index set,
scheme, or n in the theorem; the proof's r = 0 and d = 0 cases are explicitly
covered in its docstring. Universes u, v, w are independent and bound.
The dependency chooses B in `Type (max u v)`, which includes representatives
of all finitely presented k-algebras as quotients of finite-variable polynomial
rings over k; it places no size restriction on Λ or its residue field.

Independent searches (different wording from the first reading):

- LeanFinder: `Desingularization factorization at a minimal prime with regular
  localization and separable residue extension`. Eight hits about smooth
  loci, étale residue maps, and Zariski's Main Theorem, with no matching
  resolution theorem; the returned signatures concern other hypotheses
  and conclusions.
- Loogle: `IsRegularLocalRing, Algebra.FinitePresentation`. Zero hits.
- LeanSearch: `A finitely presented algebra over a field can be desingularized
  at a prime whose local ring is regular and residue field extension separable`.
  Service unavailable (Internal Server Error); recorded as unavailable,
  not a negative search result.
- Direct `rg` with `desingulari|resolve.*regular|regular.*separable|
  canBePopescuResolved_of_regularLocalRing_separable|CanBePopescuResolved`
  across pinned Mathlib RingTheory and FieldTheory, upstream WeilConjectures,
  project lean/Sheaf, and dag/lean_names_upstream.json. Only the resolution
  definitions and unrelated geometric regularity modules appeared. No
  existing statement and no declaration-name collision were found.

Mismatch and repair verdict: none. The original Lean and node record were
retained. All four imports supply notions used by the statement. Every
variable and universe is explicitly bound, every line is at most 100
characters, and the only theorem has `sorry` as its whole proof. There are
no new definitions or hollow data. Module and declaration docstrings name
07FE and the correct blueprint id. I compared all twelve proof steps to
the node: every step is verbatim after normalizing line wrapping, including
the exponent repair, dimension-zero branch, base change back to k, and
minimality check in the quotient. The node's `lean.statement` is verbatim
equal to the theorem signature before `:= by`.

Second-reader validation: the mandated `scompile.py G1
lem-weil-pbc-popescu-resolve-separable` invocation on the module succeeded
(exit 0, 1.6 seconds), with no errors or warnings.

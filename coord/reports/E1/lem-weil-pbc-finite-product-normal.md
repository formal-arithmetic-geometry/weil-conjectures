## Worker report

The module `Sheaf.RingTheory.FiniteProductNormal` states
`Pi.isNormalRing_of_finite`, with a `sorry` proof and no definitions or additional nodes.
It formalizes the finite-product normality assertion of Stacks Tag 0CYA.
The local literature checkout has no `algebra.tex`, so the source was read at
https://stacks.math.columbia.edu/tag/0CYA (Lemma 10.37.15 and its proof).

Hypothesis and clause correspondence:
- The finite family R₁,…,Rₙ is `{I : Type u} [Finite I] (R : I → Type v)`.
  Independent explicit universes permit arbitrary finite index types and ring carriers.
- The factors are commutative rings: `[∀ i : I, CommRing (R i)]`.
- Every factor is normal: `hR : ∀ (i : I) (p : Ideal (R i)) [p.IsPrime],
  IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)`.
- The product is the pointwise ring on `∀ i : I, R i` (Mathlib `Pi.commRing`).
- For every prime of this product: `∀ (p : Ideal (∀ i : I, R i)) [p.IsPrime]`.
- Its localization is a normal domain: `IsDomain (Localization.AtPrime p) ∧
  IsIntegrallyClosed (Localization.AtPrime p)`. This is exactly the definition of
  normal ring, so no additional conclusion is needed.

Dependency used: `def-weil-pbc-normal-ring` has status `mathlib` and no `lean` record.
Its `mathlib_match` explicitly prescribes the above conjunction at every prime.
The full signatures and docstrings of `IsIntegrallyClosedIn`, `IsIntegrallyClosed`
(Mathlib.RingTheory.IntegralClosure.IntegrallyClosed), and `Localization.AtPrime`
(Mathlib.RingTheory.Localization.AtPrime.Basic) were read, along with `IsDomain`
(Mathlib.Algebra.Ring.Defs). No dependency module is needed: the match supplies the
exact notion inline, as in the existing `Sheaf.RingTheory.EtaleNormalRing` module.
The module docstring and theorem docstring record the source and all three DAG proof
steps, including prime classification, localization identification, and transport.

Edge cases checked: the empty product is the zero ring, with no prime ideals, and
both the source and Lean normality condition are vacuous; no `Nonempty I` or
`Nontrivial (R i)` is imposed. A singleton product gives the same local condition as
its factor. Zero-ring factors are allowed and have no primes. Factors need not be
domains themselves (for instance products of fields); only prime localizations
must be domains. No Noetherian, characteristic, or positive-cardinality assumption
was introduced. Finite index types need no chosen enumeration or decidable equality.

Searches, using `msearch.py E1 lem-weil-pbc-finite-product-normal`:
- LeanFinder: "A finite product of commutative normal rings is normal: every prime
  localization is an integrally closed domain". Eight hits concern integral
  algebras, Noetherian products, principal ideal rings, `Pi.commRing`, and finite
  presentation; none states this assertion.
- Loogle: `IsIntegrallyClosed, Localization.AtPrime`. Two hits:
  `IsIntegrallyClosed.of_localization_maximal` and `.of_localization`, neither a
  finite-product normality result.
- LeanSearch: "finite product of normal rings is normal". Service unavailable
  (Internal Server Error); the other search kinds were completed.
- Mathlib grep: `IsIntegrallyClosed.*(pi|prod)|[Nn]ormal[Rr]ing|normal ring` in
  RingTheory. Two hits are explanatory comments in IntegrallyClosed.lean, stating
  that normal rings are a TODO, not a declaration.
- `rg` over WeilConjectures for the item id, `IsIntegrallyClosed.*(pi|prod)`, and
  `normal ring`: no hits. Broad normal-ring/name searches produced only unrelated
  normalization and group-normality occurrences.
- `rg` over `lean/Sheaf` and `dag/lean_names_upstream.json` for normal-ring and
  finite-product names: only the etale-over-normal statement was relevant; no
  existing finite-product statement or declaration-name collision was found.

No statement correction or disputed mathematical assertion was found.

## Second reading by E1

Read the sandbox node and module, the dependency node `def-weil-pbc-normal-ring`,
and the actual Mathlib declarations supplying its accepted one-line match.
The local Stacks checkout is absent. I independently read the upstream `algebra.tex`
at https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex:
its Conventions section, `definition-domain-normal`, `definition-ring-normal`,
and `lemma-finite-product-normal` with its proof. I also read the rendered Tags
https://stacks.math.columbia.edu/tag/0CYA,
https://stacks.math.columbia.edu/tag/0309 and
https://stacks.math.columbia.edu/tag/00GV. The chapter convention is commutative
rings with identity, including the zero ring; there is no standing Noetherian
or nontriviality assumption.

Object, hypothesis, and conclusion checklist (all verdicts: exact):
1. A finite family of factors R_i: `{I : Type u} [Finite I] (R : I → Type v)`.
   This expresses arbitrary finite families, including n = 0, without choosing
   an enumeration, Fintype structure, or decidable equality.
2. Each factor is a commutative ring with identity:
   `[∀ i : I, CommRing (R i)]`, exactly the source's ring convention.
3. Each factor is normal in the sense of the dependency:
   `hR : ∀ (i : I) (p : Ideal (R i)) [p.IsPrime],
   IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)`.
   The order is factor, ideal, primality evidence, normal-domain assertion.
   The prime instance is a quantified implication, not an extra hypothesis that
   primes exist. No domain structure on the factors themselves is required.
4. R is the finite product of those very factors: `∀ i : I, R i`, equipped
   with Mathlib's `Pi.commRing` from `Mathlib.Algebra.Ring.Pi`. An additional
   product ring binder or isomorphism would add no mathematical content.
5. Every prime of the product: `∀ (p : Ideal (∀ i : I, R i)) [p.IsPrime]`.
   This ranges over all primes, rather than only maximal or selected primes.
6. Its localization is a normal domain: both
   `IsDomain (Localization.AtPrime p)` and
   `IsIntegrallyClosed (Localization.AtPrime p)` occur in the conclusion.
   These are exactly the domain and integral-closure clauses of the node,
   hence exactly normality of the product; no clause is omitted or strengthened.

Dependency/signature audit: the dependency is an accepted Mathlib leaf, with no
`lean` declaration and an explicit `mathlib_match.how` prescribing this inline
conjunction. `IsDomain` (Algebra/Ring/Defs.lean:439) supplies nontriviality and
multiplicative cancellation, hence integral-domain structure for a commutative
ring. `IsIntegrallyClosedIn` and `IsIntegrallyClosed` (IntegralClosure/
IntegrallyClosed.lean:66,74) express integral closure in `FractionRing R`;
`isIntegrallyClosed_iff` gives its elementwise meaning. `Localization.AtPrime`
(Localization/AtPrime/Basic.lean:57) is `Localization P.primeCompl`, with the
prime hypothesis and no domain hypothesis. Thus no missing definition or
unusable dependency needs a new node or module. The existing project's
`RingHom.Etale.isNormalRing` uses this same accepted normal-ring rendering.

Edge cases: for an empty I the product is the zero ring and has no primes,
so the conclusion is vacuous, as the node explicitly requires. Zero-ring factors
are allowed: their own normality is vacuous and their coordinate contributes no
prime. A singleton gives precisely the factor's local assertion; non-domain
normal factors, such as products of fields, remain allowed. No restrictions on
characteristic, cardinality beyond finiteness, or Noetherianity occur. Explicit
independent universes u and v allow arbitrary finite index universes and ring
universes; finitely many carriers can be placed in a common universe. No
variables or universes are unbound. Empty schemes and zero objects are not
objects of this ring statement.

Independent searches (different wording from the worker, through msearch.py):
- LeanFinder: "Localization of a finite direct product of commutative rings at
  a prime ideal is an integrally closed integral domain if all factors are normal".
  Eight results: local-to-global integral-closure and Dedekind-localization results;
  none states normality of finite products.
- Loogle: `"IsIntegrallyClosed", "Pi"`: zero hits.
- LeanSearch: "The direct product of finitely many locally integrally closed
  commutative rings is locally integrally closed": service unavailable, Internal
  Server Error; no verdict attributed to this unavailable service.
- Mathlib grep: `isNormalRing|normal.*product|product.*normal|IsIntegrallyClosed.*(Pi|Prod)|((Pi|Prod).*)IsIntegrallyClosed`
  in RingTheory. Three hits, all unrelated or explanatory text; no declaration.
- The same independent name/concept search over the read-only WeilConjectures
  source, repository lean/Sheaf, and dag/lean_names_upstream.json found only
  unrelated normalized-product text and `RingHom.Etale.isNormalRing`. No existing
  finite-product normality theorem or declaration-name collision was found.

H5/H6/H8/H9: no definitions or private notions, one named theorem whose only
proof is `sorry`, and no proved auxiliary statement. Its module and declaration
source docstrings carry the exact blueprint id. The proof docstring reproduces
all three node steps and their dependencies: classify primes by factors,
identify the localization via projection, then transport normal-domain structure.
The topic, namespace, necessary imports, and 100-character line limit are correct.
The node's lean.statement was checked to equal the file's signature verbatim.
No statement_change, new nodes, or dependency modules are present or needed.

No mismatch found. I changed only this report by appending the second reading;
the Lean module and node record remain as written. The required server compile
via scompile.py completed cleanly (exit 0, no warnings).

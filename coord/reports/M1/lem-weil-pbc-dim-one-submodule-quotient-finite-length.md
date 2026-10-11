## Worker report

The module `Sheaf.RingTheory.LengthQuotSMulTopFractionFieldSubmodule` states Stacks
Algebra Tag 00PE, `lemma-finite-length`, as the single theorem
`Submodule.length_quotSMulTop_le_of_ringKrullDim_eq_one_of_isLocalRing`, with proof `sorry`.
No definitions or additional nodes are introduced. The node is unchanged except for `lean`.

Hypothesis and clause correspondence:

- A commutative integral domain R: `{R : Type u} [CommRing R] [IsDomain R]`.
- Noetherian: `[IsNoetherianRing R]`; local: `[IsLocalRing R]`.
- Krull dimension exactly one: `hdim : ringKrullDim R = 1`.
- Its fraction field K: `{K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]`.
  The algebra fixes the R-action and `IsFractionRing` identifies it as localization at the
  nonzerodivisors, which for a domain is its fraction field.
- A nonnegative integer r: `(r : ℕ)`.
- Any R-submodule of K to the finite direct-sum power r:
  `(M : Submodule R (Fin r → K))`. For finite `Fin r`, the product is the finite direct sum.
  M carries its inherited R-module structure. No finite-generation or spanning hypothesis occurs.
- Every nonzero x in R: `(x : R) (hx : x ≠ 0)`; the theorem quantifies over both.
- R/xR has finite length: `Module.length R (QuotSMulTop x R) < ⊤`.
- M/xM has finite length: `Module.length R (QuotSMulTop x M) < ⊤`.
- The bound: `Module.length R (QuotSMulTop x M) ≤
  (r : ℕ∞) * Module.length R (QuotSMulTop x R)`.
  `QuotSMulTop x M` is the quotient of the module M itself by x times its top submodule,
  hence exactly M/xM, not an ambient quotient. For R this is R/xR.

Dependency declarations used and read in full:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`, definition and `isNoetherianRing_iff_ideal_fg`.
- `def-weil-pbc-krull-dimension-ring`: `Mathlib.RingTheory.KrullDimension.Basic`,
  `ringKrullDim`, the supremum of lengths of prime chains in `WithBot ℕ∞`.
- `def-weil-pbc-module-length`: its Mathlib match `Mathlib.RingTheory.Length`,
  `Module.length`, and `Module.length_ne_top_iff`. The dependency has status mathlib and
  needs no separate Lean record. Finite length is length below top, equivalently not top.

Auxiliary existing notions used: `IsLocalRing` in `Mathlib.RingTheory.LocalRing.Defs`,
`IsFractionRing` in `Mathlib.RingTheory.Localization.FractionRing`, and `QuotSMulTop` in
`Mathlib.RingTheory.QuotSMulTop`. Their definitions were inspected; no private copies occur.

Source checked: `/home/ubuntu/c1-stacks-review/algebra.tex`, lines 29170–29235,
label `lemma-finite-length` (the repository's literature checkout is absent on this machine).
The source gives exactly the hypotheses and inequality. Its finite R/xR length makes the
bound imply finite M/xM length; the node explicitly includes that consequence, as does Lean.
The declaration docstring records all nine proof steps and their dependency nodes.

Edge cases: r=0 gives a zero ambient module and zero quotient; M=0 likewise. Unit x makes
both quotients zero. Arbitrary non-finitely-generated M is allowed, including the whole K^r.
The hypotheses exclude the zero ring and fields (dimension zero) exactly as the node does.
There is no characteristic restriction. R and K have independent explicit universes u,v.
All binders are explicit; there are no auto-bound variables.

Searches made:

- `msearch.py leansearch`, query `submodule of fraction field finite dimensional vector space
  quotient finite length`: service unavailable, HTTP Internal Server Error; no verdict inferred.
- `msearch.py leanfinder`, query `Noetherian local domain dimension one arbitrary submodule
  of fraction field power quotient by nonzero scalar finite length bound`: eight hits.
  `isFiniteLength_quotient_span_singleton` covers only R/xR; dimension inequalities and regular
  quotient equalities do not state the arbitrary-submodule bound.
- `msearch.py loogle`, query `Module.length, Submodule, IsFractionRing`: zero hits.
- `msearch.py grep`, query `length.*quotient|quotient.*length|QuotSMulTop`, subdirectory
  `RingTheory`: 25 hits, including the reusable quotient abbreviation, general length identities,
  and the R/xR finite-length theorem, but no arbitrary M bound.
- `rg` over `WeilConjectures` and `lean/Sheaf` for the item id and
  `length.*quotient|quotient.*length`: no declaration of this item. The global lemma
  `Submodule.length_quotSMulTop_lt_top_of_ringKrullDim_eq_one` in
  `Sheaf.RingTheory.FiniteLengthGlobalSubmodule` has only the M/xM finite-length conclusion,
  without the length bound, and therefore does not state this item.
- Read `WeilConjectures/RingTheory/DiscreteValuationRing/Dominating.lean`: its length estimates
  concern valuation subrings and ideal chains, not arbitrary submodules of K^r.
- `rg` in `dag/lean_names_upstream.json` for `dim-one-submodule|finite_length.*submodule`:
  no hits. No declaration with the chosen full name was found in the searched sources.

Validation: the server single-file compiler succeeded, exit code 0, with no warnings (1.3 s).
No statement dispute or dependency fault was found.

## Second reading by M1

I independently read the sandbox node and Lean module against Stacks Algebra,
Tag 00PE (`lemma-finite-length`), in `/home/ubuntu/c1-stacks-review/algebra.tex`,
lines 29170–29235, including the surrounding text. The source introduces all
hypotheses in the lemma itself; there is no additional standing hypothesis.
No statement correction, new definition node, or dependency module is present.

Object, hypothesis, and conclusion checklist (all verdicts: exact):

- Commutative integral domain R: `{R : Type u} [CommRing R] [IsDomain R]`.
  The domain and local-ring predicates exclude the zero ring, as does the source.
- Noetherian R: `[IsNoetherianRing R]`. I opened its dependency node and
  `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherian R R`, equivalently every
  ideal is finitely generated (`isNoetherianRing_iff_ideal_fg`).
- Local R: `[IsLocalRing R]`, the usual nontrivial local commutative ring
  predicate in `Mathlib.RingTheory.LocalRing.Defs`; no completeness is assumed.
- Krull dimension one: `(hdim : ringKrullDim R = 1)`. I opened its dependency
  node and `Mathlib.RingTheory.KrullDimension.Basic`: the dimension of the
  inclusion-ordered prime spectrum, in `WithBot ℕ∞`. This is equality, not
  a bound or a regularity hypothesis.
- Fraction field K of R: `{K : Type v} [Field K] [Algebra R K]
  [IsFractionRing R K]`. I opened `Localization.FractionRing`: this means
  `IsLocalization (nonZeroDivisors R) K`. For a domain these are exactly the
  nonzero denominators; the algebra fixes the intended R-action.
- Nonnegative integer r: `(r : ℕ)`, including zero.
- Arbitrary R-submodule M of the finite direct sum of r copies of K:
  `(M : Submodule R (Fin r → K))`. Finite products and finite direct sums
  are canonically the same module here. M has the inherited coordinatewise
  R-action. There is no finite-generation, spanning, nonzero, or freeness
  assumption on M.
- Every nonzero x in R: `(x : R) (hx : x ≠ 0)`. These universal binders
  follow the objects R, K, r, M; hdim is a hypothesis on R independent of M.
- Finite length of R/xR: `Module.length R (QuotSMulTop x R) < ⊤`.
- Finite length of M/xM: `Module.length R (QuotSMulTop x M) < ⊤`.
- The length bound: `Module.length R (QuotSMulTop x M) ≤
  (r : ℕ∞) * Module.length R (QuotSMulTop x R)`.
  I opened the length dependency node and `Mathlib.RingTheory.Length`:
  `Module.length` is the supremum of lengths of strict submodule chains;
  `length_ne_top_iff` identifies finiteness with `IsFiniteLength`.
  I opened `Mathlib.RingTheory.QuotSMulTop`: its abbreviation is
  `M ⧸ x • (⊤ : Submodule R M)`. Thus the quotient is taken inside the
  subtype M, precisely M/xM, and for M=R it is R/xR. The conjunction
  explicitly includes the finite-length consequence of the source's bound,
  exactly as the node requests, without strengthening the source.

Edge cases checked: r=0 (empty finite index set) and M=0 give zero quotient
and zero length; a unit x gives both quotients zero. Non-finitely-generated
M, including all of K^r, is allowed. x=0 is deliberately excluded. Fields
have dimension zero and are excluded by hdim. No characteristic is fixed.
The independent explicit universes u and v cover arbitrary R and K;
all variables and universes in the signature are bound. Empty schemes
are inapplicable to this ring/module statement.

Independent searches, using words different from the first reading:

- LeanFinder via msearch: `length of torsion free module modulo a scalar
  over a one dimensional local domain bounded by rank`. Eight hits include
  `Module.length_of_free_of_finite`, `Module.length_of_free`,
  `Module.length_eq_rank`, and support-dimension quotient formulas. I opened
  the length declarations: they concern free modules or vector spaces,
  not arbitrary submodules modulo a scalar. None states this node.
- Loogle via msearch: `Module.length, IsLocalRing`. Four hits concern
  `IsLocalRing.length_restrictScalars`, `IsLocalRing.length_baseChange`,
  and their CovBy forms. Their signatures concern scalar restriction or
  flat base change, not the present submodule bound.
- LeanSearch via msearch: `torsion free module over one dimensional
  Noetherian local domain reduction modulo nonzero element length bounded
  by rank`. HTTP Internal Server Error, recorded unavailable; no verdict
  inferred from that service.
- Independent rg over Mathlib/RingTheory, upstream WeilConjectures, and
  project lean/Sheaf for `QuotSMulTop`, `length.*[Rr]ank`, `length.*finrank`,
  `length_quotSMulTop`, and `finiteLength.*[Ss]ubmodule`: existing quotient,
  length, and support-dimension results, but no theorem giving this bound.
  I opened `Sheaf.RingTheory.FiniteLengthGlobalSubmodule`: its theorem
  `Submodule.length_quotSMulTop_lt_top_of_ringKrullDim_eq_one` drops locality
  and concludes only finite length, with no bound. It is not this statement.
- rg of the full proposed declaration name and the item name in upstream,
  lean/Sheaf, and dag/lean_names_upstream.json found no duplicate declaration.

H3–H9 review: no mathematical mismatch, private definition, hollow data,
extra proof, or unbound binder found. The module and theorem docstrings
name 00PE and the blueprint id. Their nine proof steps follow the node:
principal quotient, unit case, smaller span, clearing denominators,
power containment via radicals, successive quotient lengths, free-module
length, sandwich bound, and finite-chain reduction for arbitrary M.
All six imports supply notions used in the signature. The stored
`lean.statement` is verbatim the declaration signature up to `:=`.
No Lean or node changes were needed; I appended only this review.

Validation: reran scompile with the absolute sandbox module path; the
server compiled the single file in 1.3 seconds, exit code 0, no warnings.

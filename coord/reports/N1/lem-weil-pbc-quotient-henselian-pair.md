## Worker report

The module `Sheaf.RingTheory.QuotientHenselianPair` states
`IsLocalRing.henselianRing_quotient_maximalIdeal`, with one `sorry` proof and no definitions.
The node is unchanged except for its `lean` record. No missing notion or dependency module
is needed, and there is no statement dispute or correction.

Hypothesis and clause correspondence:
- The local commutative ring `(A,m)` is `(A : Type u) [CommRing A] [IsLocalRing A]`,
  with `m = IsLocalRing.maximalIdeal A`.
- Henselianity of its maximal-ideal pair is
  `[HenselianRing A (maximalIdeal A)]`, the predicate recorded by the dependency.
  Its equivalence with the finite-algebra idempotent criterion is Stacks 09XI (3).
- The ideal `I` and containment are `(I : Ideal A) (hI : I ≤ maximalIdeal A)`.
- The quotient pair is `A ⧸ I` and `(maximalIdeal A).map (Ideal.Quotient.mk I)`;
  this image ideal is precisely `m/I`. The first conjunct asserts `HenselianRing`
  for this pair, without requiring a new chosen local-ring instance on the quotient.
- Every finite quotient algebra is quantified by `∀ (B : Type (max u v))
  [CommRing B] [Algebra (A ⧸ I) B] [Module.Finite (A ⧸ I) B]`.
- Extension of `m/I` to B is its `Ideal.map (algebraMap (A ⧸ I) B)`.
- An arbitrary idempotent of the indicated quotient is `∀ e : B ⧸ ...,
  IsIdempotentElem e → ...`.
- Existence, idempotency, lifting, and uniqueness are respectively `∃! b : B`,
  `IsIdempotentElem b`, and `Ideal.Quotient.mk ... b = e` in the same predicate.
  The explicit finite-algebra conjunct restates the node's explanatory clause and
  is equivalent to the first conjunct, rather than imposing an additional condition.

Dependency declarations read and used: `Sheaf.RingTheory.HenselianTerminology`
records Mathlib's `HenselianRing` and `HenselianLocalRing` as the pair/local notions.
The full signature and docstring of both were read in `Mathlib.RingTheory.Henselian`,
as was `WeilConjectures.Mathlib.RingTheory.Henselian`, whose module documentation
fixes those notions for this blueprint. The dependency's new strict-henselian predicate
is not needed here. `Mathlib.RingTheory.Finiteness.Defs` supplies `Module.Finite`;
`Mathlib.Algebra.Group.Idempotent` supplies `IsIdempotentElem`.

Edge cases checked: I=0 gives the original pair up to the canonical quotient;
I=m gives a field quotient with zero ideal, so the quotient map in the conclusion
is an isomorphism and lifts are unique. Zero finite algebras are allowed and have
one idempotent. No nonzero or positive-rank condition is imposed on B. The zero ring
A is excluded already by the node's local-ring hypothesis, as in Mathlib's
`IsLocalRing`. No assumption on characteristic or Noetherianity is introduced.
`Type (max u v)` for test algebras avoids a universe smaller than A and permits
arbitrarily large test algebras as v varies. Every universe and binder is explicit.

Source checked online because this machine has no `literature/stacks-project/` copy:
[09XK](https://stacks.math.columbia.edu/tag/09XK),
[09XI](https://stacks.math.columbia.edu/tag/09XI), and
[0DYD](https://stacks.math.columbia.edu/tag/0DYD).
The three proof steps in the node are included in the theorem docstring:
finiteness descends through the surjection, the two extended ideals coincide,
and the original pair supplies unique idempotent lifts.

Searches for an existing statement:
- `msearch.py ... leansearch "quotient of henselian pair finite algebra idempotents"`:
  service unavailable (Internal Server Error), recorded as unavailable.
- `msearch.py ... leanfinder "quotient of henselian local ring idempotents finite algebra
  lift uniquely"`: eight hits, including `HenselianRing`, `HenselianLocalRing`,
  nilpotent-kernel idempotent lifting and standard-etale square-zero lifting;
  none states quotient descent for henselian pairs.
- `msearch.py ... loogle "HenselianRing, Ideal.Quotient"`: zero hits,
  unknown identifier `Ideal.Quotient`.
- `msearch.py ... grep "quotient|Quotient|⧸" RingTheory/Henselian.lean`: five hits,
  all root-lifting descriptions or the local quotient homomorphism proof;
  no quotient henselian theorem.
- `rg` over Mathlib/RingTheory, WeilConjectures and lean/Sheaf for
  `henselian.*quotient|quotient.*henselian|HenselianRing.*⧸|henselianRing_quotient`:
  only related docstrings and the stronger strictly henselian quotient statement;
  none has this statement. The latter requires separable closedness, so is not reused.
- The item id was searched in upstream source and `dag/lean_names_upstream.json`:
  no declaration. Related project modules were read to ensure consistent use of
  the recorded henselian notion and explicit idempotent clauses.

Validation: server single-file compilation and the delivery dry run are run on
this module. Only the expected sorry warning is permitted. The independent second
reading is left to the second worker, as instructed.

## Second reading by N1

I independently opened the item JSON and module, the sole statement dependency
`def-weil-pbc-henselian-terminology` and its module, Mathlib's `HenselianRing`
and `HenselianLocalRing` signatures/docstrings, and the upstream
`WeilConjectures.Mathlib.RingTheory.Henselian` module. There are no new definition
nodes, dependency modules, or statement corrections in this delivery.

Source reading: the local Stacks checkout is absent. I read the actual
`more-algebra.tex` from https://raw.githubusercontent.com/stacks/stacks-project/master/more-algebra.tex
at `lemma-integral-over-henselian-pair` (09XK),
`lemma-henselian-henselian-pair` (0DYD), and
`lemma-characterize-henselian-pair` (09XI), as well as the corresponding tag pages.
09XK assumes a henselian pair and an integral ring map, with no Noetherian,
characteristic, or finiteness assumption on the base. A surjection is integral;
0DYD explicitly applies it to the quotient in (2) ⇒ (1). Condition (3) of 09XI
is the finite-algebra bijection on idempotents. This confirms the node as written.

The complete object/hypothesis/conclusion checklist, with verdicts:

- Local commutative ring `(A,m)`: `(A : Type u) [CommRing A] [IsLocalRing A]`,
  with `m` rendered as `maximalIdeal A`. Exact; no chosen additional ideal.
- Its maximal-ideal pair is henselian: `[HenselianRing A (maximalIdeal A)]`.
  Exact via the recorded dependency, which intentionally uses Mathlib's equivalent
  root criterion; 09XI (3) identifies the finite-algebra criterion. No extra
  henselian-local-ring instance is assumed.
- Ideal `I` and containment `I ⊆ m`: `(I : Ideal A) (hI : I ≤ maximalIdeal A)`.
  Exact, inclusive containment, not strict containment or a finiteness condition.
- Quotient ring and ideal `(A/I,m/I)`: `A ⧸ I` and
  `(maximalIdeal A).map (Ideal.Quotient.mk I)`. Exact: surjectivity of the quotient
  map makes this image the quotient ideal, since `I ≤ m`.
- Henselianity of this pair: first conjunct `HenselianRing (A ⧸ I) ...`.
  Exact; no extra local structure on the quotient is needed to state a pair.
- Every finite commutative quotient algebra: `∀ (B : Type (max u v))
  [CommRing B] [Algebra (A ⧸ I) B] [Module.Finite (A ⧸ I) B]`.
  Exact: I read `Module.Finite` as finite generation of the top submodule,
  not finite type as an algebra and not a finite underlying set.
- Quotient by the extended ideal: `B ⧸ ((maximalIdeal A).map
  (Ideal.Quotient.mk I)).map (algebraMap (A ⧸ I) B)`. Exact ideal extension.
- Every idempotent in that quotient: `∀ e : B ⧸ ..., IsIdempotentElem e → ...`.
  Exact: `IsIdempotentElem e` means `e * e = e`, as read in Mathlib.
- Unique idempotent lift: `∃! b : B, IsIdempotentElem b ∧
  Ideal.Quotient.mk ... b = e`. Exact: existence and uniqueness apply only
  to idempotent lifts, not to all representatives. Quantifiers occur in the
  node's order (algebra, quotient idempotent, unique lift).
- The conjunction states both the named pair property and its explicit
  idempotent meaning. These are equivalent clauses of the node's conclusion,
  so the conjunction adds no stronger property.

Edge cases: `I = 0` is allowed; `I = m` gives a field quotient and zero image
ideal, so the reduction on each B is an isomorphism. Zero finite algebras B are
allowed by `CommRing B` without `Nontrivial B`; their unique element is the unique
idempotent lift. Empty generating families (rank zero) are allowed by
`Module.Finite`. The local-ring convention excludes the zero base ring:
Mathlib's `IsLocalRing` explicitly extends `Nontrivial`, matching the usual
one-maximal-ideal local ring in the source. No scheme or independent index set
is quantified here. There is no characteristic restriction. Universes `u v`
are declared explicitly; `Type (max u v)` permits test algebras at least as
large as the base, with arbitrarily larger universes, without a vacuous
small-universe hypothesis. Every variable is visibly bound.

Independent searches (different phrasing from the first reader):

- LeanSearch through `msearch.py`: "A surjective ring homomorphism carries a
  henselian maximal ideal pair to a henselian quotient pair". Service unavailable
  with Internal Server Error; no negative search verdict is inferred.
- LeanFinder: "surjective image of a henselian pair is henselian and finite
  algebra idempotents lift". Eight results: HenselianRing, local-root TFAE,
  adic-completion surjectivity, and formal-smoothness results. None states this
  quotient-pair theorem.
- Loogle: `HenselianRing, "map"`. Successful search, zero hits.
- `rg` on Mathlib/RingTheory, upstream WeilConjectures, and project lean/Sheaf
  for henselian with quotient, surjective, or idempotent in either word order.
  Opened project `IntegralOverHenselianPair`, `StrictlyHenselianQuotient`, and
  `HenselianIntegralIdempotentLifting`: respectively a more general integral
  transfer without this explicit lifting conclusion, a strict-henselian
  specialization with stronger hypotheses, and lifting for integral algebras
  without quotient-pair descent. None is this exact statement. Upstream
  `HenselianFiniteEtale` concerns global sections of finite schemes, not this
  algebraic quotient statement. The exact declaration name and item id are
  absent from upstream and `dag/lean_names_upstream.json`.

No mathematical mismatch found; no Lean or node field needed repair. Added only
this independent review. There are no definitions (hence no hollow definitions),
no private notions or local notation/instances, and the sole theorem has a
`sorry` proof as stage 2 requires. Both docstrings name the source and blueprint;
the theorem docstring carries all three proof steps: finite generators descend
through the surjection, the extended ideals agree, and henselianity supplies
unique lifts. The dependency import supplies the recorded henselian notion;
the other imports supply finite modules and idempotency. Checked line lengths
and mechanically verified `lean.statement` equals the signature verbatim.

## Stage-2 review R-qhp (FIX)

Dropped the second conjunct (the explicit finite-algebra idempotent clause). By the H1
record of def-weil-pbc-henselian-terminology (a0c53a4be) a henselian pair is `HenselianRing A I`;
the node's colon clause only spells out that definition in its 09XI (3) form, so the conjunct is
derivable from the first one (a restated definition, not a clause of its own). Rule: no
tautological or derivable conjunct (brief, C1 f683186fb, 52041d948). The statement is now
`HenselianRing (A ⧸ I) ((maximalIdeal A).map (Ideal.Quotient.mk I))`, in the form of the landed
sibling `henselianRing_of_isIntegral`. The universe `v` and the imports of `Module.Finite` and
`IsIdempotentElem` are no longer used and were removed. Mathlib (pinned) has no quotient result for
`HenselianRing`, so `existing: false` stays. Compiled with SHEAF_GROUP=L in 1.4 s.

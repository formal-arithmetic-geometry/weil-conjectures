## Worker report

Item: `lem-sfb-fixed-subring-normal-localizations`.
Module: `Sheaf.RingTheory.FixedSubringNormalLocalizations`.
Declaration: `FixedPoints.isDomain_and_isIntegrallyClosed_subring_localizations`.
The module states the whole item as one theorem with `sorry`. It introduces no definition,
instance, helper theorem, or extra hypothesis. Only the node's `lean` field changes.

Hypotheses and clauses, read against the unchanged node:

- A commutative integrally closed domain D is `(D : Type u) [CommRing D] [IsDomain D]
  [IsIntegrallyClosed D]`. The dependency's normal-domain convention is exactly
  `IsDomain D` together with `IsIntegrallyClosed D`; no Noetherian assumption is used.
- The arbitrary group is `(G : Type v) [Group G]`, with its universe independent of D.
- The action by unital ring automorphisms is `[MulSemiringAction G D]`. This is the
  usual equivalent encoding of alpha: `MulSemiringAction.toRingEquiv G D` has type
  `G →* (D ≃+* D)`. The action laws, preservation of zero, addition, one and multiplication,
  and inverses in G give exactly the stipulated unital ring automorphisms. Conversely an
  alpha of that type acts by evaluation, with these same laws. No extra compatibility
  with a base algebra is requested.
- C is Mathlib's `FixedPoints.subring D G`, whose carrier consists exactly of d with
  `∀ g : G, g • d = d`, with inherited ring operations. It is the actual fixed subring,
  not a ring equipped with an arbitrary comparison map or an existentially chosen ring.
- C being a domain is the first conclusion `IsDomain (FixedPoints.subring D G)`.
- C being integrally closed in its own fraction field is the second conclusion
  `IsIntegrallyClosed (FixedPoints.subring D G)`.
- Every prime ideal p of C is quantified as
  `∀ (p : Ideal (FixedPoints.subring D G)) [p.IsPrime], ...`.
- Its localization is exactly `Localization.AtPrime p`. The last conclusion is
  `IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)`.
- The same universally quantified last clause is precisely the inline normal-ring
  definition recorded by `def-weil-pbc-normal-ring`; no second normality predicate or
  duplicate conjunct is needed for the word “consequently”.
- There is no `Finite`, `Fintype`, `FaithfulSMul`, characteristic assumption, group-order
  invertibility assumption, or extra algebra structure among the binders.

Dependency declarations and source inspection:

- `def-weil-pbc-normal-ring`: public import
  `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`, declaration `IsIntegrallyClosed`
  (abbreviation for integral closedness in `FractionRing`), together with `IsDomain`.
  Read the abbreviation's full signature and docstring at lines 65–74 and the domain
  mixin/docstring in `Mathlib.Algebra.Ring.Defs` at lines 422–439. The general normal-ring
  convention in the node's lean.note and coord/STATE.md is used verbatim inline.
- `def-weil-pbc-localization-at-prime`: public import
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, declaration `Localization.AtPrime`.
  Read its full definition and docstring: `Localization p.primeCompl`, i.e. localization
  at C minus p. The dependency also records residue fields and fibre rings, which this
  item does not mention and therefore does not use.
- Existing fixed-subring definition: public import
  `Mathlib.Algebra.Algebra.Subalgebra.Operations`, `FixedPoints.subring`; read its complete
  definition at lines 97–100, combining `FixedPoints.addSubgroup` and `FixedPoints.submonoid`.
  Read `MulSemiringAction` in `Mathlib.Algebra.Ring.Action.Basic` and
  `MulSemiringAction.toRingEquiv` in `Mathlib.Algebra.Ring.Action.Group` to check the alpha
  encoding, including the unit and inverse conditions.
- Proof dependency `lem-weil-pbc-localization-normal-domain` is a Mathlib leaf with no
  lean record, as permitted. Its recorded declarations were read in full:
  `isIntegrallyClosed_of_isLocalization` (IntegrallyClosed.lean:379),
  `IsLocalization.isDomain_of_le_nonZeroDivisors` (Localization.Defs:891), and
  `IsFractionRing.isFractionRing_of_isLocalization`
  (Localization.LocalizationLocalization:260). Its modules are available through the
  public imports above and the proof-only import
  `Mathlib.RingTheory.Localization.LocalizationLocalization`. No unusable interface
  was encountered and no dependency repair was necessary.

Sources read locally: `literature/stacks-project/algebra.tex`, definition-domain-normal
(Tag 0309, line 7979), lemma-localize-normal-domain (Tag 00GY, lines 8048–8063, including
its denominator-clearing proof), and definition-ring-normal (Tag 00GV, line 8206).
The fixed-subring proof is agent-formulated as the item's source explicitly records,
not attributed to Stacks as a separately quoted theorem. The theorem docstring contains
all five DAG proof steps, including the fraction-field embedding, the monic equation,
fixed-denominator cancellation, localization, and the normal-ring conclusion.

Edge cases checked mathematically before writing:

- The zero ring is correctly excluded by the source's domain assumption `IsDomain D`.
  A fixed subring contains 0 and 1 distinctly, so it is also nontrivial.
- A trivial action (including an arbitrarily large group acting trivially) gives C = D;
  no faithfulness or finiteness is necessary. Infinite groups are allowed by the binders.
- A field D is allowed; the fixed ring is then a field, and its sole prime localization
  is again a field. For an arbitrary D the prime p = (0) is included: C_p is Frac(C).
- In characteristic p the translation action on F_p[t] is allowed with no division by p.
  Its fixed ring is F_p[t^p-t], a normal domain.
- The sign action on Q[t] has fixed ring Q[t²]. It is integrally closed in its own fraction
  field, although not integrally closed in Q[t]. Thus no assumption
  `IsIntegrallyClosedIn C D` may replace the required proof, and none was added.
- The action by all nonzero rational scalings on Q[t] has fixed ring Q and demonstrates
  that the assertion does not rely on D being integral over C for infinite groups.

Searches actually run through `msearch.py NX lem-sfb-fixed-subring-normal-localizations`:

1. LeanFinder, “The subring fixed by an arbitrary group of automorphisms of an integrally
   closed domain is integrally closed, and so are its prime localizations”: eight hits;
   first `isIntegrallyClosed_of_isLocalization`. The remaining results concerned integral
   closures, localization and normal closures. No exact fixed-subring theorem.
2. Loogle, `IsIntegrallyClosed, FixedPoints.subring`: zero hits.
3. Mathlib grep, `(IsIntegrallyClosed|integrallyClosed).*(fixed|Fixed|invariant)|
   (fixed|Fixed|invariant).*(IsIntegrallyClosed|integrallyClosed)`, RingTheory: zero hits.
4. LeanSearch, “The invariant subring of an integrally closed domain under an arbitrary
   group action by ring automorphisms is integrally closed”: eight hits. Invariant-extension
   integrality is a different assertion; `IsIntegrallyClosed.of_equiv` and integral-closure
   declarations do not give this assertion either.
5. Direct rg in `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`,
   query `FixedPoints.subring|fixedSubring|fixed_subring|IsIntegrallyClosed.*[Ff]ixed|
   [Ff]ixed.*[Ii]ntegrally|lem-sfb-fixed-subring-normal-localizations`: existing fixed-subring
   uses for inertia, strict Henselian invariants and trace-one finiteness; no normality
   theorem for fixed subrings. A direct grep for the item id in `lean/WeilConjectures`
   found no occurrence.
6. Direct rg for `isDomain_and_isIntegrallyClosed_subring_localizations` in Mathlib,
   `lean/WeilConjectures`, and `lean/Sheaf`: no existing declaration with this name.

Read the promising descent lemma
`IsIntegrallyClosed.of_isIntegrallyClosed_of_isIntegrallyClosedIn`: its extra ambient
integral-closedness assumption fails for Q[t²] inside Q[t], so it is not an exact match.
No new notion is needed: C is specified inline in the item and its existing Mathlib
construction is reused. There are no new nodes, dependency modules, statement changes,
or disputed statements.

Validation: `scompile.py NX lem-sfb-fixed-subring-normal-localizations` compiled this file
separately in sandbox and library naming modes, in 3.0 s and 3.4 s respectively, with no
errors or unexpected warnings. All universes and variables are bound explicitly; the
file has no diagnostic commands, local notation, private definition, or lines over 100
characters. The node signature is copied verbatim from `theorem` through the type before
`:=`; all other existing JSON fields are preserved, with indent 1 and a final newline.

## Second reading by NX

This is a second pass by the same dispatcher worker, not a claim of an independent agent
review; the prompt forbids starting other agents and assigns independent review to the
maintainer. Reopened the original node and the finished module and compared the signature
clause by clause. D has exactly commutative-ring, domain and integral-closedness binders;
G has exactly the group and ring-action binders. In particular `[MulSemiringAction G D]`
requires unit preservation and, with `[Group G]`, automorphisms, matching alpha. The actual
fixed subring appears in both global conclusions and as the underlying ring of every
ideal in the local conclusion. The `p.IsPrime` binder selects every prime ideal, including
zero. Both the domain and integral-closedness conclusions for each localization are
present; that whole universal clause is the recorded inline normal-ring condition.
No extra assumptions or missing clauses were found. No statement edits were needed.
The docstring gives all five proof steps and the source distinguishes the agent-written
fixed-subring argument from the Stacks localization lemma. There are no new nodes or
dependency modules to review. Independent review remains with the maintainer as instructed.

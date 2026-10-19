## Worker report

This repairs the returned immutable head 1a37d2e25fba with a complete stage-2
`existing: true` binding to `Algebra.IndEtale.isSeparable_residueField` in
`WeilConjectures.RingTheory.ProEtale.IndEtale`, lines 141–161. The signature in
`lean.statement` is copied verbatim from that declaration; its surrounding
variables bind `(R S : Type u) [CommRing R] [CommRing S] [Algebra R S]`.
No Lean module is delivered because the declaration already exists, as required
by brief-stage2 §1 and §5. The old attachment's incomplete lean record is replaced,
not merely rebased. Only `lean` changes in the node copy.

Clause and hypothesis correspondence:

- The arbitrary commutative rings A,T are `R,S : Type u` with `[CommRing R]`
  and `[CommRing S]`. The map f is `[Algebra R S]`, hence `algebraMap R S`.
  Any given ring map is represented by its `RingHom.toAlgebra` structure.
- The ind-etale hypothesis is `[Algebra.IndEtale R S]`. This is exactly the
  definition exposed by the dependency's module
  `Sheaf.RingTheory.IndPrincipalZariski`, publicly importing the upstream
  `WeilConjectures.RingTheory.ProEtale.IndEtale`. Its class uses filtered
  colimit presentations with etale terms; etale includes finite presentation.
- Every prime q is `(q : Ideal S) [q.IsPrime]`; put
  `p := q.comap (algebraMap R S)` at the use site. The theorem's
  `(p : Ideal R) [p.IsPrime] [q.LiesOver p]` says precisely this relation:
  `q.over_def p` identifies p with the contraction. For this p, both prime
  and LiesOver instances synthesize without extra assumptions.
- Residue fields are the dependency's `Ideal.ResidueField`, defined in
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal:33` as the quotient of
  `Localization.AtPrime p` by its maximal ideal. The localization dependency
  is a Mathlib leaf; its `mathlib_match` is used without a replacement notion.
- The canonical map is encoded by
  `[Algebra (Localization.AtPrime p) (Localization.AtPrime q)]` and
  `[Localization.AtPrime.IsLiesOverAlgebra p q]`. These are canonical
  construction/compatibility structures, not additional restrictions on f.
  `Localization.AtPrime.algebraOfLiesOver p q` (AtPrime/Basic:365–368) is
  `(Localization.localRingHom p q (algebraMap R S) Ideal.LiesOver.over).toAlgebra`.
  The standard instance at lines 379–381 proves `IsLiesOverAlgebra` for it.
  The construction is intentionally not a global instance to avoid diamonds.
  Installing that named construction locally in the scratch consumer suffices.
  The residue algebra is induced by this canonical local map.
- The conclusion is `Algebra.IsSeparable p.ResidueField q.ResidueField`.
  This is the recorded separable-algebraic dependency
  `Mathlib.FieldTheory.Separable.Algebra.IsSeparable`, whose docstring and
  definition at lines 541–550 explicitly include algebraicity:
  nonalgebraic elements have zero, hence nonseparable, minimal polynomial.
  `Algebra.IsSeparable.isAlgebraic` at line 570 supplies algebraicity.
- For `[p.IsMaximal] [q.IsMaximal]`,
  `Algebra.isSeparable_residueField_iff.mp
    (Algebra.IndEtale.isSeparable_residueField R S p q)` gives
  `Algebra.IsSeparable (R ⧸ p) (S ⧸ q)` directly. The iff is read in full
  at `Mathlib.RingTheory.LocalRing.ResidueField.Instances:55–57`.
  `Ideal.Quotient.algebraOfLiesOver` (Ideal/Over:287–288) supplies exactly
  the quotient map: on the class of r it is the class of f(r), as witnessed
  by `Ideal.Quotient.algebraMap_mk_of_liesOver`. The equivalence uses the
  canonical maps from these maximal quotients to the corresponding residue
  fields, bijective by `Ideal.bijective_algebraMap_quotient_residueField`.
  Thus the final clause is a one-line specialization of existing declarations,
  not an omitted clause or an arbitrary identification.
- There is no finite-type, Noetherian, perfect-field, finite-dimensional,
  local-ring, or maximality hypothesis in the arbitrary-prime assertion.

Sources opened: `more-algebra.tex`, lemma-weakly-etale-residue-field-extensions
(Tag 092R), lines 30556ff; `proetale.tex`, lemma-ind-etale-implies (Tag 097N),
lines 1210ff. The first gives separable algebraic residue extensions for weakly
etale maps and the second applies to every ind-etale map. The exact upstream
proof also gives a direct argument: represent an element of S at an etale stage,
base change to kappa(p), map to the local ring kappa(q), and use separability of
images. Every residue-field element is a ratio of images; the separable closure
is closed under division. No extra node carrying this entire conclusion is needed.

Edge cases checked: S=0 has no prime q, so the conclusion is vacuous; a prime q
forces both residue fields nontrivial; identity maps give the separable identity
field extension; nonmaximal primes remain allowed; arbitrary characteristic is
allowed. Infinite filtered colimits/infinite separable algebraic residue
extensions are allowed because neither the theorem nor its conclusion demands
finite generation or finite degree. Both rings may be placed in a common
universe u, matching the recorded Algebra.IndEtale interface; no relation of
site universes or extra size assumption is introduced.

Searches run in this repair:

- `msearch.py ... leanfinder "An ind etale homomorphism of rings induces separable
  algebraic extensions on residue fields at every prime"`: 8 hits including
  finite-type formally-unramified residue separability and the maximal quotient
  iff; no general ind-etale Mathlib theorem. Its finite-type alternative does
  not replace this node.
- `msearch.py ... loogle '"ResidueField", Algebra.IsSeparable'`: 10 hits;
  `Algebra.isSeparable_residueField_iff` and the two maximal-quotient conversion
  instances supply the final clause. Other hits assume separability or impose
  finite type.
- `msearch.py ... grep "isSeparable_residueField|algebraOfLiesOver"`: 25 hits,
  including the canonical localization algebra and its compatibility instance
  in AtPrime/Basic, and canonical quotient algebra in Ideal/Over.
- `msearch.py ... leansearch "Residue fields of ind etale algebras are separable
  algebraic extensions"`: 8 hits including `Algebra.IsSeparable.isAlgebraic`,
  the maximal quotient/residue instances and finite-type variants.
- `rg -n 'isSeparable_residueField'` in the upstream WeilConjectures tree and
  project's lean/Sheaf: the exact upstream theorem and its callers were found;
  there is no competing Sheaf declaration of this node. The node-id search in
  WeilConjectures and DAG search found the item and its Artin-dichotomy consumer.
  The dependency's IndPrincipalZariski module and all recorded signatures and
  relevant docstrings were opened in full. No new notion is introduced.

Validation: `scompile.py Q50 lem-trf-ind-etale-residue-separable
scratchpad/ExistingChecks.lean` compiled the ordinary-prime separability and
algebraicity, and the maximal-quotient separability and algebraicity, with the
canonical localization construction installed. The consumer imports
`Sheaf.RingTheory.IndPrincipalZariski` and
`Mathlib.RingTheory.LocalRing.ResidueField.Instances`; the quotient iff is supplied
by the latter, not re-exported by the upstream ind-etale module. It printed no
error or warning.
`#print axioms Algebra.IndEtale.isSeparable_residueField` reports only
`propext`, `Classical.choice`, `Quot.sound`. The scratch consumer is validation
only, not a duplicate delivered theorem or part of the landing.

No STATEMENT-DISPUTED finding, statement correction, new node, or dependency
module is needed.

## Repair of the return

H2/H3: replaced the incomplete attachment with the full module/declaration/
verbatim-statement/branch/by/date/existing record. The above correspondence
accounts for every clause, including algebraicity and the maximal quotient map.

D1/D2: no new statement node or proof step simply restates the conclusion.
The exact upstream statement is reused; its existing proof stays upstream.
No split is needed when the item already has that declaration (B10).
The current base has no such spurious new node, and none is reintroduced.

B10: the canonical `algebraOfLiesOver` and `IsLiesOverAlgebra` structures are
accepted and were validated in a real consumer, rather than rejected as extra
mathematical hypotheses. There is no arbitrary map or choice replacing them.

H1: report now has `## Worker report`, this point-by-point repair section and
`## Second reading by Q50`. No new-node or dependency-module section is required
because neither is delivered. The absence of a delivered Lean file is deliberate
under the exact-existing-declaration rule, and the wrapper checks that declaration
through a real compile.

## Second reading by Q50

No independent worker was started: this dispatch explicitly forbids other agents;
the maintainer supplies the independent review. As the author's final audit, I
reopened the item, full upstream signature/docstring/proof, the three dependency
records, canonical localization constructor and maximal quotient iff. In
particular I checked that LiesOver means equality with the contraction, that
IsLiesOverAlgebra fixes the actual canonical local map, that separability includes
algebraicity, and that the quotient algebra sends [a] to [f(a)]. The compiled
scratch consumer covers both clauses with no finite-type assumption. The repair
changes the binding and report, not the mathematical node statement or its users.

## Worker report

The module `lean/Sheaf/RingTheory/QuotientGRing.lean` states `isGRing_quotient`, with
its proof deliberately `sorry`. No definition or proof is added. The node is unchanged
except for its `lean` record; no new nodes, dependency modules or corrections are needed.

Hypothesis and conclusion correspondence:

- “Let R be a G-ring”: `{R : Type u} [CommRing R] (hR : IsGRing R)`.
  Commutativity is part of the dependency's definition, not an additional assumption.
  Noetherianity and regularity of every prime-localization completion map are supplied
  together by the recorded predicate `IsGRing`.
- “I ⊆ R an ideal”: `(I : Ideal R)`. There is no restriction on the ideal.
- “The quotient ring R/I is a G-ring”: `IsGRing (R ⧸ I)`, using Mathlib's ideal quotient
  and its canonical commutative ring structure.
- The parenthesis referencing the finite type, quasi-finite quotient map explains the
  source application; these properties are automatic and need no extra hypotheses.

Dependency declarations read and used: `IsGRing` in `Sheaf.RingTheory.GRing`
(`def-weil-pbc-g-ring`). Its complete signature and body, together with the signatures
and docstrings of `Algebra.IsGeometricallyRegular` and `RingHom.IsRegular`, were read.
The quotient uses `Ideal.instHasQuotient` and `Ideal.Quotient.commRing` from
`Mathlib.RingTheory.Ideal.Quotient.Defs`, whose source was read. The proof docstring
carries all five steps of the node's proof and names the nodes they use.

Source checked: the local Stacks source file is absent on this machine, so the original
source was read at https://stacks.math.columbia.edu/tag/07PP. Item (3) gives preservation
under quasi-finite maps between Noetherian rings; applying it to the finite type
surjection R → R/I gives exactly this statement. No source hypothesis is missing.

Edge cases checked mathematically before writing: I = 0 gives a quotient isomorphic
to R; I = R gives the zero ring, which is Noetherian and has no primes, hence satisfies
IsGRing; the zero source ring is also allowed. Arbitrary nonprime ideals are included.
There is no Nontrivial, domain, local-ring, field or characteristic restriction.
The explicitly bound universe u covers rings and their quotients in any universe;
no test-object universe is newly introduced.

Searches (2026-10-11):

- msearch.py leanfinder, query “A quotient of a G-ring is a G-ring”: eight hits,
  all quotient ring structures, including Ideal.Quotient and RingQuot; no G-ring theorem.
- msearch.py loogle, query “IsG Ring, Ideal.Quotient”: no hits; unknown identifier IsG.
- msearch.py grep, query `IsG[Rr]ing|G-ring|formal.?fib`, directory RingTheory:
  no Mathlib hits.
- rg of `IsG[Rr]ing|G-ring|lem-weil-pbc-g-ring-quotient` in the source project's
  WeilConjectures and the project's lean/Sheaf: the project has the GRing definition
  and finite-type/complete-local results, but no quotient theorem; the source has none.
- grep -rn of the exact node id in source WeilConjectures: no hits.
- rg of `isGRing_quotient|IsGRing.*⧸` across Mathlib, source WeilConjectures and
  lean/Sheaf: no hits, confirming the new declaration name is unused.
- Read dag/lean_names_upstream.json using rg for quotient/IsGRing: no G-ring
  declaration or blueprint association for this node.

No STATEMENT-DISPUTED condition or node fault was found. The theorem does not use the
more general finite-type theorem as a substitute or introduce a second G-ring predicate.

## Second reading by C1

Read independently with the item node, QuotientGRing.lean, the dependency node
`def-weil-pbc-g-ring`, and its recorded module `Sheaf.RingTheory.GRing` open.
The item has no `statement_change`; there are no new definition nodes or dependency
modules in this delivery. No mismatch was found, so the Lean and node were retained.

Objects, hypotheses, and conclusion, item by item:

1. A commutative ring R: `{R : Type u} [CommRing R]`. Verdict: exact; commutativity
   belongs to the cited G-ring definition, and arbitrary universe u is explicitly bound.
2. R is a G-ring: `(hR : IsGRing R)`. Verdict: exact. Read the dependency's full body:
   `IsNoetherianRing R` and, for every prime ideal p, `RingHom.IsRegular` of the
   canonical map from `Localization.AtPrime p` to its maximal-ideal `AdicCompletion`.
   This is the same completion map as the dependency node and Stacks 07GH.
3. An arbitrary ideal I of R: `(I : Ideal R)`. Verdict: exact. No prime, proper,
   finitely generated, or maximal ideal assumption is added.
4. The quotient ring R/I: `R ⧸ I`. Verdict: exact. Opened Mathlib's
   `Ideal.instHasQuotient` and `Ideal.Quotient.commRing` in Ideal/Quotient/Defs.lean;
   they construct the usual ideal quotient with its canonical commutative ring structure.
5. The sole conclusion is that this quotient is a G-ring: `IsGRing (R ⧸ I)`.
   Verdict: exact, using the same predicate on both sides. The binders universally
   quantify over R, its ring structure, hR, and then I; no hidden instance is demanded.
6. The parenthetical application of 07PP(3) is source justification, not an additional
   conclusion or hypothesis about a separately chosen map. Verdict: exact. The quotient
   map is automatically surjective, finite type, and quasi-finite; the Noetherian
   hypotheses on both rings follow from hR and preservation under quotients.

Source reading: the local literature checkout has no Stacks .tex. Fetched the official
Stacks repository's `more-algebra.tex` into the sandbox scratchpad and read
`lemma-G-ring-goes-up-quasi-finite`, including all preceding hypotheses and its proof,
plus `definition-G-ring`. Checked the rendered source at
https://stacks.math.columbia.edu/tag/07PP and https://stacks.math.columbia.edu/tag/07GH.
The lemma assumes a finite type map of Noetherian rings; all these assumptions hold
for R -> R/I. Its local prime data serves clauses (1) and (2); clause (3) is the global
assertion used here and does not select any particular primes.

Also read `RingHom.IsRegular` and `Algebra.IsGeometricallyRegular` in the dependency
module against Stacks 07BZ and 0381(2). The former is flatness plus geometric regularity
of every `p.Fiber S`; the latter includes Noetherianity and regularity after every finite
purely inseparable extension. Opened Mathlib's `Ideal.Fiber`, which is κ(p) tensor S;
this is the fibre in the dependency node, with tensor factors exchanged canonically
relative to the source notation. The extension universe `max u v` includes a model of
every finite extension and avoids vacuous tests. No private predicate or hollow data
is introduced. The recorded dependency is usable without a replacement module.

Edge cases: I = 0 gives R up to the canonical quotient isomorphism; I = top gives the
zero ring, whose prime condition is vacuous and whose Noetherianity holds. A zero source
ring is admitted. Nonprime ideals, all characteristics, and rings in every universe
are included. In characteristic zero the geometric-regularity test still includes the
trivial purely inseparable extension. No scheme, index family, or integer n occurs;
the finite-type quotient presentation uses zero polynomial variables without excluding
that case. No Nontrivial, field, domain, local-ring, or extra Noetherian instance binder
has been added.

Independent searches, with wording different from the first worker:

- msearch leanfinder: “Noetherian commutative rings with geometrically regular completion
  maps remain so after dividing by an arbitrary ideal”. Eight results concern quotient
  Noetherianity, flatness of completion, and Hausdorffness; none states this G-ring result.
- msearch leansearch: “regular formal fibers descend to quotient rings”. Service returned
  Internal Server Error; this is an unavailable search, not a negative search verdict.
- msearch loogle: `"GRing", "quotient"`. Zero results.
- msearch grep in RingTheory: `Grothendieck|formal.*fib|isGRing_quotient|IsGRing`.
  Seven hits are bibliographical references and smooth-fibre results, not this theorem.
- rg with `grothendieck.*ring|formal.{0,25}fib|isGRing_quotient|IsGRing|quotient.*G-ring`
  over the source WeilConjectures, project lean/Sheaf, and upstream-name index.
  Only the project's shared predicate and other G-ring results are relevant. Opened
  `isGRing_of_finiteType` in FiniteTypeGRing.lean: it quantifies over a separate algebra
  S with a finite-type instance and is the more general parent statement, not the
  same quotient statement. The quotient theorem is absent from the source and Mathlib.

H5/H6/H8/H9 checks: the delivery contains one named theorem with proof exactly `sorry`,
no definitions, no proved lemmas, no extra axioms. The module and theorem docstrings
name Stacks 07PP and the correct blueprint id. The five docstring proof steps match
all five node steps: quotient Noetherianity and prime inverse image; localization and
kernel; regular base change; tensor quotient and completion identification; transport
of flatness and geometric regularity and conclusion. Every proof dependency is named.
Both imports supply notions used by the signature. Names have no Sheaf prefix; lines
fit the 100-character convention. The explicitly declared u and bound R, hR, I leave
no unbound variable. The node's lean.statement equals the signature before `:=` verbatim.

Validation: scompile.py C1 lem-weil-pbc-g-ring-quotient on QuotientGRing.lean returned
exit code 0, “Compiled in 1.5 s”, with no warnings. Second reading changed only this
report and appended independent search evidence; no statement or implementation repair
was necessary.

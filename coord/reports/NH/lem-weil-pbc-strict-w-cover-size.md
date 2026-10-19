## Worker report

The module `Sheaf.RingTheory.StrictWCoverSize` states
`PrincipalWLocalization.StrictWCover.cardinalMk_le`, with its sole proof `sorry`.
No definitions, helper nodes, dependency repairs, or statement corrections were needed.

Clause-by-clause correspondence:

- A commutative ring A: `(A : Type u) [CommRing A]`; no nontriviality assumption.
- An infinite cardinal κ: `(κ : Cardinal.{v}) (hκ : Cardinal.aleph0 ≤ κ)`.
- The size hypothesis |A| ≤ κ: `hA : Cardinal.lift.{v} (Cardinal.mk A) ≤
  Cardinal.lift.{u} κ`. The lifts compare cardinals in the common universe max u v.
- W = A^w, E = W^e, I the closed-point vanishing ideal, and C_A = E_[V(IE)]:
  the conclusion uses exactly `PrincipalWLocalization.StrictWCover.algebra A` from
  `Sheaf.RingTheory.StrictWCover`, without substituting an arbitrary cover.
  Read the entire dependency module: `closedIdeal` uses `PrimeSpectrum.vanishingIdeal`
  on `closedPoints`; `contraction` uses `CommRingCat.etaleContraction` of the principal
  w-localization; `contractionMap` is its zeroth-stage map; `extendedIdeal` uses
  `Ideal.map`; `retainedAlgebra` uses the zero locus of that ideal and the recorded
  retained localization; `structuralMap` composes all structural maps; `algebra`
  bundles this exact composite as an A-algebra. Thus all intermediate objects in
  the node are fixed by the imported definition, with no additional hypotheses.
- The sole conclusion |C_A| ≤ κ: `Cardinal.lift.{v} (Cardinal.mk (algebra A)) ≤
  Cardinal.lift.{u} κ` inside namespace `PrincipalWLocalization.StrictWCover`.

Dependencies and proof imports:

- Statement dependency `def-weil-pbc-strict-w-cover`: module
  `Sheaf.RingTheory.StrictWCover`, declaration
  `PrincipalWLocalization.StrictWCover.algebra` (read in full, including its docstrings).
- `lem-weil-pbc-finite-list-cardinality`: `Cardinal.mk_list_le_max`, module
  `Mathlib.SetTheory.Cardinal.Arithmetic` (also provides the public cardinal notation/API).
- `def-weil-pbc-w-local`: `IsWLocalRing`, module
  `WeilConjectures.RingTheory.ProEtale.WLocal`.
- `def-weil-pbc-w-localization`: `PrincipalWLocalization.algebra`, module
  `Sheaf.RingTheory.PrincipalWLocalization`.
- `lem-pc-filtered-colimit-commrings-elementwise`: the recorded Mathlib declarations
  `CategoryTheory.Limits.Concrete.isColimit_exists_rep`,
  `CategoryTheory.Limits.Concrete.isColimit_rep_eq_iff_exists`, and
  `CommRingCat.FilteredColimits.forget_preservesFilteredColimits`, available through
  `Mathlib.Algebra.Category.Ring.FilteredColimits`.
- `def-weil-pbc-finitely-presented-algebra`: `Algebra.FinitePresentation`, module
  `Mathlib.RingTheory.FinitePresentation`.
- `def-weil-pbc-etale-contraction`: `CommRingCat.etaleContraction`, module
  `Sheaf.RingTheory.EtaleContraction`.
- `def-weil-pbc-retained-localization`: `PrincipalWLocalization.Retained.algebra`, module
  `Sheaf.RingTheory.RetainedLocalization`.

The theorem docstring carries all seven proof steps, including the counting of
representatives rather than arbitrary isomorphic copies. Read the source in
`literature/stacks-project/proetale.tex`: remarks `remark-size-w`, `remark-size-T`,
`remark-size-w-contractible`, and the first proof paragraph of
`lemma-get-w-local-algebraic-residue-field-extensions`. These agree with the statement.

Edge cases checked: the zero ring and empty spectrum remain admitted; the empty
intersection of closed-point ideals is the unit ideal in the imported definition.
Empty partitions and empty tensor products are included by the constructions.
The whole spectrum is a retained-localization index even when the retained closed
set is empty; the empty constructible subset is then also allowed. Finite rings
are covered by any infinite κ, including κ = aleph0. Equality in either cardinal
bound is included. Ring universe u and cardinal universe v are independent; the
common-universe lifts impose no additional equality or size restriction.
No counterexample, ambiguity, or STATEMENT-DISPUTED issue was found.

Searches (msearch.py, group NH, item lem-weil-pbc-strict-w-cover-size):

- LeanFinder query: "The strict w local cover of a commutative ring of cardinality
  at most an infinite cardinal kappa has cardinality at most kappa". Eight hits:
  generic ObjectProperty/MorphismProperty cardinal bounds, filtered diagram size,
  model-theory cardinality, and dynamical covering bounds; no strict w-cover theorem.
- Loogle query: "Cardinal.mk, Cardinal.aleph0". Twelve hits concerning cardinalities
  of naturals/integers, countability, and infinitude; no strict w-cover theorem.
- LeanSearch query: "Cardinality of the strict w local cover of a commutative ring
  is at most an infinite cardinal bounding the ring". Service unavailable:
  Internal Server Error; no conclusion drawn from this unavailable search.
- msearch grep query: `StrictWCover|strict.?w.*cardinal|cardinal.*strict.?w`.
  Zero Mathlib hits.
- rg in upstream WeilConjectures and project lean/Sheaf for
  `strict.w.*(size|cardinal)|[Ss]trictWCover|lem-weil-pbc-strict-w-cover-size`:
  only the project's StrictWCover definition module. Upstream has no occurrence
  of this node id. The proposed full theorem name has no upstream-name-table hit.

Validation: the server-only entry point `scompile.run_server` of scompile.py
compiled this file cleanly (nice 19, two threads, 60 seconds per file). The default
scompile.run_many currently attempts local compilation, so it was routed to
run_server in memory, including for the delivery dry run, to follow the explicit
server-only instruction. No tool files or upstream files were modified.


## Second reading by NH

Independent second reading, with the sandbox node, StrictWCoverSize.lean, the
recorded dependency nodes and their source declarations open. Verdict: exact
statement; no mathematical, signature, node, import or docstring repair needed.
Only this second-reading report was added.

The node's objects, hypotheses and conclusion, in order:

1. A commutative ring A: `(A : Type u) [CommRing A]`. Exact; there is no
   Nontrivial, field, characteristic, reducedness or Noetherian hypothesis.
2. An infinite cardinal kappa: `(κ : Cardinal.{v})` and
   `(hκ : Cardinal.aleph0 ≤ κ)`. Exact; includes the least infinite cardinal.
3. The bound |A| ≤ kappa: `(hA : Cardinal.lift.{v} (Cardinal.mk A) ≤
   Cardinal.lift.{u} κ)`. Exact comparison in the common universe max u v.
4. W = A^w: the imported `StrictWCover.algebra A` uses
   `PrincipalWLocalization.algebra A`, the recorded finite-constructible-partition
   colimit. I read Index, Stage, transition, diagram and algebra; the denominators
   and refinement relation are precisely the dependency node's, including the
   empty partition. No upstream generalization-submonoid construction is substituted.
5. I is the radical ideal defining W's closed points:
   `StrictWCover.closedIdeal A` is `PrimeSpectrum.vanishingIdeal (closedPoints ...)`.
   This is the intersection of the corresponding prime ideals, as the node requires.
6. E = W^e: `StrictWCover.contraction A` is `CommRingCat.etaleContraction` of W.
   I read Representatives, finiteDiagram, step, stage, sequence and the colimit
   inclusion. The skeleton supplies one faithfully flat etale representative per
   isomorphism class; finite tensor coproducts and the sequential colimit are the
   recorded definition, not all isomorphic copies. There is no extra input instance.
7. C_A = E_[V(IE)]: `extendedIdeal` maps I along the zeroth-stage contraction map;
   `retainedAlgebra` applies `PrincipalWLocalization.Retained.algebra` to its zero
   locus. I read its concrete selectors, Neighborhood, localizationDiagram and
   algebra: constructible supersets ordered by reverse inclusion, exactly as in
   the dependency node. `structuralMap` and `algebra` retain the specified composite
   A-algebra structure. Hence the theorem's `(algebra A)` is precisely C_A.
8. The sole conclusion |C_A| ≤ kappa: `Cardinal.lift.{v}
   (Cardinal.mk (algebra A)) ≤ Cardinal.lift.{u} κ`. Exact; no extra conjunct,
   existential replacement, changed quantifier order or weakened bound.

Source check: I read Stacks proetale.tex, remark-size-w (0976), remark-size-T
(097S), remark-size-w-contractible (0984), and the first proof paragraph of
lemma-get-w-local-algebraic-residue-field-extensions (097X). The first two size
remarks assume only a ring and an infinite cardinal bounding it. The third
explicitly bounds C, after the first three stages, by kappa. The residue-field
hypothesis on A → B in 097X serves the subsequent D construction and imposes no
hypothesis on A for these first three stages. The theorem correctly stops at C.

I checked the proof-only dependency records too: Cardinal.mk_list_le_max includes
empty lists; Algebra.FinitePresentation is the finite polynomial presentation
class; Concrete.isColimit_exists_rep and isColimit_rep_eq_iff_exists, together
with CommRingCat.FilteredColimits.forget_preservesFilteredColimits, give the
recorded elementwise filtered-colimit interface. IsWLocalRing in the group
clone is the recorded prime-spectrum notion. These proof imports introduce no
hypothesis into this theorem. There are no new nodes or dependency modules in
this delivery, and no statement_change needing a citer audit.

Edge cases: zero ring and empty spectrum remain allowed (empty partition/product
and empty intersection defining I are accounted for). Empty finite subsets give
base-ring tensor coproducts. For empty retained set, the whole spectrum still
indexes a neighbourhood and the empty constructible set is allowed. Finite rings
and kappa = aleph0, equality in either bound, and all characteristics are included.
There is no positive-degree or n > 0 restriction. Universes u and v are explicitly
bound and independent; both algebra and A have universe u and the lifts impose
no equality between u and v. No hidden instance or unbound variable was found.

Independent duplicate searches, using other wording:

- LeanFinder: "An infinite cardinal bounds the size of the ring obtained by strict
  w localization". Eight hits, principally IsLocalization.cardinalMk_le and
  lift_cardinalMk_le; none bounds this strict w-cover construction.
- Loogle: `"cardinalMk_le"`. Twelve hits including polynomial, free-algebra and
  W-type bounds; none states this construction's bound.
- LeanSearch: "The ring constructed by w localization followed by etale contraction
  has size bounded by any infinite cardinal bounding the original ring". Service
  returned Internal Server Error; recorded unavailable, not evidence of absence.
- Direct rg on Mathlib, upstream WeilConjectures and project lean/Sheaf for
  `strictwcover|w.?local.*(cardinal|size)|(?:cardinal|size).*w.?local`
  (case insensitive). Only the strict-cover definition namespace and an unrelated
  bounded-extension documentation hit in the project; no existing theorem.

H5/H6/H8/H9: this module introduces no definitions and has exactly one theorem,
whose entire proof is sorry. Both docstrings cite the source and exact blueprint
id. The declaration docstring follows all seven node proof steps, including
finite-data coding, one representative per algebra isomorphism class, empty
finite tensor products, countable iteration and the second w-localization before
retaining V(IE). Imports correspond to statement/proof dependencies; lines meet
the width convention. The lean.statement signature was checked verbatim against
the file. No mismatch or disputed mathematical assertion was found.

Compilation uses scompile.run_server, the server-only entry point of scompile.py,
with nice 19, two threads and the 60-second per-file limit. For delivery, the
in-memory run_many binding is routed to that same entry point to avoid the
script's default local-first path; no tool source is edited.

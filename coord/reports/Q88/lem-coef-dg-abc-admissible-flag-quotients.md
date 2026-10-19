## Worker report

This is the substantive repair of returned head c6b4fbf4e0f1. The retained packet was
inspected first and `deliver2.py N6 lem-coef-dg-abc-admissible-flag-quotients --no-push`
was run before editing. It passed mechanically at 2ad18be0a0, but the required self-check
confirmed the maintainer's H5, H3 and H11 findings. An unchanged re-push would preserve
those defects. The module and report are repaired; the mathematical node statement,
source, proof and proof dependencies are unchanged from the current shared node.

The delivered module is `Sheaf.CategoryTheory.DgAbcAdmissibleFlagQuotients`; its theorem
is `CategoryTheory.dg_abc_admissible_flag_quotients`, whose only local postponed proof
is `sorry`. Its docstring gives all ten proof steps of the DAG node. All definitions
have actual data or explicit predicates, with no postponed definition proofs.

The self-contained conventions introduced by this node are helpers in its owning
module, listed in `lean.declarations`. No independent definition node is introduced.
The obsolete, hollow `CochainDGCategory` has been removed. The existing declaration
`CategoryTheory.IntegralDGCategory` is imported from
`Sheaf.CategoryTheory.SemiFreeDGModule`; the already landed owning node
`lem-coef-dg-semi-free-homotopically-projective` is added to `stmt_deps` for this reuse.
Its complete dg-category signature and docstring were read. Its other definitions and
its semi-free-module theorem are not assumptions of this theorem. No theorem about
modules or triangulated categories is used in the statement.

The statement's hypotheses and conventions are rendered as follows.

- A small cochain dg category over the integers is `A : IntegralDGCategory.{u,v}`.
  Its object set is `A.Obj`; `A.hom x y` is a Mathlib
  `CochainComplex AddCommGrpCat ℤ`, so its differential is additive and has square
  zero. `A.comp p q` is bilinear, `A.d_comp` is the Leibniz equation with
  `p.negOnePow`, `A.assoc` is associativity, and `A.unit_comp`, `A.comp_unit`, and
  `A.d_unit` give closed two-sided identities. There are no free auxiliary
  `comp0`, additive operations, or degree-minus-one differentials.
- Closed degree-zero arrows, the arrows of `Z⁰ A`, are `DgClosedHom A x y`, with
  field `hom` in the actual degree-zero group and equation `closed : d hom = 0`.
- Equality in `H⁰ A` is `DgHomologyEq A f g`, namely an actual degree-minus-one
  element `h` such that the actual Hom differential sends `h` to `f - g`.
  The theorem uses it only between closed arrows or their closed composites.
- Axiom (A) is `hA : DgZeroBinarySums A`. Its `zero_to` and `zero_from` say every
  graded Hom group to or from `zero` is trivial. Its binary sums have four closed
  degree-zero structure maps and the two diagonal, two off-diagonal, and total
  biproduct equations, stated as equalities using `A.comp` and actual addition.
- Axiom (B) is `B : DgShiftData A`. `shiftObj` and additive `shiftMap` in every
  integer degree give the dg functors. `map_d`, `map_unit`, `map_comp` are their
  differential, identity and composition laws. `shift_zero`, `map_zero`,
  `shift_add`, `map_add` state the strict integer action on objects and arrows.
  `homIso` is an additive equivalence in every degree from `Hom(x,y[n])^j` to
  `Hom(x,y)^(j+n)`. `homIso_d` explicitly states the factor `n.negOnePow`, so
  the differential is `(-1)^n d`. `homIso_precomp` gives right-composition
  compatibility; `homIso_postcomp` gives left-composition compatibility with
  the Koszul factor `(n*p).negOnePow` for a shifted degree-p arrow. At degree zero
  this is ordinary naturality. `HEq` expresses only the canonical identifications
  of equal integer degrees and objects identified by the strict shift equations.
- The five equations defining admissibility are exactly `DgGradedSplitting`:
  `pi a = 1`, `b s = 1`, `a pi + s b = 1`, `b a = 0`, and `pi s = 0`.
  `DgAdmissibleSequence A a` packages a quotient object `w`, closed quotient
  arrow `b`, graded maps `pi,s`, and these five equations. Only `a,b` are required
  to be closed; no closedness is incorrectly imposed on the graded splittings.
- The boundary is the actual definition `DgBoundary A B pi s`:
  `(B.homIso 1 z x 0).symm (A.comp 0 1 pi ((A.hom z y).d 0 1 s))`.
  Thus it is precisely the degree-zero form of `pi ∂s`, not an arbitrary map.
- Admissible monomorphisms are `DgAdmissibleMono`, defined as existence of such
  a sequence. Axiom (C), `hC : DgConeAxiom A B`, quantifies over every closed
  `f : x → y` and asserts existence of `c`, closed arrows `y → c → x[1]`, graded
  `pi,s`, all five splitting equations, and the exact equation
  `DgBoundary A B pi s = B.shiftMap 1 0 f.hom`. It is a genuine proposition
  about the specified data, not a bare `Prop` field or a selected arbitrary cone.
- Homotopy equivalence is `DgHomotopyEquivalence`, existence of a closed inverse
  with the two compositions equal to identity modulo the actual boundaries.
- The given composable closed maps are `alpha : DgClosedHom A x y` and
  `beta : DgClosedHom A y z`. Their admissibility is `ha,hb`; the chosen
  sequences and graded splittings are precisely `S1,S3`. Their quotient objects
  and arrows are `S1.w,S1.b` and `S3.w,S3.b`. The chosen boundaries delta1 and
  delta3 are the expressions `DgBoundary A B S1.pi S1.s` and
  `DgBoundary A B S3.pi S3.s`, so no extra boundary binder can trivialize a clause.

Every conclusion clause has the following counterpart in Lean.

- The existential closed `gamma : x → z` satisfies
  `gamma.hom = A.comp 0 0 beta.hom alpha.hom`; hence it is the specified composite.
  `S2 : DgAdmissibleSequence A gamma` is the required admissible composite
  sequence. Its fields supply `q2 = S2.w`, `p2 = S2.b`, `pi2 = S2.pi`, `s2 = S2.s`
  and all five splitting equations.
- The prescribed composite retraction is the explicit conjunct
  `S2.pi = A.comp 0 0 S1.pi S3.pi`.
- `uMap` and `vMap` are `DgClosedHom`, not unconstrained graded maps. Their `.closed`
  fields give both required closedness assertions. The next two equalities force
  `uMap.hom = p2 beta s1` and `vMap.hom = p3 s2` exactly.
- `DgGradedSplitting A uMap.hom vMap.hom r t`, with the displayed terms
  `r = A.comp 0 0 S1.b.hom (A.comp 0 0 S3.pi S2.s)` and
  `t = A.comp 0 0 S2.b.hom S3.s`, gives all five equations for the second
  admissible sequence. In particular `v u = 0` strictly, rather than merely
  equality to zero modulo boundaries.
- The following boundary conjunct uses those same terms `r,t` in
  `DgBoundary A B r t = A.comp 0 0 (B.shiftMap 1 0 S1.b.hom)
  (DgBoundary A B S3.pi S3.s)`. This is exactly `r ∂t = p1[1] delta3` under (B).
- Delta2 is exactly `DgBoundary A B S2.pi S2.s`. Three explicit differential-zero
  conjuncts give closedness of delta1, delta2 and delta3, as asserted in the
  node's boundary convention. The fourth boundary is equal to the displayed
  composite of closed maps, so is closed as well.
- The final four `DgHomologyEq` conjuncts state, in the node's order,
  `u p1 = p2 beta`, `delta2 u = delta1`, `v p2 = p3`, and
  `delta3 v = alpha[1] delta2` in `H⁰ A`. Every delta in them is the defined
  expression; every shifted map is the degree-zero part of the given dg shift.
- No triangulated or pretriangulated structure is assumed. The conclusion is
  expressed wholly using the dg operations, the stated (A),(B),(C), and the
  chosen admissible sequences.

Edge cases and type checks: all integer shifts, including zero, negative and odd
shifts, are present; the odd-shift differential has the minus sign. Degree-minus-one
boundaries use `A.hom.d (-1) 0`, so there is no independent differential. The zero
category and trivial Hom groups are permitted. An empty object set is ruled out by
(A)'s own zero object, not by an extra nonemptiness hypothesis. No nonzero condition
is imposed on alpha or beta; identity, zero, and split sequences are covered. Objects
and Hom groups retain their independent universes `u,v`. The splittings need not be
closed. Expanding `DgGradedSplitting` verifies the two source typo corrections via
`alpha pi + s b = 1` and `S3.splitting`'s `pi3 beta = 1`. The conclusion does not
strengthen any of the four H⁰ identities to a strict equality.

Searches (repair session, in addition to the retained packet's searches):

- `msearch.py ... leanfinder` with query `differential graded category admissible
  split sequences shifts cones quotients of a composable pair of monomorphisms`:
  eight hits, on ordinary cochain-complex cones, spectral objects and abstract
  triangulated categories; no arbitrary dg-category flag theorem.
- `msearch.py ... loogle 'Dg.Cat, IntegralDGCategory, ShortComplex.Splitting'`:
  no hits, `unknown identifier 'Dg.Cat'` on the search service.
- `msearch.py ... grep 'dgCategory|DGCategory|namespace Dg|admissible.*mono'`:
  no Mathlib hits. The pinned Mathlib has Hom complexes and ordinary-complex
  splitting APIs; these do not state this theorem on a general dg category.
- `rg` in the shared `lean/Sheaf`, upstream `WeilConjectures`, DAG and recorded
  names: found the already landed `IntegralDGCategory` in `SemiFreeDGModule` and
  read its full structure rather than copying it. No `DgShiftData`, `DgBoundary`
  or general dg admissible-sequence API was found. The upstream search for the
  item id found no statement. The current node has no `blueprint_update` and
  originally had no statement dependencies; its proof-dependency list is empty.
- Read local Stacks `dga.tex`: situation-ABC, definition-dg-direct-sum,
  definition-functor-dga-categories, lemma-get-triangle, and
  lemma-dgc-analogue-tr4, including the two printed typo locations. No internet
  copy or inferred source quotation was used.

No statement correction or disputed statement is needed. The only node changes are
`lean` and the addition of the existing landed dg-category-owning node to `stmt_deps`.

## Second reading by N6

A second pass in this worker session was used, as this dispatch explicitly prohibits
starting other agents. It compared the node's complete statement, Stacks source, and
the repaired module, rather than repeating the old report's conclusions.

H5: the old category's four unconstrained proposition fields and disconnected
operations were genuine defects. They are gone; the imported `IntegralDGCategory`
has real cochain complexes and the named dg equations. Axiom (A) now has all closed
structure maps and biproduct identities. Axiom (B) now has the full dg-functor equations,
strict shift laws on objects and arrows, additive Hom isomorphisms, the signed
differential law and both composition compatibilities. Axiom (C) now asserts an actual
admissible splitting with its boundary equal to the specified shifted arrow. The
boundary is computed by `DgBoundary`, with no hidden choice or postponed data.

H3: matched every clause using the correspondence above. In particular the repaired
conclusion contains the missing `S2.pi = pi1 pi3`, the closed structures of `uMap,vMap`,
all five equations with the exact `r,t`, and the exact boundary equation. It binds no
free delta1, delta2 or delta3. All four H⁰ equations use the three defined boundaries.
The composite arrow is a closed existential fixed by its equation to beta alpha;
this avoids adding a separate postponed closed-composition theorem or assuming
closedness as an extra hypothesis. The existential package has exactly the required
objects, arrows, graded splittings and properties.

H11: the old report's statement that nothing was omitted was false. This report names
each omitted or hollow part and its repair. The added dependency reuses a landed
dg-category definition and does not assert the other node's semi-free-module result.
The node's mathematical statement has not been changed. Final signatures and the
`lean.declarations` list were checked against the actual module text.

Compilation is through the authorized `scompile.py` wrapper on the absolute sandbox
file, not through an inaccessible snapshot path or a direct `nt_compile.py` call.

## Second reading by Q88

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

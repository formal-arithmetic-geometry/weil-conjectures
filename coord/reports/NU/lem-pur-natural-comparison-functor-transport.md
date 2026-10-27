## Worker report

The module Sheaf.CategoryTheory.NaturalComparisonFunctorTransport states
CategoryTheory.Endofunctor.Algebra.naturalComparisonFunctorTransport. Its sole
proof is `sorry`. There are no new definitions, new nodes, dependency repairs,
or natural-language statement changes. The Q125 PASS on this node records the
stage-1 split, not a Lean statement review: the current base node has no lean
record. This delivery adds only that record and its statement module.

Source read: main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/
prop-pur-weil-equivariance-scheme-frobenius.proof.md, entire proof. Its comparison
is compatible with pullback composition and with f; precomposition preserves
the squares. The DAG expands this categorical compatibility into five elementary
steps, all retained in the declaration's proof-plan docstring.

Hypotheses and objects, clause by clause:

- The categories C and D are `{C : Type uC} [Category.{vC} C]` and
  `{D : Type uD} [Category.{vD} D]`, with four independently bound universes.
- The functor L is `(L : C ⥤ D)`; the four endofunctors are `(FC GC : C ⥤ C)`
  and `(FD GD : D ⥤ D)`. No exactness, faithfulness, additivity or equivalence
  assumption is made on L or these endofunctors.
- The two comparisons are `(kC : FC ≅ GC)` and `(kD : FD ≅ GD)`.
- The commutation isomorphisms are `(cF : FC ⋙ L ≅ L ⋙ FD)` and
  `(cG : GC ⋙ L ≅ L ⋙ GD)`. Lean's composition order is diagrammatic:
  FC ⋙ L denotes the paper's L composed with FC.
- The assumed square for every M is `compat : ∀ M : C,
  L.map (kC.hom.app M) ≫ cG.hom.app M = cF.hom.app M ≫ kD.hom.app (L.obj M)`.
- A strict GC-fixed pair is `(A : Algebra GC) [IsIso A.str]`. Its underlying
  object is A.a and its isomorphism is the invertible arrow A.str. This is
  exactly the dependency's specialization of Mathlib's endofunctor algebras,
  rather than a new fixed-pair notion; an IsIso proof supplies the inverse
  uniquely, with no additional data or law. No monad laws are imposed.
- The paper's u_M is written out as `kC.hom.app A.a ≫ A.str`.
  Its transported GC-structure phi^L is `cG.inv.app A.a ≫ L.map A.str`.
  Both have the exact sources and targets in the DAG.

Conclusions, clause by clause:

- The first conjunct is the equality of the structure map obtained by transport
  then change, `kD.hom.app (L.obj A.a) ≫ cG.inv.app A.a ≫ L.map A.str`,
  and the structure map obtained by change then transport,
  `cF.inv.app A.a ≫ L.map (kC.hom.app A.a ≫ A.str)`.
  Both belong to `FD.obj (L.obj A.a) ⟶ L.obj A.a`: the underlying object is
  literally the same L.obj A.a in both expressions.
- The stated inverse is written
  `L.map (inv A.str ≫ kC.inv.app A.a) ≫ cF.hom.app A.a`.
  The second conjunct says common-map followed by inverse is the identity of
  `FD.obj (L.obj A.a)`. The third says inverse followed by common-map is the
  identity of `L.obj A.a`. These two equations give invertibility with exactly
  the inverse formula of the DAG, including the order of the two inverse factors.
- The fourth conjunct quantifies over every `(B : Algebra GC)` with
  `(_hB : IsIso B.str)` and every `(h : A ⟶ B)`. Algebra.Hom supplies exactly
  `GC.map h.f ≫ B.str = A.str ≫ h.f`, the paper's intertwiner assumption.
  It concludes `a_A ≫ L.map h.f = FD.map (L.map h.f) ≫ a_B`, where a is the
  common structure map written out in full. Thus the same arrow L.map h.f is
  a morphism of the resulting fixed pairs in either order. The equality in the
  first conjunct, applied at A or B, also identifies the other expression for a.
- The final sentence about the same objects, structure maps and underlying
  morphisms is rendered by their literal common carrier L.obj A.a, the first
  equality, and the final clause using the literal arrow L.map h.f. This is an
  arrow-level statement as the DAG is, and does not replace equality by an
  unspecified natural isomorphism. Identities and compositions are inherited
  from the existing Algebra category and L; no new functor data is postulated.

Dependency declarations read and used:

- def-nagata-category: Mathlib.CategoryTheory.Category.Basic,
  CategoryTheory.Category and CategoryStruct; read the identity, composition,
  associativity fields and their full signatures/docstrings. Available through
  the module's public Algebra import.
- def-weil-endofunctor-fixed-pair-category: the recorded mathlib_match is
  Mathlib.CategoryTheory.Endofunctor.Algebra, CategoryTheory.Endofunctor.Algebra,
  specialized to IsIso A.str. Read Algebra, Algebra.Hom, their category instance,
  forget, functorOfNatTrans, functorOfNatTransEq and equivOfNatIso in full.
  The full-subcategory record in Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
  has precisely objects with a property and the ambient algebra morphisms;
  using Algebra plus IsIso and Algebra.Hom therefore supplies the same pairs
  and arrows without reimplementing the category. Its full-subcategory module
  need not be imported because the signature uses the equivalent unpacked form.

Edge cases checked before drafting: empty C makes the fixed-pair quantification
vacuous; empty D permits only L whose existence is consistent with its domain.
Identity functors/comparisons give the ordinary structure map and its inverse.
In a one-object noncommutative category, inverse of kC then phi is phi inverse
then kC inverse, exactly `inv A.str ≫ kC.inv.app A.a`; no commutativity was used.
General noninvertible h is allowed. The zero-object case requires no special
hypothesis and gives identity equations on the zero object. Unrelated object
and morphism universes for C and D remain independent.

Searches made before writing:

- msearch.py leanfinder, query: "Compatible natural isomorphisms of endofunctors
  commute with transport of invertible algebra structure maps along a functor".
  Eight hits: Algebra.isoMk, isoMk_hom_f, functorOfNatTransEq_inv_app_f and
  several Monad algebra comparison lemmas. None states the two-category transport
  equality together with its inverse and intertwiner clauses.
- msearch.py loogle, query: CategoryTheory.Endofunctor.Algebra.functorOfNatTransEq.
  Five hits, the named declaration and its projection/counit/unit lemmas; it
  changes endofunctors in a single category, not the requested compatible L.
- msearch.py grep, query: functorOfNatTransEq|mapOfNatIso|mapOfNatTrans in
  CategoryTheory/Endofunctor. Five Mathlib Algebra.lean hits, all same-category
  functorOfNatTransEq constructions (including dual coalgebras).
- msearch.py leansearch, query: "Transport of invertible endofunctor algebras
  commutes with compatible natural comparisons between endofunctors on two
  categories". Eight hits including Algebra.isoMk, functorOfNatTrans and its
  object formula, functorOfNatTransEq projection lemmas, Monad.transport and
  Functor.Monoidal.coreMonoidalTransport; no full matching statement.
- rg over lean/WeilConjectures and lean/Sheaf for the node id and the proposed
  declaration name: no hits. Conceptual transport search found the upstream
  IsoAlgebra transport API and derived comparison modules, not this statement.
  Read upstream CategoryTheory/Endofunctor/IsoAlgebra.lean: its mapOfNatIso
  results concern a single transport, exactness, forgetful compatibility and
  Grothendieck categories; no simultaneous comparison theorem. The dependency
  already provides the simpler Mathlib representation used here.

No STATEMENT-DISPUTED issue or node fault was found. Every binder is explicit;
no extra notion, arbitrary comparison, or sorry-valued definition is introduced.

## Second reading by NU

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

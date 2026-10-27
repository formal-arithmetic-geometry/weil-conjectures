## Worker report

`Sheaf.AlgebraicGeometry.StackMaximalSmoothOpen` states
`CategoryTheory.exists_maximal_smooth_open_moduliSubstack`. Its only proof is
`by sorry`. There are no new definitions or helper proof obligations. The source
statement and proof were read in `literature/stacks-project/stacks-morphisms.tex`,
`lemma-where-smooth`, Tag 0DZR, existence and clause (3), lines 7440--7482.
The node's mathematical statement, proof and proof dependencies are unchanged.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The scheme base is `{S : Scheme.{u}}`. The structural morphism of the stack is
  encoded by `(F : BasedCategory.{v, w} (Over S))`, its projection to schemes over S.
  The universe levels `u v w` are explicitly declared and unconstrained. Schemes
  and test schemes use `Scheme.{u}`, while the total category can use larger levels.
- The algebraic-stack hypotheses are exactly `(hF : IsAlgebraicModuliStack F)`.
  Reading that definition gives `IsModuliStack F`, `HasAlgebraicSpaceDiagonal F`,
  and a smooth surjective scheme atlas. Reading `IsModuliStack` gives a category
  fibred in groupoids and effective etale descent with unique gluing of arrows.
  `HasSpaceBaseChange` and `IsRepresentableByAlgebraicSpaces` use the actual
  scheme-test 2-fibre product and a projection-compatible representing equivalence.
  Thus this is an algebraic stack, not a DM stack or a set-valued presheaf.
- An open substack is `U : OpenModuliSubstack F`. Its existing definition is a full
  subcategory selected by a pullback-stable predicate, with every scheme inverse
  image represented over that scheme by an open immersion. The restriction of
  the structural morphism is precisely the inherited projection of `U.category`.
- Existence and smoothness are `∃ U, IsSmoothModuliStack U.category ∧ ...`.
  This smoothness predicate uses a smooth surjective atlas with smooth structural
  composite. No local finite presentation or flatness assumption precedes existence.
- Largest means `∀ V : OpenModuliSubstack F, IsSmoothModuliStack V.category →
  V.IsContainedIn U`. Reading `IsContainedIn` gives implication of object predicates
  for every object. This is largest, rather than merely a maximal element.
- Local finite presentation of f occurs only as the antecedent
  `∃ (P : Over S) (a : BasedFunctor (discreteModuli (yoneda.obj P)) F),
  IsSmoothModuliAtlas F P a ∧ LocallyOfFinitePresentation P.hom`.
  This is exactly the smooth-atlas test specified by the node; an atlas is not
  arbitrary data supplied as an additional hypothesis. It is the same interface
  used by the landed infinitesimal criterion and open-stack lfp theorem.
- Arbitrary flat base change is `∀ (S' : Scheme.{u}) (g : S' ⟶ S), Flat g → ...`.
  No surjectivity, faithful flatness, local finite presentation of g, finite type,
  quasi-compactness, separatedness or characteristic restriction is imposed.
- The base-changed stack f' is the existing `moduliSchemeBaseChange F g`.
  Its objects are iso-comma triples `(x,T,alpha)`; arrows are compatible pairs,
  and `x.obj.left` is the actual original F-object, not a chosen replacement.
  Its projection to `Over S'` is the structural morphism f'.
- The witness `U' : OpenModuliSubstack (moduliSchemeBaseChange F g)` satisfies
  both smoothness and the identical largest-open condition on the new stack.
- Equality `U_f' = U_f ×_S S'` is
  `∀ x, U'.property x ↔ U.property x.obj.left`.
  Both are full substacks of this particular iso-comma category. Pullback of a
  full substack selects exactly the triples whose first object belongs to U;
  the arrows remain all compatible pairs between selected triples. Thus equality
  of predicates is the stated equality of full substacks, including all arrows,
  rather than an unrelated equivalence of categories or equality just on field points.
  Scheme fibre products in the imported atlas base-change construction are the
  recorded categorical pullbacks, via `Over.pullback`.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its category
  of morphisms, with the underlying locally ringed space and affine-local property.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  the full subcategory of fppf sheaves with representable diagonal and etale
  surjective scheme atlas; its scheme-test property definitions are reused by
  the stack and atlas definitions, not copied.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`,
  used in `IsSmoothModuliStack` and `IsSmoothModuliAtlas` through the chart test.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat` on g.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation` on the structural atlas map.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, underlying the existing scheme atlas base change.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`:
  `CategoryTheory.IsAlgebraicModuliStack`, `IsSmoothModuliStack`,
  `IsSmoothModuliAtlas`, with their full signatures and docstrings read.
- `Sheaf.AlgebraicGeometry.OpenModuliSubstack`:
  `CategoryTheory.OpenModuliSubstack`, `.category`, `.IsContainedIn`.
- `Sheaf.AlgebraicGeometry.ModuliSchemeBaseChange`:
  `CategoryTheory.moduliSchemeBaseChange` and its explicit iso-comma construction.
- Proof-only import `Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus`:
  `CategoryTheory.stack_chartwise_smooth_etale_calculus` and the companion calculus
  statements, as recorded on the proof dependency. The three other proof nodes
  (`lem-sfb-invariant-open-substack-descent`, `lem-sfb-space-maximal-smooth-open`,
  `lem-sfb-space-smooth-source-point-locality`) currently have no Lean record or
  Mathlib match, so there is no module to import for them. Their proof uses are
  retained explicitly in the theorem docstring and unchanged DAG proof.
- `def-weil-size-convention` is a recorded metatheoretic convention, with no
  importable declaration. Its role is the explicit universe parameters above.

The item's `stmt_deps` gains three already landed definition nodes:
`def-sfb-algebraic-moduli-stack`, `def-sfb-open-moduli-substack`, and
`def-sfb-moduli-scheme-base-change`. These own the exact notions already introduced
inline in the item; the brief's section 5 permits adding landed definition nodes.
No dependency node is modified and no new node is introduced.

Edge cases checked before drafting:

- The existence clause permits the empty scheme, empty open, and an everywhere
  nonsmooth map. It does not require any point, nonempty atlas or nonempty locus.
- If f is smooth, largest forces U to be the whole stack. If no nonempty smooth
  open exists, the empty open is admitted.
- Neither f nor its atlas is assumed locally of finite presentation for existence.
  Without that property the implication concerning flat base change adds no assertion.
- The identity base change retains the same objects up to their explicit base
  isomorphism, and the last clause recovers the same full-substack predicate.
- Flat open immersions and the map from the empty scheme are allowed even when
  nonsurjective. Arbitrarily large flat base schemes within the fixed scheme
  universe are allowed; no local finite presentation condition is imposed on g.
- All characteristics, automorphisms in stack fibres, and independent total-category
  universes are retained. There is no hidden use of a discrete or DM fibre condition.

Searches for an existing exact statement, all on 2026-10-24:

- `msearch.py ... leanfinder "An algebraic stack over a scheme has a largest smooth
  open substack, and for locally finitely presented stacks it commutes with flat
  base change"`: eight hits about smooth scheme morphisms, their base change,
  universal openness and smooth algebra loci; no algebraic-stack statement.
- `msearch.py ... leansearch "An algebraic stack has a largest smooth open substack
  compatible with flat base change"`: eight hits about schemes or rings, including
  `Algebra.isOpen_smoothLocus` and smooth-base-change results; no matching stack theorem.
- `msearch.py ... loogle "CategoryTheory.IsSmoothModuliStack,
  CategoryTheory.OpenModuliSubstack"`: zero hits, unknown first identifier in the
  Mathlib search index. The actual project declarations were found and read locally.
- `msearch.py ... grep "AlgebraicStack|OpenSubstack|IsSmoothModuliStack"
  AlgebraicGeometry`: zero Mathlib hits.
- Direct `rg` in `lean/WeilConjectures` and `lean/Sheaf` for algebraic-stack,
  open-substack, largest/maximal smooth open, and the exact node identifier found
  the existing foundation interfaces and scheme smooth-locus theorems, but no
  theorem stating this node. The exact proposed declaration name has no existing hit
  in Mathlib or either project source tree. The upstream name index contains no match.
- Direct inspection also found `StackSmoothAtlasBaseChange`, which states stability
  of a smooth stack under arbitrary base change, but does not give a largest smooth
  open or the reverse inclusion in its flat-base-change equality. It is not a match.

No `STATEMENT-DISPUTED` issue or source correction is needed.

Validation: `scompile.py Q154 lem-sfb-stack-maximal-smooth-open <module>` compiled
both the sandbox probe (4.1 s) and the actual module (3.6 s), with no errors or
unexpected warnings. The recorded Lean signature is extracted verbatim from the file.

## Second reading by Q154

This section records a separate self-check pass with the node, source and final
module open. The dispatcher explicitly forbids starting other agents; an independent
maintainer review remains the separate reader for this delivery.

The pass checked the three conjunction levels: existence and largestness occur before
the finite-presentation implication; local finite presentation is on f via its smooth
atlas, while flatness is on g; the base-changed witness has both smoothness and
largestness before its predicate equality is asserted. In particular, no locally
finitely presented atlas was assumed for unconditional existence, and no lfp or
surjectivity condition on g was accidentally introduced. Reading the base-change
definition confirmed that `x.obj.left` is the original stack object, whereas
`x.obj.right` is the new test scheme. Reading the open-substack definition confirmed
that predicate equality identifies the full substacks, not only their objects up to
some unrelated equivalence. The source's other two clauses are not part of this node
and were not added. No mismatch was found in this pass and no statement was changed.

## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicStackSetoidSpace` states
`CategoryTheory.algebraicStack_setoid_space`, with its sole proof `sorry`.
It introduces no definitions. The source read was `literature/stacks-project/algebraic.tex`,
Tag 04SZ, `proposition-algebraic-stack-no-automorphisms`, implication (1) to (3),
including the proof; the algebraic-stack definition preceding it (Tag 026O) was also read.
The natural-language statement and proof are unchanged. The node gains three already-landed
statement dependencies that own predicates needed by its existing statement:
`def-sfb-fppf-stackification`, `def-sfb-algebraic-moduli-stack`, and
`def-sfb-surjective-moduli-map`. Their dependency closures were checked;
none reaches this item, so these edges create no cycle.

Hypotheses and conclusions, clause by clause:

- The scheme S is `{S : Scheme.{u}}`. The test category is `Over S`, the actual category
  of S-schemes, with Scheme object universe u+1 and morphism universe u. The total category
  is `W : BasedCategory.{v, w} (Over S)`; v and w are independently explicit universes.
  The size-convention node is metatheoretic and is rendered by these universe binders.
- A category fibred in groupoids and an fppf stack with isomorphism sheaves and effective
  object descent is `hstack : IsFppfModuliStack W`. Its existing definition includes
  `IsFibredInGroupoids W` and colimiting descent cocones on every covering sieve for
  `Scheme.fppfTopology.over S`; it uses the same total-category conventions as the node's
  recorded moduli-groupoid dependency. No new descent encoding is introduced.
- Representability of the diagonal by algebraic spaces is
  `hdiag : HasAlgebraicSpaceDiagonal W`. This tests fibre products of two scheme maps
  and gives an algebraic space with an equivalence to their actual 2-fibre product.
- The scheme atlas and its map are existentially bound in `hatlas` as `(U : Over S)`
  and `a : BasedFunctor (discreteModuli (yoneda.obj U)) W`.
- Representability and smoothness of that particular atlas are the first conjunct of
  `hatlas`: for every scheme T and map t to W, there exist Z and its actual projection p
  with `HasSpaceBaseChange a T t Z p ∧ SpaceMapIsSmooth Z T p`. The former includes an
  equivalence to the actual 2-base change, with the comparison of the projection over T.
  The latter tests `Smooth` on every representable étale scheme chart of Z. Thus neither
  an arbitrary projection nor smoothness of an unrelated chart is substituted.
- Surjectivity in the field-extension meaning is the second conjunct
  `IsSurjectiveModuliMap a`. Its recorded definition quantifies over K : Type u, Field K,
  Spec K → S, and its target object; it supplies L : Type u, Field L, a unital map
  K →+* L (automatically injective), a source object over Spec L, and the actual vertical
  2-isomorphism to the restriction of the original object. The field universes are the
  scheme universe u, rather than an independent potentially smaller universe.
- The setoid-fibre hypothesis is precisely
  `hsetoid : ∀ (T : Over S) (x y : Functor.Fiber W.p T), Subsingleton (x ⟶ y)`.
  This imposes at most one vertical arrow between each pair, not equality of objects,
  existence of an arrow, or thinness of the entire total category.
- The conclusion is `∃ (E : AlgebraicSpace S) (e : BasedFunctor W
  (discreteModuli E.obj.obj)), e.toFunctor.IsEquivalence`. The presheaf `E.obj.obj` is the
  underlying functor of the fppf sheaf E. Its `discreteModuli` total category has fibre
  E(T), expressed by Yoneda maps h_T → E, with only identity fibre arrows. The based
  functor enforces compatibility with Sch/S, and its underlying IsEquivalence gives
  the required equivalence in the displayed direction W → h_E. This is an existential
  theorem, not an object chosen from an unspecified existence proof.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage` and `Scheme.fppfTopology`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.Algebra.Field.Defs`: `Field`, the mathlib_match of the field node, which
  correctly has no lean record because it is a Mathlib leaf.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`: `IsFibredInGroupoids`,
  `ModuliTwoIso`, `discreteModuli`, `moduliTwoFiberProduct`, `HasSpaceBaseChange`,
  `HasAlgebraicSpaceDiagonal`, and the étale-stack convention `IsModuliStack` used
  by the proof plan. The full signatures and docstrings in its generic CFG section
  were read, including projection compatibility in `HasSpaceBaseChange`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace` and its
  `IsAlgebraicSpace`, `IsRepresentableWith`, and `IsEtale` predicates.
- `Sheaf.CategoryTheory.SiteStackification`: `IsFppfModuliStack`, read in full.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`: `SpaceMapIsSmooth` and the
  `IsAlgebraicModuliStack` proof-plan predicate, read in full.
- `Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus`:
  `IsSurjectiveModuliMap`, read in full and owned by the live definition node
  `def-sfb-surjective-moduli-map` (Q87, existing:true). This is a plain definition,
  independent of the theorem conclusions in its source module. The statement has
  no dependency on the chartwise-calculus theorem node.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale` is a proof import for the recorded
  étale-cover-to-fppf-cover step. The original proof dependency
  `lem-sfb-algebraic-setoid-space` has no Lean record on the read base, so there is
  no module to import for it yet. It is not needed to elaborate this statement;
  its future proof is still explicitly named in the docstring and DAG proof plan.

Edge cases checked before drafting: arbitrary (including nonreduced) test schemes
remain quantified; empty Hom sets satisfy Subsingleton, so arrows between distinct
nonisomorphic objects are not forced to exist; several isomorphic objects are allowed,
so the fibres need not be skeletal. The empty algebraic space and the empty base are
not excluded: no Nonempty, nonempty-atlas, Noetherian, separated, reduced, finite-type,
or characteristic restriction is imposed. Descent includes the empty covering where
applicable and retains its object-descent condition over the empty scheme. The identity
of every object still exists, so the setoid assumption implies trivial automorphisms
on every test scheme, not only on geometric points. The equivalence conclusion retains
objects and arrows naturally over the base, rather than merely their pointwise classes.

Searches actually run using `msearch.py Q23 lem-sfb-algebraic-stack-setoid-space`:

- leanfinder, `An algebraic stack with setoid fibres is an algebraic space`: eight hits
  on schemes, sheafed spaces, affine schemes and gluing; no algebraic-stack result.
- leansearch, `An algebraic stack with no nontrivial automorphisms is an algebraic space`:
  eight hits on affine schemes, formally unramified morphisms, empty spaces and étale
  base change; no matching theorem.
- loogle, `"IsStack", "IsPrestack"`: two hits, the generic pseudofunctor stack-to-prestack
  implications; neither is algebraic-space representability of a setoid stack.
- grep, `AlgebraicStack|algebraic.stack|setoid.*stack|stack.*setoid`: zero Mathlib hits.
- Local rg on `lean/WeilConjectures` for the item id: no hits; concept searches in that
  tree and `lean/Sheaf` found the listed CFG, fppf-stack, smoothness and field-lifting
  interfaces, but no theorem with this conclusion. Broader setoid/trivial-automorphism
  searches found torsor isomorphism-class setoids and unrelated fibre statements.
  The chosen declaration name is new. No missing notion needed a new definition node.

The example CompactObject module requested by the brief is now a withdrawn module
with no declarations; the current module follows the header and declaration conventions
of the actual dependency modules instead. No mathematical node fault or statement
correction was needed.

Validation: the initial module compiled cleanly using scompile.py, both as the isolated
sandbox file and under its library module name. The final explicit dependency imports
are checked again by the required deliver2.py dry run. Only the expected theorem proof
is postponed, and the source-based three-step proof is in its docstring.

## Repair of returned delivery eb2c35d302c5

H2 repaired: refreshed the item node from current main, retained the returned Lean
record and existing added definition dependencies, and replaced exactly the
`lem-sfb-stack-chartwise-smooth-etale-calculus` statement-dependency edge with
`def-sfb-surjective-moduli-map`. Read the live definition node and its recorded
`CategoryTheory.IsSurjectiveModuliMap` declaration at
`Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus`, including its full
signature and field-extension lifting definition. The new node records the same
plain definition with existing:true; no theorem or choice operation supplies it.
Updated lean.note to explain the repair. The mathematical statement, proof plan,
and all Lean bytes are unchanged from the returned sandbox version.

H9 advisory acknowledged: the plain Morphisms.Etale import is retained as a proof
import for def-weil-etale-morphism, a recorded proof dependency. The return
explicitly requires the Lean file to remain byte-identical. It adds no statement
hypothesis or conclusion. No independent second reading is claimed; the maintainer
reviews the repaired immutable delivery.

## Second reading by Q23

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

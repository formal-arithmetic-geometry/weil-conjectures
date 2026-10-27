## Worker report

The module `Sheaf.AlgebraicGeometry.StackFibreProductSeparatedComparison` states the node
in two theorem declarations: `CategoryTheory.stack_fibreProduct_separated_comparison` and
`CategoryTheory.stack_fibreProduct_separated_comparison_overIntegers`. Their proofs are
`sorry`. Three explicit construction helpers belong to this same comparison notion:
`moduliFibreProductComparison`, `moduliFibreProductPair`, and
`moduliFibreProductDiagonalComparison`. All definition data are actual functors.

Clause-by-clause correspondence:

- The base scheme is `{S : Scheme.{u}}`. All six object and morphism universes of the
  three total categories are explicit and independent (`v₁,w₁,v₂,w₂,v₃,w₃`). The generic
  construction helpers additionally allow an intermediate target in `v₄,w₄`.
- The stacks X,Y,Z are `F,G,H : BasedCategory (Over S)` and the three hypotheses
  `hF,hG,hH : IsDeligneMumfordModuliStack ...` are exactly the three DM assumptions.
  The maps a,b are `BasedFunctor F H` and `BasedFunctor G H`, hence functors over S.
- P is the recorded `moduliTwoFiberProduct a b`, retaining objects, isomorphisms and
  all compatible arrows. R is `moduliTwoFiberProduct (a.comp (moduliBaseStructure H))
  (b.comp (moduliBaseStructure H))`. Here the represented base is the existing
  `BasedCategory.ofFunctor (𝟭 (Over S))`, as specified by the structural-map node.
- The top map j is `moduliFibreProductComparison a b (moduliBaseStructure H)`.
  It retains x,y and applies the structure functor to their specified isomorphism;
  this forgets that isomorphism in H, retaining only its identity-base comparison.
- The bottom map is `moduliRelativeDiagonal (moduliBaseStructure H)`. The right map
  is `moduliFibreProductPair a b (moduliBaseStructure H)`, applying a,b to the two
  factors. The left map is a on the first projection. The comparison into the
  2-pullback is `moduliFibreProductDiagonalComparison`; its structural isomorphism
  has components `(id,φ)`, where φ is exactly the isomorphism of the original P-object.
  Thus its first conjunct `.toFunctor.IsEquivalence` states that this specified
  square is 2-cartesian, including the asserted commutativity 2-isomorphism.
- The second conjunct `IsRepresentableByAlgebraicSpaces j` states representability
  for every scheme base change using the recorded algebraic-space presentations.
- The last implication has hypothesis `ModuliSchemeTest @IsClosedImmersion
  (moduliRelativeDiagonal (moduliRelativeDiagonal (moduliBaseStructure H)))`.
  This is separatedness of the bottom diagonal, itself representable by spaces.
  Its conclusion is the same closed-immersion scheme-test predicate on
  `moduliRelativeDiagonal j`. For a representable map f, this means precisely that
  for every scheme T mapping to its target, the space E_T has closed-immersion
  diagonal over T: testing Δ_f by a scheme U into F×_G F is the same as testing
  Δ_(E_T/T) by U after the scheme projection T. Conversely those tests cover every
  scheme test of Δ_f. The closed-immersion test includes the representing scheme
  and its actual projection, rather than an arbitrary map or chart-local separated
  atlas. In particular we do not test separatedness only on source charts of f.
- The absolute theorem repeats all three assertions after
  `moduliChangeBaseMap (specULiftZIsTerminal.from S)` on a,b and
  `moduliChangeBase` on H. It assumes closed-immersion tests for the relative
  diagonal of the recorded `moduliDiagonalOverIntegers H`; it never infers absolute
  separatedness from relative separatedness. `Spec (ULift.{u} ℤ)` is the integer
  spectrum at universe u, without a size restriction on S. Its source P is the
  fibre product of the underlying stacks over the underlying H, canonically
  identified with underlying P by the recorded change-of-base theorem. Its R
  is the product over the integer spectrum, not the product over S.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `def-weil-size-convention` is a metatheoretic convention; explicit universe
  parameters implement it without introducing a replacement definition.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`: `BasedCategory` interface,
  `moduliTwoFiberProduct`, `moduliTwoFiberFst`, `IsDeligneMumfordModuliStack`,
  `HasSpaceBaseChange` and `IsRepresentableByAlgebraicSpaces`. The full definitions
  of fibres, descent, diagonal representability and the atlas predicate were read.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace` and
  `AlgebraicSpace.IsRepresentableWith`, including its actual pullback-square test.
- `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`: `moduliRelativeDiagonal`
  and `ModuliSchemeTest`, including the projection comparison through
  `IsSchemeModuliBaseChange` from `ModuliChartNormalization`.
- `Sheaf.AlgebraicGeometry.RelativeModuliInertia`: `moduliBaseStructure`.
- `Sheaf.AlgebraicGeometry.AlgebraicStackChangeBaseToIntegers`: `moduliChangeBase`,
  `moduliChangeBaseMap`, and `moduliDiagonalOverIntegers`, with the absolute product
  `moduliProductOverIntegers`. These existing declarations are recorded on the new definition node
  `def-sfb-algebraic-stack-change-base-to-integers`.
- The same module also supplies `algebraicStack_changeBase_toIntegers`, used only in
  the proof and retained in the original proof_deps. The module is publicly imported
  because its existing definitions occur in the statement.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack` is a plain proof import: the
  absolute proof first views DM stacks as algebraic stacks. The other two proof
  dependencies, `lem-sfb-groupoid-diagonal-two-pullback-identities` and
  `lem-sfb-fibred-groupoid-representable-smooth-calculus`, have no recorded Lean
  declarations in the read repository; their future proof imports are omitted.

The already-landed nodes `def-sfb-dm-stack-morphism-properties`,
`def-sfb-relative-moduli-inertia` are added to `stmt_deps` for their existing
constructions. The new definition node
`def-sfb-algebraic-stack-change-base-to-integers` replaces the rejected theorem-node
addition. The natural-language statement, theorem signatures and proof fields are unchanged.
There are no statement corrections or disputed assertions.

Sources checked directly: `literature/stacks-project/stacks-morphisms.tex`,
lemma-fibre-product-after-map (050H), especially its displayed square and (1),(3);
`categories.tex`, lemma-fibre-product-after-map; the recorded change-of-base interface
and its full proof docstring for Tags 04X5--04X6. The source's extra local finite type
conclusion is deliberately not added: the node asks only the stated three assertions.

Edge cases checked before and during formulation: empty stacks and empty test schemes
are allowed without Nonempty hypotheses; a,b and the base may be identities; for schemes
this is the usual diagonal base-change square. For maps Spec k→BG the comparison keeps
G-valued automorphisms and is not incorrectly asserted to be a monomorphism. A possibly
non-separated base S is permitted. Absolute hypotheses concern the absolute diagonal
independently of the relative one. No equality of the category universes or scheme
universes beyond the fixed scheme universe is imposed.

Existing-declaration searches (the msearch wrapper records these in searches.jsonl):

- LeanFinder: “The comparison between two fibre products of Deligne Mumford stacks is
  the base change of the diagonal and is representable and separated if the diagonal
  is separated”. Eight hits: scheme separatedness/base-change and diagonal lemmas,
  with no statement about these fibred groupoids.
- Loogle: `CategoryTheory.Limits.pullback_map_diagonal_isPullback,
  AlgebraicGeometry.IsSeparated`. Zero hits for this combined query.
- msearch grep, Mathlib CategoryTheory:
  `IsDeligneMumford|Moduli.*Separated|TwoCartesian|TwoPullback`. Zero hits.
- LeanSearch: “The natural map from the fiber product of algebraic stacks over Z to
  their product over S is separated if the diagonal of Z over S is separated”.
  Eight hits concern scheme separatedness and an unrelated topological diagonal.
- Direct rg in `lean/WeilConjectures` for the node ID: no declaration. The same
  search and searches for comparison, relative diagonal, separatedness, two-cartesian
  and two-pullback in `lean/Sheaf` found the recorded relative diagonal, structural
  map, scheme tests and algebraic-space separated predicate, but no comparison theorem.
  Algebraic-space `MapIsSeparated` has the same closed-immersion test on its presheaf
  diagonal; it does not itself state the present stack comparison.
- Direct rg in Mathlib inspected `BasedFunctor`, `Functor.IsHomLift`, comma
  isomorphisms and full-subcategory isomorphisms; these existing constructors give
  the actual maps without any new geometric notion.

Validation uses only `scompile.py`, then `deliver2.py --no-push`, then delivery.


## Returned delivery repairs

The first return (head `2d55030f84d6`, H2) required a definition node for the plain
change-of-base definitions, replacing the added theorem node in stmt_deps. The second
return (head `16386997a7be`) flagged all seven helper names in the extracted module as
already declared by `AlgebraicStackChangeBaseToIntegers`, and instructed importing and
reusing the existing declarations.

This repair follows that instruction literally. The new definition node uses
`existing: true` and records the seven existing helpers in
`Sheaf.AlgebraicGeometry.AlgebraicStackChangeBaseToIntegers`. There is no new helper
module, no renamed declaration, and no replacement of the theorem module or its node.
The previously proposed `ModuliChangeBase.lean` and theorem-module replacement files
are removed from the sandbox packet. The comparison publicly imports the existing
module and uses the original names. Its stmt_deps cites the new definition node;
the theorem stays in the original proof_deps, not in stmt_deps. Both comparison
theorem signatures and their three construction helpers retain their original text.

The current read source contains the seven definitions in the original theorem module;
the current item still has no Lean record and its original five stmt_deps. The repair
therefore adds only the two accepted relative-definition dependencies and the new
existing-declaration definition node. It does not depend on the unlanded extraction.

## New nodes

`def-sfb-algebraic-stack-change-base-to-integers` records existing construction A of
Stacks 04X5--04X6 (algebraic.tex definition-viewed-as, stacks.tex section-localize),
and the absolute product/diagonal used in Tag 050L (stacks-morphisms.tex
lemma-separated-over-separated (5)--(8)). Its Lean record is existing:true, points to
`AlgebraicStackChangeBaseToIntegers`, and supplies no file and no new declarations.
No existing definition node records this notion; the existing theorem node asserts
algebraicity, equivalence and qcqs properties, which are not its definition.

Each clause uses the existing declaration: `moduliChangeBase` composes the original
projection with `Over.map g`; `moduliChangeBaseMap` retains the underlying functor;
`moduliChangeBaseProjection` is the original S-projection;
`moduliChangeBaseScheme` applies `Over.map` to scheme arrows;
`moduliChangeBasePairHom` is the full subcategory satisfying the equality of S-projections;
`moduliProductOverIntegers` is the recorded two-fibre-product of changed structural
projections to the identity category over Spec Z; `moduliDiagonalOverIntegers` is the
recorded relative diagonal of that structural projection. Their universes and hypotheses
are those of the existing signatures, without algebraicity or separation assumptions.
Identity maps, empty schemes and categories, and a non-separated S are all permitted.
The absolute product is over Spec Z rather than over S.

Searches from the actual retained wrapper log: LeanSearch on changing the base of a
fibred category by composing the projection returned eight hits including
`Grothendieck.base` and `BasedFunctor.w`; no exact packaged construction. Loogle
`CategoryTheory.Over.map` returned twelve slice-functor hits. Mathlib grep
`moduliChangeBase|moduliProductOverIntegers|moduliDiagonalOverIntegers` returned zero.
Direct rg in WeilConjectures found none; rg in Sheaf found the seven existing helpers
in the original theorem module. DAG search found that theorem node and no definition
node. These existing definitions are reused, not recreated. The node's search records
retain the actual queries, dates and results, with the reuse decision in their verdicts.
The inherited created.item chain terminates outside the DAG; blueprint_refs.py ancestor
returns None, which the new node records while naming the genuine supporting blueprint
paragraph in its place field.

## Repair self-check by Q48

Both comparison theorem signatures, including all DM hypotheses and the independent
absolute separatedness implication, remain unchanged from the mathematically accepted
packet. The only delivered Lean module is the comparison module, which imports the
existing definitions and declares none of the seven returned names. The definition-node
record's signature is verbatim from the existing source. The theorem dependency has no
delivered replacement module or node. Validation uses scompile.py on the comparison,
then deliver2.py --no-push, which also checks every existing helper declaration, followed
by delivery. The maintainer performs the independent review.

## Second reading by Q48

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

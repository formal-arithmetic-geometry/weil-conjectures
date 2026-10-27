## Worker report

The delivery states `CategoryTheory.stack_inertia_separated_diagonal` in
`Sheaf.AlgebraicGeometry.StackInertiaSeparatedDiagonal`. Its single proof is `sorry`.
The original mathematical statement, proof plan, and proof dependencies are unchanged.
The statement dependencies gain the existing nodes owning the constructions used and
one definition node for separated representable stack maps.

Hypothesis and clause correspondence:

- A scheme S is `{S : Scheme.{u}}`. The explicit universes `u v w` retain arbitrary
  scheme size and total-category object and morphism sizes; `autoImplicit` is false.
- A stack X over S is `F : BasedCategory.{v, w} (Over S)`, with
  `hF : IsDeligneMumfordModuliStack F`. That predicate includes fibred groupoids,
  etale stack descent, algebraic-space diagonal, and a surjective etale scheme atlas.
  No finite type, quasi-compactness, separatedness of S, or chosen atlas is assumed.
- The objects (x,alpha), their verticality, and commuting arrows are precisely
  `ModuliInertiaObject F` and `moduliInertiaCategory F`, already defined in
  `Sheaf.AlgebraicGeometry.ModuliInertia`. The map p is `moduliInertiaProjection F`.
- The map e is the real-data helper `moduliInertiaNeutral F`. It composes the existing
  `relativeModuliInertiaNeutral (moduliBaseStructure F)` with the canonical inclusion
  `relativeModuliInertiaToAbsolute (moduliBaseStructure F)`. Unfolding sends x to
  (x,Iso.refl x), and an arrow to itself; no equivalence or object is chosen.
- The relative diagonal is the existing
  `moduliRelativeDiagonal (moduliBaseStructure F)`. The target is the existing
  2-fibre product of F with itself over the represented base, and the functor sends
  x to (x,x,id), as required.
- Separatedness of a representable stack map is
  `IsSeparatedRepresentableModuliMap`. It quantifies over EVERY `T : Over S` and
  `t : BasedFunctor (discreteModuli (yoneda.obj T)) G`; its existential Z,p satisfies
  `HasSpaceBaseChange f T t Z p` and `AlgebraicSpace.IsSeparatedPresheafMap p`.
  `HasSpaceBaseChange` pins the projection by an equivalence and a 2-isomorphism over
  T. The reused presheaf predicate says its actual diagonal is representable by
  scheme closed immersions. Representability of the map is included in the predicate,
  rather than assumed as extra data.
- The first two conjuncts are `p separated ↔ relative diagonal separated` and
  `p separated ↔ ModuliSchemeTest @IsClosedImmersion e`. The latter predicate tests
  every scheme base change of e and requires an actual representing scheme and its
  closed-immersion projection. These are the three equivalent conditions in the node.
- The absolute diagonal is written inline as `moduliRelativeDiagonal` of
  `moduliBaseStructure (BasedCategory.ofFunctor
  (F.p ⋙ Over.map (AlgebraicGeometry.specULiftZIsTerminal.from S)))`.
  This uses the same total category over `Spec (.of (ULift.{u} ℤ))`, with only
  the projection changed by composition with `Over.map`.
  Thus Spec Z has the scheme universe u; no universe equality or base separation
  is imposed. The third conjunct is exactly the final assertion
  `p over S separated ↔ absolute diagonal separated`.
- The fourth and fifth conjuncts explicitly give the three equivalent conditions
  for the underlying stack over Spec Z: its canonical inertia projection is separated
  iff its absolute diagonal is separated, and iff its canonical neutral section is
  a closed immersion. These expand the node's sentence that the same criterion holds
  also for the underlying stack, rather than leaving that sentence implicit.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `def-weil-size-convention`: metatheoretic only; explicit Lean universe binders.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`: `IsDeligneMumfordModuliStack`,
  `discreteModuli`, `moduliTwoFiberProduct`, `HasSpaceBaseChange`, `ModuliTwoIso`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace` and
  `AlgebraicSpace.IsRepresentableWith`, used through the existing predicates.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Sheaf.AlgebraicGeometry.ModuliInertia`: `moduliInertia`, `moduliInertiaProjection`
  and the inertia object/category definitions.
- `Sheaf.AlgebraicGeometry.RelativeModuliInertia`: `moduliBaseStructure`,
  `relativeModuliInertiaNeutral`, `relativeModuliInertiaToAbsolute`.
- `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`: `ModuliSchemeTest`,
  `moduliRelativeDiagonal`.
- `Mathlib.AlgebraicGeometry.Limits`: `AlgebraicGeometry.specULiftZIsTerminal`.
  The canonical total category over the integers is written using Mathlib's
  `BasedCategory.ofFunctor` and `Over.map`, and the absolute diagonal uses the
  already-cited `moduliRelativeDiagonal` and `moduliBaseStructure`.
- `Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal`:
  `AlgebraicGeometry.AlgebraicSpace.IsSeparatedPresheafMap` and its canonical diagonal,
  owned by `def-sfb-presheaf-map-separated-diagonal`, are reused unchanged.
- Plain proof imports: `Sheaf.AlgebraicGeometry.RelativeInertiaSecondDiagonalGeometry`
  (`relative_inertia_second_diagonal_geometry`, `relative_moduli_inertia_absolute`)
  and `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`
  (`AlgebraicSpace.fibreProduct_isAlgebraicSpace`, etale-cover/base-change clauses).
  The proof dependency `lem-sfb-fibred-groupoid-representable-smooth-calculus`
  has no Lean record or Mathlib match, so there is no module to import for it.

Edge cases checked before writing: the empty stack has empty inertia and its neutral
section and diagonal meet the closed-immersion tests. For a scheme regarded as a stack,
vertical automorphisms are identities, so the inertia projection and section are
identities; the diagonal of a scheme morphism is separated even when that morphism
or S is not separated. For BG the identity-locus and difference-map arguments use
actual automorphisms and conjugation, and do not assume G commutative. Scheme tests
include nonreduced schemes, so the criterion retains closed subscheme structure,
not just equality on geometric points. No finiteness or characteristic is imposed.

Sources opened: `literature/stacks-project/stacks-morphisms.tex`,
`lemma-diagonal-diagonal` (Tag 0CL0), the preceding second-diagonal identification,
its proof of (1), and `lemma-inertia` (Tag 050Q). They give exactly the three conditions.
The full five-step accepted DAG proof is carried into the theorem docstring.
No mathematical correction or STATEMENT-DISPUTED issue was found.

Searches made:

- `msearch.py ... leanfinder` with "The inertia projection of a Deligne Mumford stack
  is separated if and only if its diagonal is separated if and only if its neutral
  section is a closed immersion": eight scheme-separatedness results, including
  `AlgebraicGeometry.isSeparated_iff`, none about stack inertia.
- `msearch.py ... loogle` with
  `CategoryTheory.moduliInertia, AlgebraicGeometry.IsSeparated`: zero hits, unknown
  first identifier in the Mathlib search index.
- `msearch.py ... grep 'inertia|Inertia' CategoryTheory`: zero Mathlib hits.
- `msearch.py ... leansearch` with "separated representable morphism of stacks
  algebraic spaces closed diagonal": eight scheme/topology results, no stack map.
- `msearch.py ... leanfinder` with "Representable morphism of categories fibred in
  groupoids separated on every algebraic space scheme base change": eight scheme
  representability/separation results, no matching stack predicate.
- `msearch.py ... grep 'MapIsSeparated|SeparatedModuli|ModuliInertiaNeutral'`: zero hits.
- `rg` on `lean/WeilConjectures` for this item ID: no hit. Searches on inertia and
  separatedness found Galois/ramification material, no matching stack theorem.
- `rg` on `lean/Sheaf` found the existing inertia, relative inertia, scheme-test,
  and absolute diagonal constructions; these are used. It found presheaf separatedness
  and algebraic-space `MapIsSeparated`, but no predicate for separated representable
  maps of fibred groupoids and no theorem matching the item.
- DAG definition-node searches found the existing presheaf-diagonal node and
  algebraic-space morphism-properties node, not a stack-map separatedness definition.
  `blueprint_refs.py search 'separated inertia'` and
  `blueprint_refs.py search 'separated representable'`: zero blueprint matches.
  `blueprint_refs.py ancestor` reports the item's nearest blueprint ancestor is null,
  which is retained in the new node's provenance.

## New nodes

`def-sfb-separated-representable-moduli-map` defines the missing stack-map wrapper
`CategoryTheory.IsSeparatedRepresentableModuliMap` in its own module. Its source is
Stacks 0CL0(1), with algebraic-space separatedness from 03HL. For every scheme test
it requires an algebraic-space presentation with the actual projection and uses the
already-defined `IsSeparatedPresheafMap` on that projection. It does not redefine
presheaf or algebraic-space separatedness, impose a stack hypothesis, choose an atlas,
or replace a canonical map by an arbitrary map. The search results are recorded in
`mathlib_searches` of the new node. The item directly cites the new node.

## Second reading by Q05

A fresh in-thread reading compared the original node, both complete Lean files,
and the imported definitions; no independent worker was started, as the dispatcher
explicitly prohibits starting other agents. The maintainer's independent review remains
part of delivery. The clause check found that a relative triple plus the final
cross-base equivalence would leave "this holds also for the underlying stack" implicit.
The theorem was expanded to give both absolute equivalences explicitly. The neutral
section was checked by unfolding the two existing relative functors: it has identity
automorphism and the same underlying arrow. The separated predicate was checked against
`HasSpaceBaseChange` and `IsSeparatedPresheafMap`, and the closed-immersion predicate
against `IsSchemeModuliBaseChange`: all retain their actual scheme projections.
There are no new theorem hypotheses, universe restrictions, hollow definitions,
private notations, file-local instances, or assertions of scheme representability for
arbitrary algebraic-space base changes. Every helper has the owning node's source and
blueprint docstring. The only postponed theorem is the item's theorem.

Validation: `scompile.py Q05 lem-sfb-stack-inertia-separated-diagonal` compiled BOTH
modules separately in dependency order against the live published build. The final
expanded theorem compiled in 3.3 seconds; the definition module compiled in 14.7 seconds.
No errors or unexpected warnings were reported. All Lean lines are at most 100 characters.
The item copy differs only in `lean` and the authorized added `stmt_deps`; both recorded
signatures occur verbatim in their files. The helper and new definition contain real data;
there is exactly one `sorry`, in the item's theorem.


## Returned delivery repair

H2 on returned head `e6dad2685873`: removed
`lem-sfb-algebraic-stack-change-base-to-integers` from `stmt_deps` and removed its
module import. The final three conjuncts now spell out the canonical change of
projection as `BasedCategory.ofFunctor (F.p ⋙ Over.map
(AlgebraicGeometry.specULiftZIsTerminal.from S))`; each absolute diagonal is the
existing `moduliRelativeDiagonal` of the existing `moduliBaseStructure` on that
category. This is the reviewer's explicitly authorized inline alternative.
The change is definitionally the former expression, not a new hypothesis, conclusion,
or construction. The five conjuncts, all universe parameters, and the Spec(ULift Z)
base are retained. The theorem node is no longer used for any plain definition.
`Mathlib.AlgebraicGeometry.Limits` directly supplies the canonical terminal integer
spectrum formerly imported through that module. The neutral-section helper remains
real data in the owning theorem module, as permitted by the original brief; moving it
was advisory, and its canonical construction and node ownership have not changed.

Repair second reading: compared the returned signature with the repaired one and
unfolded the former `moduliChangeBase` and `moduliDiagonalOverIntegers` definitions.
The new terms are exactly their bodies, with the structural functor given by
`moduliBaseStructure`. No semantic statement change is needed. Compared with the
current read-only main node: only `lean` and authorized definition-node additions to
`stmt_deps` change. The original statement and accepted five-step proof are preserved.
The wrapper will create the repaired delivery on the current server base.

Repair validation: `scompile.py` compiled both delivered modules separately and returned
exit code 0, with no compiler errors or unexpected warnings. The repaired item signature
is verbatim in its node record. A source comparison against current main again found
only `lean` and the authorized `stmt_deps` additions changed on the existing item.

## Worker report

This is a stage-2 statement delivery repairing the return of immutable head
e1fc7593ee40. The retained packet was inspected before editing. The live node
still has no Lean record; no already-landed statement is being redelivered.

The main module is
`Sheaf.AlgebraicGeometry.StackProperLocallyQuasiFiniteComposition`. It contains five
named theorem statements, all with `by sorry`. They realize the clauses of the one
item, and every name is listed in its `lean.declarations`. No theorem was proved.
The item's natural-language statement, proof, proof dependencies and status are
unchanged. Its statement dependencies gain the new definition node below and the
four landed definition nodes used by the repaired ordinary-space interface.

Clause-by-clause correspondence:

- The base scheme S is `{S : Scheme.{u}}`. Three arbitrary DM stacks over S are
  `A`, `B`, `C : BasedCategory (Over S)`, with independent explicitly bound object
  and arrow universes. `hA`, `hB`, `hC` use the recorded
  `CategoryTheory.IsDeligneMumfordModuliStack`. The maps are `BasedFunctor A B`
  and `BasedFunctor B C`. They are not assumed representable.
- The two properness hypotheses are `hf : IsProperModuliMap f` and
  `hg : IsProperModuliMap g`. The two local-quasi-finiteness hypotheses are
  `hfq` and `hgq`. The conclusion of `proper_locallyQuasiFinite_moduli_comp`
  is the conjunction of these same properties for `f.comp g`, whose underlying
  functor is f followed by g, hence the mathematical composite g o f.
- For every algebraic-space map `f : E ⟶ F`,
  `proper_locallyQuasiFinite_discrete_space` gives the two equivalences with
  `SpaceMapIsProper f` and `SpaceMapIsLocallyQuasiFinite f`. The ordinary
  properness predicate uses local finite type on compatible étale scheme charts,
  `AlgebraicSpace.MapIsQuasiCompact f.hom.hom`, closedness of the actual
  base-change projections on `AlgebraicSpace.Point` with `pointTopologicalSpace`,
  and a presheaf diagonal representable by CLOSED IMMERSIONS; the stack predicate
  uses its own finite-type, point-space, and PROPER-diagonal conditions.
  The statement identifies those different separatedness tests. It also states
  explicitly that properness gives `ModuliSchemeTest @IsClosedImmersion` for
  the relative diagonal. That test quantifies over every scheme base change
  with the actual projection compared over S, rather than an unrelated map.
- `SpaceMapIsLocallyQuasiFinite` quantifies over every pair U,V of scheme charts,
  both actual chart maps a,b, and a scheme map p with `a ≫ f.hom.hom = yoneda.map p ≫ b`.
  The two chart hypotheses are exactly `AlgebraicSpace.IsEtale a` and
  `AlgebraicSpace.IsEtale b`. The conclusion uses the recorded Stacks predicate
  `Scheme.Hom.IsLocallyQuasiFinite p.left`. Neither chart must be surjective.
- With target a scheme T, `locallyQuasiFinite_space_chart_to_scheme` takes the
  actual presheaf map `f : E.obj.obj ⟶ yoneda.obj T`, the intrinsic local
  quasi-finiteness hypothesis, and each étale chart a. Its conclusion concerns
  exactly `(yoneda.preimage (a ≫ f)).left`. There is no chosen or arbitrary lift.
- `proper_locallyQuasiFinite_discrete_scheme` identifies the two intrinsic
  predicates on the Yoneda map of each `f : U ⟶ V` with `IsProper f.left` and
  the recorded `Scheme.Hom.IsLocallyQuasiFinite f.left`.
- Invariance is `proper_locallyQuasiFinite_moduli_equivalence`: arbitrary DM
  sources and targets, arbitrary equivalences e,d, and the specified over-S
  2-isomorphism `e.comp f' ≅ f.comp d` give two separate iff conclusions.
  Taking e,d to be identities includes 2-isomorphic maps. The new source and
  target have independent explicit universes, so equivalence invariance does
  not silently demand matching category sizes.

The intrinsic definitions are in the new definition module. Finite type is
`IsLocallyFiniteTypeModuliMap f ∧ IsQuasiCompactModuliMap f`. Local finite type
uses scheme projections on every étale atlas of every scheme base change.
For DM stacks these tests are equivalent to smooth-chart tests in the source:
étale atlases exist, and local finite type descends along smooth covers.
Quasi-compactness means an affine test scheme has a quasi-compact étale atlas.
Universal closedness uses the actual point map after every scheme base change;
these tests imply closedness after arbitrary stack base changes because inverse
images of closed sets are tested on atlases of their targets. Properness retains
all four conditions, including the proper relative diagonal. DM diagonals are
unramified; if a base change is proper, it is finite over the test scheme and
therefore a scheme. Scheme tests here therefore impose exactly the proper
algebraic-space diagonal condition, without incorrectly making properness
étale-local on the source.

Local quasi-finiteness retains local finite type, local quasi-finiteness of the
representable relative diagonal, and discrete field fibres. In the last clause
`ModuliPointIsClosed ... ({x}ᶜ)` says the singleton {x} is open for every point x;
this is exactly discreteness, including an empty fibre. The diagonal's scheme
chart tests use `Scheme.Hom.IsLocallyQuasiFinite`, not bare Mathlib
`LocallyQuasiFinite`: the upstream comparison explicitly says the latter must
be combined with local finite type to give the Stacks convention.

Points are `Quot (ModuliFieldRelation F)`, where field objects retain their actual
F-object and have field-scheme base. Arrows between field objects are precisely
pullback along field extensions followed by isomorphism, since stack fibres are
groupoids and every arrow is cartesian. The equivalence closure built into Quot
therefore identifies exactly the common-field-extension point classes. The point
map is the functor's actual map on these objects, with projection equality from
`BasedFunctor.w_obj`. `moduliChartPreimage` uses the range of the actual field
point of the chart scheme. `ModuliPointIsClosed` tests closedness of those inverse
images on all étale surjective atlases. This closed-set presentation gives the
same topology as smooth atlases for a DM stack; no arbitrary topology or point
bijection is supplied. All these definitions have real data and no sorry.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms;
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `Limits.pullback`
  and its projections. Scheme fibre products remain those of the dependency.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `IsDeligneMumfordModuliStack`, `IsModuliStack`, `ModuliTwoIso`,
  `moduliTwoFiberProduct`, `moduliTwoFiberFst`, `discreteModuli`,
  `discreteModuliMap`, `HasSpaceBaseChange`, `SpaceMapIsEtale`,
  `SpaceMapIsSurjective`. The existing over-S/2-fibre-product interfaces are used
  directly and not repaired or replaced.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`
  and `AlgebraicSpace.IsEtale`, the recorded sheaf and scheme-test definitions.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`;
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`:
  `Scheme.Hom.IsLocallyQuasiFinite`, including local finite type in every affine
  witness, is the dependency's recorded notion.
- Plain proof imports are `Sheaf.AlgebraicGeometry.IsLocallyQuasiFiniteAffineCriterion`
  (`Scheme.Hom.isLocallyQuasiFinite_affine_criterion`),
  `Sheaf.RingTheory.QuasiFiniteComposition`
  (`RingHom.finiteType_and_isQuasiFiniteAtPrime_comp`), and
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`
  (`AlgebraicSpace.fibreProduct_isAlgebraicSpace` and its covering results).
  The other six stack proof-dependency nodes have no Lean records yet; no
  nonexistent modules were imported and no assumption replaces their results.

Edge cases checked before finalizing the statements: empty stacks and schemes;
empty field fibres; identity maps and identity equivalences; nonsurjective étale
charts; maps with nontrivial stabilizers, for example the structure map of the
classifying stack of a finite étale group (no representability restriction was
added); non-quasi-compact locally quasi-finite charts (quasi-compactness is only
in properness); arbitrary characteristic and non-Noetherian base; schemes as
discrete stacks; independent universes for equivalent stacks. Field tests use
Type u, the scheme universe, so are not vacuous through a smaller independent
field universe. There is no `STATEMENT-DISPUTED` issue or source-based correction.

Searches made:

- msearch leanfinder: "Composition of proper and locally quasi finite morphisms
  of Deligne Mumford stacks" returned eight scheme-only declarations, including
  `IsProper.stableUnderComposition` and the scheme local-quasi-finite composition
  instance; none asserts the stack theorem.
- msearch loogle: "IsDeligneMumfordModuliStack, IsProper" returned zero hits,
  reporting the project-only first identifier unknown to the search index.
- msearch grep: "AlgebraicStack|DeligneMumford|ModuliStack" returned zero hits.
- For the new definition node, actual unedited outputs of msearch LeanSearch,
  LeanFinder and grep, plus project rg, are in its `mathlib_searches`.
  LeanSearch "Underlying topological space of an algebraic stack and proper
  morphisms of algebraic stacks" returned scheme definitions and topology only.
  LeanFinder "Point space and intrinsic proper locally quasi finite morphisms
  of Deligne Mumford stacks" returned scheme properties only. The grep query
  "ModuliPoints|IsProperModuliMap|AlgebraicStack" found no Mathlib definition.
- rg over both `lean/WeilConjectures` and `lean/Sheaf` found no existing proper
  or local-quasi-finite stack-map predicate, field-point quotient, or point-closed
  predicate. The item id has no upstream source declaration.
- DAG searches for field points and proper/local-quasi-finite stack notions found
  the item and its statement-level supporting lemmas, which have no Lean
  definitions of these notions. `tools/blueprint_refs.py search` for "proper
  locally quasi-finite" returned zero blueprint-node matches. The ancestor
  command reports None, matching the item's inherited blueprint.from.node.
  Existing `ModuliStackProperties` defines an absolute proper diagonal and an
  absolute smooth finite-type atlas, not relative morphism properness. Existing
  `FiniteStackSchemeTests` defines representable finite maps, not these
  nonrepresentable morphism properties. These were read and not duplicated.

Validation: both delivered modules compiled individually through the prescribed
scompile.py server wrapper, including private dependency overlay and public
module-name checks; no errors or warnings were printed. Each of the five postponed
theorems has a source, blueprint tag and natural-language proof from the node.

## New nodes

`def-sfb-dm-stack-morphism-properties` introduces the point quotient, actual induced
point maps, relative diagonal, scheme/space tests and intrinsic relative DM
properness/local quasi-finiteness used by the item. It also gives the ordinary
space chart predicate and closed-immersion-diagonal properness predicate needed
for the compatibility clauses. Its source is Stacks Tags 0CL5, 06PU, 06UF and
03XJ, together with the stack point-space construction. The previously recorded
definitions give stacks, atlases and algebraic spaces, but no relative predicates
or point space. The searches above rule out a usable existing declaration. All
helper declarations belong to this one notion, are documented with this node's
blueprint tag, and are listed in its Lean record. No theorem or axiom is added
in the definition module.

Retry validation (2026-10-22): reread the live item and its statement dependencies,
the recorded framework signatures and the cited Stacks definitions and atlas
criterion. Repeated LeanFinder, Loogle, Mathlib grep and project searches agree
with the retained search record. Both modules compiled cleanly again through
scompile.py. The first dry run found that two dependency references in the new
node shared a bracket; they now have separate [id] citations. No mathematical
statement or Lean declaration changed in this repair. The maintainer performs
the independent review required by the dispatcher brief.

## Returned-delivery repair

The return for immutable head b89b017a2d1c identified the forbidden
`import_flags` field on `def-sfb-dm-stack-morphism-properties`. The retained
sandbox packet removes that field. Checked the new node against the exact
field set in brief-stage2 §5: no extra or missing keys remain. The item differs
from the current read clone only in `lean` and the added definition dependency.
That earlier metadata-only repair passed at 98cc8a184dd. The current semantic
repair is described below and changes the ordinary-space definition.

## Repair of return e1fc7593ee40

The initial saved-packet dry run passed at 74b1df17e67. The semantic H12/H4+H3
return still required a change: ordinary space properness used to reuse the new
stack finite-type, quasi-compactness and universal-closedness predicates.
`SpaceMapIsProper` now has four independent ordinary clauses:

- Local finite type: for all actual étale charts `a : h_U ⟶ E`,
  `b : h_V ⟶ F`, and `p : U ⟶ V`, the equation
  `a ≫ f.hom.hom = yoneda.map p ≫ b` implies `LocallyOfFiniteType p.left`.
- Quasi-compactness: the existing `AlgebraicSpace.MapIsQuasiCompact f.hom.hom`.
- Universal closedness: for every `T : Over S` and `a : h_T ⟶ F`,
  `IsClosedMap (AlgebraicSpace.mapPoint (pullback.snd f.hom.hom a))`.
  This uses the existing quotient `AlgebraicSpace.Point` and its
  `pointTopologicalSpace`; it retains the actual scheme-base-change projection.
- Separatedness: `AlgebraicSpace.IsRepresentableWith
  (fun _ _ p ↦ IsClosedImmersion p.left) (pullback.diagonal f.hom.hom)`.
  This tests the ordinary presheaf diagonal after every scheme base change.

These are the finite-type, closedness and properness definitions read in
`literature/stacks-project/spaces-morphisms.tex`, labels
`definition-locally-finite-type`, `definition-closed`, `definition-proper` and
`lemma-proper-local`. Scheme tests of closedness suffice by descent along an
étale atlas of any algebraic-space base change. The definition node's sentence
now states precisely these independent ordinary conditions. Consequently proof
step 6 genuinely identifies finite type and universal closedness in addition to
the two diagonal conditions.

The added statement dependencies are `def-a1-algebraic-space-point-classes`
(module `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses`, `Point`),
`def-a1-space-point-topology` (module
`Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`, `pointTopologicalSpace`),
and `def-sfb-proper-curve-moduli` (module
`Sheaf.AlgebraicGeometry.ProperCurveModuli`, `mapPoint` and
`MapIsQuasiCompact`). Their full definitions and docstrings were read; none is
copied. All three are cited by the new definition node and by the item.

The advisory is also addressed. `ModuliSchemeTest` uses the existing
`IsSchemeModuliBaseChange e p`; `IsEtaleModuliAtlas` uses the existing
`IsEtaleModuliMap a`, together with scheme-base-change surjectivity.
Both are imported from `Sheaf.AlgebraicGeometry.ModuliChartNormalization`,
recorded by the additionally cited `def-sfb-moduli-chart-normalization`.
The two redundant target-DM assumptions `hA'` and `hB'` were removed from the
equivalence-invariance theorem: they follow from source DM and the supplied
equivalences. The other theorem signatures are retained.

Self-check against the return: all four ordinary properness clauses now avoid
the stack predicates; every new name uses its recorded dependency module;
chart tests allow empty and nonsurjective charts and impose no compactness on
those charts; scheme-base-change tests quantify over all schemes in the same
universe as S; diagonal representability uses its actual projection. Empty
spaces, identity maps, non-quasi-compact étale charts and independent universes
of equivalent stacks remain covered. There are no new theorems, sorries in
construction data, or changes to the item's mathematical statement.

Validation of the semantic repair (2026-10-23): both delivered modules compiled
separately through `scompile.py`, including private overlay and public module-name
checks, with no errors or warnings. The definition module has no `sorry`; the
statement module has exactly its five postponed theorem proofs. The item's only
changed fields are `lean` and added `stmt_deps`; both primary signatures match
their Lean records verbatim. Every Lean line is at most 100 characters. Independent
mathematical review is performed by the maintainer as prescribed in this brief.

## Second reading by Q01

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

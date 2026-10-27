## Worker report

The module `Sheaf.AlgebraicGeometry.RepresentableFppfEtaleOpenDescent` states the
node in five named theorems, all with `sorry` proofs. It defines no new notion.
The mathematical statement, proof steps, and proof dependencies are unchanged.
Five already landed owning nodes were added to statement dependencies so that the
interfaces actually used have their proper DAG citations.

Source read: `literature/stacks-project/stacks-properties.tex`,
`lemma-check-property-covering` (04XD), including its two cartesian squares;
`spaces-descent.tex`, `lemma-descending-property-flat` (041W),
`lemma-descending-property-locally-finite-presentation` (041T),
`lemma-descending-property-open-immersion` (041X),
`lemma-descending-property-etale` (042B),
`lemma-flat-fpqc-local-source` (06ET), and
`lemma-locally-finite-presentation-fppf-local-source` (06EV).
The typo already recorded by stage 1 in 04XD's final covering sentence is avoided:
the covering is V ×_Y T → T, not the pullback of X → Y. Nothing requires f surjective.

Hypothesis and clause correspondence:

- The base scheme is `{S : Scheme.{u}}` in every declaration.
- The two algebraic stacks are `F` and `G`, independently sized
  `BasedCategory.{v₁,w₁}` and `BasedCategory.{v₂,w₂}` over `Over S`, with
  `hF : IsAlgebraicModuliStack F` and `hG : IsAlgebraicModuliStack G`.
  The definition includes stack descent, algebraic-space diagonal, and smooth
  surjective scheme atlas. This imposes no DM or etale-atlas assumption.
- The given morphism is `f : BasedFunctor F G`, with
  `hf : IsRepresentableByAlgebraicSpaces f`.
- The cover comes from `V : AlgebraicSpace S`; its actual map to G is
  `q : BasedFunctor (discreteModuli V.obj.obj) G`. Its representability is `hq`.
- Cover surjectivity is `hs : IsSurjectiveModuliMap q`: every field-valued
  target object has a lift after a field extension, with the required 2-isomorphism.
  Flatness is `hflat : ModuliSpaceTest @Flat q`; local finite presentation is
  `hlfp : ModuliSpaceTest @LocallyOfFinitePresentation q`. No quasi-compactness,
  smoothness, or etaleness of q is assumed.
- The canonical base change projection X_V → V is `moduliTwoFiberFst q f`.
  Its source is the actual existing `moduliTwoFiberProduct q f`, with isomorphism
  data retained, rather than a product of sets of isomorphism classes.
- `representable_fppf_target_property` quantifies over the three-member list
  `P = @Flat ∨ P = @LocallyOfFinitePresentation ∨ P = @Etale`, and concludes
  `ModuliSpaceTest P f ↔ ModuliSpaceTest P (moduliTwoFiberFst q f)`.
  The disjunction encodes three independent assertions: it never assumes the
  other two properties of f or its pullback. `ModuliSpaceTest` uses all scheme
  base changes and all representable etale scheme source charts.
- `representable_fppf_target_openImmersion` supplies the fourth equivalence with
  `ModuliSchemeTest @IsOpenImmersion`. This requires the whole base change to be
  a scheme open in the test scheme. Applying a merely source-local chart predicate
  to open immersion would be wrong, and is deliberately not the statement here.
- The same assertions for algebraic spaces are stated explicitly as
  `AlgebraicSpace.fppf_target_property` and `fppf_target_openImmersion`.
  All four spaces X,Y,V,Xv are actual `AlgebraicSpace S`. The maps f,q,r,p and
  `hpb : IsPullback r.hom p.hom f.hom q.hom` specify any cartesian model Xv
  of X ×_Y V, with p its actual projection to V. This is a universal-property
  presentation of the node's fibre product, not an added mathematical restriction.
  Every such pullback exists by the recorded fibre-product theorem.
- Space cover hypotheses are `IsJointlySurjective (fun _ : Unit ↦ q.hom.hom)`,
  `MapIsFlat q`, and `MapIsLocallyOfFinitePresentation q`. The singleton field-lift
  predicate is used because general space maps need not be representable by schemes;
  `AlgebraicSpace.IsSurjective` would incorrectly require that representability.
- On space maps, the three local properties are `MapIsLocally P`. The open-immersion
  clause uses `IsRepresentableWith (fun _ _ a ↦ IsOpenImmersion a.left)` instead.
- `AlgebraicSpace.fppf_source_target_property` has the same cartesian square and
  additionally `W : AlgebraicSpace S`, `h : W ⟶ Xv`, with its singleton
  field-lifting surjectivity, `MapIsFlat h` and
  `MapIsLocallyOfFinitePresentation h`. These are exactly the second cover.
  The two independent conclusions are encoded by
  `P = @Flat ∨ P = @LocallyOfFinitePresentation`, and the equivalence is
  `MapIsLocally P f ↔ MapIsLocally P (h ≫ p)`. Thus W → V is the specified
  composite. There is no source-local claim for etale or open immersion.

Dependency declarations read and reused:

- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `IsFibredInGroupoids`, `IsModuliStack`, `discreteModuli`, `discreteModuliMap`,
  `moduliTwoFiberProduct`, `moduliTwoFiberFst`, `HasSpaceBaseChange`,
  `IsRepresentableByAlgebraicSpaces`, `HasAlgebraicSpaceDiagonal`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`,
  `AlgebraicSpace.IsAlgebraicSpace`, `IsRepresentableWith`, `IsEtale`.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`: `IsAlgebraicModuliStack`,
  `IsSmoothModuliAtlas`, `SpaceMapIsSmooth` (added owning statement dependency
  `def-sfb-algebraic-moduli-stack`).
- `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`: `ModuliSpaceTest` and
  `ModuliSchemeTest` (added owner `def-sfb-dm-stack-morphism-properties`).
  These predicates have no DM-stack hypotheses and apply to the general stacks here.
  Their projection comparison uses `IsSchemeModuliBaseChange` from the publicly
  imported `Sheaf.AlgebraicGeometry.ModuliChartNormalization`, whose definition
  and docstring were also read.
- `Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus`:
  `IsSurjectiveModuliMap` (statement dependency
  `def-sfb-surjective-moduli-map`, existing:true, Q87, landed 2026-10-24).
  The calculus theorem remains only in `proof_deps`; its conclusion is not a
  statement prerequisite.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally`,
  `MapIsFlat`, `MapIsLocallyOfFinitePresentation` (added owner
  `def-sfb-space-morphism-properties`).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity`: `IsJointlySurjective`
  (added owner `def-trf-algebraic-space-jointly-surjective-family`).
- Mathlib's `AlgebraicGeometry.Scheme` and `Scheme.Hom`; `Flat` in
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`; `LocallyOfFinitePresentation` in
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`; `Etale` in
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`; `Smooth` in
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`; `IsOpenImmersion` in
  `Mathlib.AlgebraicGeometry.OpenImmersion`; `Field` in
  `Mathlib.Algebra.Field.Defs`. Their source signatures and docstrings were read.
- The fibre-product dependency records `CategoryTheory.Limits.pullback`, fst and
  snd in Mathlib's `Limits.Shapes.Pullback.HasPullback`. Their signatures and
  docstrings were read. The space statements use the equivalent existing
  `CategoryTheory.IsPullback` interface to avoid inventing a second bundled product.

Every recorded proof-dependency module is imported, with plain imports when used
only for proofs. The two proof nodes `lem-sfb-representable-pullback-over-space`
and `lem-sfb-space-fpqc-open-immersion-descent` have no Lean attachment in the
read checkout, so there is no recorded module to import for them. Their intended
uses are retained explicitly in the proof docstrings. They are not missing
statement notions and no copy of either theorem is introduced.

Edge cases checked by reading the definitions and the source arguments:

- Empty base/target/source are allowed: there is no `Nonempty` condition or point
  choice. A surjective cover of the empty target can be empty; all universal tests
  retain this case. An empty source over a nonempty target is permitted for f.
- Identity covers give the identity equivalence, with no restriction on f.
- Arbitrary surjective flat locally finitely presented covers are allowed, even
  when the cover map is not quasi-compact. The proof plan passes to finite affine
  refinements only on each affine target open.
- Source covers are allowed to have positive relative dimension. For example the
  smooth surjection A¹_k → Spec k shows why etaleness must not be included in the
  source-local theorem; a two-point etale cover similarly prevents a source-local
  open-immersion claim. Both are excluded exactly as the node requests.
- Stack category universes are independent. All scheme tests, field spectra and
  extension fields use the existing big-site universe u, so field testing is not
  accidentally moved to an independent smaller universe.
- All source charts in `ModuliSpaceTest` and both charts in `MapIsLocally` are
  universally quantified; neither is silently required to be surjective.

Searches actually run:

- `msearch.py ... leanfinder` query: “Flat locally finitely presented etale open
  immersion representable stack morphism descent along surjective flat locally
  finitely presented algebraic space cover”. Eight hits: scheme descent instances,
  universal openness, and flat monomorphisms; no stack/space theorem matching the node.
- `msearch.py ... loogle` query: `AlgebraicGeometry.Flat,
  AlgebraicGeometry.LocallyOfFinitePresentation, CategoryTheory.ModuliSpaceTest`.
  Zero hits; service reports unknown identifier CategoryTheory.ModuliSpaceTest.
  The project declaration was found and read directly instead.
- `msearch.py ... grep` query: `DescendsAlong|flat.*surjective|etale.*fppf`,
  Mathlib subdirectory `AlgebraicGeometry`. Twenty-five hits including scheme
  descent and singleton fppf membership, none an exact space/stack statement.
- `rg` in `lean/WeilConjectures` for the exact item id returned no match; searches
  for `fppf.*[Dd]escent|[Dd]escent.*fppf|representable.*fppf` in its algebraic
  geometry and category theory directories gave no matching declaration.
- `rg` over `lean/Sheaf/AlgebraicGeometry` for `ModuliSpaceTest`,
  `IsAlgebraicModuliStack`, and fppf descent found the interfaces above and nearby
  results. `AlgebraicSpaceFourPropertyFppfDescent` concerns affine, finite type,
  quasi-finite and separated, not this node's list.
  `RepresentableLocallyQuasiFiniteCalculus` concerns local quasi-finiteness only.
  Neither is an exact duplicate. Existing chart and field-lifting notions are reused.
- Existing DAG records for every added owning node were read, and their full
  statement/proof dependency closures were checked not to contain this item.

Validation: `scompile.py Q24 lem-sfb-representable-fppf-etale-open-descent`
compiled the delivered module both as sandbox and under its final library module
name, with no errors or warnings (18.3 s and 12.7 s). An initial namespace lookup
error was repaired by opening `CategoryTheory` explicitly. `autoImplicit` is false;
all universe variables and binders are explicit. No statement fault or
STATEMENT-DISPUTED flag remains.


## Repair of returned head 4a38e969cd5c

H2 repaired: replaced `lem-sfb-stack-chartwise-smooth-etale-calculus` in
`stmt_deps` with the currently landed definition node
`def-sfb-surjective-moduli-map`. Its existing:true attachment is precisely
`CategoryTheory.IsSurjectiveModuliMap` in
`Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus`. Read the new node's
statement, record, and the full predicate and docstring at lines 63–80 of that
module: it is field-extension-local lifting with the specified actual 2-isomorphism,
exactly the predicate used by both stack-cover hypotheses. No theorem conclusion
is needed to state these hypotheses. The calculus theorem remains in `proof_deps`,
unchanged, and its module remains publicly imported to expose the predicate.

Compared the retained sandbox node with the current shared main node: only
`lean` and the five added owning statement dependencies differ. This repair changes
only the erroneous dependency ownership and this report; the Lean module and all
five mathematical statements remain byte-for-byte as independently accepted at
returned head 4a38e969cd5c. The prescribed delivery wrapper refreshes the base before
preflight and delivery. No definition node or dependency module is delivered.

## Second reading by Q24

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

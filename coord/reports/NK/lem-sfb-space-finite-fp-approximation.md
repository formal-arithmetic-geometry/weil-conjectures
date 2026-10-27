## Worker report

Item: lem-sfb-space-finite-fp-approximation. Group NK, stage 2.
The delivery states
`AlgebraicGeometry.AlgebraicSpace.exists_finite_finitePresentation_limit_of_finite`
in `Sheaf.AlgebraicGeometry.FiniteSpaceFinitePresentationLimit`.
Its only proof is `by sorry`. No definitions or other theorems are introduced.
Only the item's `lean` field changes; the accepted stage-1 split is preserved.

The inherited BLOCKED ending concerned the already accepted Q06 stage-1 split,
not a stage-2 Lean delivery. The current node has no `lean` record or
`reviewed_lean`, its queue row is stage 2, and no repair note exists.
The handoff in coord/brief-stage2.md §0 explicitly permits this stage-2 work.

Source read: literature/stacks-project/spaces-limits.tex, Tag 07VR,
`lemma-finite-in-finite-and-finite-presentation`, statement and proof.
Also read spaces-properties.tex, `lemma-characterize-quasi-separated`,
including the proof reducing to Spec Z and the equivalence with the affine-pair
criterion. This is the same absolute quasi-separatedness, for arbitrary S.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A scheme S and algebraic spaces X,Y over S: explicit binders
  `{S : Scheme.{u}} {X Y : AlgebraicSpace S}`. The existing algebraic-space
  category is the full subcategory of fppf sheaves with representable diagonal
  and an étale surjective scheme atlas; its arrows are natural transformations.
- The morphism f is `(f : X ⟶ Y)`.
- Finite on every scheme test, including representability:
  `hf : IsRepresentableWith (fun _ _ g ↦ IsFinite g.left) f.hom.hom`.
  This uses the existing scheme finiteness class; it is not a new space predicate.
- Quasi-compact Y: `hqc : CompactSpace (Point Y.obj.obj)`, with the existing
  atlas/final topology on the point classes. CompactSpace is finite-subcover
  compactness without any Hausdorff condition.
- Absolute quasi-separated Y: `hqs` quantifies over all affine schemes U,V
  over S and arbitrary maps a,b into Y, requiring
  `CompactSpace (Point (Limits.pullback a b))`. This is exactly condition (3)
  of the cited Stacks characterization, equivalent to quasi-compactness of
  the absolute diagonal. No property of S's diagonal is assumed.
- The test-scheme and space sizes use the recorded `universe u`. The index
  set is `I : Type u`, so it has the same small bound as the scheme carriers,
  as required by the project's index-universe convention. No independent
  smaller universe or countability bound is imposed.
- A small nonempty directed set: existential `I`, `PartialOrder I`,
  `Nonempty I`, and `IsDirected I (· ≤ ·)`.
- Spaces X_i and compatible Y-maps: `D : Iᵒᵖ ⥤ Over Y`.
  The stage space is `(D.obj i).left` and its Y-map is `(D.obj i).hom`.
  The functor laws give the identity and composition laws for transitions.
  Arrows i → j in the opposite order are precisely transitions from the
  later underlying index to the earlier one.
- Compatible maps p_i from X: the natural transformation
  `π : (Functor.const Iᵒᵖ).obj (Over.mk f) ⟶ D`.
  Each `(π.app i).left` is a map of algebraic spaces X → X_i;
  naturality is the cone compatibility equation. Because each component
  is an arrow in `Over Y`, its defining equation is
  `(π.app i).left ≫ (D.obj i).hom = f`, the stated factorization for every i.
- Every stage is finite: first conjunct of the first universal clause,
  `IsRepresentableWith (fun _ _ g ↦ IsFinite g.left)
    (D.obj i).hom.hom.hom`.
- Every stage is of finite presentation: the next three conjuncts are
  `MapIsLocallyOfFinitePresentation (D.obj i).hom`,
  `MapIsQuasiCompact (D.obj i).hom.hom.hom`, and
  `MapIsQuasiCompact (pullback.diagonal (D.obj i).hom.hom.hom)`.
  These express precisely local finite presentation on compatible étale
  scheme charts, quasi-compactness, and relative quasi-separatedness.
  Algebra finite presentation, not module finite presentation, is used.
- Closed immersion transitions, representable on all scheme tests:
  `IsRepresentableWith (fun _ _ g ↦ IsClosedImmersion g.left)
    (D.map a).left.hom.hom` for every transition arrow a.
- Affineness of every transition is the following conjunct, using
  `IsRepresentableWith (fun _ _ g ↦ IsAffineHom g.left)`.
  This retains the node's explicit 'hence affine' clause.
- X, with the specified projections, is the inverse limit as a space over Y:
  `Nonempty (IsLimit (Cone.mk (Over.mk f) π))`. This states the universal
  property among all objects of `Over Y`; it does not assume a separately
  chosen limit or only test affine spaces. It is equivalent to the asserted
  cone-compatible isomorphism X ≅ lim X_i over Y.

Dependency declarations read and used:

- def-pc-scheme: Mathlib.AlgebraicGeometry.Scheme,
  `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- def-trf-algebraic-space: Sheaf.AlgebraicGeometry.AlgebraicSpace,
  `AlgebraicGeometry.AlgebraicSpace`, `IsAlgebraicSpace`,
  `IsRepresentableWith`, `IsRepresentable`, and `IsEtale`.
  Read the full signatures and definitions, including the scheme-test
  representing pullback square in `IsRepresentableWith`.
- def-weil-size-convention: its recorded metatheoretic convention, implemented
  with explicit universes and a same-universe index set, has no declaration.
- lem-trf-space-fibre-products-etale-covers:
  Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers,
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, and
  `etale_fibreProduct_isScheme`. Their full statements and proof docstrings
  were read. The theorem uses the actual presheaf fibre products, and the
  imported result identifies their algebraic-space interpretation.
- def-a1-space-point-topology:
  Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology,
  `pointTopologicalSpace`, `pointImage`, `PointRepresentative.map`.
  The topology is the existing supremum of coinduced étale-chart topologies.
- def-sfb-space-morphism-properties:
  Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties,
  `MapIsLocally` and `MapIsLocallyOfFinitePresentation`.
  Quasi-compactness is the existing `MapIsQuasiCompact` from its imported
  Sheaf.AlgebraicGeometry.ProperCurveModuli, tested on affine schemes.
- def-weil-finite-integral-morphism:
  Mathlib.AlgebraicGeometry.Morphisms.Finite, `AlgebraicGeometry.IsFinite`;
  the accompanying Integral.lean `IsIntegralHom` signature was also read.
- def-weil-closed-immersion:
  Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion,
  `AlgebraicGeometry.IsClosedImmersion`.
- The stated proof dependency lem-a1-space-affine-etale-cover is imported
  without public: Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover,
  `exists_affine_etale_cover_and_point_topology`; its statement/docstring
  were read. The finite/closed-immersion and fibre-product proof dependencies
  are already public imports used by the statement.
- Other proof dependencies currently have no Lean records:
  lem-sfb-space-relative-spec-correspondence,
  lem-sfb-space-finite-algebra-surjective-fp-colimit,
  lem-sfb-space-closed-immersion-atlas-locality,
  lem-sfb-space-affine-limits-schematic-stages, and
  lem-sfb-space-affine-locality. There is no module to import for these;
  they are not needed to type this statement. Their complete proof roles
  are retained in the theorem docstring, matching the four DAG proof steps.

Edge cases checked before finalizing the statement:

- Empty Y (and necessarily empty X) is allowed. The index is still nonempty,
  as in the statement; a constant singleton diagram suffices.
- Empty X over a nonempty qcqs Y is allowed; no nonemptiness of point spaces
  or of affine tests is required. CompactSpace admits the empty space.
- If f is already finite and finitely presented, a singleton constant diagram
  with identity transition is allowed.
- For a quotient R → R/J with a non-finitely-generated ideal J, finite as a
  module does not assert finite presentation of f. The conclusion permits
  a nonconstant directed system of finite-presentation quotient stages.
- Arbitrary non-quasi-separated S is allowed: hqs tests absolute
  quasi-separatedness of Y, not the relative diagonal of Y → S.
- There is no characteristic restriction, separatedness of Y, scheme
  hypothesis on X or Y, or extra finiteness hypothesis on their base maps.

Searches (actual wrapper results preserved in searches.jsonl):

1. LeanFinder, query 'A finite morphism of algebraic spaces over a quasi compact
   quasi separated base is a directed inverse limit of finite finitely presented
   morphisms with closed immersion transitions': eight hits, including scheme
   IsFinite, LocallyOfFinitePresentation, LocallyQuasiFinite and finiteness
   permanence; none is this algebraic-space inverse-limit assertion.
2. Loogle, query 'AlgebraicGeometry.IsFinite, CategoryTheory.Limits.IsLimit':
   zero hits.
3. Mathlib grep through msearch.py, query
   `finite.*[Ff]inite[Pp]resentation|finite.*[Ii]sLimit|AlgebraicSpace`
   under AlgebraicGeometry: ten hits, concerning affine spaces, scheme
   finite-presentation classes and flat rank; no matching theorem.
4. rg in live lean/WeilConjectures and lean/Sheaf for the item id, the proposed
   declaration name, and finite/fp/limit patterns: no existing copy of this
   statement. The related
   Sheaf.AlgebraicGeometry.IntegralSpaceFinitePresentationLimit theorem has
   integral input and only affine transitions, so does not assert the closed
   transition conclusion required here. Its full statement and docstring were
   read and its established absolute affine-pair convention was followed.

No new nodes or dependency repairs are needed. No statement correction or
STATEMENT-DISPUTED flag is warranted. All binders and the universe are explicit;
`set_option autoImplicit false` enforces this. Lines are at most 100 characters.
Compilation uses only the prescribed scompile.py wrapper.

## Second reading by NK

This is an in-session rereading of the node, the cited Stacks statements and
this file, not a claim that an additional agent reviewed it. The dispatcher
forbids starting other agents; the maintainer supplies the independent review.

I checked the potentially lossy translations explicitly. The hqs affine-pair
condition is the source's equivalent absolute notion even when S is not
quasi-separated. A relative diagonal of Y over S would be incorrect here and
is not used. Conversely the stage finite-presentation clause correctly uses
the relative diagonal of each X_i → Y. The two uses of diagonal must differ.
The cone is in Over Y, so both transition commutation and every factorization
through X_i are enforced; no additional unrecorded cone data is assumed.
The IsLimit quantifies over all spaces over Y, not an affine subcategory.
Closed immersions and affine transitions are both retained. I changed the
preserved draft's index binder from Preorder to PartialOrder to render the
node's directed set literally. No other mathematical clause was changed.
Every named theorem has only sorry as proof, with all four node proof steps
and their node references in its docstring. There are no hollow definitions.

## Resumption validation (2026-10-23 UTC)

Reopened the current node and every statement-dependency record and read the
recorded declarations and source docstrings. The live node still has no Lean
record or reviewed_lean; its queue row remains stage 2. No repair note exists.
The sandbox node, excluding its lean field, is identical to the current node.
Fresh LeanFinder, Loogle and Mathlib grep searches again found no exact theorem;
project and upstream-name searches found only the distinct integral-input lemma.
I reread Tag 07VR and the absolute quasi-separated affine-pair characterization,
and checked the diagram direction, its Over Y component equations, and the
relative stage diagonals against the actual definitions. No Lean change was
needed on this resumption.

The prescribed scompile.py compiled this file against the live server build
successfully (sandbox 10.6 seconds, library module 8.8 seconds), with no errors
or unexpected warnings. The prescribed deliver2.py --no-push printed
`OK (dry run): commit cc393c80886 passes the preflight and compiles; nothing pushed`.
The delivery includes this validation paragraph; the push repeats its gates.

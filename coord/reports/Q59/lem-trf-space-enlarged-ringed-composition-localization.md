## Worker report

Item: `lem-trf-space-enlarged-ringed-composition-localization`.
Module: `Sheaf.AlgebraicGeometry.EnlargedRingedCompositionLocalization`.
All seven theorem proofs are `sorry`. Definitions contain actual data, and every
new declaration is recorded in `lean.declarations` with this item's blueprint tag.
One new definition node attaches the four already published chart-normalization
and coefficient-transport definitions. It is cited in `stmt_deps`; the chart-ringed
morphism theorem remains a proof dependency. No mathematical statement correction
is needed. The existing universe-general ringed-topos definition node is also cited;
the original `def-weil-pbc-ringed-topos-morphism` record is unchanged from live.

The original scheme, algebraic space, chartwise etaleness, enlarged site,
precoverage, scheme inclusion, base-change functor, direct image, postcomposition,
localization functor, restriction functor and scheme-comparison isomorphism are
all reused. No second site, algebraic space, or structure sheaf is introduced.
The comparisons are constructed from Mathlib's pullback-pasting isomorphism and
the second projection, with no use of the parent enlarged-site composition or
identity theorems. The graph counit explicitly pins each localization adjunction.

Hypothesis and clause correspondence:

1. A scheme S and algebraic spaces over S: explicit universe `u`,
   `{S : Scheme.{u}}`, and `AlgebraicSpace S`. Every local object and every arrow
   is explicitly bound. Set sheaves use `Type (max (u + 1) w)`, with independent
   `w`; ring sheaves use `RingCat.{u}` before canonical coefficient lifting.
   The generic coherence statement allows an arbitrary coefficient category
   `A : Type v` with `[Category.{w} A]`; specializing to the large set universe
   gives the sheaf-topos statement. No site/coefficient universe equality is imposed.
2. Chartwise etale sites and coverings: the original `EnlargedEtaleSite`,
   `enlargedEtalePrecoverage`, and `enlargedEtaleTopology`, with
   `enlargedSchemeInclusion`, are imported unchanged. The permanence theorem is
   imported, including its composition and cancellation clauses.
3. Arbitrary chosen rings and specified i_A^* R_A ≅ O_A:
   `EnlargedNormalizedRingDiagram.ring` and `.normalization`. These use
   `RingCat`, so noncommutativity is NOT excluded by a binder. The structure
   only packages the data quantified in the node, for all spaces and arrows.
   It has no mathematical construction or proof hidden in its fields.
4. Adjoint structural maps and their chart formula:
   `.map f : ring Y ⟶ (enlargedDirectImage f RingCat).obj (ring X)` and `.chart`.
   The latter quantifies every commuting scheme-chart triangle and says exactly
   that the map, after both specified identifications, is `Scheme.Γ.map q.left.op`.
   This is the f-map formula of Stacks 03G8 and of the recorded chart-ringed
   morphism dependency. Charts need not be surjective, so the formula includes
   every scheme chart in the node. Its projections identify a chart of the
   fibre product with such a triangle.
5. The projection-preserving iterated fibre-product isomorphism:
   `enlargedCompositionIso`, constructed by `NatIso.ofComponents`, lifting
   `Limits.pullbackRightPullbackFstIso` through the algebraic-space full subcategory,
   the over category and the enlarged-site full subcategory. Naturality is checked
   against both pullback projections in the definition. Both projection identities are in
   `enlargedComposition_projection_coherence`. `enlargedIdentityIso` lifts
   `asIso (Limits.pullback.snd (𝟙 X.obj) V.obj.hom.hom)` through the same categories,
   with the over-condition following from `pullback.condition`. Its underlying map
   is literally the second projection. That theorem states associativity and both
   unit laws at the site-functor level. `HEq` only accommodates the equality of
   composite algebraic-space arrows `(h ≫ g) ≫ f = h ≫ (g ≫ f)` and the
   corresponding identity equalities; it does not replace an equation by an
   unspecified isomorphism.
6. Direct images (fg)_* ≅ f_* g_*:
   the inverse of `enlargedDirectCompositionIso g f A`. It is constructed by
   `Functor.sheafPushforwardContinuousComp'` from exactly the site comparison.
   Thus its sections are the action of a sheaf on the specified projection
   isomorphism, and `enlargedDirectImage` remains literal base-change evaluation
   on objects, restriction maps and sheaf morphisms. The direct-image unit is
   `enlargedDirectIdentityIso`.
7. Adjoint-compatible inverse-image comparison:
   `enlargedInverseCompositionIso` is precisely Mathlib's
   `Adjunction.leftAdjointCompIso` for that direct comparison. This is the
   conjugate isomorphism, with the defining unit equation supplied by Mathlib,
   not an existential comparison with no normalization.
   `enlargedDirectInverse_coherence` states the direct and inverse associativity
   diagrams and all four unit equations. Its left-adjoint arguments allow any
   specified adjunctions, rather than choosing a preferred inverse image.
8. Structural ring maps compose:
   the first conjunct of `enlargedNormalizedRing_composition` is
   alpha_f ≫ f_*(alpha_g) ≫ comparison = alpha_(g≫f).
   Its third conjunct transposes exactly these maps, giving
   g^sharp ∘ g^{-1}(f^sharp) after the adjoint-compatible comparison. The second
   and fourth conjuncts give the adjoint and inverse-image identity formulas.
   Together with the explicit comparison associativity equations, these binary
   identities give the three-arrow structural diagrams: each path is the same
   ordered triple of structural maps. There is no separate hypothesis of
   structural-map coherence.
9. Given ringed-topos morphisms, not just ring-valued abstractions:
   `IsNormalizedEnlargedRingedMorphism` packages the EXISTING
   `IsChartNormalizedRingMap` plus equality of its canonically lifted underlying
   map with the adjoint transpose of the GIVEN `p.ringMap`. This is the same
   interface and faithful sectionwise ULift used by the chart-ringed dependency.
   `enlargedRingedMorphism_composition` binds arbitrary p, q, r with their
   specified direct functors and this normalization. It specifies the exact
   projection-induced right comparison `d`, its exact conjugate `a`, and the
   equation `a.hom.app _ ≫ r.ringMap = q.inverse.map p.ringMap ≫ q.ringMap`.
   No arbitrary ring map, module functor, or inverse-image comparison is substituted.
   This full ringed statement uses commutative-ring presentations as the existing
   dependency does; the preceding RingCat statements retain the unrestricted
   formulation. These presentations lose no cases: by scheme density each ring
   of sections injects into the commutative ring of sections of a scheme atlas.
   Its multiplication is therefore commutative, with the same data and maps.
10. Etale site localization and its inverse on factorizations:
    `enlargedLocalization_covering_families` binds arbitrary f with
    `hf : IsChartwiseEtale f`. It provides an equivalence E whose functor is
    exactly `enlargedLocalization f hf`. The inverse has the same underlying
    space and the factorization map `T.hom.hom.left`; its action on arrows is
    also specified. The final iff compares the ORIGINAL covering presieves
    through `Presieve.overEquiv`, not only their generated covering sieves.
    Thus it preserves and reflects precisely the node's covering families.
11. Unique normalized ring-sheaf identification:
    `enlargedNormalizedRing_localization` has an `∃! ρ` for arbitrary RingCat
    extensions. The equation for every scheme U says exactly that ρ is the
    identity on Γ(U,O_U), under the two supplied identifications. It includes
    noncanonical choices of the extensions and of their normalizations.
12. Inverse image is restriction; direct image evaluates on fibre products:
    the same theorem supplies the adjunction with actual
    `enlargedEtaleRestriction f hf` as left adjoint and actual
    `enlargedDirectImage f` as right adjoint, and states left exactness. Its
    ring-valued adjunction identifies ρ's transpose with the actual `R.map f`.
    Both adjunctions satisfy `IsEnlargedLocalizationAdjunction`: at every sheaf G
    and enlarged object T, the counit is G applied to `enlargedLocalizationGraph`.
    This graph is the actual pullback pair `(T → X, id_T)`, constructed by
    `pullback.lift`; there is no existence-theorem choice in its data.
    For any given inverse-image adjunction its `leftAdjointUniq` comparison
    explicitly takes its structural map to ρ.
13. The actual given ringed morphism is this localization:
    `enlargedRingedMorphism_localization` supplies the set-sheaf localization
    adjunction pinned by the graph counit, normalized original ring isomorphism ρ, the specified conjugate
    comparison `c : p.inverse ≅ enlargedEtaleRestriction ...`, and the equation
    `p.ringMap = c.hom.app _ ≫ (enlargedLiftedLocalizationRingIso ... ρ).hom`.
    The latter helper is the actual functorial lift of ρ, not a chosen arrow.
    The unique unlifted ring identification is stated separately in clause 11.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsEtale`,
  `EtaleSite`, `structureSheaf`.
- `def-weil-size-convention`: the recorded metatheoretic convention has no
  declaration; it is implemented by the explicit universes above.
- `Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence`:
  `chartwise_etale_permanence` (composition and cancellation).
- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`, used by the original site's
  interface. Covering families remain its original precoverage.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace`,
  `enlargedSchemeInclusion`, `enlargedBaseChange`, `enlargedDirectImage`,
  `enlargedLocalization`, `enlargedEtaleRestriction`, `chartwiseEtaleMap`,
  `enlargedPostcomposeSchemeIso`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, which constructs the original fibre product.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous` and
  `Mathlib.CategoryTheory.Sites.Over`: `SheafOfModules.overFunctor`,
  `GrothendieckTopology.over`, `Presieve.overEquiv`. Existing localization is used.
- `Sheaf.Paper.SequenceSiteCompletionProjection`:
  `CategoryTheory.RingedToposMorphismOfUniverses`, via its existing definition node
  `def-pur-ringed-topos-morphism-of-universes` (Q111), without rebinding NH's node.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting`:
  `Limits.pullbackRightPullbackFstIso` and its projection identities.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso`:
  `pullback_snd_iso_of_left_iso`, used to make the identity comparison actual data.
- `Sheaf.AlgebraicGeometry.EnlargedChartRingedMorphism`:
  `IsChartNormalizedRingMap`, `chartNormalizedRing`, `chartNormalizedLiftedRing`,
  `chartNormalizedUnderlyingMap`, attached by
  `def-trf-enlarged-chart-normalized-ring-data`; the theorem
  `enlarged_chart_ringed_morphism` is a proof dependency only.
- `Mathlib.CategoryTheory.Adjunction.Basic`: `Adjunction.comp`, `.id`,
  `.comp_homEquiv` (recorded composite-adjunction Mathlib leaf).
- `Mathlib.CategoryTheory.Adjunction.Mates`: `conjugateIsoEquiv`,
  `unit_conjugateEquiv_symm` (recorded conjugate-iso Mathlib leaf).
- `Mathlib.CategoryTheory.Adjunction.CompositionIso`:
  `Adjunction.leftAdjointCompIso`, `.leftAdjointIdIso`,
  `.leftAdjointCompIso_assoc`, and both unit laws (recorded coherence Mathlib leaf).
- `Sheaf.CategoryTheory.Sites.SliceSubtoposSitePresentation`:
  `slice_subtopos_site_presentation`, imported for the localization proof.
- The proof-only nodes `lem-trf-space-enlarged-site-scheme-density` and
  `lem-trf-space-enlarged-atlas-algebraic-extension` presently have no Lean
  record, so they have no additional module to import. Their objects already
  exist in the enlarged-site module; no unstated notion is needed to TYPE this
  item. Its proof docstrings retain these proof dependencies.

Sources opened: local `spaces-properties.tex` at lemma-functoriality-etale-site,
lemma-morphism-ringed-topoi, lemma-etale-morphism-topoi, equation-localize and
equation-localize-ringed. In particular 03G8 supplies the all-scheme-triangle
regular-function formula; 03LP and 04LY identify postcomposition and restriction.
The node is a derived node of the historical enlarged-site split, not a unit's
own statement. No source or unit statement correction is required.

Edge cases checked before and after writing:

- f or g an identity: all site, direct, inverse and structural unit formulas
  are present, without a nonidentity hypothesis.
- Three arrows: both association orders occur, with the same ordered maps;
  heterogeneous equality accounts only for associativity of the base arrows.
- f an isomorphism: it is allowed in every composition/localization formula.
- X or Y empty, including localization at the empty etale object: no nonempty,
  point, chart, or nonzero ring hypothesis occurs.
- Empty covering families: the exact presieve iff includes the empty presieve.
- Zero ring: all sheaves of rings are unital rings allowing 0 = 1; no domain or
  nontriviality hypothesis is introduced.
- Noncanonical ring extensions and normalization automorphisms: these remain
  parameters in the diagram and the full ringed morphism statements.
- Universe sizes: original small coefficient rings are not equated with the
  larger set-sheaf universe; canonical ULift and the generalized existing
  ringed-topos interface retain both sizes.

Searches (all performed through the prescribed search wrapper or read-only rg):

- leanfinder, "Composition and localization of ringed etale topoi of algebraic
  spaces with arbitrary normalized structure ring extensions": eight hits,
  concerning scheme etale composition and ring localizations; no exact match.
- loogle, "CategoryTheory.Adjunction.leftAdjointCompIso,
  CategoryTheory.GrothendieckTopology.over": zero hits for the combined query.
  The exact declarations were nevertheless opened directly in Mathlib.
- grep, "enlargedEtale_localization|enlargedBaseChange_composition|leftAdjointCompIso":
  fourteen Mathlib hits, including CompositionIso and module pullbacks; none
  is the algebraic-space normalized ringed theorem. These existing categorical
  comparisons are reused.
- leansearch, "Morphisms of ringed topoi of algebraic spaces compose canonically
  and an etale morphism is ringed site localization": eight hits on locally
  ringed spaces and scheme etale cancellation; no exact match.
- rg in `lean/WeilConjectures` and `lean/Sheaf`, enlarged composition/localization
  patterns: existing `enlargedBaseChange_composition` and
  `enlargedEtale_localization` were found and read in full. They concern the
  SINGLE canonical extension, do not quantify arbitrary normalized rings,
  and do not state all the requested coherence diagrams. Their functors and
  projection comparisons are reused, not restated as new constructions.
- Exact item-id search of `lean/WeilConjectures`: no match.
- rg in both source roots and `dag/lean_names_upstream.json` for the new
  declaration names: no collision.

Validation: `scompile.py Q59 <item> <module>` compiled both the sandbox and final
library module cleanly, with the expected postponed theorem proofs. The first
extended compile found a private import of the chart-ringed dependency; this was
changed to a public import because its definitions occur in public signatures.
No Lean warnings or errors remain.

## New nodes

`def-trf-enlarged-chart-normalized-ring-data` owns the four existing plain definitions
`chartNormalizedRing`, `chartNormalizedLiftedRing`, `chartNormalizedUnderlyingMap`
and `IsChartNormalizedRingMap`, in the unchanged published module
`Sheaf.AlgebraicGeometry.EnlargedChartRingedMorphism`. Its `existing: true` attachment
follows the already accepted ownership pattern of `def-trf-scheme-algebraic-space`:
the existing definitions stay in their published module and are never copied.
The new node states forgetting commutativity, sectionwise ULift with independent
ambient universe, the lifted underlying map, and the all-scheme-triangle pullback
predicate. It does not assert existence or uniqueness of a normalized map.
The item cites this definition node instead of using the theorem node as a
statement prerequisite. Its dependencies define the spaces, charts, fibre products,
and the existing ULift transport. No dependency or theorem record is overwritten.

Searches for this ownership node were run afresh through `msearch.py`:

- LeanSearch: "Chart normalized sheaves of rings on enlarged etale sites with
  canonical coefficient universe lifting and normalized pullback on scheme charts":
  eight scheme étale topology and module pullback hits, no exact notion.
- Loogle: "chartNormalizedRing, IsChartNormalizedRingMap": no hits; unknown identifier.
- Mathlib grep: "chartNormalizedRing|IsChartNormalizedRingMap|chartNormalizedLiftedRing":
  no hits.
- Read-only DAG and project rg: the chart-ringed theorem node lists exactly these
  four plain definitions, but there is no definition node for them. The declarations
  are in its published module; WeilConjectures has no matching declaration.
- `blueprint_refs.py search 'chart-normalized ring'`: zero matches. The ancestor
  command returns `lem-trf-local-term-locality`; the new node retains the item's
  historical ancestry and puts this item first in its `via` chain.

## Repairs of immutable head e55682ddfde6

R1: restored `def-weil-pbc-ringed-topos-morphism.json` byte for byte from live.
Its NH `RingedToposMorphism` binding and all metadata are untouched. The item now
also cites Q111's landed `def-pur-ringed-topos-morphism-of-universes`, whose actual
`RingedToposMorphismOfUniverses` signature was reread. No §1(B) rebinding remains.

R2: added the definition ownership node above, with `existing: true` for its
unchanged module and all four declarations. Removed the chart-ringed theorem
node from the item's `stmt_deps`; its proof-dependency use is retained. This
separates the definitions needed to type the item from the theorem needed to
prove it, without creating duplicate Lean definitions.

R3: replaced both `.choose` constructions. The composition isomorphism now has
Mathlib pullback-pasting data; the identity isomorphism has second-projection data.
The only proof fields involved establish over-compatibility and naturality from
existing pullback equations. Neither definition refers to
`enlargedBaseChange_composition` or `enlargedBaseChange_identity`. The parent node's
proof can consequently use this item without choosing the needed comparisons
from that parent's postponed theorem.

Advisory: added the real pullback graph `enlargedLocalizationGraph` and the predicate
`IsEnlargedLocalizationAdjunction`. The set-valued and ring-valued adjunctions in
`enlargedNormalizedRing_localization`, and the actual ringed-morphism adjunction
in `enlargedRingedMorphism_localization`, now require the graph-counit formula of
node step 7. Thus their counits, and hence their Hom bijections, are pinned.
This renders the source's localization morphism explicitly, with the original
inverse and direct functors; it adds no assumption on f, the rings or the given p.

## Second reading by Q59

A second source-to-signature pass by this worker, not a claim of independent
review. The dispatcher forbids starting another agent; the maintainer supplies
the independent review after delivery.

I reread the node and every public signature together. The first pass provided
arbitrary RingCat extensions and the ring-object adjunction equations, but did
not explicitly name the given set-sheaf ringed morphisms. I added
`IsNormalizedEnlargedRingedMorphism`, `enlargedRingedMorphism_composition` and
`enlargedRingedMorphism_localization` to bind those morphisms, retain their
normalization through the existing coefficient lift, and specify their actual
structural-map equalities. I also checked the slice inverse on arrows and added
the exact covering-family iff, rather than relying only on covering sieves.
The arbitrary RingCat theorem retains the node's unrestricted word "rings";
commutative presentations in the full lifted interface are justified by the
same atlas-injection argument already present in the node's proof. The site
projection equations, direct/inverse associativity, both units, normalized
structural composition, unique ring identification and actual localization
morphism now each have the signature counterpart enumerated above. No false
statement or disputed source assertion was found.


Repair self-reading: reread Stacks 03G2(2), 03G8 and 04LY/04LZ against the
post-repair signatures. The composition comparison still has the same type and
both projections, but now actual Mathlib data. The identity underlying map is
second projection. The normalized ring map equations, direct/inverse coherence,
exact covering-family iff, unique normalized ρ, empty-space and identity cases
are preserved. The graph-counit condition is the source's precise adjunction
normalization. The new ownership node contains definitions only, without any
existence theorem. No `STATEMENT-DISPUTED` issue was found.

The repair dry run requested the current schema's required `import_flags` key on
the new definition node (schema update 2026-10-23); added its empty list.

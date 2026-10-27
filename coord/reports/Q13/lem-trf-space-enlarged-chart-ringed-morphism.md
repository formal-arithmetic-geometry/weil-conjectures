## Worker report

The module `Sheaf.AlgebraicGeometry.EnlargedChartRingedMorphism` states
`AlgebraicGeometry.AlgebraicSpace.enlarged_chart_ringed_morphism`. Its only
postponed proof is that theorem. The four supporting declarations are actual
abbreviations/constructions or a proposition with an explicit formula, with no
postponed data. The node's mathematical statement is unchanged.

Hypotheses and objects, individually:

- `S : Scheme.{u}` is the arbitrary base scheme; `X Y : AlgebraicSpace S` and
  `f : X ⟶ Y` impose no representability, étaleness or surjectivity on f.
- The existing `EnlargedEtaleSite`, `enlargedEtalePrecoverage`, and
  `enlargedEtaleTopology` are precisely the objects, all over-maps, and jointly
  surjective chartwise étale covers in the node. `enlargedSchemeInclusion` is the
  existing Yoneda scheme-object inclusion. These notions are not copied.
- `RX`, `RY : Sheaf ... CommRingCat.{u}` are arbitrary commutative-ring sheaves,
  not the chosen `enlargedStructureSheaf`. `chartNormalizedRing` only forgets
  commutativity. `eX`, `eY` are the specified restriction isomorphisms to the
  actual structure sheaves, whose source is explicit global sections.
  A ring isomorphism between commutative rings is automatically an isomorphism
  of commutative rings; using RingCat here matches the existing structureSheaf
  API without weakening the normalization.
- Sites have objects and arrows in `u+1`. Sheaves of sets use `max (u+1) w`.
  There is no equality imposed between scheme/coefficient and site universes.
  `chartNormalizedLiftedRing` reuses the existing coefficient transport: its
  sections are ULift of the original ring, restrictions act through down/up,
  and no arbitrary ring or map is selected. The two landed definition nodes
  for this transport and the universe-general ringed-topos interface are added
  to stmt_deps under brief-stage2 §5 (landed nodes may be added).

Conclusion clauses, individually:

1. `PreservesFiniteLimits (enlargedBaseChange f)` states finite-limit
   preservation for the actual sheaf-fibre-product functor, including its
   published action on arrows.
2. `∀ V P, P ∈ ... → P.map ... ∈ ...` states covering preservation for every
   covering presieve. The next `IsContinuous` conjunct states continuity.
3. `∃! α : RY ⟶ (enlargedDirectImage f CommRingCat).obj RX, ...` gives existence
   and uniqueness on the entire enlarged site. Direct image is literal
   precomposition: its V-value is RX(X ×_Y V).
4. `IsChartNormalizedRingMap` says that for every scheme chart triangle U, V, q
   over f the composite eY inverse, α at V, restriction along the actual
   `enlargedChartLift`, and eX is Γ(q). In particular, it holds on every
   surjective representable étale scheme chart of X ×_Y V, with exactly the
   direction of the two specified isomorphisms required by the node.
   This is the equivalent f-map formulation used verbatim in the proof of
   Stacks 03G8. The node's atlas formula implies this all-triangle version:
   refine the arbitrary triangle by the pullback of an atlas, where the two
   formulas agree, and use the sheaf's separatedness. Conversely the
   all-triangle formula includes all those atlases. Thus no stronger geometric
   hypothesis or conclusion is introduced.
5. Overlap agreement is encoded by the existence of a section over the fibre
   product and functorial restriction. For any overlap square the two composites
   to that fibre product are equal, so its two restrictions agree. Chart
   independence follows because the formula applies to every chart and refers
   to the same α-value. Naturality under every V' → V is the naturality of α
   as a morphism of sheaves; no étaleness is required of an arrow. Ring operations
   (including zero, one, addition, negation and multiplication) are preserved
   by the CommRingCat-valued components of α. These are structural parts of
   the type, not extra assumptions or independently chosen maps.
6. For every normalized α, the theorem supplies a
   `RingedToposMorphismOfUniverses` g. Its `direct` is pinned to the existing
   precomposition functor by hd. Its inverse, adjunction and leftExact fields
   are precisely the required geometric morphism data. Its ringMap preserves
   all ring operations on generalized elements; the supplied additive module
   direct image is the one induced by that ring map.
7. `g.adj.homEquiv _ _ g.ringMap ≫ eqToHom ... =
   chartNormalizedUnderlyingMap f α` pins the adjoint transpose to this very
   α, after the existing faithful ULift. `chartNormalizedUnderlyingMap` is
   obtained by applying ringFunctor and the two forgetful functors to α;
   coefficient transport and precomposition commute definitionally. In
   particular there is no arbitrary structural ring map or mere Nonempty
   geometric isomorphism in place of the canonical one.
8. The final geometric morphism h on the small étale sites has direct image
   `(enlargedSetEquivalence X).inverse ⋙ g.direct ⋙
   (enlargedSetEquivalence Y).functor`. With hd this is exactly the existing
   `enlargedSmallDirectImage f`, i.e. the small étale morphism defined by
   transport in Stacks 03G2(3). The adjoint inverse image is then determined
   up to its canonical adjunction-compatible isomorphism.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `Scheme.Hom`; the former is a locally ringed space with local affine charts,
  the latter a morphism of its locally ringed spaces.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, scheme-test
  `IsEtale`/`IsSurjective`, `EtaleSite`, `structurePresheaf`, `structureSheaf`.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace`,
  `IsChartwiseEtale`, `EnlargedEtaleSite`, `enlargedEtalePrecoverage`,
  `enlargedSchemeInclusion`, `enlargedRestriction`, `enlargedBaseChange`,
  `enlargedDirectImage`, `enlargedChartLift`, `enlargedSetEquivalence`.
- `Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence`:
  `chartwise_etale_permanence` (full eight-conjunct statement read).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`,
  `etale_fibreProduct_isScheme`.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `Precoverage.IsSiteForCoverings` is the recorded site notion.
- `Sheaf.CategoryTheory.Sites.GeometricMorphism`: `GeometricMorphism`.
- `Sheaf.CategoryTheory.RingedToposMorphism`: `RingedToposMorphism` read in
  full, including its generalized-element and induced module fields. Its
  equal-universe specialization cannot apply directly to this site. The
  already-landed `CategoryTheory.RingedToposMorphismOfUniverses` in
  `Sheaf.Paper.SequenceSiteCompletionProjection` is used, with no replacement
  or edit of either dependency record.
- `Sheaf.CategoryTheory.CochainCoefficientUniverseTransport`:
  `SheafOfModules.CochainUniverseTransport.ringFunctor` and `ring`.
- Proof imports: `Sheaf.CategoryTheory.SiteInverseImageTensor`:
  `siteInverseImage_tensor`; `Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects`:
  `Adjunction.liftsGroupRingObjects`. Their signatures and proof docstrings
  were read. The former is a proof-plan input, not an extra smallness
  assumption in this statement. The two other proof-dependency nodes
  `lem-trf-space-enlarged-site-scheme-density` and
  `lem-trf-space-enlarged-atlas-algebraic-extension` presently have no Lean
  record, so there are no recorded modules to import; the already-published
  restriction/extension interfaces in EnlargedEtaleRingedSite supply their
  needed notions here. No missing datum is assumed.
- `def-weil-size-convention` has a convention record and no declaration;
  explicit universe binders render it.

Sources read: local Stacks `spaces-properties.tex`, the complete paragraphs
labelled remark-explain-equivalence (03H7), lemma-functoriality-etale-site
(03G2), and lemma-morphism-ringed-topoi (03G8), including the proofs.
The current blueprint directory was searched for this derived node's id;
there was no direct unit statement for this auxiliary site lemma.

Edge cases checked before writing: identity f (the formula is ordinary identity
pullback), scheme f (ordinary Γ(q)), empty X or V and the zero ring (all
formulas still type and impose no nonzero-section assumption), arbitrary
nonrepresentable f (its fibre product may be a space, and all evaluation is
on the enlarged site), arbitrary normalization automorphisms eX/eY (both are
retained in the formula), every nonsurjective chart triangle and every
surjective atlas, and coefficient/set universes differing. There are no
nonempty-chart, chosen-atlas, finite-cover, representability-of-f, or flatness
hypotheses. No statement dispute or correction.

Searches performed:

- msearch leanfinder: "A morphism of algebraic spaces induces a geometric
  morphism of enlarged etale sites and a unique ring sheaf map normalized by
  scheme chart pullback". Eight hits, all scheme étale categories and their
  permanence; no matching statement.
- msearch loogle: "Functor.IsContinuous, PreservesFiniteLimits". Zero hits;
  endpoint reported unknown identifier Functor.IsContinuous.
- msearch grep: "RingedToposMorphism|IsEnlargedStructuralMap|enlargedBaseChange".
  Zero Mathlib hits.
- rg of the same pattern in lean/WeilConjectures and lean/Sheaf: the enlarged
  site module has the canonical chosen-extension map and its uniqueness,
  but no arbitrary-normalized-extension statement with all clauses here.
  Ringed-topos uses led to the existing independent-universe interface,
  whose owning DAG node was read and reused.
- rg for the exact item id in lean/WeilConjectures: no match. rg for the new
  declaration names in lean/WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json: no conflicting declaration. Similar unrelated
  chartNormalizedModelComparison names were inspected and are distinct.

Validation: scompile.py compiled both sandbox and library-name forms cleanly
(5.8 and 4.8 seconds for the first clean version); final version is compiled
again after adding the explicit transport equality and direct dependency
imports. The initial probe diagnosed the available universe-general
interface. An initial compile's ambiguous forgetful-functor universe was
fixed by writing its universes explicitly. No global build was run.

## Second reading by Q13

Performed a separate clause-by-clause self-review with the node, final module,
and source proofs open. No second agent was started, as the dispatcher's brief
forbids it; the maintainer supplies the independent review.

The review checked RX/RY are arbitrary, eX/eY are specified, f has no hidden
representability assumption, the site functor is the published actual fibre
product, both the cover and continuity clauses are present, α is unique on
all enlarged objects, and the map is normalized on every chart rather than
one selected atlas. It checked the direction of eY.inv/eX.hom against Γ(q),
the exact homEquiv direction for f-sharp, the transport eqToHom direction,
and the small-site morphism's direct-image composite. The small-site clause
was tightened to use g.direct explicitly rather than state only existence
with the preexisting small-direct-image functor. Overlap/naturality/ring
clauses were checked as structural consequences of the stated morphism and
universal chart formula. All helper data is explicit and all universes and
variables are bound with autoImplicit false. The theorem's proof alone is
sorry. No dependency record, source file, target or blueprint unit is changed.

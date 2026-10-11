## Worker report

The module states `AlgebraicGeometry.etale_restriction_pullback_unit` in
`lean/Sheaf/Paper/EtaleRestrictionPullbackUnit.lean` (as repaired in M1's second reading
below; the first draft's arbitrary section types are gone). The square is `g`, `p`, `g'`,
`p'` with `hcomm`; `ι : W' ⟶ pullback p g` with `hι₁`, `hι₂` and `[IsIso ι]` is the
cartesian comparison; `[Etale p]` is assumed and `Etale p'` is concluded. For every
`F : Sheaf X.smallEtaleTopology AddCommGrpCat` the conclusion equates the two
abelian-group homomorphisms built from `Etale.upperStar`, the units of
`Etale.upperStarLowerStarAdjunction`, `Etale.upperStarComp` (κ),
`Etale.upperStarIsoLocalizationRestriction` (ρ) and restriction along ι.

## Second reading by M1

The Worker report and earlier second reading describe the original draft and are
superseded by this reading. I opened the node, every statement-dependency record,
the recorded source declarations, and Stacks sites.tex at the labels
lemma-localize-morphism (03CF) and lemma-localize-morphism-strong (03EF).
The Stacks text was read on the server, since this machine has only the literature
indices. Tag 03CF assumes a morphism of sites induced by a continuous functor;
03EF assumes finite limits, continuity, and preservation of finite limits.
Small étale sites and their base-change functor supply these conditions; neither
source adds Noetherian, finite-type, separated, characteristic, or field hypotheses.
The node explicitly supplies the agent-written unit counterpart and its proof.

Object/hypothesis/conclusion checklist (H3):

- Schemes X, Y, W, W': `{X Y W W' : Scheme.{u}}`. Exact.
- Morphisms g:Y→X, p:W→X, g':W'→W, p':W'→Y: the four typed binders. Exact.
- Commutativity: `hcomm : g' ≫ p = p' ≫ g`. Exact, with Lean composition order.
- Induced comparison ι:W'→W×ₓY: the binder `ι` and equations `hι₁`, `hι₂`
  give precisely its projections; uniqueness is the pullback universal property.
  `[IsIso ι]` now supplies the node's cartesian hypothesis. Missing in the draft.
- Étaleness of p: `[hp : Etale p]`. Exact, the recorded Mathlib notion.
- Étaleness of p': `∃ hp' : Etale p', ...` asserts this conclusion rather than
  assuming it. Proof irrelevance makes the following identity independent of hp'.
- Small étale objects: `w`, `w'` are the identity objects of W and W'; `wx` is
  (W,p); `wy'` is (W',p'). Base change of wx along g is the node's
  (W×ₓY,pr₂), through `MorphismProperty.Over.pullback @Etale ⊤ g`.
  `iotaSite` is the same ι as a morphism in Y.Etale, using `hι₂`.
  It is an isomorphism there since ι is, with the inverse also over Y.
- Abelian sheaf F on X: `∀ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u+1}`,
  expressed through the local abbreviation A. The draft instead used arbitrary
  types for F and its sections, so did not quantify over abelian sheaves at all.
- Inverse images: `pF`, `gF`, `K` use the recorded `Etale.upperStar`, not
  independent section types; K is g'⁻¹p⁻¹F on W'. Exact.
- Direct images and their units: components of
  `Etale.upperStarLowerStarAdjunction A g'` at pF and w, and of the analogous
  adjunction for g at F and wx. These have exactly the node's section domains
  and fibre-product targets because `Etale.lowerStar` is precomposition by
  `MorphismProperty.Over.pullback`. The previous arbitrary eta functions are gone.
- Identification Γ(W,g'_*K) with K(W'): `theta` is the site morphism with
  underlying scheme map `(g',id)` into W×_W W'; `K.obj.map theta.op` is exactly
  the node's specified identification. It is essential and was absent before.
- The two restriction comparisons: `rhoF`, `rhoG` are components of the recorded
  `Etale.upperStarIsoLocalizationRestriction`, at F and gF respectively, not
  arbitrary functions. `eW` and `eW'` remove only the identity composites in
  structure maps; their underlying scheme isomorphisms are identities.
- κ: `(Etale.upperStarComp A g' p).inv.app F` followed by
  `(Etale.upperStarComp A p' g (g' ≫ p) hcomm).hom.app F`. The source comparison
  points opposite to the node's c, so these directions give exactly c_g,p'⁻¹ c_p,g'.
  hcomm identifies the two composite morphisms. No independent κ is assumed.
- Restriction along ι: `gF.obj.map iotaSite.op`, the actual sheaf restriction.
- Equality for every a: the conclusion equates the two abelian-group
  homomorphisms with domain pF(w) and codomain gF(wy'). This is equivalent,
  by extensionality of group homomorphisms, to the node's displayed identity
  for every a in Γ(W,p⁻¹F). The left route is ηg', θ, κ, ρgF, identity transport;
  the right route is ρF, identity transport, ηg, restriction along ι. Exact.

Dependency audit (H4/H13): Mathlib Scheme/Hom, Etale, pullback/fst/snd/lift,
Scheme.smallEtaleTopology and Sheaf were opened at their definitions. The
base-change functor and its finite-limit preservation are the recorded
MorphismProperty.Over.pullback and its instance in Limits/MorphismProperty.
In WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs I read lowerStar,
upperStar, upperStarLowerStarAdjunction, lowerStarComp and upperStarComp,
including the conjugate-adjunction construction of the last comparison.
In LowerShriek.OpenImmersion.Defs I read localizationRestriction,
localizationRestrictionLowerStarAdjunction, and upperStarIsoLocalizationRestriction.
Despite that module's filename, these declarations require only Etale f, not
Mono f or an open immersion; their signatures supply exactly the general
étale comparison needed here. No missing definition, private notion, new node,
or dependency module is needed. The new imports use these declarations directly.

Edge cases: empty schemes are allowed, as is the zero abelian sheaf; there is no
nonempty or inhabited assumption on schemes or sections. The identity is an
equality of group homomorphisms, so includes zero sections. No indexed family,
integer n, field, or coefficient characteristic occurs. Universe u is bound;
schemes are arbitrary Scheme.{u} and coefficients use the project's recorded
AddCommGrpCat.{u+1} convention for small étale sheaves (site morphisms have
universe u+1). No additional size instance is assumed. All local objects and
proof binders are bound explicitly; server compilation uses relaxedAutoImplicit=false.

Independent searches: msearch.py leanfinder query "etale sheaf pullback unit
naturality cartesian square localization restriction" returned module-pullback
and topological-stalk lemmas, not this statement. Loogle query
"CategoryTheory.Adjunction.leftAdjointUniq" returned the generic uniqueness
comparison and its unit/counit lemmas; these explain the existing restriction
comparison but do not state the cartesian étale section identity. LeanSearch
query "The unit of inverse image of abelian etale sheaves commutes with restriction
to an etale scheme in a cartesian square" returned HTTP Internal Server Error,
recorded as unavailable rather than a negative result. msearch grep for
"localization.*unit|unit.*localization|Beck.Chevalley" in CategoryTheory/Sites
found no match. Independent rg of WeilConjectures, lean/Sheaf, the upstream
name index, Mathlib CategoryTheory/Sites and AlgebraicGeometry/Sites for
localization/unit identities and the proposed name found no exact statement.
ProEtale/UpperLowerStar/InternalHom has a unit-component computation in another
site, not this two-factorization compatibility; no duplicate is introduced.

Repairs (H3/H8/H9): added the missing IsIso hypothesis; replaced arbitrary
section types/functions with the actual sheaf functors and canonical maps;
restored θ and the identity structure-map transports; expanded the docstring
to carry all five proof steps and their dependency names; added the standard
header and the imports needed by the real statement. The node's mathematical
statement and dependencies are unchanged, and lean.statement was synchronized
verbatim with the repaired signature. No definitions with sorry were introduced;
the sole theorem still has proof `by sorry`, as stage 2 requires.

Validation: the repaired module compiled cleanly on the server (2.1 s), with
no errors or warnings. No library build or local source-checkout build was run.

## Reviewer fix (R-erp1009, stage 2)

The superseded Worker report and earlier second reading (which described a draft with
arbitrary section types) were removed. The étale objects w, w', wx, wy' are now written
with Mathlib's constructor `Scheme.Etale.mk` (an abbrev for the same
`MorphismProperty.Over.mk ⊤ _ inferInstance` term), as the other landed modules do for
sections at `op (Scheme.Etale.mk (𝟙 _))`; the statement is otherwise unchanged and
recompiles cleanly.

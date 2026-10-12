module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Continuous
import Sheaf.CategoryTheory.SiteEquivalenceMorphismOfSites
import Sheaf.CategoryTheory.Sites.CohomologyRightDerivedSections

@[expose] public section

universe u
namespace CategoryTheory

/-- Source: Stacks Project, Sites, Lemma 03A0 (equivalence of topoi), Homology,
Lemma 015Z (functors with exact left adjoints preserve injectives), and Cohomology on Sites,
Section 01FT and Lemmas 03F3, 03YU (injective-resolution computation over objects):
https://stacks.math.columbia.edu/tag/03A0, https://stacks.math.columbia.edu/tag/015Z,
https://stacks.math.columbia.edu/tag/01FT, https://stacks.math.columbia.edu/tag/03F3,
https://stacks.math.columbia.edu/tag/03YU. The argument specializes these constructions
as in lem-weil-pbc-etale-cohomology-invariance-under-site-equivalence, steps 1--3.
(blueprint: cohomology-site-equivalence-fixed-degree)

Proof: Apply site_equivalence_is_morphism_of_sites to J, K, e.functor, e.inverse,
e.unitIso, e.counitIso and hcover_iff. It supplies continuity in both directions and
quasi-inverse functors on abelian sheaves. The forward sheaf functor E is precisely
precomposition with e.inverse, the pushforward in the conclusion using hi. Continuity
is a proposition, so the supplied continuity proof and hi give the same functor by
proof irrelevance. Its quasi-inverse is precomposition with e.functor; their composite
isomorphisms come from the unit and counit. E is additive since sheaf morphisms add
sectionwise. As an equivalence it preserves kernels and cokernels, hence is exact.
Its exact quasi-inverse is a left adjoint, so 015Z gives preservation of injectives.
These are the clauses of lem-weil-pbc-equivalence-injective-resolutions.

For an abelian sheaf G choose an injective resolution G to I. Such resolutions exist
by lem-weil-pbc-site-sheaves-enough-injectives for the small site. Applying E termwise
therefore gives an injective resolution of E(G). Additivity also transports chain
maps, equations defining lifts, and homotopies. At W the transported section complex
has terms I^n(e.inverse(e(W))). The restriction map I^n(e.unitIso.hom.app W) gives an
isomorphism to I^n(W), with inverse induced by the inverse unit component. Naturality
of each differential and the augmentation makes these maps a complex isomorphism
compatible with the augmentation.

Taking degree-q cohomology of the inverse of this complex isomorphism gives the map
from H'(G,q,W) to H'(E(G),q,e(W)). The Lean H' is Ext from the sheafified free abelian
representable, not a definition by resolutions: the sheafification/free adjunctions
and Yoneda identify Hom from this object with sections at W. The comparison
lem-sc-site-cohomology-right-derived-sections identifies its Ext cohomology naturally
with derived sections, so the section-complex computation applies to the exact
cohomologyPresheafFunctor in the signature, including q = 0.

For a morphism G to G', lift it to a map of injective resolutions. The termwise unit
maps commute with that lift because its components are sheaf morphisms. The induced
cohomology square therefore commutes; independence of lifts follows because homotopic
lifts induce the same map, as in lem-weil-pbc-derived-functor-map-via-lift. For a morphism
W' to W, naturality of the unit makes the corresponding restriction square commute
in every degree, hence on cohomology. The representation of sections by free sheafified
representables is likewise natural in W, so these squares are the restrictions of
cohomologyPresheafFunctor itself. Thus for each G the objectwise isomorphisms assemble
into an isomorphism of presheaves on C, and the squares in G assemble these into the
natural isomorphism of functors asserted by Nonempty. The last whiskering evaluates
at e(W) and on e of each object morphism, exactly as in those restriction squares. -/
theorem cohomology_presheaf_iso_fixed_degree
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : Precoverage C) (K : Precoverage D) [J.HasIsos]
    [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    [K.HasIsos] [K.IsStableUnderComposition] [K.IsStableUnderBaseChange]
    [K.HasPullbacks]
    [HasSheafify J.toGrothendieck AddCommGrpCat.{u}]
    [HasSheafify K.toGrothendieck AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf J.toGrothendieck AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf K.toGrothendieck AddCommGrpCat.{u})]
    (e : C ≌ D)
    (hcover_iff : ∀ (W : C) (R : Presieve W), R ∈ J W ↔
      R.map e.functor ∈ K (e.functor.obj W))
    (hi : e.inverse.IsContinuous K.toGrothendieck J.toGrothendieck)
    (q : ℕ) : Nonempty
      (Sheaf.cohomologyPresheafFunctor J.toGrothendieck q ≅
        e.inverse.sheafPushforwardContinuous AddCommGrpCat.{u}
          K.toGrothendieck J.toGrothendieck ⋙
        Sheaf.cohomologyPresheafFunctor K.toGrothendieck q ⋙
        (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ AddCommGrpCat.{u}).obj e.functor.op) := by
  sorry

end CategoryTheory

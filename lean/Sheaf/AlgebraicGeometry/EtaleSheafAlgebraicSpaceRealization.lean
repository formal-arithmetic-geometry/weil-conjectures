/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Mathlib.CategoryTheory.Sites.Whiskering
import Sheaf.AlgebraicGeometry.EtaleDescentThroughSourceCover
import Sheaf.AlgebraicGeometry.EtaleRelationQuotient
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import WeilConjectures.AlgebraicGeometry.EtaleSubsheafFinalOpen
import Sheaf.AlgebraicGeometry.FpqcFinerThanEtale
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import Sheaf.AlgebraicGeometry.WeaklyEtaleStability
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFpqcSheaf
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence

/-!
# Algebraic-space realization of étale sheaves

Source: Stacks Project, Tag 0GF6 and its size footnote; Bhatt--Scholze, Lemmas 5.1.1
and 5.4.1 (blueprint: lem-a1-etale-sheaf-algebraic-space-realization).

Algebraic spaces use the existing fppf-sheaf definition. Their section sets are in
`Type u`. For the published comparison adjunction they are lifted to `Type (u + 1)`.
The large étale realization is restriction of the same pro-étale Hom sheaf, so its
values are exactly the lifted étale section sets. The comparison is the counit;
its adjoint is the identity on these Hom sets.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Chartwise étaleness over a scheme: every representable étale scheme chart has
étale structure map. Source: Stacks, Tags 03FS and 0GF6
(blueprint: lem-a1-etale-sheaf-algebraic-space-realization). -/
def IsEtaleOver {X : Scheme.{u}} (E : AlgebraicSpace X) : Prop :=
  ∀ (T : Over X) (a : yoneda.obj T ⟶ E.obj.obj), IsEtale a → Etale T.hom

/-- Étale algebraic spaces over `X`, with all morphisms over `X`.
Source: Stacks, Tag 0GF6
(blueprint: lem-a1-etale-sheaf-algebraic-space-realization). -/
abbrev EtaleSpaces (X : Scheme.{u}) :=
  ObjectProperty.FullSubcategory (IsEtaleOver (X := X))

private theorem isSheafFor_fpqc_family {X : Scheme.{u}} (E : AlgebraicSpace X)
    (T : Over X) {I : Type (u + 1)} (Z : I → Over X) (f : ∀ i, Z i ⟶ T)
    (hf : Presieve.ofArrows (fun i ↦ (Z i).left) (fun i ↦ (f i).left) ∈
      Scheme.fpqcPrecoverage T.left) :
    Presieve.IsSheafFor E.obj.obj (Presieve.ofArrows Z f) := by
  let W (i : I) : Over X := Over.mk ((f i).left ≫ T.hom)
  let e (i : I) : W i ≅ Z i := Over.isoMk (Iso.refl _) (by simp [W])
  let g (i : I) : W i ⟶ T := Over.homMk (f i).left rfl
  have he (i : I) : (e i).hom ≫ f i = g i := by
    ext
    simp [e, g]
  rw [← Presieve.isSheafFor_ofArrows_comp_iff f e]
  simp_rw [he]
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  apply (existsUnique_section_and_eq_of_fpqc_cover E T
    (fun i ↦ (Z i).left) (fun i ↦ (f i).left) hf).1 x
  intro i j
  let P : Over X :=
    Over.mk (pullback.fst (f i).left (f j).left ≫ (f i).left ≫ T.hom)
  let p : P ⟶ W i := Over.homMk (pullback.fst (f i).left (f j).left) rfl
  let q : P ⟶ W j := Over.homMk (pullback.snd (f i).left (f j).left)
    (pullback.condition_assoc (f := (f i).left) (g := (f j).left) T.hom).symm
  exact hx i j P p q (by ext; exact pullback.condition)

set_option backward.isDefEq.respectTransparency.types false in
/-- Both Hom presheaves are sheaves. Source: Stacks, Tag 04P2 and the coverings
in Bhatt--Scholze, Section 4.1
(blueprint: lem-a1-etale-sheaf-algebraic-space-realization).

Proof: the algebraic space is an fpqc sheaf (lem-a1-algebraic-space-fpqc-sheaf).
Every étale covering is fpqc (lem-weil-pbc-fpqc-finer-than-etale), and every
pro-étale covering is fpqc by def-weil-pbc-proetale-site. Apply the fpqc gluing
and uniqueness axioms to the same underlying scheme families. The lift of sets
preserves this unique gluing condition. These are Steps 6 and 9 of the node. -/
theorem realizationPresheaves_isSheaf {X : Scheme.{u}} (E : AlgebraicSpace X) :
    Presheaf.IsSheaf X.smallEtaleTopology ((Scheme.Etale.forget X).op ⋙ E.obj.obj) ∧
    Presheaf.IsSheaf (Scheme.ProEt.topology X)
      ((Scheme.ProEt.forget X).op ⋙ E.obj.obj ⋙ uliftFunctor.{u + 1, u}) := by
  have hfpqc : Presheaf.IsSheaf (Scheme.fpqcTopology.over X) E.obj.obj := by
    rw [isSheaf_iff_isSheaf_of_type,
      over_toGrothendieck_eq_toGrothendieck_comap_forget,
      Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
    intro T R hR
    obtain ⟨I, Z, f, rfl⟩ := R.exists_eq_ofArrows
    apply isSheafFor_fpqc_family E T Z f
    simpa only [Precoverage.mem_comap_iff, Presieve.map_ofArrows,
      Over.forget_obj, Over.forget_map] using hR
  let : RepresentablyFlat (Scheme.Etale.forget X) := flat_of_preservesFiniteLimits _
  let : (Scheme.Etale.forget X).LocallyCoverDense (Scheme.etaleTopology.over X) :=
    Scheme.locallyCoverDense_of_le X le_rfl
  have : (Scheme.Etale.forget X).IsContinuous X.smallEtaleTopology
      (Scheme.etaleTopology.over X) := by
    rw [Functor.isContinuous_iff_coverPreserving]
    exact Functor.coverPreserving_restrictedTopology (Scheme.Etale.forget X)
      (Scheme.etaleTopology.over X)
  constructor
  · apply (Scheme.Etale.forget X).op_comp_isSheaf_of_isSheaf
      X.smallEtaleTopology (Scheme.etaleTopology.over X) E.obj.obj
    apply hfpqc.of_le
    intro T R hR
    exact Scheme.proetaleTopology_le_fpqcTopology _
      (Scheme.etaleTopology_le_proetaleTopology _ hR)
  · apply Presheaf.isSheaf_comp_of_isSheaf (Scheme.ProEt.topology X)
      ((Scheme.ProEt.forget X).op ⋙ E.obj.obj) uliftFunctor
    apply (Scheme.ProEt.forget X).op_comp_isSheaf_of_isSheaf
      (Scheme.ProEt.topology X) (Scheme.proetaleTopology.over X) E.obj.obj
    exact hfpqc.of_le (fun _ _ hR ↦ Scheme.proetaleTopology_le_fpqcTopology _ hR)

/-- The actual étale Hom sheaf, functorial by postcomposition in the algebraic space.
Source: Stacks, Tag 0GF6
(blueprint: lem-a1-etale-sheaf-algebraic-space-realization). -/
def etaleRealizationFunctor (X : Scheme.{u}) :
    EtaleSpaces X ⥤ Sheaf X.smallEtaleTopology (Type u) where
  obj E := ⟨(Scheme.Etale.forget X).op ⋙ E.obj.obj.obj,
    (realizationPresheaves_isSheaf E.obj).1⟩
  map f := ⟨Functor.whiskerLeft (Scheme.Etale.forget X).op f.hom.hom.hom⟩

/-- The lifted pro-étale Hom sheaf, with the same postcomposition maps.
Source: Bhatt--Scholze, Section 5.1, applied to the presentation in Stacks 0GF6
(blueprint: lem-a1-etale-sheaf-algebraic-space-realization). -/
def proEtaleRealizationFunctor (X : Scheme.{u}) :
    EtaleSpaces X ⥤ Sheaf (Scheme.ProEt.topology X) (Type (u + 1)) where
  obj E := ⟨(Scheme.ProEt.forget X).op ⋙ E.obj.obj.obj ⋙ uliftFunctor.{u + 1, u},
    (realizationPresheaves_isSheaf E.obj).2⟩
  map f := ⟨Functor.whiskerRight
    (Functor.whiskerLeft (Scheme.ProEt.forget X).op f.hom.hom.hom) uliftFunctor⟩

/-- The étale Hom sheaf in the universe of the published comparison adjunction.
Restriction along `toProEt` leaves schemes and arrows unchanged.
Source: Bhatt--Scholze, Section 5.1
(blueprint: lem-a1-etale-sheaf-algebraic-space-realization). -/
def largeEtaleRealizationFunctor (X : Scheme.{u}) :
    EtaleSpaces X ⥤ Sheaf X.smallEtaleTopology (Type (u + 1)) :=
  proEtaleRealizationFunctor X ⋙ (Scheme.toProEt X).sheafPushforwardContinuous
    (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X)

/-- The large realization is exactly the universe lift of the small one.
Source: the size convention in Stacks, Tag 0GF6
(blueprint: lem-a1-etale-sheaf-algebraic-space-realization). -/
def largeEtaleRealizationLiftIso (X : Scheme.{u}) :
    etaleRealizationFunctor X ⋙ sheafCompose X.smallEtaleTopology uliftFunctor.{u + 1, u} ≅
      largeEtaleRealizationFunctor X :=
  Iso.refl _

/-- The canonical comparison: its adjoint is the identity on the restricted Hom sheaf.
It is a natural transformation in the algebraic space, constructed from the counit.
Source: Bhatt--Scholze, Section 5.1
(blueprint: lem-a1-etale-sheaf-algebraic-space-realization). -/
def etaleProEtaleRealizationComparison (X : Scheme.{u}) :
    largeEtaleRealizationFunctor X ⋙
      Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt X)
        (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X) ⟶
    proEtaleRealizationFunctor X :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (proEtaleRealizationFunctor X) (Scheme.proEtaleSiteComparison X).counit ≫
    (Functor.rightUnitor _).hom

/-- The actual functor of points of `E ×_X U`, before bundling it as an algebraic space.
Source: Stacks, Tag 03I4(6); it sends `T → U` to `Hom_X(T,E)`
(blueprint: lem-a1-etale-sheaf-algebraic-space-realization). -/
def realizationBaseChangeSheaf {X U : Scheme.{u}} (f : U ⟶ X) (E : EtaleSpaces X) :
    Sheaf (Scheme.fppfTopology.over U) (Type u) :=
  ((Over.map f).sheafPushforwardContinuous (Type u)
    (Scheme.fppfTopology.over U) (Scheme.fppfTopology.over X)).obj E.obj.obj

/-- The explicit base-change sheaf is algebraic and étale over the new base.
Source: Stacks, Tags 03I4(6), 03FS and 03FV
(blueprint: lem-a1-etale-sheaf-algebraic-space-realization).

Proof (Step 12): its diagonal is represented by the same fibre products of test
schemes as the diagonal of `E` (def-trf-algebraic-space). Base change an étale
surjective atlas `A → E` to `A ×_X U`; every test pullback is `A ×_E T → T`,
still surjective étale. This gives an algebraic space over `U`. Chartwise étaleness
is stable under base change by lem-trf-space-chartwise-etale-permanence, using
lem-trf-space-fibre-products-etale-covers for the scheme fibre products. -/
theorem realizationBaseChange_isEtaleSpace {X U : Scheme.{u}} (f : U ⟶ X)
    (E : EtaleSpaces X) :
    IsAlgebraicSpace (realizationBaseChangeSheaf f E) ∧
      ∀ (T : Over U) (a : yoneda.obj T ⟶ (realizationBaseChangeSheaf f E).obj),
        IsEtale a → Etale T.hom := by
  sorry

/-- The base change uses the explicit sheaf of points, rather than an existence choice.
Source: Stacks, Tag 03I4(6)
(blueprint: lem-a1-etale-sheaf-algebraic-space-realization). -/
def realizationBaseChange {X U : Scheme.{u}} (f : U ⟶ X) (E : EtaleSpaces X) :
    EtaleSpaces U :=
  ⟨⟨realizationBaseChangeSheaf f E, (realizationBaseChange_isEtaleSpace f E).1⟩,
    (realizationBaseChange_isEtaleSpace f E).2⟩

/-- Restriction to `U_proet`, identified with the slice at a weakly étale `U → X`.
Source: Bhatt--Scholze, Lemma 5.4.1; weakly étale composition and cancellation
(blueprint: lem-a1-etale-sheaf-algebraic-space-realization). -/
def proEtaleRealizationRestrictionFunctor {X U : Scheme.{u}} (f : U ⟶ X)
    (hf : WeaklyEtale f) :
    Sheaf (Scheme.ProEt.topology X) (Type (u + 1)) ⥤
      Sheaf (Scheme.ProEt.topology U) (Type (u + 1)) :=
  (MorphismProperty.Over.map ⊤ hf).sheafPushforwardContinuous (Type (u + 1))
    (Scheme.ProEt.topology U) (Scheme.ProEt.topology X)

/-- The fibre-product bijection `Hom_X(T,E) = Hom_U(T,E ×_X U)` is the identity on
the displayed section sets; it commutes with every further restriction.
Source: Stacks, Tag 03I4(6); Bhatt--Scholze, Lemma 5.4.1
(blueprint: lem-a1-etale-sheaf-algebraic-space-realization). -/
def proEtaleRealizationRestriction {X U : Scheme.{u}} (f : U ⟶ X)
    (hf : WeaklyEtale f) (E : EtaleSpaces X) :
    (proEtaleRealizationRestrictionFunctor f hf).obj
        ((proEtaleRealizationFunctor X).obj E) ≅
      (proEtaleRealizationFunctor U).obj (realizationBaseChange f E) :=
  Iso.refl _

/-- The restricted comparison is the comparison over `U`, followed by the inverse of
the fibre-product identification. Source: Bhatt--Scholze, Lemma 5.4.1
(blueprint: lem-a1-etale-sheaf-algebraic-space-realization). -/
def restrictedRealizationComparison {X U : Scheme.{u}} (f : U ⟶ X)
    (hf : WeaklyEtale f) (E : EtaleSpaces X) :
    (Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt U)
      (Type (u + 1)) U.smallEtaleTopology (Scheme.ProEt.topology U)).obj
        ((largeEtaleRealizationFunctor U).obj (realizationBaseChange f E)) ⟶
      (proEtaleRealizationRestrictionFunctor f hf).obj
        ((proEtaleRealizationFunctor X).obj E) :=
  (etaleProEtaleRealizationComparison U).app (realizationBaseChange f E) ≫
    (proEtaleRealizationRestriction f hf E).inv

/-- Étale algebraic spaces are exactly étale sheaves, and their canonical pro-étale
comparison and its restrictions are isomorphisms.
Source: Stacks, Tag 0GF6 with its size footnote; Bhatt--Scholze, Section 5.1 and
Lemma 5.4.1 (blueprint: lem-a1-etale-sheaf-algebraic-space-realization).

Proof:
1. Choose representable generators with sections, and form their scheme coproduct
   `V`, in the enlarged universe of def-weil-size-convention. Yoneda and
   lem-weil-pbc-small-etale-representable-presheaf-sheaf give `h_V → F`, an epi.
   Use lem-weil-pbc-scheme-coproduct-family and lem-weil-pbc-etale-local-on-source.
2. On `V ×_X V`, equality of the two universal sections is a subsheaf of the final
   sheaf. By lem-weil-pbc-etale-subsheaf-final-open it is represented by an open `R`.
   The chartwise permanence lemma shows `h_R = h_V ×_F h_V` on étale tests.
3. Yoneda gives reflexivity, symmetry and composition as scheme maps. The open
   immersion makes the relation monomorphic. The epi kernel-pair coequalizer lemma
   identifies its quotient with `F`.
4. Apply lem-trf-etale-relation-quotient to obtain the algebraic space `E = V/R`,
   its atlas, its kernel pair and étale-local lifting of sections.
5. For any étale chart `B → E`, the atlas pullback is étale surjective over `B`
   and étale over `X`. Apply lem-trf-etale-descent-through-source-cover to prove
   `B → X` étale, which is precisely `IsEtaleOver E`.
6. Fpqc descent and lem-weil-pbc-fpqc-finer-than-etale make `h_E` a sheaf. Local
   atlas lifting makes `h_V → h_E` epi, with kernel pair `h_R`. The two coequalizer
   universal properties give `h_E ≅ F`, proving essential surjectivity.
7. For any étale space choose a scheme atlas `A` and scheme kernel pair `B`.
   Local lifts present the space by `h_B ⇉ h_A` on both the small étale and big
   fppf sites (the epi kernel-pair coequalizer lemma).
8. Given a transformation of small étale Hom sheaves, Yoneda gives a map from `A`.
   Naturality on `B` makes it descend uniquely on the big fppf site. Atlas
   epimorphy shows that its restriction is the original transformation. This proves
   full faithfulness and therefore the equivalence of the displayed functor.
9. Fpqc descent gives the pro-étale Hom sheaf. Pulling back the atlas along a
   section over a weakly étale test scheme gives an étale surjective, hence fpqc
   covering with a lift. Weakly étale stability keeps it in the site. Thus its
   atlas has the same kernel-pair coequalizer on the pro-étale site.
10. The comparison adjunction and Yoneda identify inverse images of scheme
    representables with their pro-étale Hom sheaves. Being a left adjoint, inverse
    image preserves the atlas coequalizer (def-weil-pbc-category-colimit).
11. The identity on restricted Hom sections has the canonical adjoint given here
    by the counit. The preceding coequalizers show this comparison is an
    isomorphism, naturally in the space; no abstract isomorphism is chosen.
12. The explicit base-change construction above is étale over `U`. Weakly étale
    composition and cancellation identify `U_proet` with `X_proet/U`, with the
    same fpqc covers. The identity on `Hom_X(T,E) = Hom_U(T,E_U)` identifies the
    restricted Hom sheaf with the base-changed one. Apply Steps 9--11 over `U`.
-/
theorem etaleSheaf_algebraicSpace_realization (X : Scheme.{u}) :
    (etaleRealizationFunctor X).IsEquivalence ∧
      IsIso (etaleProEtaleRealizationComparison X) ∧
      ∀ (U : Scheme.{u}) (f : U ⟶ X) (hf : WeaklyEtale f) (E : EtaleSpaces X),
        IsIso (restrictedRealizationComparison f hf E) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace

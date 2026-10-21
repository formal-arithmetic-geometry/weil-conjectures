/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O2
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Algebraic transport of unit-normalized site composition and identity

Source: Stacks Project, Sites, Tags 03CB, 00VE, 00WX, 00WH and 00YV;
Modules on Sites, Tag 03D2 (blueprint: lem-pur-site-algebraic-composition-unit).

The composite inverse image is the specified comma-colimit/sheafification construction.
Its comparison is obtained from the specified adjunctions, without choosing another unit.
The predicates below spell out the algebraic clauses using the recorded presentations;
they do not choose new ring or module structures.
-/

@[expose] public section

universe uC vC uD vD uE vE w s

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

/-- The specified inverse image for the composite site functor. The continuity proof is
Mathlib's composition lemma; the functor is exactly left Kan extension then sheafification.
Source: Stacks Project, Sites, Tags 03CB and 00WX
(blueprint: lem-pur-site-algebraic-composition-unit). -/
noncomputable def siteAlgebraicCompositePullback
    {C : Type uC} {D : Type uD} {E : Type uE}
    [Category.{vC} C] [Category.{vD} D] [Category.{vE} E]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (L : GrothendieckTopology E) (v : C ⥤ D) (u : D ⥤ E)
    [v.IsContinuous J K] [u.IsContinuous K L] :=
  letI := Functor.isContinuous_comp v u J K L
  sheafPullback (v ⋙ u) (Type (max uC vC uD vD uE vE w)) J L

/-- The specified composite-site adjunction, with right adjoint written as successive
precomposition. These precomposition functors are definitionally identical.
Source: Stacks Project, Sites, Tags 03CB, 00VE, 00WX and 00WH
(blueprint: lem-pur-site-algebraic-composition-unit). -/
noncomputable def siteAlgebraicCompositeAdjunction
    {C : Type uC} {D : Type uD} {E : Type uE}
    [Category.{vC} C] [Category.{vD} D] [Category.{vE} E]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (L : GrothendieckTopology E) (v : C ⥤ D) (u : D ⥤ E)
    [v.IsContinuous J K] [u.IsContinuous K L] :
    siteAlgebraicCompositePullback.{uC, vC, uD, vD, uE, vE, w} J K L v u ⊣
      u.sheafPushforwardContinuous (Type (max uC vC uD vD uE vE w)) K L ⋙
        v.sheafPushforwardContinuous (Type (max uC vC uD vD uE vE w)) J K :=
  letI := Functor.isContinuous_comp v u J K L
  sheafAdjunctionContinuous (v ⋙ u) (Type (max uC vC uD vD uE vE w)) J L

/-- The comparison determined by the specified units, directed from composite to iterated
inverse image. No existence choice or arbitrary natural isomorphism is used.
Source: Stacks Project, Sites, Tag 03CB, with the unit normalization of Tags 00VE and 00WX
(blueprint: lem-pur-site-algebraic-composition-unit). -/
noncomputable def siteAlgebraicCompositionIso
    {C : Type uC} {D : Type uD} {E : Type uE}
    [Category.{vC} C] [Category.{vD} D] [Category.{vE} E]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (L : GrothendieckTopology E) (v : C ⥤ D) (u : D ⥤ E)
    [v.IsContinuous J K] [u.IsContinuous K L] :
    siteAlgebraicCompositePullback.{uC, vC, uD, vD, uE, vE, w} J K L v u ≅
      sheafPullback v (Type (max uC vC uD vD uE vE w)) J K ⋙
        sheafPullback u (Type (max uC vC uD vD uE vE w)) K L :=
  (siteAlgebraicCompositeAdjunction.{uC, vC, uD, vD, uE, vE, w} J K L v u).leftAdjointUniq
    ((sheafAdjunctionContinuous v (Type (max uC vC uD vD uE vE w)) J K).comp
      (sheafAdjunctionContinuous u (Type (max uC vC uD vD uE vE w)) K L))

/-- The ring and module clauses for a comparison of algebraic inverse-image presentations.
The ring isomorphism and additive natural isomorphism have precisely the prescribed
underlying maps; semilinearity is required on every section. Isomorphisms of ring sheaves
preserve zero, one, addition and multiplication; additive sheaf isomorphisms preserve zero
and addition. The natural-isomorphism type includes naturality on all module morphisms.
Source: Stacks Project, Sites, Tag 00YV, and Modules on Sites, Tag 03D2
(blueprint: lem-pur-site-algebraic-composition-unit). -/
def SiteAlgebraicComparison
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [J.HasSheafCompose (forget₂ CommRingCat.{s} RingCat.{s})]
    [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{s} ⋙ uliftFunctor.{s, s})]
    [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{s} ⋙ uliftFunctor.{s, s})]
    [K.HasSheafCompose (forget₂ CommRingCat.{s} RingCat.{s})]
    [K.HasSheafCompose (CategoryTheory.forget CommRingCat.{s} ⋙ uliftFunctor.{s, s})]
    [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{s} ⋙ uliftFunctor.{s, s})]
    {L₀ L₁ : Sheaf J (Type s) ⥤ Sheaf K (Type s)} (γ : L₀ ⟶ L₁) : Prop :=
  ∀ (R : Sheaf J CommRingCat.{s}) (R₀ R₁ : Sheaf K CommRingCat.{s})
    (A₀ : SheafOfModules.AlgebraicInverseImageOfUniverses L₀ R R₀)
    (A₁ : SheafOfModules.AlgebraicInverseImageOfUniverses L₁ R R₁),
    ∃ eR : R₀ ≅ R₁,
      (sheafCompose K (CategoryTheory.forget CommRingCat.{s} ⋙ uliftFunctor.{s, s})).map
          eR.hom =
        A₀.ringUnderlying.inv ≫ γ.app _ ≫ A₁.ringUnderlying.hom ∧
      ∃ eM : A₀.modules ⋙ SheafOfModules.toSheaf _ ≅
          A₁.modules ⋙ SheafOfModules.toSheaf _,
        (∀ M : ringedSiteModules.{s} ((sheafCompose J
            (forget₂ CommRingCat.{s} RingCat.{s})).obj R),
          (sheafCompose K (CategoryTheory.forget AddCommGrpCat.{s} ⋙
              uliftFunctor.{s, s})).map (eM.hom.app M) =
            A₀.moduleUnderlying.hom.app M ≫ γ.app _ ≫ A₁.moduleUnderlying.inv.app M) ∧
        (∀ (M : ringedSiteModules.{s} ((sheafCompose J
            (forget₂ CommRingCat.{s} RingCat.{s})).obj R))
          (V : Dᵒᵖ) (a : R₀.obj.obj V) (x : (A₀.modules.obj M).val.obj V),
          (eM.hom.app M).hom.app V (a • x) =
            (@id (R₁.obj.obj V) (eR.hom.hom.app V a)) •
              (@id ((A₁.modules.obj M).val.obj V) ((eM.hom.app M).hom.app V x)))

/-- The algebraic identity-unit clauses, with their underlying maps fixed by the set unit.
Both the ring and module source are the original sheaves, so this also includes the
literal identity case rather than only a comparison between two chosen lifts.
Source: Stacks Project, Sites, Tags 00WX and 00YV, and Modules on Sites, Tag 03D2
(blueprint: lem-pur-site-algebraic-composition-unit). -/
def SiteAlgebraicIdentityUnit
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{s} RingCat.{s})]
    [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{s} ⋙ uliftFunctor.{s, s})]
    [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{s} ⋙ uliftFunctor.{s, s})]
    {I : Sheaf J (Type s) ⥤ Sheaf J (Type s)} (η : 𝟭 _ ⟶ I) : Prop :=
  ∀ (R RI : Sheaf J CommRingCat.{s})
    (A : SheafOfModules.AlgebraicInverseImageOfUniverses I R RI),
    ∃ eR : R ≅ RI,
      (sheafCompose J (CategoryTheory.forget CommRingCat.{s} ⋙ uliftFunctor.{s, s})).map
          eR.hom = η.app _ ≫ A.ringUnderlying.hom ∧
      ∃ eM : SheafOfModules.toSheaf ((sheafCompose J
            (forget₂ CommRingCat.{s} RingCat.{s})).obj R) ≅
          A.modules ⋙ SheafOfModules.toSheaf _,
        (∀ M : ringedSiteModules.{s} ((sheafCompose J
            (forget₂ CommRingCat.{s} RingCat.{s})).obj R),
          (sheafCompose J (CategoryTheory.forget AddCommGrpCat.{s} ⋙
              uliftFunctor.{s, s})).map (eM.hom.app M) =
            η.app _ ≫ A.moduleUnderlying.inv.app M) ∧
        (∀ (M : ringedSiteModules.{s} ((sheafCompose J
            (forget₂ CommRingCat.{s} RingCat.{s})).obj R))
          (V : Cᵒᵖ) (a : R.obj.obj V) (x : M.val.obj V),
          (eM.hom.app M).hom.app V (a • x) =
            (@id (RI.obj.obj V) (eR.hom.hom.app V a)) •
              (@id ((A.modules.obj M).val.obj V) ((eM.hom.app M).hom.app V x)))

/-- The specified compositor is uniquely unit normalized, including on individual sections;
it respects canonical products, terminal objects and the ring/module operation transports.
The identity inverse-image unit is invertible and has the same algebraic compatibilities.

Source: Stacks Project, Sites, Tags 03CB, 00VE, 00WX, 00WH and 00YV;
Modules on Sites, Tag 03D2 (blueprint: lem-pur-site-algebraic-composition-unit).

Proof:
1. Precomposition by v then u is literally precomposition by their composite. The specified
   adjunctions therefore have the same right adjoint. Compose the individual adjunctions
   using def-weil-pbc-composite-adjunction; its unit is eta_v followed by P_v(eta_u).
2. Apply lem-weil-pbc-conjugate-iso-unit-equation to the identity right-adjoint comparison.
   It gives the invertible compositor and uniqueness with the displayed unit normalization.
3. Evaluate that equation at W and s. Conversely, equality at every W and s is equality
   of sheaf morphisms, so the section equation alone gives the same uniqueness.
4. Compose the product equation with each projection and use naturality. The terminal
   equation follows from the unique map to a terminal object. Finite-limit preservation
   makes these canonical comparisons invertible. For the composite functor, successive
   product comparisons have exactly the images of the original projections as components.
5. A transported binary operation o is L(o) after the inverse product comparison, and a
   transported constant is L(e) after the inverse terminal comparison. The previous step
   shows that composite and iterated transports coincide. Naturality of gamma then proves
   preservation of ring addition, multiplication, zero and one. Bijectivity makes this a
   ring-sheaf isomorphism, with precisely the underlying-sheaf comparison recorded here.
6. Apply the same calculation to module addition, zero and scalar action. It gives the
   natural additive comparison and sectionwise semilinearity through the ring comparison.
   Naturality on module morphisms follows from gamma and the presentation identifications
   of def-weil-pbc-algebraic-inverse-image. The modules are exactly those of
   def-weil-sheaf-of-modules-category.
7. Compare the specified identity adjunction with the identity adjunction using the same
   conjugate-unit lemma. Its compositor c satisfies c eta_id = id, so eta_id is c inverse.
   Its product and terminal comparisons are consequently invertible without a further
   finite-limit hypothesis on the identity inverse image.
8. Naturality of eta_id with projections and operation maps gives preservation of the
   ring and module operations, including constants and scalar action. Its already proved
   invertibility yields the asserted ring and natural additive semilinear isomorphisms.
-/
theorem siteAlgebraicCompositionUnit
    {C : Type uC} {D : Type uD} {E : Type uE}
    [Category.{vC} C] [Category.{vD} D] [Category.{vE} E]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (L : GrothendieckTopology E) (v : C ⥤ D) (u : D ⥤ E)
    [v.IsContinuous J K] [u.IsContinuous K L]
    [PreservesFiniteLimits (sheafPullback v
      (Type (max uC vC uD vD uE vE w)) J K)]
    [PreservesFiniteLimits (sheafPullback u
      (Type (max uC vC uD vD uE vE w)) K L)]
    [PreservesFiniteLimits
      (siteAlgebraicCompositePullback.{uC, vC, uD, vD, uE, vE, w} J K L v u)] :
    (∀ H : Sheaf J (Type (max uC vC uD vD uE vE w)),
      (siteAlgebraicCompositeAdjunction.{uC, vC, uD, vD, uE, vE, w} J K L v u).unit.app H ≫
          (v.sheafPushforwardContinuous (Type (max uC vC uD vD uE vE w)) J K).map
            ((u.sheafPushforwardContinuous (Type (max uC vC uD vD uE vE w)) K L).map
              ((siteAlgebraicCompositionIso.{uC, vC, uD, vD, uE, vE, w} J K L v u).hom.app H)) =
        (sheafAdjunctionContinuous v (Type (max uC vC uD vD uE vE w)) J K).unit.app H ≫
          (v.sheafPushforwardContinuous (Type (max uC vC uD vD uE vE w)) J K).map
            ((sheafAdjunctionContinuous u (Type (max uC vC uD vD uE vE w)) K L).unit.app
              ((sheafPullback v (Type (max uC vC uD vD uE vE w)) J K).obj H))) ∧
    (∀ (H : Sheaf J (Type (max uC vC uD vD uE vE w))) (W : C) (x : H.obj.obj (op W)),
      ((siteAlgebraicCompositionIso.{uC, vC, uD, vD, uE, vE, w} J K L v u).hom.app H).hom.app
          (op (u.obj (v.obj W)))
          (((siteAlgebraicCompositeAdjunction.{uC, vC, uD, vD, uE, vE, w} J K L v u).unit.app
              H).hom.app (op W) x) =
        ((sheafAdjunctionContinuous u (Type (max uC vC uD vD uE vE w)) K L).unit.app
            ((sheafPullback v (Type (max uC vC uD vD uE vE w)) J K).obj H)).hom.app
          (op (v.obj W))
          (((sheafAdjunctionContinuous v (Type (max uC vC uD vD uE vE w)) J K).unit.app
            H).hom.app (op W) x)) ∧
    (∀ δ : siteAlgebraicCompositePullback.{uC, vC, uD, vD, uE, vE, w} J K L v u ≅
        sheafPullback v (Type (max uC vC uD vD uE vE w)) J K ⋙
          sheafPullback u (Type (max uC vC uD vD uE vE w)) K L,
      (∀ (H : Sheaf J (Type (max uC vC uD vD uE vE w))) (W : C)
          (x : H.obj.obj (op W)),
        (δ.hom.app H).hom.app (op (u.obj (v.obj W)))
            (((siteAlgebraicCompositeAdjunction.{uC, vC, uD, vD, uE, vE, w} J K L v u).unit.app
              H).hom.app (op W) x) =
          ((sheafAdjunctionContinuous u (Type (max uC vC uD vD uE vE w)) K L).unit.app
              ((sheafPullback v (Type (max uC vC uD vD uE vE w)) J K).obj H)).hom.app
            (op (v.obj W))
            (((sheafAdjunctionContinuous v (Type (max uC vC uD vD uE vE w)) J K).unit.app
              H).hom.app (op W) x)) →
        δ = siteAlgebraicCompositionIso.{uC, vC, uD, vD, uE, vE, w} J K L v u) ∧
    (∀ A B : Sheaf J (Type (max uC vC uD vD uE vE w)),
      (siteAlgebraicCompositionIso.{uC, vC, uD, vD, uE, vE, w} J K L v u).hom.app (A ⨯ B) ≫
          prodComparison (sheafPullback v (Type (max uC vC uD vD uE vE w)) J K ⋙
            sheafPullback u (Type (max uC vC uD vD uE vE w)) K L) A B =
        prodComparison (siteAlgebraicCompositePullback.{uC, vC, uD, vD, uE, vE, w} J K L v u) A B ≫
          prod.map ((siteAlgebraicCompositionIso.{uC, vC, uD, vD, uE, vE, w} J K L v u).hom.app A)
            ((siteAlgebraicCompositionIso.{uC, vC, uD, vD, uE, vE, w} J K L v u).hom.app B)) ∧
    ((siteAlgebraicCompositionIso.{uC, vC, uD, vD, uE, vE, w} J K L v u).hom.app (⊤_ _) ≫
        terminalComparison (sheafPullback v (Type (max uC vC uD vD uE vE w)) J K ⋙
          sheafPullback u (Type (max uC vC uD vD uE vE w)) K L) =
      terminalComparison (siteAlgebraicCompositePullback.{uC, vC, uD, vD, uE, vE, w} J K L v u)) ∧
    SiteAlgebraicComparison
      (siteAlgebraicCompositionIso.{uC, vC, uD, vD, uE, vE, w} J K L v u).hom ∧
    (∀ H : Sheaf J (Type (max uC vC uD vD uE vE w)),
      IsIso ((sheafAdjunctionContinuous (𝟭 C)
        (Type (max uC vC uD vD uE vE w)) J J).unit.app H)) ∧
    SiteAlgebraicIdentityUnit
      (sheafAdjunctionContinuous (𝟭 C) (Type (max uC vC uD vD uE vE w)) J J).unit :=
  sorry

end CategoryTheory

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SecSmoothPurity.ProperSupportPullbackSectionMap
public import Sheaf.AlgebraicGeometry.ProperSupportGeometricStalk
public import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
public import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.PointedEtaleStalk
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Fibre restriction compatibility for proper-support pullback

Source: Stacks Project, More on Étale Cohomology, Tag 0F55 (lemma-base-change-f-shriek-separated),
construction and geometric-stalk verification.
(blueprint: lem-cbc-proper-support-fibre-restriction-compatibility).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

set_option autoImplicit false

/-- The canonical proper-support pullback map and its inverse-image/direct-image adjunct agree
on geometric stalks with restriction to the identified geometric fibre.

The maps `qG` and `qH` are the restriction maps supplied by `properSupport_geometricStalk`,
normalized by `geometricFibreSectionRestriction`; `eG` and `eH` have submodule codomains and
are characterized by the proper-support inclusion equations.  The coefficient/fibre transport
`κ₀` is characterized on every pulled-back representative by the two geometric-fibre
restriction maps and the inverse-image composition unit, and `κ` is its induced isomorphism on
proper-support submodules.  Thus no arbitrary stalk or fibre isomorphism occurs.

Proof (the four source computations).  (1) Represent a stalk germ by a pointed étale
neighbourhood.  The germ equation for `c` identifies the unit pullback germ with the original
germ, and the normalization of `qG` gives restriction to the geometric fibre.  (2) The adjunct
unit equation `b_*β ⋙ η = α` identifies the germ of `β` with the section-pullback map.  (3) The
Cartesian fibre isomorphism, the coefficient transport `κ₀`, and the inverse-image composition
unit identify the restriction of that pulled-back section with the restriction of the original
section.  (4) The explicit germ equality for every pointed neighbourhood implies equality of the
stalk maps by the colimit description of geometric stalks; the submodule inclusion equations
then give the displayed equality.
Source: Stacks Project, More on Étale Cohomology, Tags 0F55 and 0F76.
(blueprint: lem-cbc-proper-support-fibre-restriction-compatibility). -/
theorem properSupport_fibre_restriction_compatibility
    {Λ : Type (u + 1)} [CommRing Λ]
    {X X' Y Y' : Scheme.{u}}
    (a : X' ⟶ X) (f : X ⟶ Y) (b : Y' ⟶ Y) (f' : X' ⟶ Y')
    [IsSeparated f] [LocallyOfFiniteType f]
    (sq : IsPullback a f' f b)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (H : Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (ιG : G ⟶ (lowerStar (ModuleCat.{u + 1} Λ) f).obj F)
    (ιH : H ⟶ (lowerStar (ModuleCat.{u + 1} Λ) f').obj
      ((upperStar (ModuleCat.{u + 1} Λ) a).obj F))
    [Mono ιG] [Mono ιH]
    (hG : ∀ (U : Y.Etale)
      (s : ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F).obj.obj (op U)),
      (∃ t, (ιG.hom.app (op U)) t = s) ↔
        SectionHasProperSupport Λ F (f.Etale.obj U) (pullback.fst U.hom f) s)
    (hH : ∀ (V : Y'.Etale)
      (s : ((lowerStar (ModuleCat.{u + 1} Λ) f').obj
        ((upperStar (ModuleCat.{u + 1} Λ) a).obj F)).obj.obj (op V)),
      (∃ t, (ιH.hom.app (op V)) t = s) ↔
        @SectionHasProperSupport Λ _ X' V.left
          ((upperStar (ModuleCat.{u + 1} Λ) a).obj F)
          ((MorphismProperty.Over.pullback @Etale ⊤ f').obj V)
          (pullback.fst V.hom f')
          (MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
            (IsPullback.of_hasPullback V.hom f').flip
            (MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sq inferInstance)) s)
    (α : G ⟶ (lowerStar (ModuleCat.{u + 1} Λ) b).obj H)
    (hα : ∀ (U : Y.Etale) (s : G.obj.obj (op U)),
      (ιH.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ b).obj U)))
          ((α.hom.app (op U)) s) =
        (properSupportUnitPullback a f b f' sq F U)
          ((ιG.hom.app (op U)) s))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y' : Spec (.of Ω) ⟶ Y') :
    ∃ (qG : lowerStar (ModuleCat.{u + 1} Λ) f ⋙
        (Scheme.pointSmallEtale (y' ≫ b)).sheafFiber ⟶
          upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f (y' ≫ b)) ⋙
            (sheafSections (pullback f (y' ≫ b)).smallEtaleTopology
              (ModuleCat.{u + 1} Λ)).obj
              (op (Scheme.Etale.mk (𝟙 (pullback f (y' ≫ b))))))
      (qH : lowerStar (ModuleCat.{u + 1} Λ) f' ⋙
        (Scheme.pointSmallEtale y').sheafFiber ⟶
          upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f' y') ⋙
            (sheafSections (pullback f' y').smallEtaleTopology
              (ModuleCat.{u + 1} Λ)).obj
              (op (Scheme.Etale.mk (𝟙 (pullback f' y')))))
      (S_G : Submodule Λ
        (((upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f (y' ≫ b))).obj F).obj.obj
          (op (Scheme.Etale.mk (𝟙 (pullback f (y' ≫ b)))))))
      (S_H : Submodule Λ
        (((upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f' y')).obj
          ((upperStar (ModuleCat.{u + 1} Λ) a).obj F)).obj.obj
          (op (Scheme.Etale.mk (𝟙 (pullback f' y'))))))
      (eG : (Scheme.pointSmallEtale (y' ≫ b)).sheafFiber.obj G ≅ ModuleCat.of Λ S_G)
      (eH : (Scheme.pointSmallEtale y').sheafFiber.obj H ≅ ModuleCat.of Λ S_H)
      (κ₀ :
        (((upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f' y')).obj
          ((upperStar (ModuleCat.{u + 1} Λ) a).obj F)).obj.obj
          (op (Scheme.Etale.mk (𝟙 (pullback f' y'))))) ⟶
        (((upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f (y' ≫ b))).obj F).obj.obj
          (op (Scheme.Etale.mk (𝟙 (pullback f (y' ≫ b)))))))
      (κ : ModuleCat.of Λ S_H ≅ ModuleCat.of Λ S_G),
      (∀ (V : Y.Etale) (v : (Scheme.pointSmallEtale (y' ≫ b)).fiber.obj V),
        (Scheme.pointSmallEtale (y' ≫ b)).toPresheafFiber V v
            ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F).obj ≫ qG.app F =
          geometricFibreSectionRestriction Λ
            (IsPullback.of_hasPullback f (y' ≫ b)).toCommSq F V v) ∧
      (∀ (V : Y'.Etale) (v : (Scheme.pointSmallEtale y').fiber.obj V),
        (Scheme.pointSmallEtale y').toPresheafFiber V v
            ((lowerStar (ModuleCat.{u + 1} Λ) f').obj
              ((upperStar (ModuleCat.{u + 1} Λ) a).obj F)).obj ≫
              qH.app ((upperStar (ModuleCat.{u + 1} Λ) a).obj F) =
          geometricFibreSectionRestriction Λ
            (IsPullback.of_hasPullback f' y').toCommSq
            ((upperStar (ModuleCat.{u + 1} Λ) a).obj F) V v) ∧
      eG.hom ≫ ModuleCat.ofHom S_G.subtype =
        (Scheme.pointSmallEtale (y' ≫ b)).sheafFiber.map ιG ≫ qG.app F ∧
      eH.hom ≫ ModuleCat.ofHom S_H.subtype =
        (Scheme.pointSmallEtale y').sheafFiber.map ιH ≫
          qH.app ((upperStar (ModuleCat.{u + 1} Λ) a).obj F) ∧
      κ.hom ≫ ModuleCat.ofHom S_G.subtype =
        ModuleCat.ofHom S_H.subtype ≫ κ₀ ∧
      (∀ (U : Y.Etale) (v : (Scheme.pointSmallEtale (y' ≫ b)).fiber.obj U)
        (s : F.obj.obj (op (f.Etale.obj U))),
        κ₀ ((geometricFibreSectionRestriction Λ
          (IsPullback.of_hasPullback f' y').toCommSq
          ((upperStar (ModuleCat.{u + 1} Λ) a).obj F)
          ((MorphismProperty.Over.pullback @Etale ⊤ b).obj U)
          ((Scheme.pointSmallEtaleFiberEtaleIso b y').inv.app U v)).hom
          ((properSupportUnitPullback a f b f' sq F U) s)) =
          (geometricFibreSectionRestriction Λ
            (IsPullback.of_hasPullback f (y' ≫ b)).toCommSq F U v).hom s) ∧
      (let β :=
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) b).homEquiv G H).symm α
       ((Scheme.pointSmallEtale y').sheafFiber.map β) ≫ eH.hom ≫ κ.hom =
          ((Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) b y').app G).hom ≫ eG.hom)
    := by
  sorry

end AlgebraicGeometry.Etale

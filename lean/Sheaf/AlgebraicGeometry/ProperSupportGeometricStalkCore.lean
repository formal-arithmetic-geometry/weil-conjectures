/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSectionProperSupport
public import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeGerms
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import Sheaf.AlgebraicGeometry.ClosedProperSupportLocality
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import WeilConjectures.SixFunctors.OpenClosed.Complex

/-! The geometric part of the proper-support stalk image calculation. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

open Scheme

/--
The restriction map on the geometric stalk is injective on a proper-support subsheaf, and
its range consists exactly of the properly supported fibre sections.  This is the geometric
content of Stacks Project, Tag 0F76: represent a stalk element on a pointed étale
neighbourhood, use the inverse-image germ formula to identify its fibre support, and use
extension by zero after shrinking and compactifying to lift every properly supported fibre
section.  The proof is deliberately separated from the elementary construction of the range
submodule and its canonical isomorphism.
Source: Stacks Project, Tag 0F76, support-image and extension-by-zero paragraphs.
(blueprint: lem-cbc-proper-support-geometric-stalk-image-core).
-/
theorem properSupport_geometricStalk_image_core
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (i : G ⟶ (lowerStar (ModuleCat.{u + 1} Λ) f).obj F) (hi : Mono i)
    (hG : ∀ (V : Y.Etale) (s : F.obj.obj (op (f.Etale.obj V))),
      (∃ t, i.hom.app (op V) t = s) ↔
        SectionHasProperSupport Λ F (f.Etale.obj V) (pullback.fst V.hom f) s)
    (c : lowerStar (ModuleCat.{u + 1} Λ) f ⋙ (Scheme.pointSmallEtale y).sheafFiber ⟶
      upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f y) ⋙
        (sheafSections (pullback f y).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (op (Scheme.Etale.mk (𝟙 (pullback f y)))))
    (hc : ∀ (V : Y.Etale) (v : (Scheme.pointSmallEtale y).fiber.obj V)
      (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      (Scheme.pointSmallEtale y).toPresheafFiber V v
          ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F).obj ≫ c.app F =
        geometricFibreSectionRestriction Λ (IsPullback.of_hasPullback f y).toCommSq F V v) :
    Function.Injective
        (((Scheme.pointSmallEtale y).sheafFiber.map i ≫ c.app F).hom) ∧
      ∀ s, s ∈ LinearMap.range
          (((Scheme.pointSmallEtale y).sheafFiber.map i ≫ c.app F).hom) ↔
        SectionHasProperSupport Λ
          ((upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f y)).obj F)
          (Scheme.Etale.mk (𝟙 (pullback f y))) (pullback.snd f y) s := by
  sorry

end AlgebraicGeometry.Etale

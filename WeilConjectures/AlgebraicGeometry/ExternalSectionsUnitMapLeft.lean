/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ScalarGlobalSectionsComparison
import WeilConjectures.AlgebraicGeometry.ExternalOpenFactorUnitsLeft

/-! # The first-factor external section map from pullback units

## References

* Stacks Project, Tags 0096, 01F7 and 0BED
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type w} [Field k] {X Y : Scheme.{w}}

/-- The field-linear pullback unit on the presheaf of sections (Stacks, Tag 0096). -/
def scalarSectionUnit (f : X ⟶ Spec (CommRingCat.of k))
    (g : Y ⟶ Spec (CommRingCat.of k)) (a : Y ⟶ X) (h : a ≫ f = g)
    (F : X.Modules) : scalarPresheaf f F ⟶
      (TopologicalSpace.Opens.map a.base).op ⋙ scalarPresheaf g ((tensorPullback a).obj F) :=
  ((((TopologicalSpace.Opens.map a.base).sheafAdjunctionContinuous (ModuleCat.{w} k)
    _ _).homEquiv _ _) (Classical.choose (exists_scalarPullbackCoefficient f g a h F))).hom

/-- The section unit is the chosen tensor-pullback unit (Stacks, Tag 0096). -/
theorem scalarSectionUnit_apply (f : X ⟶ Spec (CommRingCat.of k))
    (g : Y ⟶ Spec (CommRingCat.of k)) (a : Y ⟶ X) (h : a ≫ f = g)
    (F : X.Modules) (U : X.Opens) (s : F.val.obj (op U)) :
    (scalarSectionUnit f g a h F).app (op U) s =
      ((Classical.choose (exists_tensorPullbackAdjunction a)).unit.app F).val.app
        (op U) s :=
  Classical.choose_spec (exists_scalarPullbackCoefficient f g a h F) U s

/-- Pull a section of the second factor back globally, then restrict it above U (Stacks, Tag 0BED).
-/
def externalSecondSectionLeft (f : X ⟶ Spec (CommRingCat.of k))
    (g : Y ⟶ Spec (CommRingCat.of k)) (G : Y.Modules) (U : X.Opens) :
    scalarObj g G (op ⊤) ⟶
      scalarObj (pullback.fst f g ≫ f) ((tensorPullback (pullback.snd f g)).obj G)
        (op (pullback.fst f g ⁻¹ᵁ U)) :=
  (scalarSectionUnit g (pullback.fst f g ≫ f) (pullback.snd f g)
      pullback.condition.symm G).app (op ⊤) ≫
    (scalarPresheaf (pullback.fst f g ≫ f)
      ((tensorPullback (pullback.snd f g)).obj G)).map
        (homOfLE (by simp : pullback.fst f g ⁻¹ᵁ U ≤ pullback.snd f g ⁻¹ᵁ ⊤)).op

/-- Tensor the first pullback unit with the restricted second section (Stacks, Tag 0BED). -/
def externalSectionsUnitAppLeft (f : X ⟶ Spec (CommRingCat.of k))
    (g : Y ⟶ Spec (CommRingCat.of k)) (F : X.Modules) (G : Y.Modules)
    (U : X.Opens) : scalarObj f F (op U) ⊗ scalarObj g G (op ⊤) ⟶
      scalarObj (pullback.fst f g ≫ f) (externalCupCoefficients f g F G)
        (op (pullback.fst f g ⁻¹ᵁ U)) :=
  ((scalarSectionUnit f (pullback.fst f g ≫ f) (pullback.fst f g) rfl F).app (op U)
    ⊗ₘ externalSecondSectionLeft f g G U) ≫
      scalarTensorCoefficientApp (pullback.fst f g ≫ f)
        ((tensorPullback (pullback.fst f g)).obj F)
        ((tensorPullback (pullback.snd f g)).obj G) (op (pullback.fst f g ⁻¹ᵁ U))

/-- The component maps commute with restriction (Stacks, Tags 0096, 01F7 and 0BED). -/
theorem externalSectionsUnitAppLeft_naturality
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules) {U V : X.Opensᵒᵖ} (i : U ⟶ V) :
    (scalarPresheaf f F ⋙ MonoidalCategory.tensorRight (scalarObj g G (op ⊤))).map i ≫
      externalSectionsUnitAppLeft f g F G V.unop =
    externalSectionsUnitAppLeft f g F G U.unop ≫
      ((TopologicalSpace.Opens.map (pullback.fst f g).base).op ⋙
        scalarPresheaf (pullback.fst f g ≫ f) (externalCupCoefficients f g F G)).map i := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro s t
  let p := pullback.fst f g
  let q := pullback.snd f g
  let β := scalarSectionUnit f (p ≫ f) p rfl F
  let Q := (tensorPullback q).obj G
  change tmulSection (β.app V ((scalarPresheaf f F).map i s))
      (externalSecondSectionLeft f g G V.unop t) =
    (externalCupCoefficients f g F G).presheaf.map
      (homOfLE (show p ⁻¹ᵁ V.unop ≤ p ⁻¹ᵁ U.unop from
        (TopologicalSpace.Opens.map p.base).map i.unop |> leOfHom)).op
      (tmulSection (β.app U s) (externalSecondSectionLeft f g G U.unop t))
  rw [tmulSection_map]
  congr 1
  · exact ConcreteCategory.congr_hom (β.naturality i) s
  · change (scalarPresheaf (p ≫ f) Q).map _
        ((scalarSectionUnit g (p ≫ f) q pullback.condition.symm G).app (op ⊤) t) =
      ((scalarPresheaf (p ≫ f) Q).map _ ≫
        (scalarPresheaf (p ≫ f) Q).map _)
        ((scalarSectionUnit g (p ≫ f) q pullback.condition.symm G).app (op ⊤) t)
    rw [← Functor.map_comp]
    rfl

/-- The canonical external section morphism on opens of the first factor (Stacks, Tag 0BED). -/
def externalSectionsUnitLeft
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules) :
    scalarPresheaf f F ⋙ MonoidalCategory.tensorRight (scalarObj g G (op ⊤)) ⟶
      (TopologicalSpace.Opens.map (pullback.fst f g).base).op ⋙
        scalarPresheaf (pullback.fst f g ≫ f) (externalCupCoefficients f g F G) where
  app U := externalSectionsUnitAppLeft f g F G U.unop
  naturality _ _ i := externalSectionsUnitAppLeft_naturality f g F G i

/-- At the top open the unit construction is the canonical external product (Stacks, Tag 0BED). -/
theorem externalSectionsUnitLeft_top
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules) :
    (externalSectionsUnitLeft f g F G).app (op ⊤) ≫
      ((scalarPresheaf (pullback.fst f g ≫ f) (externalCupCoefficients f g F G)).mapIso
        (eqToIso (by simp))).hom =
      ModuleCat.ofHom (externalGlobalSectionsTensor f g F G) := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro s t
  change (externalCupCoefficients f g F G).presheaf.map _
      (tmulSection
        ((scalarSectionUnit f (pullback.fst f g ≫ f) (pullback.fst f g) rfl F).app
          (op ⊤) s)
        (externalSecondSectionLeft f g G ⊤ t)) = _
  have hm : (eqToIso (by simp : op (pullback.fst f g ⁻¹ᵁ (⊤ : X.Opens)) =
      op (⊤ : (CategoryTheory.Limits.pullback f g).Opens))).hom =
      (homOfLE (by simp : (⊤ : (CategoryTheory.Limits.pullback f g).Opens) ≤
        pullback.fst f g ⁻¹ᵁ ⊤)).op :=
    Subsingleton.elim _ _
  rw [hm, tmulSection_map, scalarSectionUnit_apply]
  change tmulSection (M := (tensorPullback (pullback.fst f g)).obj F)
      (N := (tensorPullback (pullback.snd f g)).obj G) (U := ⊤)
      (tensorPullbackTopSection (pullback.fst f g) F s)
      (((tensorPullback (pullback.snd f g)).obj G).presheaf.map _
        (((tensorPullback (pullback.snd f g)).obj G).presheaf.map _
          ((scalarSectionUnit g (pullback.fst f g ≫ f) (pullback.snd f g)
            pullback.condition.symm G).app (op ⊤) t))) =
    tmulSection (M := (tensorPullback (pullback.fst f g)).obj F)
      (N := (tensorPullback (pullback.snd f g)).obj G) (U := ⊤)
      (tensorPullbackTopSection (pullback.fst f g) F s)
      (tensorPullbackTopSection (pullback.snd f g) G t)
  congr 1
  change ((((tensorPullback (pullback.snd f g)).obj G).presheaf.map _ ≫
      ((tensorPullback (pullback.snd f g)).obj G).presheaf.map _)
      ((scalarSectionUnit g (pullback.fst f g ≫ f) (pullback.snd f g)
        pullback.condition.symm G).app (op ⊤) t)) = _
  rw [← Functor.map_comp, scalarSectionUnit_apply]
  rfl

/-- The cartesian open-immersion square transports the unit-defined external
product on pure tensors to the external product on the open subscheme
(Stacks, Tags 0BED, 0096, 0097 and 01CD). -/
theorem exists_externalSectionsUnitOpenTransportLeft
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules) (V : X.Opens) :
    ∃ eS : scalarObj f F (op V) ⊗ scalarObj g G (op ⊤) ≅
        ModuleCat.of k (scalarObj (V.ι ≫ f) (F.restrict V.ι) (op ⊤) ⊗[k]
          scalarObj g G (op ⊤)),
    ∃ eT : scalarObj (pullback.fst f g ≫ f) (externalCupCoefficients f g F G)
        (op (pullback.fst f g ⁻¹ᵁ V)) ≅
        scalarObj (pullback.fst (V.ι ≫ f) g ≫ (V.ι ≫ f))
          (externalCupCoefficients (V.ι ≫ f) g (F.restrict V.ι) G) (op ⊤),
      ∀ (s : scalarObj f F (op V)) (t : scalarObj g G (op ⊤)),
        eT.hom (externalSectionsUnitAppLeft f g F G V (s ⊗ₜ[k] t)) =
          externalGlobalSectionsTensor (V.ι ≫ f) g (F.restrict V.ι) G
            (eS.hom (s ⊗ₜ[k] t)) := by
  obtain ⟨hTop, hRange, eF, eM, eN, hM, hN⟩ :=
    exists_externalOpenFactorUnitsLeft f g F G V
  have hb : externalOpenBaseChangeLeft f g V ≫ (pullback.fst f g ≫ f) =
      pullback.fst (V.ι ≫ f) g ≫ (V.ι ≫ f) := by
    simp [externalOpenBaseChangeLeft, ← Category.assoc]
  obtain ⟨eT, hT⟩ := exists_scalarOpenTensorTransport (pullback.fst f g ≫ f)
    (pullback.fst (V.ι ≫ f) g ≫ (V.ι ≫ f)) (externalOpenBaseChangeLeft f g V) hb
    (pullback.fst f g ⁻¹ᵁ V) hTop hRange
    ((tensorPullback (pullback.fst f g)).obj F)
    ((tensorPullback (pullback.snd f g)).obj G) _ _ eM eN
  refine ⟨tensorIso eF (Iso.refl _), eT, ?_⟩
  intro s t
  change eT.hom (tmulSection
    ((scalarSectionUnit f (pullback.fst f g ≫ f) (pullback.fst f g) rfl F).app (op V) s)
    (externalSecondSectionLeft f g G V t)) = _
  rw [hT]
  rw [scalarSectionUnit_apply, hM]
  unfold externalSecondSectionLeft
  change tmulSection _ (eN.hom.app ⊤
    (tensorPullbackOpenSection (externalOpenBaseChangeLeft f g V)
      ((tensorPullback (pullback.snd f g)).obj G) (pullback.fst f g ⁻¹ᵁ V) hTop
      (((tensorPullback (pullback.snd f g)).obj G).val.map _
        ((scalarSectionUnit g (pullback.fst f g ≫ f) (pullback.snd f g)
          pullback.condition.symm G).app (op ⊤) t)))) = _
  rw [scalarSectionUnit_apply]
  refine (congrArg (fun z ↦ tmulSection
    (M := (tensorPullback (pullback.fst (V.ι ≫ f) g)).obj (F.restrict V.ι))
    (N := (tensorPullback (pullback.snd (V.ι ≫ f) g)).obj G) (U := ⊤)
    (tensorPullbackTopSection (pullback.fst (V.ι ≫ f) g) (F.restrict V.ι) (eF.hom s)) z)
    (hN t)).trans ?_
  simp only [tensorIso_hom, Iso.refl_hom]
  rfl

end
end AlgebraicGeometry.Scheme.Modules

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.Paper.SfOpenClosedTriangleData
import Sheaf.Paper.SfExactLocalizationTriangle
import Sheaf.Paper.SfIntegralConstructibleTriangulated

/-! # Triangles and orthogonality of normalized recollement presentations

The normalization on representative complexes determines both arrows, so the exact
sheaf localization sequence applies to every normalized presentation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (hX : IsNoetherian X)

private theorem integral_normalized
    (P : SfRecollementPresentation (sfIntegralConstructibleCategory l E X))
    (hp : SfIntegralRecollementNormalization l E i hX P) :
    (∀ K, ∃ δ, Triangle.mk (P.counit.app K) (P.unit.app K) δ ∈ distTriang _) ∧
    ∀ (K L : sfIntegralConstructibleCategory l E X) (n : ℤ),
      Subsingleton ((P.openTerm.obj K)⟦n⟧ ⟶ P.closedTerm.obj L) := by
  let := hX
  let S := sfIntegralConstructible l E X
  let F := S.ι
  let A := sfExactLocalizationPresentation (sfRecollementModuleOpen l E i)
    (sfRecollementModuleClosed l E i) (sfRecollementModuleCounit l E i)
    (sfRecollementModuleUnit l E i)
  obtain ⟨a, c, hn⟩ := hp
  have hmaps (K : S.FullSubcategory) :
      a.hom.app K ≫ F.map (P.counit.app K) = A.counit.app K.obj ∧
      F.map (P.unit.app K) ≫ c.inv.app K = A.unit.app K.obj := by
    let B := (DerivedCategory.Q (C := scalarReductionSource.{u, u} l E X)).objPreimage K.obj
    let e := (DerivedCategory.Q (C := scalarReductionSource.{u, u} l E X)).objObjPreimageIso K.obj
    have hB : S (DerivedCategory.Q.obj B) := S.prop_of_iso e.symm K.property
    let KB : S.FullSubcategory := ⟨DerivedCategory.Q.obj B, hB⟩
    let e' : KB ≅ K := S.isoMk e
    have hb := hn B hB
    have hb₁ : a.hom.app KB ≫ F.map (P.counit.app KB) = A.counit.app KB.obj := by
      exact hb.1.trans (sfExactLocalizationPresentation_counit _ _ _ _ B).symm
    have hb₂ : F.map (P.unit.app KB) ≫ c.inv.app KB = A.unit.app KB.obj := by
      change (P.unit.app KB).hom ≫ c.inv.app KB = A.unit.app KB.obj
      apply (cancel_mono ((sfRecollementModuleClosed l E i).mapDerivedCategoryFactors.hom.app B)).mp
      simpa only [Category.assoc] using hb.2.trans (sfExactLocalizationPresentation_unit
        (sfRecollementModuleOpen l E i) (sfRecollementModuleClosed l E i)
        (sfRecollementModuleCounit l E i) (sfRecollementModuleUnit l E i) B).symm
    have han : A.openTerm.map e.hom ≫ a.hom.app K =
        a.hom.app KB ≫ F.map (P.openTerm.map e'.hom) := a.hom.naturality e'.hom
    have hcn : F.map (P.closedTerm.map e'.hom) ≫ c.inv.app K =
        c.inv.app KB ≫ A.closedTerm.map e.hom := c.inv.naturality e'.hom
    have he : F.map e'.hom = e.hom := rfl
    have hpn : F.map (P.openTerm.map e'.hom) ≫ F.map (P.counit.app K) =
        F.map (P.counit.app KB) ≫ e.hom := by
      simpa only [Functor.map_comp, Functor.id_map, he] using
        congrArg F.map (P.counit.naturality e'.hom)
    have hun : e.hom ≫ F.map (P.unit.app K) =
        F.map (P.unit.app KB) ≫ F.map (P.closedTerm.map e'.hom) := by
      simpa only [Functor.map_comp, Functor.id_map, he] using
        congrArg F.map (P.unit.naturality e'.hom)
    constructor
    · apply (cancel_epi (A.openTerm.map e.hom)).mp
      calc
        _ = a.hom.app KB ≫ F.map (P.openTerm.map e'.hom) ≫
            F.map (P.counit.app K) := by rw [← Category.assoc, han, Category.assoc]
        _ = a.hom.app KB ≫ F.map (P.counit.app KB) ≫ e.hom := by rw [hpn]
        _ = A.counit.app KB.obj ≫ e.hom := by rw [← Category.assoc, hb₁]
        _ = _ := (A.counit.naturality e.hom).symm
    · apply (cancel_epi e.hom).mp
      calc
        _ = F.map (P.unit.app KB) ≫ F.map (P.closedTerm.map e'.hom) ≫ c.inv.app K := by
          rw [← Category.assoc, hun, Category.assoc]
        _ = F.map (P.unit.app KB) ≫ c.inv.app KB ≫ A.closedTerm.map e.hom := by rw [hcn]
        _ = A.unit.app KB.obj ≫ A.closedTerm.map e.hom := by rw [← Category.assoc, hb₂]
        _ = _ := (A.unit.naturality e.hom).symm
  have : (kernel (sfRecollementModuleUnit l E i)).Additive :=
    sfRecollementModuleOpen_additive l E i
  have : PreservesFiniteLimits (kernel (sfRecollementModuleUnit l E i)) :=
    sfRecollementModuleOpen_limits l E i
  have : PreservesFiniteColimits (kernel (sfRecollementModuleUnit l E i)) :=
    sfRecollementModuleOpen_colimits l E i
  have ht (K) : ∃ δ, Triangle.mk (A.counit.app K) (A.unit.app K) δ ∈ distTriang _ :=
    sfExactLocalizationPresentation_distinguished _ _ _ _
      (kernel.condition (sfRecollementModuleUnit l E i))
      (sfRecollementModule_shortExact l E i) K
  have ho (K L) (n : ℤ) :
      Subsingleton ((A.openTerm.obj K)⟦n⟧ ⟶ A.closedTerm.obj L) := by
    let R := completedIntegralCommRingSheafUnrestricted l E X
    let T := completedIntegralCommRingSheafUnrestricted l E Z
    let t := asIso (sfRecollementCoefficientMap l E i)
    let I := proEtaleRingModuleDirectImage i R T t
    have : PreservesFiniteLimits I := (sfRecollementModuleDirect_exact l E i).1
    have : PreservesFiniteColimits I := (sfRecollementModuleDirect_exact l E i).2
    have : ∀ N, IsIso ((sfRecollementModuleAdjunction l E i).counit.app N) :=
      (sfRecollementModule_closed_adjunction l E i).2
    have : IsIso (sfRecollementModuleAdjunction l E i).counit :=
      NatIso.isIso_of_isIso_app _
    have : (kernel (sfRecollementModuleAdjunction l E i).unit).Additive :=
      sfRecollementModuleOpen_additive l E i
    have : PreservesFiniteLimits (kernel (sfRecollementModuleAdjunction l E i).unit) :=
      sfRecollementModuleOpen_limits l E i
    have : PreservesFiniteColimits (kernel (sfRecollementModuleAdjunction l E i).unit) :=
      sfRecollementModuleOpen_colimits l E i
    exact sfExactLocalizationKernel_orthogonality
      (proEtaleRingModulePullback i R T t) I (sfRecollementModuleAdjunction l E i) K L n
  constructor
  · intro K
    obtain ⟨δ, hδ⟩ := ht K.obj
    let δ' : P.closedTerm.obj K ⟶ (P.openTerm.obj K)⟦(1 : ℤ)⟧ := F.preimage
      (c.inv.app K ≫ δ ≫ (shiftFunctor _ (1 : ℤ)).map (a.hom.app K) ≫
        (F.commShiftIso (1 : ℤ)).inv.app (P.openTerm.obj K))
    refine ⟨δ', ?_⟩
    change F.mapTriangle.obj (Triangle.mk (P.counit.app K) (P.unit.app K) δ') ∈ distTriang _
    apply isomorphic_distinguished _ hδ
    refine Triangle.isoMk _ _ ((a.app K).symm) (Iso.refl _) ((c.app K).symm) ?_ ?_ ?_
    · change F.map (P.counit.app K) ≫ 𝟙 _ = a.inv.app K ≫ A.counit.app K.obj
      rw [← (hmaps K).1]
      simp only [Category.comp_id, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
    · change F.map (P.unit.app K) ≫ c.inv.app K = 𝟙 _ ≫ A.unit.app K.obj
      simpa only [Category.id_comp] using (hmaps K).2
    · change (F.map δ' ≫ (F.commShiftIso (1 : ℤ)).hom.app _) ≫
        (shiftFunctor _ (1 : ℤ)).map (a.inv.app K) = c.inv.app K ≫ δ
      simp only [δ', Functor.map_preimage, Category.assoc,
        Iso.inv_hom_id_app_assoc]
      rw [← Functor.map_comp, Iso.hom_inv_id_app]
      erw [(shiftFunctor (DerivedCategory (scalarReductionSource l E X)) (1 : ℤ)).map_id
        (A.openTerm.obj K.obj)]
      simp only [Category.comp_id]
  · intro K L n
    let e := Iso.homCongr
      ((F.commShiftIso n).app (P.openTerm.obj K) ≪≫
        (shiftFunctor _ n).mapIso (a.app K).symm) (c.app L).symm
    have : Subsingleton (F.obj ((P.openTerm.obj K)⟦n⟧) ⟶ F.obj (P.closedTerm.obj L)) :=
      ⟨fun f g ↦ e.injective (@Subsingleton.elim _ (ho K.obj L.obj n) (e f) (e g))⟩
    exact F.map_injective.subsingleton

/-- Every rational presentation normalized from the exact completed sheaf sequence has
its specified distinguished triangles and shifted cross-object orthogonality.
Source: blueprint localization proof, triangle and Hom-vanishing paragraphs;
Stacks 0152 and exact scalar localization
(blueprint: lem-sf-normalized-rational-recollement-triangles).
Proof: the normalization identifies the maps on images of all complexes with the
termwise kernel inclusion and closed unit. Essential surjectivity and naturality
identify these maps on every integral object. The exact sheaf sequence supplies a
distinguished triangle; the closed adjunction kills the shifted kernel-to-image Hom.
The full triangulated constructible inclusion reflects triangles and is faithful.
Apply exact scalar localization to each integral triangle. Its Hom groups are tensor
products, so the zero integral cross-Hom groups remain zero. Finally conjugate by the
two rational normalization isomorphisms, retaining the given counit and unit. -/
theorem sfNormalizedRationalRecollement_triangle_orthogonality
    (P : SfRecollementPresentation (sfIntegralConstructibleCategory l E X))
    (Q : SfRecollementPresentation (sfRationalConstructibleCategory l E X))
    (hp : SfIntegralRecollementNormalization l E i hX P)
    (hq : SfRationalRecollementNormalization l E X P Q) :
    (∀ K, ∃ δ, Triangle.mk (Q.counit.app K) (Q.unit.app K) δ ∈ distTriang _) ∧
    ∀ (K L : sfRationalConstructibleCategory l E X) (n : ℤ),
      Subsingleton ((Q.openTerm.obj K)⟦n⟧ ⟶ Q.closedTerm.obj L) := by
  obtain ⟨ht, ho⟩ := integral_normalized l E i hX P hp
  obtain ⟨_, a, c, ha, hc⟩ := hq
  let F := sfRationalConstructibleLocalization l E X
  constructor
  · intro K
    obtain ⟨δ, hδ⟩ := ht K.obj
    let δ' := c.hom.app K.obj ≫ F.map δ ≫
      (F.commShiftIso (1 : ℤ)).hom.app (P.openTerm.obj K.obj) ≫
      (shiftFunctor _ (1 : ℤ)).map (a.inv.app K.obj)
    refine ⟨δ', isomorphic_distinguished _ (F.map_distinguished _ hδ) _
      (Triangle.isoMk _ _ (a.app K.obj) (Iso.refl _) (c.app K.obj) ?_ ?_ ?_)⟩
    · change Q.counit.app K ≫ 𝟙 _ = a.hom.app K.obj ≫ F.map (P.counit.app K.obj)
      simpa only [Category.comp_id, F, sfRationalConstructibleLocalization,
        ScalarLocalization.localization] using (ha K.obj).symm
    · change Q.unit.app K ≫ c.hom.app K.obj = 𝟙 _ ≫ F.map (P.unit.app K.obj)
      simpa only [Category.id_comp, F, sfRationalConstructibleLocalization,
        ScalarLocalization.localization] using hc K.obj
    · change δ' ≫ (shiftFunctor _ (1 : ℤ)).map (a.hom.app K.obj) =
        c.hom.app K.obj ≫ (F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app _)
      simp only [δ', Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
      erw [(shiftFunctor (sfRationalConstructibleCategory l E X) (1 : ℤ)).map_id
        (F.obj (P.openTerm.obj K.obj))]
      exact congrArg (fun f ↦ c.hom.app K.obj ≫ F.map δ ≫ f)
        (Category.comp_id ((F.commShiftIso (1 : ℤ)).hom.app (P.openTerm.obj K.obj)))
  · intro K L n
    have := ho K.obj L.obj n
    have hz : Subsingleton (F.obj ((P.openTerm.obj K.obj)⟦n⟧) ⟶
        F.obj (P.closedTerm.obj L.obj)) := by
      change Subsingleton (Localization.Away (Padic.coefficientExtensionUniformizer l E) ⊗[
        Padic.coefficientExtensionIntegers l E]
          ((P.openTerm.obj K.obj)⟦n⟧ ⟶ P.closedTerm.obj L.obj))
      infer_instance
    let e := Iso.homCongr
      ((shiftFunctor _ n).mapIso (a.app K.obj) ≪≫
        (F.commShiftIso n).symm.app (P.openTerm.obj K.obj)) (c.app L.obj)
    exact ⟨fun f g ↦ e.injective (@Subsingleton.elim _ hz (e f) (e g))⟩

end WeilConjectures

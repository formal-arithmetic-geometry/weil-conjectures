/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Authors: SHEAF group U3
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import Mathlib.CategoryTheory.EssentialImage
import Sheaf.AlgebraicGeometry.FiniteAffineDerivedEquivalence
import Sheaf.AlgebraicGeometry.FiniteScalarRightAdjointQCoh

/-! # The finite derived adjunction mate

Source: Stacks Project, Tags 0AX2 and 0AX3
(blueprint: lem-sc-finite-exact-hom-derived-mate). -/

@[expose] public section

universe u wX wY wA

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem adjunctionMate
    {C D A B : Type*} [Category* C] [Category* D] [Category* A] [Category* B]
    {R : C ⥤ D} {a : D ⥤ C} (adj : R ⊣ a)
    (J : C ⥤ A) (i : D ⥤ B) (hJ : J.FullyFaithful) (hi : i.FullyFaithful)
    {ρ : A ⥤ B} {ρR : B ⥤ A} (adjA : ρ ⊣ ρR)
    (β : R ⋙ i ≅ J ⋙ ρ) (K : D) (hK : J.essImage (ρR.obj (i.obj K))) :
    ∃ φ : J.obj (a.obj K) ≅ ρR.obj (i.obj K),
      ρ.map φ.hom ≫ adjA.counit.app (i.obj K) =
        β.inv.app (a.obj K) ≫ i.map (adj.counit.app K) := by
  classical
  let φ := (adjA.homEquiv _ _) (β.inv.app (a.obj K) ≫ i.map (adj.counit.app K))
  have hφ : ρ.map φ ≫ adjA.counit.app (i.obj K) =
      β.inv.app (a.obj K) ≫ i.map (adj.counit.app K) := by
    exact (adjA.homEquiv _ _).symm_apply_apply _
  have hbij (N : C) : Function.Bijective
      (fun g : J.obj N ⟶ J.obj (a.obj K) ↦ g ≫ φ) := by
    let e : (N ⟶ a.obj K) ≃ (J.obj N ⟶ ρR.obj (i.obj K)) :=
      (adj.homEquiv N K).symm.trans (hi.homEquiv.trans
        ((Iso.homCongr (β.app N) (Iso.refl _)).trans (adjA.homEquiv _ _)))
    have he (f : N ⟶ a.obj K) : e f = J.map f ≫ φ := by
      apply (adjA.homEquiv _ _).symm.injective
      dsimp [e]
      rw [Equiv.symm_apply_apply, adj.homEquiv_counit]
      rw [adjA.homEquiv_naturality_left_symm]
      change β.inv.app N ≫ i.map (R.map f ≫ adj.counit.app K) ≫ 𝟙 _ =
        ρ.map (J.map f) ≫ (adjA.homEquiv _ _).symm φ
      have hn := β.inv.naturality f
      dsimp only [Functor.comp_map] at hn
      rw [Category.comp_id, i.map_comp, ← Category.assoc, ← hn]
      rw [Category.assoc, adjA.homEquiv_counit]
      exact congrArg (fun g ↦ ρ.map (J.map f) ≫ g) hφ.symm
    have he' : (fun g : J.obj N ⟶ J.obj (a.obj K) ↦ g ≫ φ) =
        e ∘ hJ.homEquiv.symm := by
      funext g
      rw [Function.comp_apply, he, Functor.FullyFaithful.homEquiv_symm_apply,
        hJ.map_preimage]
    rw [he']
    exact e.bijective.comp hJ.homEquiv.symm.bijective
  obtain ⟨N, ⟨e⟩⟩ := hK
  obtain ⟨g, hg⟩ := (hbij N).surjective e.hom
  let ψ := e.inv ≫ g
  have hright : ψ ≫ φ = 𝟙 _ := by
    simp [ψ, Category.assoc, hg]
  have hleft : φ ≫ ψ = 𝟙 _ := by
    apply (hbij (a.obj K)).injective
    simp [Category.assoc, hright]
  exact ⟨⟨φ, ψ, hleft, hright⟩, hφ⟩

set_option maxHeartbeats 800000 in
-- Elaborating the derived scalar adjunction unfolds the two ring-sheaf presentations.
/-- The mate of the geometric counit is an algebra-linear derived isomorphism.
Source: Stacks Project, Tag 0AX2, comparison of right adjoints, and Tag 0AX3
(blueprint: lem-sc-finite-exact-hom-derived-mate).

Proof: Put J = iX followed by Rg_*. The affine derived equivalence identifies J with
an equivalence followed by the full inclusion of algebra-quasi-coherent complexes,
so J is fully faithful. The given gamma and comparison identify R followed by iY
with J followed by derived scalar restriction. Transpose the inverse of this
identification followed by iY of the geometric counit under the derived adjunction
of adjH. For every N, composition with this transpose is a bijection on Hom from J(N):
the two adjunction hom equivalences and the fully faithful inclusions identify it
with the identity on Hom from N to a(K). The finite scalar-right-adjoint theorem,
applied to the bounded-below K, puts RH(K) in the essential image of J. Choose an
isomorphism J(N0) to RH(K). Surjectivity at N0 supplies a right inverse to the
transpose. Injectivity at a(K) then supplies the left inverse. Package the transpose
as an isomorphism. The inverse adjunction hom equivalence is exactly the displayed
counit equation. This argument allows zero objects and empty schemes, and places no
condition on a choice of gamma beyond being the indicated natural isomorphism. -/
theorem finite_exactHom_derived_mate
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wA} (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)))]
    [IsFinite f] [IsNoetherian X] [IsNoetherian Y]
    (R : schemeDerivedQCohCategory X ⥤ schemeDerivedQCohCategory Y)
    (comparison : R ⋙ (schemeDerivedQCohProperty Y).ι ≅
      (schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (adj : R ⊣ a) (K : schemeDerivedQCohCategory Y) (hK : ∃ n : ℤ, K.obj.IsGE n)
    [PreservesFiniteLimits (SheafOfModules.restrictScalars
      (R := moduleRings Y.toRingedSpace)
      (R' := moduleRings (directImageAlgebraSpace f)) f.toRingCatSheafHom)]
    [PreservesFiniteColimits (SheafOfModules.restrictScalars
      (R := moduleRings Y.toRingedSpace)
      (R' := moduleRings (directImageAlgebraSpace f)) f.toRingCatSheafHom)]
    (H : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)))
    [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (adjH : SheafOfModules.restrictScalars
        (R := moduleRings Y.toRingedSpace)
        (R' := moduleRings (directImageAlgebraSpace f)) f.toRingCatSheafHom ⊣ H)
    (γ : RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace f) ⋙
      (SheafOfModules.restrictScalars
        (R := moduleRings Y.toRingedSpace)
        (R' := moduleRings (directImageAlgebraSpace f)) f.toRingCatSheafHom).mapDerivedCategory ≅
        schemeDerivedDirectImage f)
    : ∃ φ : (RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace f)).obj
        (a.obj K).obj ≅ H.rightDerivedFunctor.obj K.obj,
      (SheafOfModules.restrictScalars
        (R := moduleRings Y.toRingedSpace)
        (R' := moduleRings (directImageAlgebraSpace f)) f.toRingCatSheafHom).mapDerivedCategory.map
          φ.hom ≫
        adjH.mapDerivedCategoryRightDerivedAdjunction.counit.app K.obj =
      γ.hom.app (a.obj K).obj ≫ comparison.inv.app (a.obj K) ≫
        (adj.counit.app K).hom := by
  classical
  let T := SheafOfModules.restrictScalars
    (R := moduleRings Y.toRingedSpace)
    (R' := moduleRings (directImageAlgebraSpace f)) f.toRingCatSheafHom
  let G := RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace f)
  let J := (schemeDerivedQCohProperty X).ι ⋙ G
  let adjA := adjH.mapDerivedCategoryRightDerivedAdjunction
  obtain ⟨E, ⟨eE⟩, _⟩ := finite_affine_derived_equivalence f
  have hJ : J.FullyFaithful :=
    ((Functor.FullyFaithful.ofFullyFaithful E.functor).comp
      (directImageAlgebraDerivedQCohProperty f).fullyFaithfulι).ofIso eE
  let adjA' : T.rightDerivedFunctor ⊣ H.rightDerivedFunctor :=
    adjA.ofNatIsoLeft T.rightDerivedFunctorIsoMapDerivedCategory.symm
  have hq := finite_scalar_right_adjoint_qcoh f H.rightDerivedFunctor adjA' K hK
  let KA : directImageAlgebraDerivedQCohCategory f := ⟨H.rightDerivedFunctor.obj K.obj, hq⟩
  have hess : J.essImage (H.rightDerivedFunctor.obj K.obj) := by
    refine ⟨E.inverse.obj KA, ⟨?_⟩⟩
    exact eE.symm.app (E.inverse.obj KA) ≪≫
      (directImageAlgebraDerivedQCohProperty f).ι.mapIso (E.counitIso.app KA)
  let β : R ⋙ (schemeDerivedQCohProperty Y).ι ≅ J ⋙ T.mapDerivedCategory :=
    comparison ≪≫ Functor.isoWhiskerLeft (schemeDerivedQCohProperty X).ι γ.symm
  obtain ⟨φ, hφ⟩ := adjunctionMate adj J (schemeDerivedQCohProperty Y).ι hJ
    (schemeDerivedQCohProperty Y).fullyFaithfulι adjA β K hess
  refine ⟨φ, ?_⟩
  simpa only [β, Iso.trans_inv, Functor.isoWhiskerLeft_inv, NatTrans.comp_app,
    Functor.whiskerLeft_app, Iso.symm_inv, Category.assoc, adjA, J,
    ObjectProperty.ι_map, ObjectProperty.ι_obj] using hφ


end AlgebraicGeometry

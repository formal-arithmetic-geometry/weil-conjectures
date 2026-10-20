/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import WeilConjectures.AlgebraicGeometry.LocalizedPullbackPerfectModel
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat

/-! # A natural termwise comparison on local strictly perfect complexes

Source: Stacks Project, Tags 06YD and 06YJ.
(blueprint: lem-pc-localized-pullback-perfect-counit).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w wV wO
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products

/-- A finite-free retract is flat by flatness of coproducts and retracts. -/
private theorem flat_retract (Y : Scheme.{u})
    (M : SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (m : ℕ)
    (i : M ⟶ SheafOfModules.free (R := moduleRings Y.toRingedSpace) (ULift.{u} (Fin m)))
    (r : SheafOfModules.free (R := moduleRings Y.toRingedSpace) (ULift.{u} (Fin m)) ⟶ M)
    (h : i ≫ r = 𝟙 M) : SheafOfModules.IsFlat M := by
  let := SheafOfModules.monoidalCategory Y.sheaf
  let := SheafOfModules.symmetricCategory Y.sheaf
  obtain ⟨⟨mp⟩, ⟨mc⟩, _⟩ := SheafOfModules.tensorClosed Y.sheaf
  let := mp
  let := mc
  have := SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
  have hf : ObjectProperty.flat
      (SheafOfModules.free (R := moduleRings Y.toRingedSpace) (ULift.{u} (Fin m))) :=
    ObjectProperty.flat_coproduct _ (fun _ ↦ ObjectProperty.prop_unit _)
  exact (ObjectProperty.flat_of_retract ⟨i, r, h⟩ hf).2

set_option maxHeartbeats 800000 in
-- The comparison passes through module, homotopy and derived-category equivalences.
/-- The ordinary termwise computation on strictly perfect complexes comes from one
natural transformation, so it also computes chain maps.

Source: Stacks Project, Tags 06YD and 06YJ; the natural left-derived counit.
(blueprint: lem-pc-localized-pullback-perfect-counit).

Proof: transport the complexes from the localized site to U.toScheme. The tensor
pullback functor has the counit supplied by exists_derivedPullback, which is natural
on the entire homotopy category. Whisker this counit with the complex quotient and
with the exact open-site equivalence, and compose with the localization factorization
isomorphisms. Identify tensor pullback with ordinary module pullback by uniqueness of
left adjoints to module pushforward. Finally use the counit of the open-site equivalence
on the target to identify the ordinary composite with localizedPullback. These are
natural transformations, so their composite is the asserted eta on all complexes.
For a strictly perfect complex, the equivalence preserves its finite-free retracts
and boundedness. Finite-free retracts are flat, and a bounded-above flat complex is
K-flat. Thus the derived counit at that complex is invertible by the K-flat clause of
exists_derivedPullback. All other comparisons are isomorphisms, so eta is invertible
there. This also applies to zero complexes and empty opens. No arbitrary isomorphisms
between individual objects are used. -/
theorem localizedPullback_perfectCounit {T S : Scheme.{u}} (g : T ⟶ S)
    (U : S.Opens)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    [HasDerivedCategory.{wV}
      (SheafOfModules.{u} ((moduleRings T.toRingedSpace).over (g ⁻¹ᵁ U)))]
    [HasDerivedCategory.{wO}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [HasDerivedCategory.{wO}
      (SheafOfModules.{u} (moduleRings (g ⁻¹ᵁ U).toScheme.toRingedSpace))] :
    let A : SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U) ⥤
        SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) :=
      (Scheme.Modules.overEquiv U).functor
    let C : SheafOfModules.{u} ((moduleRings T.toRingedSpace).over (g ⁻¹ᵁ U)) ⥤
        SheafOfModules.{u} (moduleRings (g ⁻¹ᵁ U).toScheme.toRingedSpace) :=
      (Scheme.Modules.overEquiv (g ⁻¹ᵁ U)).functor
    ∃ η : DerivedCategory.Q ⋙ A.mapDerivedCategory ⋙
        derivedPullback (g.resLE U (g ⁻¹ᵁ U) le_rfl) ⟶
      (Scheme.Modules.localizedPullback g U).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q ⋙
          C.mapDerivedCategory,
      ∀ K : CochainComplex
          (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) ℤ,
        Scheme.IsStrictlyPerfect S U K → IsIso (η.app K) := by
  dsimp only
  let V := g ⁻¹ᵁ U
  let f := g.resLE U V le_rfl
  let A : SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U) ⥤
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) :=
    (Scheme.Modules.overEquiv U).functor
  let C : SheafOfModules.{u} ((moduleRings T.toRingedSpace).over V) ⥤
      SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace) :=
    (Scheme.Modules.overEquiv V).functor
  let B : SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace) ⥤
      SheafOfModules.{u} ((moduleRings T.toRingedSpace).over V) :=
    (Scheme.Modules.overEquiv V).inverse
  have : A.Additive := Functor.additive_of_preserves_binary_products _
  have : B.Additive := Functor.additive_of_preserves_binary_products _
  have : C.Additive := Functor.additive_of_preserves_binary_products _
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
    E, hE, hEmap, hEadd, ε, hderived, htri, hε⟩ :=
    (derivedPullback_spec f)
  have hEq : E = Scheme.Modules.tensorPullback f :=
    CategoryTheory.Functor.ext hE (fun _ _ a ↦ hEmap a)
  subst E
  have : (Scheme.Modules.tensorPullback f).Additive := hEadd
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction f
  let L := derivedPullback f
  let qU := HomotopyCategory.quotient
    (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) (.up ℤ)
  let qV := HomotopyCategory.quotient
    (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace)) (.up ℤ)
  let E : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace) :=
    Scheme.Modules.tensorPullback f
  let EH := E.mapHomotopyCategory (.up ℤ)
  let EC := E.mapHomologicalComplex (.up ℤ)
  let G : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace) :=
    Scheme.Modules.pullback f
  have : G.Additive := Scheme.Modules.instAdditivePullback f
  have : (A ⋙ G).Additive := inferInstance
  let t : E ≅ G := adj.leftAdjointUniq (Scheme.Modules.pullbackPushforwardAdjunction f)
  let GC := G.mapHomologicalComplex (.up ℤ)
  let AC := A.mapHomologicalComplex (.up ℤ)
  let CC := C.mapHomologicalComplex (.up ℤ)
  let F := Scheme.Modules.localizedPullback g U
  let FC := F.mapHomologicalComplex (.up ℤ)
  let c : DerivedCategory.Q ⋙ L ⟶ GC ⋙ DerivedCategory.Q :=
    (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso _).symm L).hom ≫
      (Functor.associator qU DerivedCategory.Qh L).hom ≫
      Functor.whiskerLeft qU ε ≫
      (Functor.associator qU EH DerivedCategory.Qh).inv ≫
      (Functor.isoWhiskerRight (E.mapHomotopyCategoryFactors (.up ℤ))
        DerivedCategory.Qh).hom ≫
      (Functor.associator EC qV DerivedCategory.Qh).hom ≫
      (Functor.isoWhiskerLeft EC (DerivedCategory.quotientCompQhIso _)).hom ≫
      (Functor.isoWhiskerRight (NatIso.mapHomologicalComplex t (.up ℤ))
        DerivedCategory.Q).hom
  let δ : F ⋙ C ≅ A ⋙ G :=
    Functor.associator A (G ⋙ B) C ≪≫
      Functor.isoWhiskerLeft A (Functor.associator G B C) ≪≫
      Functor.isoWhiskerLeft A
        (Functor.isoWhiskerLeft G (Scheme.Modules.overEquiv V).counitIso) ≪≫
      Functor.isoWhiskerLeft A (Functor.rightUnitor G)
  let r : FC ⋙ DerivedCategory.Q ⋙ C.mapDerivedCategory ≅
      AC ⋙ GC ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerLeft FC C.mapDerivedCategoryFactors ≪≫
      (Functor.associator FC CC DerivedCategory.Q).symm ≪≫
      Functor.isoWhiskerRight
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ C)) (.up ℤ)).symm ≪≫
          NatIso.mapHomologicalComplex δ (.up ℤ) ≪≫
          Functor.mapHomologicalComplexCompIso (Iso.refl (A ⋙ G)) (.up ℤ))
        DerivedCategory.Q ≪≫ Functor.associator AC GC DerivedCategory.Q
  let η : DerivedCategory.Q ⋙ A.mapDerivedCategory ⋙ L ⟶
      FC ⋙ DerivedCategory.Q ⋙ C.mapDerivedCategory :=
    (Functor.associator DerivedCategory.Q A.mapDerivedCategory L).inv ≫
      (Functor.isoWhiskerRight A.mapDerivedCategoryFactors L).hom ≫
      (Functor.associator AC DerivedCategory.Q L).hom ≫
      Functor.whiskerLeft AC c ≫ r.inv
  refine ⟨η, ?_⟩
  intro K hK
  let P := AC.obj K
  obtain ⟨⟨a, b, hb⟩, hp⟩ := hK
  have hPbounded : ∃ b : ℤ, ∀ n : ℤ, b < n → IsZero (P.X n) :=
    ⟨b, fun n hn ↦ A.map_isZero (hb n (Or.inr hn))⟩
  have hPflat : ∀ n : ℤ, SheafOfModules.IsFlat (P.X n) := by
    intro n
    obtain ⟨m, i, r, hir⟩ := hp n
    let ei : A.obj (SheafOfModules.free
        (R := (moduleRings S.toRingedSpace).over U) (ULift.{u} (Fin m))) ≅
        SheafOfModules.free (R := moduleRings U.toScheme.toRingedSpace)
          (ULift.{u} (Fin m)) :=
      (asIso (sigmaComparison A (fun _ : ULift.{u} (Fin m) ↦
        SheafOfModules.unit ((moduleRings S.toRingedSpace).over U)))).symm ≪≫
      Sigma.mapIso (fun _ ↦ U.sheafOfModulesEquivOverUnit (moduleRings S.toRingedSpace))
    apply flat_retract U.toScheme (P.X n) m (A.map i ≫ ei.hom) (ei.inv ≫ A.map r)
    change (A.map i ≫ ei.hom) ≫ ei.inv ≫ A.map r = 𝟙 (A.obj (K.X n))
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, hir]
    exact A.map_id _
  have : IsIso (ε.app (qU.obj P)) := hε P
    (CochainComplex.isKFlat_of_boundedAbove_flat_ringedSpace
      U.toScheme.toRingedSpace P hPbounded hPflat)
  dsimp only [η, c, NatTrans.comp_app, Functor.whiskerLeft_app]
  infer_instance

end AlgebraicGeometry

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import Sheaf.Algebra.Homology.DerivedInternalHom
public import Sheaf.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Sheaf.Algebra.Homology.HomComplexSingleNatural
import Sheaf.Algebra.Homology.HomComplex
import Sheaf.Algebra.Homology.QuasiIsoHomComplexMap
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives

/-! # Deriving internal Hom from a module in degree zero

Source: Stacks Project, Cohomology on Sites, Section 08J7, Lemma 0A95;
Duality for Schemes, Tag 0BV1.
-/

@[expose] public section

universe u w

open CategoryTheory Opposite TopologicalSpace

namespace CategoryTheory

/-- A right derived functor of termwise internal Hom from a fixed module agrees with
internal RHom from that module placed in degree zero. This comparison concerns only
O-modules, and requires neither an algebra structure nor an adjunction.

Source: Stacks Project, Cohomology on Sites, Section 08J7, Lemma 0A95;
Duality for Schemes, Tag 0BV1, lemma-sheafhom-affine-ext
(blueprint: lem-sc-derived-internal-hom-single-comparison).

Proof:
1. Let I be the functorial K-injective resolution of the Grothendieck abelian category
   of R-modules. The right derivability structure of K-injectives computes the given
   right derived functor S on I, with its comparison invertible on K-injective objects.
   Indeed, quasi-isomorphisms between K-injectives are homotopy equivalences;
   additive termwise Hom preserves homotopies, and Q inverts homotopy equivalences.
2. For M concentrated in degree zero, the degree n term of Hom-complex(M[0], I) is
   Hom(M, I.X n): only the degree-zero source factor survives in the product defining
   Hom-complex. Its differential is postcomposition with d_I, since d_M is zero.
   The existing homComplex_single_iso gives this identification objectwise. Its
   projection construction and the Hom-complex map formula show naturality. Thus
   projection onto that factor and insertion with zero in all other factors give a
   natural chain isomorphism with the termwise internal Hom complex.
3. Apply derivedInternalHom_comparison to this same I and fix the first variable at
   M[0]. Compose its comparison with the natural chain isomorphism from step 2.
4. The resulting comparisons identify both functors on K-injective representatives,
   naturally in all morphisms. The K-injective localization equivalence descends this
   natural isomorphism to the derived category. Equivalently, uniqueness of the right
   derived functor transports the comparison to the given S. This includes zero M,
   arbitrary unbounded complexes, and every choice of the derived-category universe. -/
theorem derivedInternalHom_single_comparison
    (X : AlgebraicGeometry.Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (AlgebraicGeometry.moduleRings X.toRingedSpace))]
    (M : SheafOfModules.{u} (AlgebraicGeometry.moduleRings X.toRingedSpace))
    [((SheafOfModules.homFunctor X.sheaf).obj (op M)).Additive]
    (S : DerivedCategory (SheafOfModules.{u}
      (AlgebraicGeometry.moduleRings X.toRingedSpace)) ⥤
      DerivedCategory (SheafOfModules.{u}
        (AlgebraicGeometry.moduleRings X.toRingedSpace)))
    (δ : ((SheafOfModules.homFunctor X.sheaf).obj (op M)).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ S)
    (hδ : S.IsRightDerivedFunctor δ (HomologicalComplex.quasiIso _ (.up ℤ))) :
    Nonempty (S ≅ (Functor.curry.obj
      (derivedInternalHom (Opens.grothendieckTopology X) X.sheaf)).obj
        (op ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  classical
  let A := SheafOfModules.{u} (AlgebraicGeometry.moduleRings X.toRingedSpace)
  let Pc := (CochainComplex.singleFunctor A 0).obj M
  let T : A ⥤ A := (SheafOfModules.homFunctor X.sheaf).obj (op M)
  let H := (homComplexFunctor (R := X.sheaf)).obj (op Pc)
  let T₀ := T.mapHomologicalComplex (ComplexShape.up ℤ)
  obtain ⟨eH⟩ := homComplex_single_natIso X M
  let _ : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let I := CochainComplex.kInjectiveResolutionFunctor.{u} A
  let η := CochainComplex.toKInjectiveResolution.{u} A
  let Φ := CochainComplex.KInjectives.localizerMorphism A
  have hderive : Φ.Derives (T₀ ⋙ DerivedCategory.Q) := by
    intro K L f hf
    have : K.obj.IsKInjective := K.property
    have : L.obj.IsKInjective := L.property
    have : QuasiIso f.hom := hf
    have hq : QuasiIso (H.map f.hom) := by
      have h := quasiIso_homComplex_map (R := X.sheaf) f.hom (𝟙 Pc)
      simpa only [op_id, Functor.map_id, NatTrans.id_app, Category.id_comp] using h
    have hi : IsIso (DerivedCategory.Q.map (H.map f.hom)) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hq
    have hnQ := congrArg DerivedCategory.Q.map (eH.hom.naturality f.hom)
    simp only [Functor.map_comp] at hnQ
    have : IsIso (DerivedCategory.Q.map (eH.hom.app K.obj) ≫
        DerivedCategory.Q.map (T₀.map f.hom)) := by
      rw [← hnQ]
      infer_instance
    have hiT : IsIso (DerivedCategory.Q.map (T₀.map f.hom)) :=
      IsIso.of_isIso_comp_left (DerivedCategory.Q.map (eH.hom.app K.obj))
        (DerivedCategory.Q.map (T₀.map f.hom))
    exact hiT
  let _ := hδ
  have hδI : IsIso (Functor.whiskerLeft I δ) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    have : (I.obj K).IsKInjective :=
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A K
    exact hderive.isIso_of_isRightDerivedFunctor (L₂ := DerivedCategory.Q) (RF := S) δ
      (CochainComplex.KInjectives.mk (I.obj K))
  have hηS : IsIso (Functor.whiskerRight η (DerivedCategory.Q ⋙ S)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    have : QuasiIso (η.app K) :=
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A K).2
    have : IsIso (DerivedCategory.Q.map (η.app K)) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr inferInstance
    exact S.map_isIso _
  obtain ⟨eR⟩ := derivedInternalHom_comparison (Opens.grothendieckTopology X) X.sheaf
    I η (fun K ↦ ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A K).2,
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A K⟩)
  let R₀ := (Functor.curry.obj
    (derivedInternalHom (Opens.grothendieckTopology X) X.sheaf)).obj
      (op (DerivedCategory.Q.obj Pc))
  let eR₀ : DerivedCategory.Q ⋙ R₀ ≅ I ⋙ H ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun K ↦ eR.app (op Pc, K)) (by
      intro K L f
      simpa only [Functor.comp_map, Functor.prod_map, Functor.prod_obj, Functor.id_obj,
        Functor.op_map, op_id, unop_id,
        Functor.map_id, Functor.uncurry_obj_map, NatTrans.id_app, Category.id_comp,
        R₀, H,
        Functor.comp_obj, Functor.op_obj,
        Functor.uncurry_obj_obj, Functor.curry_obj_obj_obj, Iso.app_hom,
        Functor.curry_obj_obj_map] using
          eR.hom.naturality (X := (op Pc, K)) (Y := (op Pc, L)) (𝟙 (op Pc), f))
  let eIQ : I ⋙ H ⋙ DerivedCategory.Q ≅ I ⋙ T₀ ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerLeft I (Functor.isoWhiskerRight eH DerivedCategory.Q)
  let eS : DerivedCategory.Q ⋙ S ≅ I ⋙ T₀ ⋙ DerivedCategory.Q :=
    asIso (Functor.whiskerRight η (DerivedCategory.Q ⋙ S)) ≪≫
      (asIso (Functor.whiskerLeft I δ)).symm
  exact ⟨Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ)) _ _ S R₀
      (eS ≪≫ eIQ.symm ≪≫ eR₀.symm)⟩

end CategoryTheory

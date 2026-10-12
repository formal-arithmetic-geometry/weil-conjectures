/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Sheaf.AlgebraicGeometry.Modules.IsKFlatTilde
import Sheaf.AlgebraicGeometry.TensorPullbackTilde
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.KFlatPullback
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.AlgebraicGeometry.Modules.AffineTildeTensor

/-! # Affine computations of derived pullback and tensor

Source: Stacks Project, Lemmas 36.3.8(2), 36.3.9(2), Tags 08DW and 08DX,
and Lemma 36.3.6, Tag 08DV
(blueprint: lem-pc-affine-derived-pullback-tensor-tilde).

The affine formulas are written for every K-flat resolution `P ⟶ M`.
Thus the right sides are the concrete representatives of the module derived tensors,
with no boundedness, flatness of the ring map, or quasi-coherence hypothesis added.

## Main statements

- `derivedPullback_openRestriction_iso`: restriction of derived pullback.
- `derivedTensor_openRestriction_iso`: restriction of derived tensor, natural in both factors.
- `derivedPullback_tilde_iso`: affine pullback on any K-flat resolution.
- `derivedTensor_tilde_iso`: affine tensor on any K-flat resolution of the first factor.
- `derivedPullback_tilde_kFlat_natIso`: natural affine pullback comparison on K-flat models.
- `derivedTensor_tilde_kFlat_natIso`: natural affine tensor comparison on K-flat models.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Derived pullback commutes naturally with restriction to opens.
Source: Stacks, Tag 08DW, proof
(blueprint: lem-pc-affine-derived-pullback-tensor-tilde).
Proof (node step 1): choose a K-flat resolution on Y (lem-pc-kflat-resolution).
Restriction to V preserves K-flatness (lem-pc-kflat-pullback-preservation).
Termwise tensor pullback and restriction commute, so both composite functors are
computed by the same pulled-back restricted resolution (def-pc-derived-pullback).
The resolution comparison is natural and descends to the derived category. -/
theorem derivedPullback_openRestriction_iso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : X.Opens) (V : Y.Opens) (hUV : U ≤ f ⁻¹ᵁ V)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))] :
    Nonempty (derivedPullback f ⋙
      (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Scheme.Modules.overEquiv U)).mapDerivedCategory ≅
      (SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) V ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V))
          (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
          (Scheme.Modules.overEquiv V)).mapDerivedCategory ⋙
        derivedPullback (f.resLE V U hUV)) := by
  sorry

/-- Derived tensor commutes with restriction to any open subscheme.
Source: Stacks, Tag 08DX, proof; the restriction computation of Tag 08DW
(blueprint: lem-pc-affine-derived-pullback-tensor-tilde).
Proof (node step 1): choose a K-flat resolution of K (lem-pc-kflat-resolution).
It remains K-flat on U (lem-pc-kflat-pullback-preservation). Restriction commutes
with sheaf tensor and all direct sums in the signed total complex
(def-pc-tensor-complex-sheaves), so it identifies the two derived tensors.
The comparisons are induced by restriction of the total tensor complex. -/
theorem derivedTensor_openRestriction_iso (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    : Nonempty
      (curriedTensor (schemeDerivedCategory X) ⋙
        (Functor.whiskeringRight (schemeDerivedCategory X) (schemeDerivedCategory X)
          (schemeDerivedCategory U.toScheme)).obj
          (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U)).mapDerivedCategory ≅
        (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U)).mapDerivedCategory ⋙
          curriedTensor (schemeDerivedCategory U.toScheme) ⋙
          (Functor.whiskeringLeft (schemeDerivedCategory X)
            (schemeDerivedCategory U.toScheme) (schemeDerivedCategory U.toScheme)).obj
            (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U)).mapDerivedCategory) := by
  sorry

private theorem moduleKFlat_acyclic (A : Type u) [CommRing A]
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat P)
    (F : CochainComplex (ModuleCat.{u} A) ℤ) (hF : F.Acyclic) :
    (CochainComplex.mapBifunctor F P (curriedTensor (ModuleCat.{u} A))).Acyclic := by
  have h := (HomotopyCategory.kFlat_iff_preserves_acyclic
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P)).mp
      ((HomotopyCategory.kFlat_quotient_obj_iff P).mpr hP)
  have hF' := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic F).mpr hF
  exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).mp
    (h _ hF').2

/-- Naturality of the affine pullback comparison on K-flat module models.
Source: Stacks, Tag 08DW(2), via Tag 08DV
(blueprint: lem-pc-affine-derived-pullback-tensor-tilde).
Proof (node step 2): apply the natural termwise tilde/base-change isomorphism
(lem-weil-pbc-tilde-pullback-base-change) to K-flat complexes. Their tilde complexes
are K-flat (lem-pc-affine-tilde-kflat), so the derived-pullback counit is invertible
there (def-pc-derived-pullback). Compose the two natural comparisons. For arbitrary
M use a K-flat resolution P to M; exact tilde sends it to an isomorphism after Q
(lem-pc-affine-qcoh-derived-equivalence). Naturality on K-flat models gives compatibility
with resolution comparisons, hence the affine formula independent of that choice. -/
theorem derivedPullback_tilde_kFlat_natIso (A B : Type u) [CommRing A] [CommRing B]
    (φ : A →+* B)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace))] :
    Nonempty
      (CochainComplex.ιKFlat (ModuleCat.{u} A) ⋙
        (@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (ModuleCat.{u} A ⥤
            SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)) ⋙
          DerivedCategory.Q ⋙ derivedPullback (Spec.map (CommRingCat.ofHom φ)) ≅
        CochainComplex.ιKFlat (ModuleCat.{u} A) ⋙
          (ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ) ⋙
          (@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (ModuleCat.{u} B ⥤
            SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace))
            (tilde.functor (.of B))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)) ⋙ DerivedCategory.Q) := by
  let f := Spec.map (CommRingCat.ofHom φ)
  let T := @Functor.mapHomologicalComplex _ _ _ _ _ _ _
    (@id (ModuleCat.{u} A ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
      (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)
  let F := CochainComplex.ιKFlat (ModuleCat.{u} A) ⋙ T
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres, E, hE, hEmap, hEadd,
    ε, hε, htri, hflat⟩ := Classical.choose_spec (exists_derivedPullback f)
  let η : E ≅ Scheme.Modules.tensorPullback f :=
    NatIso.ofComponents (fun M ↦ eqToIso (hE M)) (by
      intro M N a
      dsimp
      rw [hEmap]
      simp
      rfl)
  have : (Scheme.Modules.tensorPullback f).Additive := Functor.additive_of_iso η
  have hεiso (P : CochainComplex.KFlat (ModuleCat.{u} A)) :
      IsIso ((Functor.whiskerLeft
        (F ⋙ HomotopyCategory.quotient _ (.up ℤ)) ε).app P) := by
    apply hflat
    exact isKFlat_tilde A P.obj (moduleKFlat_acyclic A P.obj P.property)
  have : IsIso (Functor.whiskerLeft (F ⋙ HomotopyCategory.quotient _ (.up ℤ)) ε) :=
    NatIso.isIso_of_isIso_app _
  let β := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft F (DerivedCategory.quotientCompQhIso _).symm) (derivedPullback f) ≪≫
    asIso (Functor.whiskerLeft (F ⋙ HomotopyCategory.quotient _ (.up ℤ)) ε) ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft F (E.mapHomotopyCategoryFactors (.up ℤ)))
      DerivedCategory.Qh ≪≫
    Functor.isoWhiskerLeft (F ⋙ E.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso _)
  obtain ⟨θ, _⟩ := Scheme.Modules.exists_tensorPullback_tilde_iso (CommRingCat.ofHom φ)
  let γ := Functor.isoWhiskerRight (NatIso.mapHomologicalComplex η (.up ℤ)) DerivedCategory.Q
  let TB := @Functor.mapHomologicalComplex _ _ _ _ _ _ _
    (@id (ModuleCat.{u} B ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace))
      (tilde.functor (.of B))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)
  let δ₀ : T ⋙ (Scheme.Modules.tensorPullback f).mapHomologicalComplex (.up ℤ) ≅
      (ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ) ⋙ TB :=
    NatIso.ofComponents (fun P ↦ HomologicalComplex.Hom.isoOfComponents
      (fun i ↦ θ.app (P.X i)) (by
        intro i j hij
        exact (θ.hom.naturality (P.d i j)).symm)) (by
      intro P M a
      apply HomologicalComplex.hom_ext
      intro i
      exact θ.hom.naturality (a.f i))
  let QB : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) ℤ ⥤
      schemeDerivedCategory (Spec (.of B)) := DerivedCategory.Q
  let δ := Functor.isoWhiskerRight δ₀ QB
  exact ⟨β ≪≫ Functor.isoWhiskerLeft F γ ≪≫
    Functor.isoWhiskerLeft (CochainComplex.ιKFlat (ModuleCat.{u} A)) δ⟩

/-- Naturality of the affine tensor comparison in a K-flat first model and an arbitrary
second complex. Source: Stacks, Tag 08DX(2), via Tag 08DV
(blueprint: lem-pc-affine-derived-pullback-tensor-tilde).
Proof (node step 3): tilde of the first model is K-flat (lem-pc-affine-tilde-kflat).
Compute sheaf derived tensor by that model (def-pc-kflat-complex). Apply the natural
tilde/tensor isomorphism in each bidegree (lem-weil-pbc-affine-tilde-tensor), then
preservation of arbitrary coproducts by tilde, to obtain the total-complex comparison
(def-pc-tensor-complex-sheaves). All maps commute with both differentials and with
maps in both variables. Resolve an arbitrary first complex (lem-pc-kflat-resolution);
exactness of tilde (lem-pc-affine-qcoh-derived-equivalence) and naturality give the
comparison for it, independently of the chosen resolution. -/
theorem derivedTensor_tilde_kFlat_natIso (A : Type u) [CommRing A]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))] :
    Nonempty
      (CochainComplex.ιKFlat (ModuleCat.{u} A) ⋙
        (@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (ModuleCat.{u} A ⥤
            SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)) ⋙ DerivedCategory.Q ⋙
          curriedTensor (schemeDerivedCategory (Spec (.of A))) ⋙
          (Functor.whiskeringLeft (CochainComplex (ModuleCat.{u} A) ℤ)
            (schemeDerivedCategory (Spec (.of A)))
            (schemeDerivedCategory (Spec (.of A)))).obj
            ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (ModuleCat.{u} A ⥤
            SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)) ⋙ DerivedCategory.Q) ≅
        CochainComplex.ιKFlat (ModuleCat.{u} A) ⋙
          (curriedTensor (ModuleCat.{u} A)).map₂CochainComplex ⋙
          (Functor.whiskeringRight (CochainComplex (ModuleCat.{u} A) ℤ)
            (CochainComplex (ModuleCat.{u} A) ℤ)
            (schemeDerivedCategory (Spec (.of A)))).obj
            ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (ModuleCat.{u} A ⥤
            SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)) ⋙ DerivedCategory.Q)) := by
  sorry

private theorem affineTilde_Q_map_isIso (A : Type u) [CommRing A]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    {P M : CochainComplex (ModuleCat.{u} A) ℤ} (s : P ⟶ M) (hs : QuasiIso s) :
    IsIso (DerivedCategory.Q.map
      (((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
        (@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ))).map s)) := by
  let := HasDerivedCategory.standard (ModuleCat.{u} A)
  obtain ⟨e, ⟨α⟩, _⟩ := exists_affineQCohDerivedEquivalence A
  have : QuasiIso s := hs
  exact (NatIso.isIso_map_iff α s).mp (by
    change IsIso (((e.functor ⋙ (schemeDerivedQCohProperty (Spec (.of A))).ι).map
      (DerivedCategory.Q.map s)))
    infer_instance)

/-- Affine derived pullback of termwise tilde is termwise tilde of derived base change,
computed on any K-flat resolution of the input complex.
Source: Stacks, Tag 08DW(2), via Tag 08DV
(blueprint: lem-pc-affine-derived-pullback-tensor-tilde).
Proof (node step 2): resolve M by P (lem-pc-kflat-resolution). Termwise tilde
preserves quasi-isomorphisms (lem-pc-affine-qcoh-derived-equivalence), and tilde P
is K-flat (lem-pc-affine-tilde-kflat). Derived pullback is therefore represented
by termwise tensor pullback of tilde P (def-pc-derived-pullback).
The natural tilde/base-change comparison in each degree
(lem-weil-pbc-tilde-pullback-base-change) identifies this with tilde of B tensor P.
This complex computes M tensor-derived B since P is K-flat. -/
theorem derivedPullback_tilde_iso (A B : Type u) [CommRing A] [CommRing B]
    (φ : A →+* B)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace))]
    (M P : CochainComplex (ModuleCat.{u} A) ℤ) (s : P ⟶ M) (hs : QuasiIso s)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat P) :
    Nonempty
      ((derivedPullback (Spec.map (CommRingCat.ofHom φ))).obj
        (DerivedCategory.Q.obj
          ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
            (@id (ModuleCat.{u} A ⥤
              SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
              (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M)) ≅
        DerivedCategory.Q.obj
          ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
            (@id (ModuleCat.{u} B ⥤
              SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace))
              (tilde.functor (.of B))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj
                (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P))) := by
  let T := @Functor.mapHomologicalComplex _ _ _ _ _ _ _
    (@id (ModuleCat.{u} A ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
      (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)
  have : IsIso (DerivedCategory.Q.map (T.map s)) := affineTilde_Q_map_isIso A s hs
  obtain ⟨α⟩ := derivedPullback_tilde_kFlat_natIso A B φ
  exact ⟨(derivedPullback (Spec.map (CommRingCat.ofHom φ))).mapIso
    (asIso (DerivedCategory.Q.map (T.map s))).symm ≪≫ α.app ⟨P, hP⟩⟩

/-- On an affine scheme, derived tensor of termwise tilde complexes is termwise tilde
of module derived tensor, computed with any K-flat resolution of the first factor.
Source: Stacks, Tag 08DX(2), via Tag 08DV
(blueprint: lem-pc-affine-derived-pullback-tensor-tilde).
Proof (node step 3): resolve M by P (lem-pc-kflat-resolution). Exactness of termwise
tilde (lem-pc-affine-qcoh-derived-equivalence) and K-flatness of tilde P
(lem-pc-affine-tilde-kflat) allow the sheaf derived tensor to be computed by
Tot(tilde P tensor tilde N) (def-pc-kflat-complex, def-pc-tensor-complex-sheaves).
In each bidegree apply lem-weil-pbc-affine-tilde-tensor; its naturality respects
both differentials. Tilde preserves the direct sums used in totalization, yielding
tilde Tot(P tensor N). This computes M tensor-derived N since P is K-flat.
The sum over p+q=n can be infinite for unbounded complexes; all coproducts, not just
finite ones, are preserved by tilde, which is a left adjoint. -/
theorem derivedTensor_tilde_iso (A : Type u) [CommRing A]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    (M N P : CochainComplex (ModuleCat.{u} A) ℤ) (s : P ⟶ M) (hs : QuasiIso s)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat P) :
    Nonempty
      (DerivedCategory.Q.obj
        ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (ModuleCat.{u} A ⥤
            SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M) ⊗
        DerivedCategory.Q.obj
          ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
            (@id (ModuleCat.{u} A ⥤
              SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
              (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj N) ≅
        DerivedCategory.Q.obj
          ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
            (@id (ModuleCat.{u} A ⥤
              SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
              (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj
                (CochainComplex.mapBifunctor P N (curriedTensor (ModuleCat.{u} A))))) := by
  let T := @Functor.mapHomologicalComplex _ _ _ _ _ _ _
    (@id (ModuleCat.{u} A ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
      (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)
  have : IsIso (DerivedCategory.Q.map (T.map s)) := affineTilde_Q_map_isIso A s hs
  obtain ⟨α⟩ := derivedTensor_tilde_kFlat_natIso A
  exact ⟨((curriedTensor (schemeDerivedCategory (Spec (.of A)))).flip.obj
    (DerivedCategory.Q.obj (T.obj N))).mapIso
      (asIso (DerivedCategory.Q.map (T.map s))).symm ≪≫ (α.app ⟨P, hP⟩).app N⟩


end AlgebraicGeometry

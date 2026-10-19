/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Sheaf.AlgebraicGeometry.FiniteTorDimension
import Sheaf.AlgebraicGeometry.FiniteAffineCechModelDerivedComparison
import Sheaf.AlgebraicGeometry.FiniteAffineCechModelFlatOver
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.RingHom.Flat
import Sheaf.AlgebraicGeometry.AffineFlatModuleTensorFlat
import Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction
import Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle

/-! # Local finite Tor dimension of a proper relatively flat single-module direct image

Source: Stacks Project, Tag 0A1H, single-module case; Tags 08CG and 08CI.
(blueprint: lem-pc-proper-flat-single-local-finite-tor).
-/

@[expose] public section
set_option autoImplicit false
universe u wX wS
open CategoryTheory
namespace AlgebraicGeometry

/-- Relative flatness restricts along any commutative square of open immersions.
The square need not be a pullback, and the source open can be smaller than the
inverse image of the base open. -/
private theorem flatOver_openImmersion_square {X T Y B : Scheme.{u}}
    (f : X ⟶ T) (i : Y ⟶ X) (j : B ⟶ T) (p : Y ⟶ B)
    [IsOpenImmersion i] [IsOpenImmersion j] (h : i ≫ f = p ≫ j)
    (F : X.Modules) (hF : F.IsFlatOver f) :
    (F.restrict i).IsFlatOver p := by
  intro V W e
  let V' : T.affineOpens := ⟨j ''ᵁ V.1, V.2.image_of_isOpenImmersion j⟩
  let W' : X.affineOpens := ⟨i ''ᵁ W.1, W.2.image_of_isOpenImmersion i⟩
  have e' : W'.1 ≤ f ⁻¹ᵁ V'.1 := by
    rintro x ⟨y, hy, rfl⟩
    refine ⟨p y, e hy, ?_⟩
    exact congrArg (fun q : Y ⟶ T ↦ q y) h.symm
  let φ := (j.appIso V.1).inv
  let ψ := f.appLE V'.1 W'.1 e'
  let : Module Γ(T, V'.1) Γ(F, W'.1) := Module.compHom _ ψ.hom
  have : Module.Flat Γ(T, V'.1) Γ(F, W'.1) := hF V' W' e'
  let : Algebra Γ(B, V.1) Γ(T, V'.1) := φ.hom.toAlgebra
  have : Module.Flat Γ(B, V.1) Γ(T, V'.1) :=
    RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso φ)
  let : Module Γ(B, V.1) Γ(F, W'.1) := Module.compHom _ φ.hom
  let : IsScalarTower Γ(B, V.1) Γ(T, V'.1) Γ(F, W'.1) :=
    ⟨fun a b m ↦ mul_smul _ _ _⟩
  have hh := Module.Flat.trans Γ(B, V.1) Γ(T, V'.1) Γ(F, W'.1)
  have he : φ ≫ ψ = p.appLE V.1 W.1 e ≫ (i.appIso W.1).inv := by
    apply (cancel_epi (j.appIso V.1).hom).mp
    apply (cancel_mono (i.appIso W.1).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.appIso_hom',
      Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    congr 1
  convert hh using 1 <;> try rfl
  ext a m
  change (F.smul (((i.appIso W.1).inv.hom
    ((p.appLE V.1 W.1 e).hom a)))).hom m =
      (F.smul (ψ.hom (φ.hom a))).hom m
  exact congrArg (fun q : Γ(B, V.1) ⟶ Γ(X, W'.1) ↦ (F.smul (q.hom a)).hom m) he.symm

open CategoryTheory.Limits MonoidalCategory in
/-- Tensor with a module in degree zero preserves the termwise vanishing interval. -/
private theorem tensor_homology_isZero_of_term_isZero (Y : Scheme.{u})
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (G : SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (n : ℤ)
    (hn : IsZero (P.X n)) :
    letI := SheafOfModules.monoidalCategory Y.sheaf
    IsZero ((CochainComplex.mapBifunctor P
      ((HomologicalComplex.single _ (.up ℤ) 0).obj G) (curriedTensor _)).homology n) := by
  let := SheafOfModules.monoidalCategory Y.sheaf
  let T := CochainComplex.mapBifunctor P
    ((HomologicalComplex.single _ (.up ℤ) 0).obj G) (curriedTensor _)
  let e := CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) G P
  have hz : IsZero (T.X n) :=
    IsZero.of_iso ((tensorRight G).map_isZero hn)
      ((HomologicalComplex.eval _ (.up ℤ) n).mapIso e)
  exact (T.sc n).isZero_homology_of_isZero_X₂ hz

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- On each affine base open the restricted direct image has a finite Tor interval.
The interval may depend on the neighbourhood. This supplies no finite-free model
and asserts no pseudo-coherence.
Source: Stacks Project, Tag 0A1H with E=O_X and G=F[0]; Tags 01XD, 08CG, 08CI.
(blueprint: lem-pc-proper-flat-single-local-finite-tor).

Proof: On the supplied affine open U, properness makes its inverse image
quasi-compact and separated. Choose a finite affine cover of that inverse image.
The alternating Cech section complex is bounded in degrees [0,d]; intersections
are affine and its section modules are flat over the ring of U by relative
flatness. Associate module sheaves on U. This gives a bounded complex of flat
quasi-coherent sheaves representing the restricted direct image, by affine
acyclicity and the Cech-to-derived comparison. A bounded flat complex is K-flat.
Tensoring it with any module in degree zero has zero terms, hence zero homology,
outside [0,d]. Thus the same interval works for every test module, as required
by finite Tor dimension. Transport the representing isomorphism from the
K-injective computation to the supplied target localization using uniqueness of
localization; its terms, flatness and vanishing are unchanged. Empty inverse images
and zero modules give the zero complex with interval [0,0].
-/
theorem properFlat_single_local_hasFiniteTorDimension
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [LocallyOfFinitePresentation f] [QuasiCompact f]
    [HasDerivedCategory.{wX}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wS}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    (F : X.Modules) [F.IsFinitePresentation] (hF : F.IsFlatOver f)
    (U : S.Opens) (hU : IsAffineOpen U)
    [HasDerivedCategory.{wS}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))] :
    U.toScheme.HasFiniteTorDimension ((schemeOpenRestriction S U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F)))  := by
  classical
  let Y := (f ⁻¹ᵁ U).toScheme
  let G := F.restrict (f ⁻¹ᵁ U).ι
  let p := f ∣_ U
  let : IsAffine U.toScheme := hU
  let : HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
    HasDerivedCategory.standard _
  have hG : G.IsFlatOver p := flatOver_openImmersion_square f (f ⁻¹ᵁ U).ι U.ι p
    (morphismRestrict_ι f U).symm F hF
  have : CompactSpace Y :=
    isCompact_iff_compactSpace.mp (f.isCompact_preimage hU.isCompact)
  let C := Y.affineCover.finiteSubcover
  let e := (Fintype.equivFin C.I₀).symm
  let V : Fin (Fintype.card C.I₀) → Y.Opens := fun i ↦ (C.f (e i)).opensRange
  have hV : ∀ i, IsAffineOpen (V i) := fun i ↦ isAffineOpen_opensRange (C.f (e i))
  have hcover : iSup V = ⊤ :=
    (e.surjective.iSup_comp (fun i ↦ (C.f i).opensRange)).trans C.iSup_opensRange
  let P := Scheme.Modules.finiteAffineCechModel p G V
  have hle := Scheme.Modules.finiteAffineCechModel_le p G V
  have hge := Scheme.Modules.finiteAffineCechModel_ge p G V
  have hbounded : ∀ n : ℤ, n < 0 ∨ (Fintype.card C.I₀ : ℤ) < n →
      CategoryTheory.Limits.IsZero (P.X n) := by
    intro n hn
    rcases hn with hn | hn
    · exact (CochainComplex.isStrictlyGE_iff _ _).mp hge n hn
    · exact (CochainComplex.isStrictlyLE_iff _ _).mp hle n hn
  have hflat : ∀ n : ℤ, SheafOfModules.IsFlat (P.X n) := fun n ↦
    isFlat_of_affineFlatOver_identity _
      (Scheme.Modules.finiteAffineCechModel_flatOver p G hG V hV n)
  have hP := CochainComplex.isKFlat_of_boundedAbove_flat_ringedSpace
    U.toScheme.toRingedSpace P
    ⟨Fintype.card C.I₀, fun n hn ↦ hbounded n (Or.inr hn)⟩ hflat
  obtain ⟨c⟩ := Scheme.Modules.finiteAffineCechModel_derivedComparison p G V hV hcover
  obtain ⟨d⟩ := schemeDerivedDirectImage_openRestriction f U
  let R := schemeOpenRestriction X (f ⁻¹ᵁ U)
  let s : R.mapDerivedCategory.obj ((DerivedCategory.singleFunctor _ 0).obj F) ≅
      (DerivedCategory.singleFunctor _ 0).obj G :=
    (R.mapDerivedCategorySingleFunctor 0).app F ≪≫
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).mapIso
        ((Scheme.Modules.overFunctorEquiv (f ⁻¹ᵁ U)).app F)
  let c' := c ≪≫ ((schemeDerivedDirectImage p).mapIso s).symm ≪≫
    (d.app ((DerivedCategory.singleFunctor _ 0).obj F)).symm
  refine ⟨0, Fintype.card C.I₀, by omega, ?_⟩
  intro M n hn
  exact ⟨P, hP, ⟨c'⟩,
    tensor_homology_isZero_of_term_isZero U.toScheme P M n (hbounded n hn)⟩

end AlgebraicGeometry

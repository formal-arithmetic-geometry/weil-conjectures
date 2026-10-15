/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Paper.DerivedHomMayerVietoris
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

import Sheaf.AlgebraicGeometry.QCohOrdinaryTensorResolutionCoordinatesFamily
import Sheaf.Algebra.Homology.QuotientTensorResolutionLiftHomotopy

/-! # Affine ordinary tensor coordinates for quasi-coherent coefficients

Source: Stacks Project, Tags 08DX(2), 08DV, 06YT and 01I9.
(blueprint: new-j1-qcoh-ordinary-tensor-resolution-coordinates). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private noncomputable def semilinearTensorLift
    {A C : Type u} [CommRing A] [CommRing C] (φ : A →+* C)
    {B : ModuleCat.{u} A} {D : ModuleCat.{u} C} (b : B →ₛₗ[φ] D)
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} C}
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N) :
    (tensorRight B).obj M ⟶
      (ModuleCat.restrictScalars φ).obj ((tensorRight D).obj N) := by
  let f' : M →ₛₗ[φ] N :=
    { toFun := f
      map_add' := f.hom.map_add
      map_smul' := f.hom.map_smul }
  let t := TensorProduct.map f' b
  exact ModuleCat.ofHom
    (X := (tensorRight B).obj M)
    (Y := (ModuleCat.restrictScalars φ).obj ((tensorRight D).obj N))
    { toFun := t
      map_add' := t.map_add
      map_smul' := t.map_smulₛₗ }

private theorem semilinearTensorLift_tmul
    {A C : Type u} [CommRing A] [CommRing C] (φ : A →+* C)
    {B : ModuleCat.{u} A} {D : ModuleCat.{u} C} (b : B →ₛₗ[φ] D)
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} C}
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N) (x : M) (y : B) :
    semilinearTensorLift φ b f (x ⊗ₜ[A] y) =
      (show N from f x) ⊗ₜ[C] (b y) := rfl

-- Generalize the proved quotient tensor argument to arbitrary semilinear coefficients.
private theorem semilinear_tensor_resolution_lift_homotopy
    {A C : Type u} [CommRing A] [CommRing C] (φ : A →+* C)
    {M B : ModuleCat.{u} A} {N D : ModuleCat.{u} C}
    (P : ProjectiveResolution M) (R : ProjectiveResolution N) (b : B →ₛₗ[φ] D)
    (a a' : P.complex ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex
      (.down ℕ)).obj R.complex)
    (k k' : ((tensorRight B).mapHomologicalComplex (.down ℕ)).obj P.complex ⟶
      ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.down ℕ)).obj
        (((tensorRight D).mapHomologicalComplex (.down ℕ)).obj R.complex))
    (haug : ∀ x : P.complex.X 0, R.π.f 0 (a.f 0 x) = R.π.f 0 (a'.f 0 x))
    (hk : ∀ (j : ℕ) (x : P.complex.X j) (y : B),
      k.f j (x ⊗ₜ[A] y) = (show R.complex.X j from a.f j x) ⊗ₜ[C] (b y))
    (hk' : ∀ (j : ℕ) (x : P.complex.X j) (y : B),
      k'.f j (x ⊗ₜ[A] y) = (show R.complex.X j from a'.f j x) ⊗ₜ[C] (b y)) :
    Nonempty (Homotopy k k') := by
  let TA := (tensorRight B).mapHomologicalComplex (.down ℕ)
  let TC := (tensorRight D).mapHomologicalComplex (.down ℕ)
  let F := ModuleCat.restrictScalars φ
  let K := (F.mapHomologicalComplex (.down ℕ)).obj R.complex
  have hz : K.d 1 0 ≫ F.map (R.π.f 0) = 0 := by
    change F.map (R.complex.d 1 0) ≫ F.map (R.π.f 0) = 0
    rw [← F.map_comp, R.complex_d_comp_π_f_zero, F.map_zero]
  have hzero : (ShortComplex.mk (K.d 1 0) (F.map (R.π.f 0)) hz).Exact :=
    (R.exact₀).map F
  have hsucc (j : ℕ) :
      (ShortComplex.mk (K.d (j + 2) (j + 1)) (K.d (j + 1) j)
        (K.d_comp_d _ _ _)).Exact := (R.exact_succ j).map F
  have haug' : a.f 0 ≫ F.map (R.π.f 0) = a'.f 0 ≫ F.map (R.π.f 0) := by
    ext x
    exact haug x
  obtain ⟨H⟩ := ModuleCat.augmented_lift_homotopy P K _ hz hzero hsucc a a' haug'
  let T : ∀ j l, (TA.obj P.complex).X j ⟶
      ((F.mapHomologicalComplex (.down ℕ)).obj (TC.obj R.complex)).X l :=
    fun j l ↦ semilinearTensorLift φ b (H.hom j l)
  refine ⟨{ hom := T, zero := ?_, comm := ?_ }⟩
  · intro j l hjl
    have h := H.zero j l hjl
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change semilinearTensorLift φ b (H.hom j l) (x ⊗ₜ[A] y) = 0
    rw [semilinearTensorLift_tmul, h]
    exact TensorProduct.zero_tmul _ _
  · intro j
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    have hc := ConcreteCategory.congr_hom (H.comm j) x
    simp only [dNext_nat, Homotopy.prevD_chainComplex] at hc ⊢
    change a.f j x = H.hom (j - 1) j (P.complex.d j (j - 1) x) +
      K.d (j + 1) j (H.hom j (j + 1) x) + a'.f j x at hc
    change k.f j (x ⊗ₜ[A] y) =
      T (j - 1) j ((TA.obj P.complex).d j (j - 1) (x ⊗ₜ[A] y)) +
      ((F.mapHomologicalComplex (.down ℕ)).obj (TC.obj R.complex)).d (j + 1) j
        (T j (j + 1) (x ⊗ₜ[A] y)) + k'.f j (x ⊗ₜ[A] y)
    rw [hk, hk']
    change (show R.complex.X j from a.f j x) ⊗ₜ[C] (b y) =
      (show R.complex.X j from
        H.hom (j - 1) j (P.complex.d j (j - 1) x)) ⊗ₜ[C] (b y) +
      (R.complex.d (j + 1) j
        (show R.complex.X (j + 1) from H.hom j (j + 1) x)) ⊗ₜ[C] (b y) +
      (show R.complex.X j from a'.f j x) ⊗ₜ[C] (b y)
    rw [hc]
    simp only [TensorProduct.add_tmul]
    rfl

set_option maxHeartbeats 800000 in
-- Elaborating the dependent affine coordinates needs additional fuel.
/-- Affine algebraic resolutions compute ordinary tensor homology of a supplied
K-flat resolution of a quasi-coherent sheaf, naturally for supplied augmented lifts.
This statement concerns only complexes and ordinary homology. It neither constructs
algebraic lifts nor compares any derived tensor objects.

Source: Stacks Project, Tags 08DX(2), 08DV, 06YB, 06YT and 01I9.
(blueprint: new-j1-qcoh-ordinary-tensor-resolution-coordinates).

Proof: On each affine chart transport the tilde counits by sM and sN.
Quasi-coherence makes these counits invertible. Sheafify the augmentation of P
and extend chain degree j to cochain degree -j, obtaining L -> M|U[0].
Exactness of tilde preserves its quasi-isomorphism. Projective terms are flat;
associated sheaf preserves flatness, and bounded-above flatness makes L K-flat.
Exact open restriction preserves K-flatness, so K|U is another K-flat resolution.
Use the zigzag K|U tensor N|U[0] <- K|U tensor L_N -> M|U[0] tensor L_N,
where L_N is a K-flat resolution of N|U[0], and compare with L tensor N|U[0]
through L tensor L_N. Tensoring a quasi-isomorphism with a K-flat complex is a
quasi-isomorphism by the acyclic-cone criterion. Thus all comparison legs induce
homology isomorphisms. The chart total-tensor comparison identifies the last
complex with tilde of P tensor NA, extended to nonpositive cochain degrees.
Exact tilde homology comparison, extension homology at -n, and the tilde sections
unit give c_U. No inverse of an augmentation is used at chain level.

For a supplied a, sheafify its semilinear components on V by scalar extension and
the tilde adjunction. Its augmentation equation after sM identifies the induced
coefficient map with restriction of M. The equation for b after sN does the same
for N. The pure tensor equation identifies k with the tensor of these sheaf maps.
Compare the two zigzags after restricting U to V, using a common K-flat resolution
of the second coefficient. Tensor functoriality and the augmentation squares make
all squares commute. Apply homology and cancel the invertible legs. Naturality of
exact tilde homology, extension homology, and the section unit gives the stated
section equation. Refining the second resolution by another common resolution
shows independence of that choice. This works for unbounded K, arbitrary rings,
n=0, zero modules, and empty charts. -/
theorem exists_qcoh_ordinary_tensor_resolution_coordinates
    (Y : Scheme.{u}) (M N : SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    [M.IsQuasicoherent] [N.IsQuasicoherent]
    (MA NA : ∀ U : Y.affineOpens, ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (sM : ∀ U : Y.affineOpens, MA U ≃ₗ[Γ(Y, U.1)] M.val.obj (op U.1))
    (sN : ∀ U : Y.affineOpens, NA U ≃ₗ[Γ(Y, U.1)] N.val.obj (op U.1))
    (P : ∀ U : Y.affineOpens, ProjectiveResolution (MA U))
    (K : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (q : K ⟶ (CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M)
    (hK : CochainComplex.IsKFlat (R := Y.sheaf) K) (hq : QuasiIso q) (n : ℕ) :
    letI := SheafOfModules.monoidalCategory Y.sheaf
    let S := CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let Q := (CochainComplex.mapBifunctor K (S.obj N)
      (curriedTensor (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))).homology
        (-(n : ℤ))
    ∃ c : ∀ U : Y.affineOpens,
        ((((tensorRight (NA U)).mapHomologicalComplex (.down ℕ)).obj
          (P U).complex).homology n) ≃ₗ[Γ(Y, U.1)] Q.val.obj (op U.1),
      ∀ (V U : Y.affineOpens) (h : V.1 ≤ U.1)
        (_hbasic : ∃ f : Γ(Y, U.1), Y.basicOpen f = V.1),
        let φ := (Y.presheaf.map (homOfLE h).op).hom
        let TA := (tensorRight (NA U)).mapHomologicalComplex (.down ℕ)
        let TC := (tensorRight (NA V)).mapHomologicalComplex (.down ℕ)
        ∀ (b : NA U →ₛₗ[φ] NA V)
          (a : (P U).complex ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex
            (.down ℕ)).obj (P V).complex)
          (k : TA.obj (P U).complex ⟶
            ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.down ℕ)).obj
              (TC.obj (P V).complex)),
          (∀ x : (P U).complex.X 0,
            sM V ((P V).π.f 0 (a.f 0 x)) =
              M.val.map (homOfLE h).op (sM U ((P U).π.f 0 x))) →
          (∀ y : NA U, sN V (b y) = N.val.map (homOfLE h).op (sN U y)) →
          (∀ (j : ℕ) (x : (P U).complex.X j) (y : NA U),
            k.f j (x ⊗ₜ[Γ(Y, U.1)] y) =
              (show (P V).complex.X j from a.f j x) ⊗ₜ[Γ(Y, V.1)] (b y)) →
          let e := ((TC.obj (P V).complex).sc n).mapHomologyIso
            (ModuleCat.restrictScalars φ)
          ∀ x, Q.val.map (homOfLE h).op (c U x) =
            c V (e.hom (HomologicalComplex.homologyMap k n x)) := by
  dsimp only
  obtain ⟨c, hc⟩ := qcoh_ordinary_tensor_resolution_coordinates_witness
    Y M N MA NA sM sN P K q hK hq n
  refine ⟨c, ?_⟩
  intro V U h hbasic b a k ha hb hk
  obtain ⟨b', a', k', ha', hb', hk', hc'⟩ := hc V U h hbasic
  -- The section normalizations identify the coefficient maps and augmentations.
  have hbb : b = b' := by
    ext y
    apply (sN V).injective
    exact (hb y).trans (hb' y).symm
  subst b'
  have haug : ∀ x : (P U).complex.X 0,
      (P V).π.f 0 (a.f 0 x) = (P V).π.f 0 (a'.f 0 x) := by
    intro x
    apply (sM V).injective
    exact (ha x).trans (ha' x).symm
  -- Tensor the augmented lift homotopy, then use its equality on homology.
  obtain ⟨H⟩ := semilinear_tensor_resolution_lift_homotopy
    (Y.presheaf.map (homOfLE h).op).hom (P U) (P V) b a a' k k' haug hk hk'
  intro x
  rw [H.homologyMap_eq n]
  exact hc' x

end AlgebraicGeometry

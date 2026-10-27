/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.Paper.PointDerivedHomModels
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Sheaf.Paper.PointFiniteProjectiveAdjunctionUnits
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.CategoryTheory.RingedSiteGrothendieckCoefficientUniverse
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Finite-projective extension models on the pro-etale point

Source: Stacks Tags 00NX, 03EK and 06YQ.
(blueprint: lem-pod-point-finite-projective-extension-models).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory
namespace WeilConjectures.PointDerivedHom

variable (k : Type u) [Field k] {R : CommRingCat.{u + 1}}
  (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1})
  (α : constantRing.{u, u} k R ⟶ B)
  (L : ModuleCat.{u + 1} R ⥤ Modules.{u, u} k B)
  (hobj : ∀ M : ModuleCat.{u + 1} R, L.obj M = extensionObject.{u, u} k B α M)
  (adj : L ⊣ sections.{u, u} k B α)

attribute [-instance] abSheafify abLocallyBijective ringLocallyBijective
  WeilConjectures.integralReductionSiteEssentiallySmall

local instance : HasSheafify (Scheme.ProEt.topology (Spec (.of k)))
    AddCommGrpCat.{u + 1} := abSheafify.{u, u} k
local instance : (Scheme.ProEt.topology (Spec (.of k))).WEqualsLocallyBijective
    AddCommGrpCat.{u + 1} := abLocallyBijective.{u, u} k

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

private def powerFreeIso (n : ℕ) :
    (∏ᶜ fun _ : Fin n ↦ SheafOfModules.unit (ring.{u, u} k B)) ≅
      SheafOfModules.free (R := ring.{u, u} k B) (ULift.{u + 1} (Fin n)) :=
  (biproduct.isoProduct _).symm ≪≫ biproduct.isoCoproduct _ ≪≫
    Sigma.whiskerEquiv
      (g := fun _ : ULift.{u + 1} (Fin n) ↦ SheafOfModules.unit (ring.{u, u} k B))
      Equiv.ulift.symm (fun _ ↦ Iso.refl _)

private theorem extension_retract [PreservesFiniteLimits L]
    (κ : L.obj (ModuleCat.of R R) ≅ SheafOfModules.unit (ring.{u, u} k B))
    (M : ModuleCat.{u + 1} R) [Module.Finite R M] [Module.Projective R M] :
    ∃ n : ℕ, ∃ s : L.obj M ⟶ SheafOfModules.free (R := ring.{u, u} k B)
        (ULift.{u + 1} (Fin n)),
      ∃ r, s ≫ r = 𝟙 (L.obj M) := by
  obtain ⟨n, p, i, _, _, hip⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  let V := fun _ : Fin n ↦ ModuleCat.of R R
  let e : L.obj (ModuleCat.of R (Fin n → R)) ≅
      SheafOfModules.free (R := ring.{u, u} k B) (ULift.{u + 1} (Fin n)) :=
    L.mapIso (ModuleCat.piIsoPi V).symm ≪≫ PreservesProduct.iso L V ≪≫
      Pi.mapIso (fun _ ↦ κ) ≪≫ powerFreeIso k B n
  refine ⟨n, L.map (ModuleCat.ofHom i) ≫ e.hom,
    e.inv ≫ L.map (ModuleCat.ofHom p), ?_⟩
  rw [Category.assoc, Iso.hom_inv_id_assoc, ← L.map_comp]
  have h : ModuleCat.ofHom i ≫ ModuleCat.ofHom p = 𝟙 M := ModuleCat.hom_ext hip
  rw [h, L.map_id]

private theorem retract_flat (M : Modules.{u, u} k B) (n : ℕ)
    (s : M ⟶ SheafOfModules.free (R := ring.{u, u} k B) (ULift.{u + 1} (Fin n)))
    (r : SheafOfModules.free (R := ring.{u, u} k B) (ULift.{u + 1} (Fin n)) ⟶ M)
    (hsr : s ≫ r = 𝟙 M) : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} (R := B) M := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{u + 1, u, u + 1} B
  let := SheafOfModules.monoidalCategory B
  let := SheafOfModules.symmetricCategory B
  let := (SheafOfModules.nonempty_monoidalClosed_independentCoefficients.{u + 1, u + 1, u}
    (R := B)).some
  let := SheafOfModules.isGrothendieckAbelian_coefficientUniverse.{u + 1, u, u + 1}
    (ring.{u, u} k B)
  let := SheafOfModules.tensorPreadditive.{u + 1, u, u + 1} B
  have hu : ObjectProperty.flat (SheafOfModules.unit (ring.{u, u} k B)) :=
    ObjectProperty.flat_of_tensorIso (λ_ (SheafOfModules.unit (ring.{u, u} k B)))
  have hf := ObjectProperty.flat_coproduct
    (fun _ : ULift.{u + 1} (Fin n) ↦ SheafOfModules.unit (ring.{u, u} k B)) (fun _ ↦ hu)
  have hm := ObjectProperty.flat_of_retract (show Retract M _ from ⟨s, r, hsr⟩) hf
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1} B M).symm hm.2

/-- A bounded finite-projective complex extends to a bounded K-flat sheaf complex,
whose terms are flat retracts of the specified finite free sheaves.
Source: Stacks Tags 00NX, 03EK and 06YQ
(blueprint: lem-pod-point-finite-projective-extension-models).

Proof: L(R) is the coefficient unit by the normalized rank-one adjunction
comparison. L preserves finite powers; identify their product of units with the
free sheaf indexed by the lifted finite set. Apply L to a finite-free splitting
of each term and conjugate by that identification. The free sheaf is a coproduct
of flat units, and flatness passes to retracts. Additivity makes L preserve zero
terms, so the original bounds persist. Bounded-above site-flat complexes are
K-flat at the independent site and coefficient universes. Empty powers and an
empty support interval give the zero case through the same constructions. -/
theorem point_finiteProjective_extension_models
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits (sections.{u, u} k B α)]
    [PreservesFiniteColimits (sections.{u, u} k B α)]
    (hex : ExplicitAdjunction.{u, u} k B α L hobj adj)
    (hscalar : Function.Bijective (scalar.{u, u} k B α (op (finalObject k))))
    (P : CochainComplex (ModuleCat.{u + 1} R) ℤ) (a b : ℤ)
    (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b)
    (hP : ∀ i, Module.Projective R (P.X i) ∧ Module.Finite R (P.X i)) :
    let Q := (extensionComplex.{u, u} k B α L adj).obj P
    Q.IsStrictlyGE a ∧ Q.IsStrictlyLE b ∧
    CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1} (R := B) Q ∧
    ∀ i, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} (R := B) (Q.X i) ∧
      ∃ (n : ℕ) (s : Q.X i ⟶ SheafOfModules.free (R := ring.{u, u} k B)
          (ULift.{u + 1} (Fin n)))
        (r : SheafOfModules.free (R := ring.{u, u} k B)
          (ULift.{u + 1} (Fin n)) ⟶ Q.X i),
      s ≫ r = 𝟙 (Q.X i) := by
  let := adj.left_adjoint_additive
  let Q := (extensionComplex.{u, u} k B α L adj).obj P
  obtain ⟨_, _, κ, _, _⟩ := point_finiteProjective_adjunction_units.{u, u} k B α L hobj adj
    hex hscalar
  have hra (i : ℤ) : ∃ (n : ℕ) (s : Q.X i ⟶ SheafOfModules.free (R := ring.{u, u} k B)
      (ULift.{u + 1} (Fin n)))
      (r : SheafOfModules.free (R := ring.{u, u} k B) (ULift.{u + 1} (Fin n)) ⟶ Q.X i),
      s ≫ r = 𝟙 (Q.X i) := by
    have := (hP i).1
    have := (hP i).2
    exact extension_retract k B L κ (P.X i)
  have hf (i : ℤ) : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} (R := B) (Q.X i) := by
    obtain ⟨n, s, r, hsr⟩ := hra i
    exact retract_flat k B (Q.X i) n s r hsr
  have hqa : Q.IsStrictlyGE a := (Q.isStrictlyGE_iff a).mpr
    (fun i hi ↦ L.map_isZero (P.isZero_of_isStrictlyGE a i hi))
  have hqb : Q.IsStrictlyLE b := (Q.isStrictlyLE_iff b).mpr
    (fun i hi ↦ L.map_isZero (P.isZero_of_isStrictlyLE b i hi))
  exact ⟨hqa, hqb,
    SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite.{u + 1, u, u + 1}
      B Q b hf,
    fun i ↦ ⟨hf i, hra i⟩⟩

attribute [instance] abSheafify abLocallyBijective ringLocallyBijective
  WeilConjectures.scalarReductionSiteSmall
  WeilConjectures.integralReductionSiteEssentiallySmall
end WeilConjectures.PointDerivedHom

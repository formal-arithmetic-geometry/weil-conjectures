/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Shift.Adjunction

/-! # Shifted-unit cup transpose under a monoidal adjunction

Source: six-functors basics, direct-image stability proof, paragraph (3),
agent-formulated internal bar normalization and its generic monoidal-adjunction calculation
(blueprint: lem-sfb-shifted-cup-adjunction-transpose).
The blueprint paragraph motivates the application; the generic calculation is agent-supplied,
and an exact non-SGA reference remains wanted in the DAG.

## Main definitions

* `Adjunction.shiftedCupUnitIso`: the prescribed strong-unit and shift comparison.
* `Adjunction.shiftedCupNegativeArrow`: the actual negatively shifted arrow.
* `Adjunction.shiftedCupPhi`: the shifted adjunction transpose.
* `Adjunction.shiftedCupProduct`: the ordered product using the given shifted-unit comparison.

## Main statement

* `Adjunction.shiftedCupAdjunctionTranspose`: the algebra, monoidal unit and counit,
  normalization identities, degree-zero identity, and ordered transpose formula.
-/

@[expose] public section

set_option autoImplicit false

universe u₁ u₂ v₁ v₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CategoryTheory.Adjunction

/-- The comparison `L(I[-n]) ≅ I[-n]` formed from the fixed shift comparison and inverse
strong unit comparison. Source: the generic calculation under paragraph (3) of the
six-functors direct-image stability proof
(blueprint: lem-sfb-shifted-cup-adjunction-transpose). -/
def shiftedCupUnitIso
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [HasShift C ℤ]
    {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [HasShift D ℤ]
    (L : C ⥤ D) [L.Monoidal] [L.CommShift ℤ] (n : ℤ) :
    L.obj ((𝟙_ C)⟦-n⟧) ≅ (𝟙_ D)⟦-n⟧ :=
  (L.commShiftIso (-n)).app (𝟙_ C) ≪≫
    (shiftFunctor D (-n)).mapIso (Functor.Monoidal.εIso L).symm

/-- Shift `x : I ⟶ I[n]` by `-n` and cancel the successive shifts with the specified
shift-addition and zero-shift isomorphisms. Source: the generic calculation under
paragraph (3) of the six-functors direct-image stability proof
(blueprint: lem-sfb-shifted-cup-adjunction-transpose). -/
def shiftedCupNegativeArrow
    {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [HasShift D ℤ]
    (n : ℤ) (x : 𝟙_ D ⟶ (𝟙_ D)⟦n⟧) : (𝟙_ D)⟦-n⟧ ⟶ 𝟙_ D :=
  x⟦-n⟧' ≫ (shiftFunctorCompIsoId D n (-n) (add_neg_cancel n)).hom.app (𝟙_ D)

/-- The adjoint of `x[-n]`, precomposed with the prescribed shifted-unit comparison.
Source: the generic calculation under paragraph (3) of the six-functors direct-image
stability proof (blueprint: lem-sfb-shifted-cup-adjunction-transpose). -/
def shiftedCupPhi
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [HasShift C ℤ]
    {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [HasShift D ℤ]
    {L : C ⥤ D} [L.Monoidal] [L.CommShift ℤ] {F : D ⥤ C} (adj : L ⊣ F)
    (n : ℤ) (x : 𝟙_ D ⟶ (𝟙_ D)⟦n⟧) : (𝟙_ C)⟦-n⟧ ⟶ F.obj (𝟙_ D) :=
  adj.homEquiv _ _ ((shiftedCupUnitIso L n).hom ≫ shiftedCupNegativeArrow n x)

/-- Cup is tensoring the two arrows in their displayed order, followed by the lax tensor
map and the image of unit multiplication. Source: the generic calculation under
paragraph (3) of the six-functors direct-image stability proof
(blueprint: lem-sfb-shifted-cup-adjunction-transpose). -/
def shiftedCupProduct
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [HasShift C ℤ]
    {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
    (F : D ⥤ C) [F.LaxMonoidal] (p q : ℤ)
    (r : (𝟙_ C)⟦-(p + q)⟧ ≅ (𝟙_ C)⟦-p⟧ ⊗ (𝟙_ C)⟦-q⟧)
    (a : (𝟙_ C)⟦-p⟧ ⟶ F.obj (𝟙_ D)) (b : (𝟙_ C)⟦-q⟧ ⟶ F.obj (𝟙_ D)) :
    (𝟙_ C)⟦-(p + q)⟧ ⟶ F.obj (𝟙_ D) :=
  r.hom ≫ (a ⊗ₘ b) ≫ Functor.LaxMonoidal.μ F (𝟙_ D) (𝟙_ D) ≫
    F.map (λ_ (𝟙_ D)).hom

/-- The shifted-unit cup transpose, including the canonical algebra structure and both
monoidal-adjunction normalization identities. `adj.IsMonoidal` specifies exactly that the
chosen lax structure on `F` is the mate of the inverse strong structure on `L`.
Source: six-functors direct-image stability proof, paragraph (3), agent-supplied generic
internal bar normalization (blueprint: lem-sfb-shifted-cup-adjunction-transpose).

Proof:
1. The mate equivalence of lem-sfb-monoidal-adjunction-mates gives the lax structure on F;
   its unit is the adjoint of the inverse strong unit. The monoidal unit/counit theorem
   lem-sfb-monoidal-adjunction-unit-counit gives both monoidality assertions. Compose the
   counit's tensor and unit equations with the inverse strong comparisons to obtain
   the two displayed normalizations.
2. By lem-sfb-tensor-unit-monoid, I_D has identity unit and left-unitor multiplication.
   Clause 1 of det-def-sfb-ring-object-transport transports this monoid through F. Its
   multiplication is the lax tensor map followed by F of unit multiplication, and its
   unit is the lax unit followed by F of the identity, hence the lax unit itself.
3. Write h_n for shiftedCupUnitIso L n. The hypothesis hr is precisely compatibility of
   the two r comparisons with L and its inverse tensor comparison. The inverse Hom formula
   in lem-weil-pbc-adjunction-of-natural-bijection identifies L(Phi_n(x)) followed by the
   counit with h_n followed by x[-n].
4. Expand the transpose of the cup. Counit naturality at unit multiplication and the
   tensor normalization replace L of the lax multiplication by the tensor of counits.
   Naturality of the inverse strong tensor comparison moves it past the two arrows.
   Substitute step 3, then hr, obtaining h_(p+q) followed by r_D, the ordered tensor of
   x[-p] and y[-q], and unit multiplication. Precompose with h_(p+q) inverse. No symmetry
   or generation hypothesis is used, so the result holds for arbitrary arrows and integers.
5. At zero, the specified zero-shift comparisons identify x[-0] with the identity and h_0
   with the inverse strong unit. Its adjoint is the lax unit, proving the Phi_0 identity.
   Zero objects and zero arrows are included in the same calculations. -/
theorem shiftedCupAdjunctionTranspose
    {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasFiniteBiproducts C]
    [MonoidalCategory C] [MonoidalPreadditive C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D] [HasFiniteBiproducts D]
    [MonoidalCategory D] [MonoidalPreadditive D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    (L : C ⥤ D) (F : D ⥤ C) [L.Additive] [F.Additive] [L.Monoidal]
    [L.CommShift ℤ] [F.CommShift ℤ] (adj : L ⊣ F) [adj.CommShift ℤ]
    [F.LaxMonoidal] [adj.IsMonoidal]
    (rC : ∀ p q : ℤ, (𝟙_ C)⟦-(p + q)⟧ ≅ (𝟙_ C)⟦-p⟧ ⊗ (𝟙_ C)⟦-q⟧)
    (rD : ∀ p q : ℤ, (𝟙_ D)⟦-(p + q)⟧ ≅ (𝟙_ D)⟦-p⟧ ⊗ (𝟙_ D)⟦-q⟧)
    (hr : ∀ p q : ℤ,
      L.map (rC p q).hom ≫ Functor.OplaxMonoidal.δ L _ _ ≫
          ((shiftedCupUnitIso L p).hom ⊗ₘ (shiftedCupUnitIso L q).hom) =
        (shiftedCupUnitIso L (p + q)).hom ≫ (rD p q).hom) :
    (∃ A : MonObj (F.obj (𝟙_ D)),
      A.one = Functor.LaxMonoidal.ε F ∧
      A.mul = Functor.LaxMonoidal.μ F (𝟙_ D) (𝟙_ D) ≫ F.map (λ_ (𝟙_ D)).hom) ∧
    NatTrans.IsMonoidal adj.unit ∧ NatTrans.IsMonoidal adj.counit ∧
    (∀ U V : D,
      L.map (Functor.LaxMonoidal.μ F U V) ≫ adj.counit.app (U ⊗ V) =
        Functor.OplaxMonoidal.δ L (F.obj U) (F.obj V) ≫
          (adj.counit.app U ⊗ₘ adj.counit.app V)) ∧
    (L.map (Functor.LaxMonoidal.ε F) ≫ adj.counit.app (𝟙_ D) =
      Functor.OplaxMonoidal.η L) ∧
    (shiftedCupPhi adj 0 ((shiftFunctorZero D ℤ).inv.app (𝟙_ D)) =
      (shiftFunctorZero C ℤ).hom.app (𝟙_ C) ≫ Functor.LaxMonoidal.ε F) ∧
    ∀ (p q : ℤ) (x : 𝟙_ D ⟶ (𝟙_ D)⟦p⟧) (y : 𝟙_ D ⟶ (𝟙_ D)⟦q⟧),
      (shiftedCupUnitIso L (p + q)).inv ≫
          (adj.homEquiv _ _).symm
            (shiftedCupProduct F p q (rC p q) (shiftedCupPhi adj p x)
              (shiftedCupPhi adj q y)) =
        (rD p q).hom ≫ (shiftedCupNegativeArrow p x ⊗ₘ shiftedCupNegativeArrow q y) ≫
          (λ_ (𝟙_ D)).hom := by
  refine ⟨?_, inferInstance, inferInstance, adj.map_μ_comp_counit_app_tensor,
    adj.map_ε_comp_counit_app_unit, ?_, ?_⟩
  · refine ⟨F.monObjObj (𝟙_ D), ?_, rfl⟩
    simp
  · apply (adj.homEquiv _ _).symm.injective
    simp only [shiftedCupPhi, Equiv.symm_apply_apply, homEquiv_counit,
      Functor.map_comp, Category.assoc, adj.map_ε_comp_counit_app_unit]
    simp [shiftedCupUnitIso, shiftedCupNegativeArrow,
      shiftFunctorCompIsoId_zero_zero_hom_app, L.commShiftIso_zero,
      Category.assoc]
  · intro p q x y
    have ht (n : ℤ) (z : 𝟙_ D ⟶ (𝟙_ D)⟦n⟧) :
        L.map (shiftedCupPhi adj n z) ≫ adj.counit.app (𝟙_ D) =
          (shiftedCupUnitIso L n).hom ≫ shiftedCupNegativeArrow n z := by
      simpa only [shiftedCupPhi, homEquiv_counit] using
        (adj.homEquiv _ _).symm_apply_apply
          ((shiftedCupUnitIso L n).hom ≫ shiftedCupNegativeArrow n z)
    apply (cancel_epi (shiftedCupUnitIso L (p + q)).hom).mp
    simp only [Iso.hom_inv_id_assoc]
    rw [homEquiv_counit]
    simp only [shiftedCupProduct, Functor.map_comp, Category.assoc]
    rw [adj.counit_naturality, adj.map_μ_comp_counit_app_tensor_assoc,
      ← Functor.OplaxMonoidal.δ_natural_assoc,
      MonoidalCategory.tensorHom_comp_tensorHom_assoc, ht p x, ht q y,
      ← MonoidalCategory.tensorHom_comp_tensorHom_assoc]
    simpa only [Category.assoc] using
      congrArg (fun k ↦ k ≫
        (shiftedCupNegativeArrow p x ⊗ₘ shiftedCupNegativeArrow q y) ≫
          (λ_ (𝟙_ D)).hom) (hr p q)

end CategoryTheory.Adjunction

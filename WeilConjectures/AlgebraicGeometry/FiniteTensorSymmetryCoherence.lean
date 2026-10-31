/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.AlgebraicGeometry.FiniteTensorSignedReduction
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.Trace
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
import WeilConjectures.AlgebraicGeometry.FiniteScalarMonoidalRepresentative

/-! # Finite scalar tensor reduction respects the native symmetry

Source: Stacks 07A4 and 0FPT; parent proof Step 2.
(blueprint: lem-pur-finite-tensor-symmetry-coherence)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped TensorProduct
attribute [local instance] _root_.DerivedCategory.braidedCategory'

namespace WeilConjectures.PurityFiniteSetting

open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal

private theorem coreTransport_symmetry
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [BraidedCategory C] [MonoidalCategory D] [BraidedCategory D]
    (F G : C ⥤ D) [F.Braided] (e : F ≅ G) (X Y : C) :
    FiniteTensorSymmetrySquare G (Functor.Monoidal.coreMonoidalTransport e) X Y := by
  let : G.Monoidal := Functor.Monoidal.transport e
  let : e.hom.IsMonoidal := Functor.Monoidal.natTransIsMonoidal_of_transport e
  let : G.LaxBraided := Functor.LaxBraided.ofNatIso e
  change G.map (β_ X Y).hom ≫ δ G Y X =
    δ G X Y ≫ (β_ (G.obj X) (G.obj Y)).hom
  apply (cancel_epi (μ G X Y)).1
  rw [← Category.assoc, Functor.LaxBraided.braided]
  simp only [Category.assoc, Functor.Monoidal.μ_δ_assoc, Functor.Monoidal.μ_δ,
    Category.comp_id]

private theorem scalarModelSymmetry
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (U V : _root_.DerivedCategory
      (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} A))) :
    FiniteTensorSymmetrySquare
      (ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ T)
      (finiteScalarMonoidalModel φ T) U V := by
  let : Algebra A B := φ.toAlgebra
  let F := ProEtale.sheafExtendScalars φ T
  let : F.PreservesKFlatQuasiIso :=
    ProEtale.preservesKFlatQuasiIso_sheafExtendScalars A B T
  let : F.leftDerivedFunctor.Braided :=
    ProEtale.leftDerivedSheafExtendScalarsBraided (R := A) (S := B) T
  unfold finiteScalarMonoidalModel
  exact coreTransport_symmetry _ _ _ U V

/-- Finite scalar tensor reduction respects the native symmetry.
Source: Stacks 07A4 and 0FPT; parent proof Step 2.
(blueprint: lem-pur-finite-tensor-symmetry-coherence).
Proof: Resolve both inputs by flat-term K-flat complexes. On homogeneous tensors the
scalar-first tensorator sends b tensor (x tensor y) to (b tensor x) tensor
(1 tensor y). Swapping the factors on either route multiplies by the same
Koszul sign and distributes the same scalar. The quotient map preserves -1.
The cochain comparison symmetry equation therefore holds. Descend through
K-flat localization in both variables. The representative normalization of
finiteTensorCore identifies its tensorator with this descended comparison,
and the native braiding is the localization of the same signed cochain flip. -/
theorem finiteTensorSymmetryCoherence (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) (T : Scheme.{u}) :
    ∀ U V, FiniteTensorSymmetrySquare
      (P.finiteTensorReduction m hm hmn T) (P.finiteTensorCore m hm hmn T) U V := by
  let φ := (P.finiteReductionRingHom m hm hmn).ulift.{u + 1, u + 1}
  have hm' : P.FiniteTensorCoreNormalized m hm hmn T (finiteScalarMonoidalModel φ T) :=
    fun C D _ _ ↦ finiteScalarMonoidalModel_representative φ T C D
  have he : finiteScalarMonoidalModel φ T = P.finiteTensorCore m hm hmn T :=
    (P.existsUnique_finiteTensorCore m hm hmn T).choose_spec.2 _ hm'
  intro U V
  rw [← he]
  exact scalarModelSymmetry φ T U V

end WeilConjectures.PurityFiniteSetting

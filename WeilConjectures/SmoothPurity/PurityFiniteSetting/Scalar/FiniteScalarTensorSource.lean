/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Scalar.FiniteScalarTensorData

/-! # Invertibility of the certified scalar representative source -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v w uA vA uB vB wA wB
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PurityFiniteSetting

attribute [local irreducible] Functor.leftAdjoint Adjunction.ofIsRightAdjoint
  Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit

private theorem sourceRecord_isIso
    {C D K L : Type*} [Category* C] [Category* D] [Category* K] [Category* L]
    [MonoidalCategory C] [MonoidalCategory D]
    {Q : C ⥤ D} {R : K ⥤ C} {QB : L ⥤ D} {S : K → Prop}
    (d : TensorRepresentativeData Q R QB S) (X Y : K) (hX : S X) (hY : S Y) :
    IsIso (d.source X Y) := by
  let _ := d.isIso_first X Y hX hY
  let _ := d.isIso_second (d.tensor X Y) (d.tensor_closed X Y hX hY)
  let _ := d.isIso_third X Y
  unfold TensorRepresentativeData.source
  infer_instance

/-- On K-flat pairs all three factors of the representative source are invertible.
Source: thm-pur-finite-reduction-of-purity, proof Step 2; Stacks 07A4 and 0FPT.
(blueprint: lem-pur-finite-scalar-tensor-source).
Proof: the localization tensorator is invertible when the right input is K-flat.
The tensor of two K-flat complexes is K-flat, so the scalar adjunction transpose is
invertible there by the exact-right-derived-adjoint comparison. The ordinary scalar
functor is strong monoidal and preserves the sums defining cochain tensor products,
so its cochain oplax tensor comparison is invertible. Functors preserve these
isomorphisms, as does composition. -/
theorem finiteScalarTensorData_source_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (C D : CochainComplex (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) ℤ)
    (hC : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat C)
    (hD : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat D) :
    IsIso ((finiteScalarTensorData φ T).source C D) := by
  exact sourceRecord_isIso (finiteScalarTensorData φ T) C D hC hD

end WeilConjectures.PurityFiniteSetting

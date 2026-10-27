/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W8
-/
module

public import Sheaf.Paper.NativeWeilTensorRingedBridgeData
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed

/-! # Underived data for normalized native ringed tensor comparisons

This is the underived and evaluation-normalized part of the normalized complex
comparison.  It is separated so that the total-complex and localization clauses
can be proved independently.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  (b : NativeWeilTensorRingedBridge k₀ l X)
  (T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
    ProEtaleWeilSheaf k₀ l X)
  [T.Additive] [∀ P, (T.obj P).Additive]
  [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]
  (adj : T ⊣₂ ihomBifunctor k₀ l X)

abbrev nativeRingedTensorObjData (P Q : ProEtaleWeilSheaf k₀ l X) :=
  (SheafOfModules.monoidalCategory b.R).tensorObj (b.native.functor.obj Q)
    (b.native.functor.obj P)

/-- The underived comparison and its evaluation normalization.
Source: Stacks 06YS and 06YU (blueprint: lem-sf-native-weil-tensor-ringed-underived-data). -/
structure NativeWeilRingedTensorUnderivedData where
  underived (P Q : ProEtaleWeilSheaf k₀ l X) :
    b.native.functor.obj ((T.obj P).obj Q) ≅ nativeRingedTensorObjData b P Q
  uncurry (P Q I : ProEtaleWeilSheaf k₀ l X)
      (f : Q ⟶ ((ihomBifunctor k₀ l X).obj (op P)).obj I) :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients b.R
    letI := SheafOfModules.monoidalCategory b.R
    letI := SheafOfModules.symmetricCategory b.R
    (underived P Q).inv ≫
        b.native.functor.map (((adj.adj P).homEquiv Q I).symm f) =
      (β_ (b.native.functor.obj Q) (b.native.functor.obj P)).hom ≫
        ((SheafOfModules.tensorHomAdjunction b.R (b.native.functor.obj P)).homEquiv
          (b.native.functor.obj Q) (b.native.functor.obj I)).symm
            (b.native.functor.map f ≫ b.nativeHom.hom.app (op P, I))

/-- The underived comparison fixed by the native and ringed tensor-Hom adjunctions.
Source: Stacks 06YS and 06YU; the uniqueness-of-left-adjoints step in the native
tensor model proof (blueprint: lem-sf-native-weil-tensor-ringed-underived-data).

Proof: transport the native parameter adjunction through the additive equivalence
`b.native`, compare its right adjoint with the sheaf tensor-Hom adjunction by
`b.nativeHom`, and use uniqueness of left adjoints.  The counit identity is the
displayed uncurrying equation; naturality in the parameter gives the required
two-variable comparison.  The construction is independent of all derived data.
-/
theorem native_weil_tensor_ringed_underived_data :
    Nonempty (NativeWeilRingedTensorUnderivedData b T adj) := by sorry

end AlgebraicGeometry.ProEtaleWeilSheaf

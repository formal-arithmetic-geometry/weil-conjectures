/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryRestrictionTensor
import WeilConjectures.WeilSheaf.Native.NativeRestrictionForgetTotalModel

/-! # Representative restriction/forgetting square

## Implementation details

The ordinary total tensor models in `dU.models` and `dZ.models` are fixed by their adjunction
normalization. On each `(p, q)` summand of the forgotten native total tensors the comparison is
the underlying balanced tensor map, with a signed exchange for the right-parameter-first
ordinary total convention. Forgetting preserves K-flat tests: an ordinary acyclic test complex
is induced by the exact Frobenius orbit-sum left adjoint, and the ordinary tensor test is the
degree-zero orbit summand, a retract of this acyclic direct sum. Exact open restriction
preserves K-flatness by its projection formula and extension by zero.

In the formalization, the native part (K-flat forgetting, binary models and summand
comparison) is `native_restriction_forget_total_model`, giving the normalized total models
`mZ`, `mU`; the ordinary part (the tensorator normalization) is
`native_ordinary_restriction_total_model`, applied to the forgotten complexes. Both sides
followed by `mU` agree, and `mU` is cancelled. The extension to arbitrary derived objects is
proved separately from the existence of K-flat models.

## References

* Stacks 0E8I, 0GL1, 015F
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible]
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedClosedComparison
universe u a b
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtaleWeilSheaf

private theorem cancel_total_model_square
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {X Y Z : C} {A B E W V K : D} (mZ : X ≅ Z) (mU : W ≅ V)
    {t : X ⟶ Y} {z : Y ⟶ Z} {u : W ⟶ V}
    {a : A ⟶ B} {b : B ⟶ E} {c : E ⟶ W}
    {d : A ⟶ F.obj X} {q : F.obj Z ⟶ K} {r : K ⟶ V} {ord : F.obj Y ⟶ W}
    (hmZ : mZ.hom = t ≫ z) (hmU : mU.hom = u)
    (hr : a ≫ b ≫ c ≫ mU.hom = d ≫ F.map mZ.hom ≫ q ≫ r)
    (ho : ord ≫ u = F.map z ≫ q ≫ r) :
    a ≫ b ≫ c = d ≫ F.map t ≫ ord := by
  apply (cancel_mono mU.hom).1
  simp only [Category.assoc]
  rw [hr, hmZ, F.map_comp]
  simp only [Category.assoc]
  rw [← ho, ← hmU]

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
variable {U Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ Z) [IsOpenImmersion j]
  [j.IsOver (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]

/-- The restriction/forgetting square on two actual K-flat complexes, for the
ordinary comparison already constructed by normalized tensor--Hom adjunctions. -/
theorem native_open_tensor_restriction_forget_kflat (s : NativeOpenTensorData k₀ l j)
    (rho : nativeDerivedTensor k₀ l Z ⋙ nativeOpenPull k₀ l j ≅
      (nativeOpenPull k₀ l j).prod (nativeOpenPull k₀ l j) ⋙ nativeDerivedTensor k₀ l U)
    (c : OpenTensorPresentation (ProEtaleWeilSheaf k₀ l U) (ProEtaleWeilSheaf k₀ l Z))
    (_hc :
      HEq c.R (upperStar k₀ l j) ∧
      HEq c.SA (nativeOpenSheafTensor k₀ l U) ∧ HEq c.SB (nativeOpenSheafTensor k₀ l Z) ∧
      HEq c.TA (nativeTensorTotal k₀ l U) ∧ HEq c.TB (nativeTensorTotal k₀ l Z) ∧
      HEq c.DA (nativeDerivedTensor k₀ l U) ∧ HEq c.DB (nativeDerivedTensor k₀ l Z) ∧
      HEq c.flatA (NativeIsKFlat k₀ l U) ∧ HEq c.flatB (NativeIsKFlat k₀ l Z) ∧
      HEq c.modelA (nativeOpenTensorModel k₀ l U) ∧ HEq c.modelB (nativeOpenTensorModel k₀ l Z) ∧
      HEq c.iA (nativeOpenTensorInsertion k₀ l U) ∧ HEq c.iB (nativeOpenTensorInsertion k₀ l Z) ∧
      HEq c.sheafRestriction s.sheafRestriction ∧ HEq c.restriction rho)
    (dU : NativeOrdinaryTensorIdentification k₀ l U)
    (dZ : NativeOrdinaryTensorIdentification k₀ l Z) :
    ∀ (P T : CochainComplex (ProEtaleWeilSheaf k₀ l Z) ℤ),
      NativeIsKFlat k₀ l Z P → NativeIsKFlat k₀ l Z T →
      let M := DerivedCategory.Q.obj P;
      let N := DerivedCategory.Q.obj T;
        (nativeForget k₀ l U).map (rho.hom.app (M, N)) ≫
          (nativeDerivedClosedComparison k₀ l U).tensorComparison.hom.app
            ((nativeOpenPull k₀ l j).obj M, (nativeOpenPull k₀ l j).obj N) ≫
          (nativeDerivedClosedComparison k₀ l U).ordinaryClosed.tensor.map
            (Prod.mkHom ((nativeOpenForgetPull k₀ l j).hom.app M)
              ((nativeOpenForgetPull k₀ l j).hom.app N)) =
        (nativeOpenForgetPull k₀ l j).hom.app ((nativeDerivedTensor k₀ l Z).obj (M, N)) ≫
          (ProEtale.adicUpperStar l
            (Scheme.Hom.geometricFiberMap j (comp_over j _))).mapDerivedCategory.map
              ((nativeDerivedClosedComparison k₀ l Z).tensorComparison.hom.app (M, N)) ≫
          (nativeOrdinaryRestrictionTensor k₀ l j dU dZ).hom.app
            ((nativeForget k₀ l Z).obj M, (nativeForget k₀ l Z).obj N) := by
  intro P T hP hT
  dsimp only
  let F := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z)
  let R := ProEtale.adicUpperStar l
    (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀))))
  let P₀ := (F.mapHomologicalComplex (.up ℤ)).obj P
  let T₀ := (F.mapHomologicalComplex (.up ℤ)).obj T
  obtain ⟨mZ, mU, hmZ, hmU, hr⟩ :=
    native_restriction_forget_total_model k₀ l j s rho c _hc dU dZ P T hP hT
  have ho := native_ordinary_restriction_total_model k₀ l j dU dZ P₀ T₀
    ((nativeForget k₀ l Z).obj (DerivedCategory.Q.obj P))
    ((nativeForget k₀ l Z).obj (DerivedCategory.Q.obj T))
    (F.mapDerivedCategoryFactors.app P) (F.mapDerivedCategoryFactors.app T)
  dsimp only [F, P₀, T₀, Iso.app_hom] at ho
  exact cancel_total_model_square R.mapDerivedCategory mZ mU hmZ hmU hr ho

end AlgebraicGeometry.ProEtaleWeilSheaf

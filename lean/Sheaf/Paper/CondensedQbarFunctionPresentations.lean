/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

public import Mathlib.LinearAlgebra.Matrix.ToLin
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
import Sheaf.Paper.CondensedPointBasisEvaluation
import Sheaf.Paper.GeometricFieldProEtaleEvaluation
import Sheaf.Paper.ProfinitePointPullback

/-!
# Function presentations of finitely presented condensed modules

This isolates coefficient realization and geometric-fibre compatibility. It makes no
local-constancy or finite-freeness assertion. The comparison of condensed coefficients
with the sheafification of bounded functions is supplied as a hypothesis; the parent
proves it using finite-field comparisons and filtered colimits.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Evaluation of a finite-extension-valued continuous function at a point.
Source: RefactorInstruction.tex, Section 4, evaluation of coefficient functions
(blueprint: lem-weil-pbc-condensed-qbar-compatible-function-presentations). -/
noncomputable def condensedQbarFunctionEval
    {ℓ : ℕ} [Fact ℓ.Prime] {T : Type u} [TopologicalSpace T] (t : T) :
    PadicAlgCl.finiteIntermediateFieldValued ℓ T →+* PadicAlgCl ℓ where
  toFun a := a.1 t
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Restriction of bounded continuous functions along a continuous map.
The same finite extension contains all values after restriction.
Source: RefactorInstruction.tex, Section 4, restriction of coefficient functions
(blueprint: lem-weil-pbc-condensed-qbar-compatible-function-presentations). -/
noncomputable def condensedQbarFunctionComp
    {ℓ : ℕ} [Fact ℓ.Prime] {T : Type u} [TopologicalSpace T]
    {T' : Type v} [TopologicalSpace T'] (g : C(T', T)) :
    PadicAlgCl.finiteIntermediateFieldValued ℓ T →+*
      PadicAlgCl.finiteIntermediateFieldValued ℓ T' :=
  (((ContinuousMap.compRightAlgHom ℤ (PadicAlgCl ℓ) g).toRingHom.comp
    (PadicAlgCl.finiteIntermediateFieldValued ℓ T).subtype).codRestrict
      (PadicAlgCl.finiteIntermediateFieldValued ℓ T') (by
        rintro a
        obtain ⟨E, hE, ha⟩ := a.property
        exact ⟨E, hE, fun x ↦ ha (g x)⟩))

attribute [local instance] Abelian.hasFiniteBiproducts

/-- A fixed presentation has matrices of bounded continuous functions on a refinement,
whose evaluated linear cokernels agree on fibres of the original base, and whose
open restrictions present the module.

Source: RefactorInstruction.tex, Section 4, coefficient realization and geometric-fibre
comparison, steps 1--3 of the finite-matrix refinement argument
(blueprint: lem-weil-pbc-condensed-qbar-compatible-function-presentations).
Proof:
1. Unpack the given finite presentation over the coefficient object on Y as the
   cokernel of a map between free modules of fixed ranks m and n. Cover Y by affine
   objects weakly contractible over X.
   Pullback preserves the cokernel and identifies both free modules with their bases.
2. Transport coefficients through the supplied ring-object isomorphism on the original
   noetherian base X. The resulting coefficient sheaf is the sheafification of bounded
   continuous functions. On each weakly contractible affine object, basis evaluation
   identifies sections with bounded continuous functions on its profinite components,
   hence on the scheme. A finite compositum contains all matrix entries. For an empty
   matrix choose the ground field. This realizes B. On every open V the presheaf unit
   gives a ring map from bounded functions to coefficient sections. Localization along
   the weakly etale map V to X, followed by multiplication on the regular module, gives
   the displayed ring homomorphism. The basis calculation and exactness give the
   displayed cokernel isomorphism on V. No noetherianity of a covering object or open
   is used; the global coefficient comparison is applied only on X.
3. At a geometric representative above x in X, evaluate P. Geometric evaluation
   preserves cokernels and finite free modules, so the evaluated presentation is the
   ordinary linear cokernel of the value matrix. This cokernel depends only on x:
   choose an algebraic closure of its residue field and embed it into each algebraically
   closed geometric representative. The extension comparison identifies the evaluated
   modules. Coefficient realization is natural and takes each function to its value
   at the chosen point. Identify a linear cokernel with the quotient by the range to
   obtain the asserted linear equivalence for any two points above x. No dimension or
   rank calculation, local constancy, or local freeness is part of this assertion.
-/
theorem exists_condensedQbar_compatible_function_presentations
    (ℓ : ℕ) [Fact ℓ.Prime]
    (X Y : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (f : Y ⟶ X) (hf : WeaklyEtale f)
    (hcoeff : Nonempty
      (Mon.mk (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) ≅
        Mon.mk (padicAlgClSheaf X ℓ)))
    (P : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
    (hP : Mod.IsFinitelyPresented
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y)
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) f).obj P)) :
    ∃ (C : Scheme.Cover.{u} Scheme.proetalePrecoverage Y) (n m : ℕ)
      (B : ∀ i : C.I₀,
        Matrix (Fin n) (Fin m) (PadicAlgCl.finiteIntermediateFieldValued ℓ (C.X i))),
      (∀ (i j : C.I₀) (x : C.X i) (y : C.X j),
        (C.f i ≫ f) x = (C.f j ≫ f) y →
        Nonempty
          (((Fin n → PadicAlgCl ℓ) ⧸ LinearMap.range
            (((B i).map (condensedQbarFunctionEval x)).toLin')) ≃ₗ[PadicAlgCl ℓ]
            ((Fin n → PadicAlgCl ℓ) ⧸ LinearMap.range
              (((B j).map (condensedQbarFunctionEval y)).toLin')))) ∧
      ∀ (i : C.I₀) (V : (C.X i).Opens),
        ∃ φ : PadicAlgCl.finiteIntermediateFieldValued ℓ V.toScheme →+*
            End (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ) V.toScheme)),
          Nonempty
            ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
              ((V.ι ≫ C.f i) ≫ f)).obj P ≅
              cokernel (biproduct.matrix fun j k ↦
                φ (condensedQbarFunctionComp V.ι.base.hom (B i k j)))) := by
  sorry

end AlgebraicGeometry.ProEtale

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import Sheaf.Algebra.Homology.DerivedBimoduleTensorHom
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import Sheaf.AlgebraicGeometry.RingDerivedScalarExtension
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import Sheaf.CategoryTheory.DerivedCategory.PerfectComplexDerivedBiduality
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses

/-! # Perfect-algebra dual evaluation with precomposition scalars

Source: Stacks Project, more-algebra.tex, Tags 07VI, 0A66 and 0ATK(1);
dga.tex, Tags 09LN and 09LT; dualizing.tex, Tags 0A70 and 0A71
(blueprint: lem-trf-perfect-algebra-dual-evaluation).

All comparison maps below are constructed from the normalized existing adjunctions.
In particular, tensor cancellation is the mate of the existing enriched coinduction
comparison. No finite-projective model is equipped with an additional strict action.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory MonoidalCategory Opposite
open CategoryTheory.RingDerivedScalarExtension

namespace ModuleCat

variable {S B : Type u} [CommRing S] [CommRing B]
  [HasDerivedCategory.{u} (ModuleCat.{u} S)]
  [HasDerivedCategory.{u} (ModuleCat.{u} B)]

/-- The particular dual E = C_f(S[0]), retaining the coinduction B-action.
Source: Stacks 07VI and 0A70 (blueprint: lem-trf-perfect-algebra-dual-evaluation). -/
abbrev perfectAlgebraDual (f : S →+* B) : DerivedCategory (ModuleCat.{u} B) :=
  (derivedCoinduction f).obj (𝟙_ (DerivedCategory (ModuleCat.{u} S)))

/-- Forget the precomposition action on J_E to obtain RHom_S(UE,-). This is the
existing enriched coinduction comparison, specialized in its first argument.
Source: Stacks 09LN and 09LT (blueprint: lem-trf-perfect-algebra-dual-evaluation). -/
def perfectAlgebraHomRestriction (f : S →+* B) (E : DerivedCategory (ModuleCat.{u} B)) :
    derivedBimoduleHom f E ⋙ (restrictScalars f).mapDerivedCategory ≅
      ihom ((restrictScalars f).mapDerivedCategory.obj E) :=
  NatIso.ofComponents (fun V ↦ (bimoduleCoinductionHomIso f).app (op E, V))
    (fun {V W} a ↦ by
      have h := (bimoduleCoinductionHomIso f).hom.naturality
        (X := (op E, V)) (Y := (op E, W)) (𝟙 (op E), a)
      change (restrictScalars f).mapDerivedCategory.map
          ((MonoidalClosed.pre (𝟙 E)).app ((derivedCoinduction f).obj V) ≫
            (ihom E).map ((derivedCoinduction f).map a)) ≫
          (bimoduleCoinductionHomIso f).hom.app (op E, W) =
        (bimoduleCoinductionHomIso f).hom.app (op E, V) ≫
          (MonoidalClosed.pre ((restrictScalars f).mapDerivedCategory.map (𝟙 E))).app V ≫
          (ihom ((restrictScalars f).mapDerivedCategory.obj E)).map a at h
      erw [CategoryTheory.Functor.map_id] at h
      simp only [MonoidalClosed.pre_id, NatTrans.id_app, Category.id_comp] at h
      erw [Category.id_comp] at h
      dsimp only [coinductionHomLeft, coinductionHomRight, Functor.comp_obj,
        Functor.prod_obj, Functor.id_obj, Functor.op_obj, Functor.uncurry_obj_obj] at h
      exact h)

/-- Canonical cancellation U((B tensor_S V) tensor_B E) ≅ UE tensor_S V.
It is the left mate of the normalized precomposition-Hom comparison; the existing
bimodule adjunction includes the signed symmetry exchanging E and B tensor_S V.
Source: Stacks 09LN and 09LT (blueprint: lem-trf-perfect-algebra-dual-evaluation). -/
def perfectAlgebraTensorCancellation (f : S →+* B)
    (E : DerivedCategory (ModuleCat.{u} B)) :
    moduleDerivedExtension f ⋙ derivedBimoduleTensor f E ≅
      tensorLeft ((restrictScalars f).mapDerivedCategory.obj E) :=
  (((Adjunction.ofIsRightAdjoint (moduleDerivedRestriction f)).comp
    (derivedBimoduleAdjunction f E)).ofNatIsoRight
      (perfectAlgebraHomRestriction f E)).leftAdjointUniq (ihom.adjunction _)

/-- The specified B-linear adjunct of cancellation followed by epsilon tensor 1.
The counit epsilon is evaluation at one after restriction; all maps have real data.
Source: Stacks 07VI, 09LN and 09LT
(blueprint: lem-trf-perfect-algebra-dual-evaluation). -/
def perfectAlgebraDualEvaluation (f : S →+* B)
    (V : DerivedCategory (ModuleCat.{u} S)) :
    (moduleDerivedExtension f).obj V ⟶
      (derivedBimoduleHom f (perfectAlgebraDual f)).obj V :=
  (derivedBimoduleAdjunction f (perfectAlgebraDual f)).homEquiv _ _
    ((perfectAlgebraTensorCancellation f (perfectAlgebraDual f)).hom.app V ≫
      (derivedCoinductionAdjunction f).counit.app
        (𝟙_ (DerivedCategory (ModuleCat.{u} S))) ▷ V ≫ (λ_ V).hom)

/-- The natural identification UC_f(-) ≅ RHom_S(UB[0],-), assembled from Hom out
of the B-unit and the normalized enriched coinduction comparison.
Source: Stacks 0A70 and 0A71 (blueprint: lem-trf-perfect-algebra-dual-evaluation). -/
def perfectAlgebraCoinductionRestriction (f : S →+* B) :
    derivedCoinduction f ⋙ (restrictScalars f).mapDerivedCategory ≅
      ihom ((restrictScalars f).mapDerivedCategory.obj
        (𝟙_ (DerivedCategory (ModuleCat.{u} B)))) :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (derivedCoinduction f) MonoidalClosed.unitNatIso)
      (restrictScalars f).mapDerivedCategory ≪≫
    perfectAlgebraHomRestriction f (𝟙_ (DerivedCategory (ModuleCat.{u} B)))

/-- The canonical underlying-S identification U(B tensor_S -) ≅ UB tensor_S -.
Adjoint uniqueness constructs it from evaluation at one, independently of perfectness.
Source: Stacks 06YY, 09LT and 0A70
(blueprint: lem-trf-perfect-algebra-dual-evaluation). -/
def perfectAlgebraScalarTensor (f : S →+* B) :
    moduleDerivedExtension f ⋙ (restrictScalars f).mapDerivedCategory ≅
      tensorLeft ((restrictScalars f).mapDerivedCategory.obj
        (𝟙_ (DerivedCategory (ModuleCat.{u} B)))) :=
  (((Adjunction.ofIsRightAdjoint (moduleDerivedRestriction f)).comp
    (derivedCoinductionAdjunction f)).ofNatIsoRight
      (perfectAlgebraCoinductionRestriction f)).leftAdjointUniq (ihom.adjunction _)

/-- The canonical bidual map B[0] → RHom_S(UE,S[0]), transporting the native signed
bidual map along UE ≅ RHom_S(B[0],S[0]).
Source: Stacks 07VI (blueprint: lem-trf-perfect-algebra-dual-evaluation). -/
def perfectAlgebraBidualMap (f : S →+* B) :
    (restrictScalars f).mapDerivedCategory.obj
        (𝟙_ (DerivedCategory (ModuleCat.{u} B))) ⟶
      (ihom ((restrictScalars f).mapDerivedCategory.obj (perfectAlgebraDual f))).obj
        (𝟙_ (DerivedCategory (ModuleCat.{u} S))) :=
  letI := DerivedCategory.braidedCategory' (ModuleCat.{u} S)
  MonoidalClosed.toIhomIhomUnit _ ≫
    (MonoidalClosed.pre ((perfectAlgebraCoinductionRestriction f).hom.app
      (𝟙_ (DerivedCategory (ModuleCat.{u} S))))).app
        (𝟙_ (DerivedCategory (ModuleCat.{u} S)))

/-- The ordinary perfect evaluation comparison induced by the canonical bidual map:
its transpose evaluates UE against B[0], then tensors the result with V.
Source: Stacks 07VI and 0ATK(1)
(blueprint: lem-trf-perfect-algebra-dual-evaluation). -/
def perfectAlgebraRestrictedEvaluation (f : S →+* B)
    (V : DerivedCategory (ModuleCat.{u} S)) :
    (restrictScalars f).mapDerivedCategory.obj
        (𝟙_ (DerivedCategory (ModuleCat.{u} B))) ⊗ V ⟶
      (ihom ((restrictScalars f).mapDerivedCategory.obj (perfectAlgebraDual f))).obj V :=
  MonoidalClosed.curry
    ((α_ _ _ V).inv ≫
      (((restrictScalars f).mapDerivedCategory.obj (perfectAlgebraDual f) ◁
          perfectAlgebraBidualMap f) ≫
        (ihom.ev ((restrictScalars f).mapDerivedCategory.obj (perfectAlgebraDual f))).app
          (𝟙_ (DerivedCategory (ModuleCat.{u} S)))) ▷ V ≫ (λ_ V).hom)

/-- The specified dual-evaluation adjunct is invertible, natural for all derived
coefficient morphisms, and restricts to the actual canonical bidual evaluation map.
No flatness, Noetherianity or boundedness hypothesis occurs.
Source: Stacks 07VI, 0A66, 0ATK(1), 09LN and 09LT
(blueprint: lem-trf-perfect-algebra-dual-evaluation).

Proof (the DAG's five steps):
1. By lem-trf-derived-coinduction-adjunction, UE = RHom_S(B,S) and epsilon is
   evaluation at one. Apply lem-trf-perfect-complex-derived-biduality to B[0]:
   UE is perfect and the canonical bidual map is invertible. Use the ordinary
   Koszul braiding, without imposing a braided-structure hypothesis.
2. Resolve arbitrary V by a K-flat F (lem-pc-kflat-resolution). Choose K-injective
   models J of S[0] and I of F tensor J (prop-pur-kinjective-resolutions-exist).
   For any model M of UE, lem-trf-perfect-source-evaluation-quasi-isomorphism
   identifies V tensor RHom_S(UE,S) → RHom_S(UE,V) with its specified evaluation
   chain map and proves it invertible, even for unbounded F and M.
3. Compose signed exchange, tensor with the bidual map, and this evaluation.
   Its transpose evaluates z on b and multiplies V by the resulting scalar.
   This is exactly perfectAlgebraRestrictedEvaluation, including the unit map.
4. The normalized lem-trf-derived-bimodule-tensor-hom identifies the restricted
   adjunct with that same transpose: on the coinduced K-injective model,
   epsilon(b z) = (b z)(1) = z(b). Adjoint uniqueness constructs the cancellation
   and scalar-tensor maps used above from this normalized enriched comparison.
   Thus restriction of the specified alpha equals the displayed evaluation.
5. The defining pairing is natural in V, so its adjunct is natural for every
   derived morphism. Steps 1--4 make its restriction invertible; conservativity
   from lem-trf-derived-coinduction-adjunction makes alpha invertible in D(B). -/
theorem perfect_algebra_dual_evaluation (f : S →+* B)
    (hB : DerivedCategory.IsPerfectRingComplex
      ((restrictScalars f).mapDerivedCategory.obj
        (𝟙_ (DerivedCategory (ModuleCat.{u} B))))) :
    (∀ V : DerivedCategory (ModuleCat.{u} S), IsIso (perfectAlgebraDualEvaluation f V)) ∧
    (∀ (V W : DerivedCategory (ModuleCat.{u} S)) (a : V ⟶ W),
      (moduleDerivedExtension f).map a ≫ perfectAlgebraDualEvaluation f W =
        perfectAlgebraDualEvaluation f V ≫
          (derivedBimoduleHom f (perfectAlgebraDual f)).map a) ∧
    (∀ V : DerivedCategory (ModuleCat.{u} S),
      (restrictScalars f).mapDerivedCategory.map (perfectAlgebraDualEvaluation f V) ≫
          (perfectAlgebraHomRestriction f (perfectAlgebraDual f)).hom.app V =
        (perfectAlgebraScalarTensor f).hom.app V ≫
          perfectAlgebraRestrictedEvaluation f V) := by
  sorry

end ModuleCat

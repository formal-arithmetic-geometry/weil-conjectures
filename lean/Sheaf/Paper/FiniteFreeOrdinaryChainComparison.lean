/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E5
-/
module

public import Sheaf.Paper.FiniteFreeDualChainModels
import Sheaf.Paper.ScalarPerfectFiniteFree
import Sheaf.CategoryTheory.RingedSiteFiniteRetractDualExact
import Sheaf.Algebra.Homology.RingedSiteBoundedEvaluationAssembly

/-! # Ordinary signed finite-free chain evaluation

Source: Stacks Project, Tags 08JH, 08JJ and 0A8X.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.FiniteFreeDualComparison
variable (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
  (A : Type (u + 1)) [CommRing A]
  (α : (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
    (CommRingCat.of A) ⟶ ring Λ X)

/-- The ordinary finite-basis calculation, before derived localization.
Source: Stacks 08JH, 08JJ and 0A8X
(blueprint: lem-sfb-finite-free-ordinary-chain-comparison).

Proof: identify the section chart with scalarPerfectComplex by the reconstruction
counit. Constant module sheafification takes the rank-one scalar module to the
constant ring; arbitrary extension takes this unit to the coefficient unit by
multiplication. Additivity preserves finite powers and finite free splittings.
The scalar dual coordinates identify degree b with Hom_A(P^(-b),A), with
differential (-1)^(b+1) times precomposition. Extend scalar evaluation on balanced
generators through the two module sheafifications. Its inverse in a finite basis
is the dual-basis sum, and both composites are identities by the two basis
expansions, including the empty basis. Naturality identifies the differentials.
Use bounded evaluation assembly and precompose by total tensor with this scalar
dual identification and the section total comparison. The two differentials
have identical components, with no extra sign. Finite support gives exactly the
inverse sum below. Evaluating on generators proves naturality and independence
of the chosen basis. No derived tensor or adjunction is asserted here, and the second complex is
allowed to be unbounded. -/
theorem finiteFreeOrdinaryChainComparison
    (P : CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (hfinite : ∀ i : ℤ, Module.Finite A (P.X i))
    (hfree : ∀ i : ℤ, Module.Free A (P.X i))
    (l h : ℤ) (hbounded : ∀ i : ℤ, i < l ∨ h < i → IsZero (P.X i)) :
    ∃ κ : (complexForward Λ X).obj (chart Λ X A α (scalarDual A P)) ≅
        homComplex.{u + 1, u, u + 1, u + 1} (R := ring Λ X) ((complexForward Λ X).obj (chart Λ X A
          α P))
          (ringedTensorUnitComplex.{u + 1, u, u} (Scheme.ProEt.topology X) (ring Λ X)),
    (∀ (b : ℤ) (U : X.ProEtᵒᵖ) (r r' : (ring Λ X).obj.obj U)
      (z : (scalarDual A P).X b) (x : P.X (-b)),
      ringedOrdinaryDualValue.{u + 1, u, u} (Scheme.ProEt.topology X) (ring Λ X)
        ((complexForward Λ X).obj (chart Λ X A α P)) b (-b) (neg_add_cancel b) U
        ((κ.hom.f b).val.app U (scalarSection Λ X A α _ U r z))
        (scalarSection Λ X A α _ U r' x) =
          r * r' * scalar Λ X A α U ((CategoryTheory.ScalarPerfectDual.coordinates A P b).hom
            z x)) ∧
    ∃ ε : ∀ F : CochainComplex (Internal Λ X) ℤ,
        (complexForward Λ X).obj
            (internalTotalTensor Λ X F (chart Λ X A α (scalarDual A P))) ≅
          homComplex.{u + 1, u, u + 1, u + 1} (R := ring Λ X) ((complexForward Λ X).obj (chart Λ X
            A α P))
            ((complexForward Λ X).obj F),
    (∀ F : CochainComplex (Internal Λ X) ℤ,
      ∃ aEF : (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology X) (ring Λ X)).obj
          ((complexForward Λ X).obj F,
            homComplex.{u + 1, u, u + 1, u + 1} (R := ring Λ X) ((complexForward Λ X).obj (chart Λ
              X A α P))
              (ringedTensorUnitComplex.{u + 1, u, u} (Scheme.ProEt.topology X) (ring Λ X))) ⟶
            homComplex.{u + 1, u, u + 1, u + 1} (R := ring Λ X) ((complexForward Λ X).obj (chart Λ
              X A α P))
              ((complexForward Λ X).obj F),
        RingedOrdinaryEvaluationFormula.{u + 1, u, u} (Scheme.ProEt.topology X) (ring Λ X)
          ((complexForward Λ X).obj (chart Λ X A α P)) ((complexForward Λ X).obj F) aEF ∧
        (ε F).hom = (totalComparison Λ X F (chart Λ X A α (scalarDual A P))).hom ≫
          (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology X) (ring Λ X)).map
            (𝟙 ((complexForward Λ X).obj F), κ.hom) ≫ aEF) ∧
    (∀ {F G : CochainComplex (Internal Λ X) ℤ} (f : F ⟶ G),
      (complexForward Λ X).map (tensorTargetMap Λ X A α P f) ≫ (ε G).hom =
        (ε F).hom ≫ ((homComplexFunctor.{u + 1, u, u + 1, u + 1} (R := ring Λ X)).obj
          (op ((complexForward Λ X).obj (chart Λ X A α P)))).map
            ((complexForward Λ X).map f)) ∧
    (∀ (F : CochainComplex (Internal Λ X) ℤ) (n : ℤ) (U : X.ProEtᵒᵖ)
      (f : ((homComplex.{u + 1, u, u + 1, u + 1} (R := ring Λ X)
        ((complexForward Λ X).obj (chart Λ X A α P)) ((complexForward Λ X).obj F)).X n).val.obj U)
      (ι : ℤ → Type (u + 1)) [∀ b : ℤ, Fintype (ι b)]
      (e : ∀ b : ℤ, Module.Basis (ι b) A (P.X (-b))),
      ((totalComparison Λ X F (chart Λ X A α (scalarDual A P))).hom.f n).val.app U
          (((ε F).inv.f n).val.app U f) =
        ∑ b : ↥(Finset.Icc (-h) (-l)), ∑ j : ι b.val,
          coefficientTensorGenerator.{u, u + 1, u} (Scheme.ProEt.topology X) (ring Λ X)
            ((complexForward Λ X).obj F)
            ((complexForward Λ X).obj (chart Λ X A α (scalarDual A P)))
            (n - b.val) b.val n (by omega) U
            (ringedOrdinaryHomValue.{u + 1, u, u} (Scheme.ProEt.topology X) (ring Λ X)
              ((complexForward Λ X).obj (chart Λ X A α P)) ((complexForward Λ X).obj F)
              n (-b.val) (n - b.val) (by omega) U f
              (scalarSection Λ X A α _ U 1 (e b.val j)))
            (scalarSection Λ X A α _ U 1
              ((CategoryTheory.ScalarPerfectDual.coordinates A P b.val).inv
                ((e b.val).coord j)))) := by
  sorry

end AlgebraicGeometry.ProEtale.FiniteFreeDualComparison

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F6
-/
module

public import Sheaf.Paper.ProEtaleConstantReductionModels
public import Sheaf.AlgebraicGeometry.StrictConstantTowerOperations
public import Sheaf.Paper.ProEtaleCanonicalTensorPullback

/-! # Tensor interpretation of one evaluated constant reduction

Source: Stacks Tags 06YY, 07A4, 099M and 0B56.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.OrderedExchange
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {U V : Scheme.{t}} (f : U ⟶ V)

/-- Evaluated reduction is tensor by any flat K-flat resolution of the constant quotient,
and its specified pullback square is the canonical tensor square. This statement makes
no finite-support or finite-projectivity assumption on the coefficient resolution.
Source: Stacks Tags 06YY (derived localization), 07A4 (derived tensor), 099M (adic
reduction), and 0B56 (canonical tensor/pullback comparison).
(blueprint: lem-sp-constant-quotient-tensor-comparison).

Proof: construct the ordinary derived tensor models by flat K-flat localization on
both sites. On V, exact evaluation of the universal reduction counit identifies the
left-hand functor on a flat K-flat complex P with restricted scalar extension of P
to the finite coefficient ring. The canonical finite constant-to-function comparison
identifies that coefficient ring with the constant quotient. Balanced tensor symmetry
and cancellation identify restricted extension with P tensor the quotient complex.
Tensoring the given quasi-isomorphism q with P is a quasi-isomorphism, since P is
K-flat. Localize its inverse to replace the quotient by F. These comparisons are
natural in P and descend through the resolving-class localization to eV.
Exact inverse image carries F and q to the corresponding resolution on U: inverse
image preserves constant module realizations and the finite coefficient comparison.
The same construction on U therefore gives eU, with coefficient Lf^* Q(F).
On a flat K-flat P both sides of the displayed square are the balancing map sending
m tensor a to pullback(m) tensor pullback(a). The defining normalization of
reductionPullIso, together with exact evaluation and its pullback factorization,
identifies its side of this square with that same map. Cancel the resolution
quasi-isomorphisms and descend the equality along localization. This proves the
square for every M. No projection formula or invertibility of its mate is used;
zero coefficient modules and the empty site are covered by the same constructions. -/
theorem constantQuotientTensorComparison (n : ℕ)
    (F : CochainComplex (reductionModules V (exchangeConstantRing V A)) ℤ)
    (hF : proEtaleFlatRepresentatives V (exchangeConstantRing V A) F)
    (q : F ⟶ (CochainComplex.singleFunctor _ 0).obj
      ((adicLisseConstantModules V A).obj (ModuleCat.of A (A ⧸ d.ideal ^ (n + 1)))))
    (hq : QuasiIso q) :
    ∃ (a : ProEtaleTensorModel V (exchangeConstantRing V A))
      (b : ProEtaleTensorModel U (exchangeConstantRing U A))
      (eV : reduction d V ⋙
        ((CategoryTheory.evaluation ℕᵒᵖ
          (reductionModules V (exchangeConstantRing V A))).obj (op n)).mapDerivedCategory ≅
        (Functor.curryObj a.tensor).flip.obj (DerivedCategory.Q.obj F))
      (eU : reduction d U ⋙
        ((CategoryTheory.evaluation ℕᵒᵖ
          (reductionModules U (exchangeConstantRing U A))).obj (op n)).mapDerivedCategory ≅
        (Functor.curryObj b.tensor).flip.obj ((pull (A := A) f).obj
          (DerivedCategory.Q.obj F))),
      ∀ M : D (A := A) V,
        (pull (A := A) f).map (eV.hom.app M) ≫
          (proEtaleCanonicalTensorComparison f (exchangeConstantRing V A)
            (exchangeConstantRing U A) (exchangeConstantIso f A) a b).hom.app
              (M, DerivedCategory.Q.obj F) =
        (AlgebraicGeometry.ProEtale.StrictTower.evalG A f n).inv.app
            ((reduction d V).obj M) ≫
          ((CategoryTheory.evaluation ℕᵒᵖ
            (reductionModules U (exchangeConstantRing U A))).obj (op n)).mapDerivedCategory.map
              ((reductionPullIso d f).hom.app M) ≫
            eU.hom.app ((pull (A := A) f).obj M) := by sorry

end AlgebraicGeometry.Scheme.OrderedExchange

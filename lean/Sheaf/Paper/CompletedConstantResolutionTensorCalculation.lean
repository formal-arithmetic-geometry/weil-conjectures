/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.Paper.CompletedConstantRealizationData

/-! # Tensor calculation on finite-free completion resolutions

Source: Stacks Tags 06YN, 06YT, 06YU and 093M.
(blueprint: lem-weil-pbc-completed-constant-resolution-tensor-calculation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 1024
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- The chain-level quotient calculation on K-flat resolutions, before replacing
an arbitrary bounded finite target by its finite-free resolution.
Source: Stacks Tags 06YN, 06YT and 06YU; the finite-free tensor computation of
Tag 093M (blueprint: lem-weil-pbc-completed-constant-resolution-tensor-calculation).

Proof: the supplied P already has the actual quotient levels and transition maps.
Form T termwise
by extending completion modules to A/I^(n+1), taking constants, and restricting
scalars. On tensors the successor transition is p tensor x mapped to its scalar
residue tensor x, which commutes with differentials and module maps.
For a bounded-above finite-free complex F, each realized term is a finite sum of H, hence
flat, and the source vanishes above its bound. It is therefore K-flat.
In each finite-free degree, tensoring its realization with a quotient is the
constant extension of that finite-free term to the quotient. The differentials
on both sides are the same matrices with scalar residues. These maps are natural
in every chain map and compatible with every quotient transition by the formula
p tensor x mapped to residue(p) tensor x. After localization they yield the
stated natural isomorphism. Restriction along the coefficient isomorphism β
is an exact monoidal equivalence, so the same calculation holds over R; conjugate
by e to replace the restricted realization by c. No conclusion for the target Q
is assumed here. -/
theorem completed_constant_resolution_tensor_calculation (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (d : CompletedConstantModuleRealization X I)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (β : R ⟶ adicLisseCompletedRing X I) [IsIso β]
    (c : ModuleCat.{u + 1} (AdicCompletion I A) ⥤ completedConstantModules X R)
    (hc : c.Additive)
    (e : c ≅ completedConstantRealization X I d.scalar ⋙
      SheafOfModules.restrictScalars ((adicLisseForget X).map β))
    (h : ∀ n : ℕ, (adicLisseConstantModules X (A ⧸ I ^ (n + 1))).Additive)
    (P : CompletedConstantQuotientTower X I R β) :
    ∃ (T : CompletedConstantReductionTower X I R β h),
      (∀ r : (completedConstantResolutions (AdicCompletion I A)).FullSubcategory,
        CochainComplex.IsKFlatIndependentCoefficients
          (R := R)
          ((completedConstantMapComplex c hc).obj r.obj.left)) ∧
      Nonempty
        (((completedConstantResolutions (AdicCompletion I A)).ι ⋙ Arrow.leftFunc ⋙
            completedConstantMapComplex c hc ⋙
            completedConstantTensorTower X R P.diagram) ≅
          ((completedConstantResolutions (AdicCompletion I A)).ι ⋙ Arrow.leftFunc ⋙
            T.functor ⋙ (Functor.whiskeringRight _ _ _).obj (completedConstantQ _))) := by
  sorry

end AlgebraicGeometry.Scheme

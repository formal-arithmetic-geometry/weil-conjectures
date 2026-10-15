/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.Paper.ContinuousIntegralCoefficients
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs

/-! # Reduction of integral exchange to residue-coefficient exchange

Source: Bhatt--Scholze, Lemma 6.5.9(3) and Proposition 6.8.11(3)
(blueprint: lem-weil-pbc-integral-residue-exchange).
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor


-- Fix the size bound explicitly to avoid a recursive instance search on this site.
local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
  [FiniteDimensional ℚ_[ℓ] E]

variable (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
  [IsSeparated (X' ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
  [IsSeparated (Y' ↘ Spec (.of k))]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
  [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]



/-- Derived coefficient reduction compares integral exchange to residue exchange.
Source: Bhatt--Scholze, Lemma 6.5.9(3) and Proposition 6.8.11(3), using the
two-term finite free resolution of O_E/ℓ over O_E
(blueprint: lem-weil-pbc-integral-residue-exchange).

Proof in words. Multiplication by ℓ is injective on O_E and its cokernel is A = O_E/ℓ.
The proved integral module reduction sequence, pulled back by the exact monoidal
inverse image from the profinite point, is the two-term finite free resolution of A_X.
Consequently derived reduction has cohomology only one degree below the bounds of M.
On each constructible stratum, finite presentations over the discrete valuation ring
show that its cohomology is finite over A, so reduction is bounded constructible; let N
be that same reduced object, equipped with this property. Tensor associativity gives
its canonical pullback comparison. The supplied hTensor identifies reduction after
restriction as a left derived functor of tensor by the residue module. The supplied
hPerfect and the projection formula for dualizable objects make the direct-image comparison
invertible: equivalently, direct image preserves the finite distinguished triangle for
multiplication by ℓ. These comparisons are adjunction mates of the underived scalar
comparisons. Their unit and counit equations, and compatibility of pullback composition,
identify the reduction of the unit-square-counit formula with the residue formula.
The resulting commuting square has invertible endpoint maps, hence is an arrow
isomorphism. This step uses neither etale origin nor proper base change. -/
theorem integralResidueExchange_comparison
    (sq : CommSq g' f' f g)
    (M : integralConstructible ℓ E X)
    (hPerfect : ∀ T : Scheme.{u},
      IsDualizable ((DerivedCategory.singleFunctor _ 0).obj
        ((Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).obj
          (Mod.regular (condensedRingObj
            (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) T)))))
    (hTensor : ∀ T : Scheme.{u},
      ∃ ε : DerivedCategory.Qh ⋙ (integralReduction ℓ E T ⋙
            (Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).mapDerivedCategory) ⟶
          Functor.mapHomotopyCategory
            (MonoidalCategory.tensorLeft
            ((Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).obj
              (Mod.regular (condensedRingObj
                (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) T)))) (.up ℤ) ⋙
            DerivedCategory.Qh,
        Functor.IsLeftDerivedFunctor
          (integralReduction ℓ E T ⋙
            (Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).mapDerivedCategory)
          ε (HomotopyCategory.quasiIso
            (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
              (condensedRingObj (integralCoeff ℓ E) T)) (.up ℤ))) :
    ∃ N : ProEtale.BoundedConstructible
        (condensedRingObj (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) X),
      Nonempty (N.obj ≅ (integralReduction ℓ E X).obj M.obj) ∧
      Nonempty (Arrow.mk ((integralReduction ℓ E Y').map
          ((boundedConstructibleBaseChange (integralCoeff ℓ E) ℓ k sq).app M).hom) ≅
        Arrow.mk ((boundedConstructibleBaseChange
          (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) ℓ k sq).app N).hom) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing

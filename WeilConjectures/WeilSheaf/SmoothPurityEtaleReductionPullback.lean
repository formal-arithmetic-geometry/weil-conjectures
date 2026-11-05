/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingUpperStarCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionUpperStarReading

/-!
# Pullback-square coherence for integral reduction read on the étale site

Both the condensed reduction and the finite étale reading preserve pullback-square
comparisons. Their composite does too. This is the open-restriction part of the
exceptional coefficient comparison, including semilinear squares after rebasing.
-/

set_option profiler true
set_option profiler.threshold 0

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
  [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)
  {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- Integral reduction, followed by étale reading, preserves the comparison of the
two pullbacks around a commutative square. -/
theorem purity_etaleReductionUpperStarIso_cube (sq : CommSq g' f' f g)
    (M : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    L(Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) f'.left).map
        ((etaleReductionUpperStarIso ℓ E n g).inv.app M) ≫
      (etaleReductionUpperStarIso ℓ E n f').inv.app
        ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ g).obj M) ≫
      (etaleReduction ℓ E n X').map
        ((boundedConstructiblePullbackSquareComparison (Profinite.padicIntegersRingObj ℓ E) ℓ
          sq).hom.app M) =
    (Etale.derivedSquareUpperStarIso (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n))
        (⟨Over.left_comp_left_eq_of_comp_eq sq.w⟩ : CommSq g'.left f'.left f.left g.left)).hom.app
          ((etaleReduction ℓ E n Y).obj M) ≫
      L(Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) g'.left).map
        ((etaleReductionUpperStarIso ℓ E n f).inv.app M) ≫
      (etaleReductionUpperStarIso ℓ E n g').inv.app
        ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ f).obj M) := by
  have hred := boundedConstructibleUpperStarIntegersModPowReductionIso_cube ℓ E n sq M
  have hread := finiteEtaleReadingUpperStarIso_cube ℓ E n sq
    ((boundedConstructibleIntegersModPowReduction Y.left ℓ E n).obj M)
  have nf := (finiteEtaleReadingUpperStarIso ℓ E n f').inv.naturality
    ((boundedConstructibleUpperStarIntegersModPowReductionIso ℓ E n g).inv.app M)
  have ng := (finiteEtaleReadingUpperStarIso ℓ E n g').inv.naturality
    ((boundedConstructibleUpperStarIntegersModPowReductionIso ℓ E n f).inv.app M)
  simp only [Functor.comp_obj, Functor.comp_map] at nf ng
  simp only [etaleReductionUpperStarIso_eq, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
  change _ = _
  rw [reassoc_of% nf]
  rw [← (finiteEtaleReading ℓ E n X').map_comp_assoc,
    ← (finiteEtaleReading ℓ E n X').map_comp_assoc, hred]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hread, reassoc_of% ng]

end AlgebraicGeometry.ProEtale.CondensedRing

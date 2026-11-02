/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.HomologyZero

/-!
# Ordinary condensed middle image and its canonical Weil structure

Source: latest blueprint, def-wf-middle-extension, ordinary direct-image and
zeroth-derived identification clauses (blueprint: def-wf-middle-extension).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.NativeL2

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  {U₀ C₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
  [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom]

/-- The actual base change of the model open immersion to the fixed algebraic closure.
Source: latest blueprint, U and C (blueprint: def-wf-middle-extension). -/
abbrev geometricMap (j₀ : U₀ ⟶ C₀) :
    (D.geometricFiber U₀).left ⟶ (D.geometricFiber C₀).left :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left

/-- Model base change commutes with geometric Frobenius.
Source: latest blueprint, induced Weil-structure convention
(blueprint: def-wf-middle-extension).
Proof: compose both sides with the two fibre-product projections. On the model
projection both are j₀ after projection. On the coefficient projection both are
projection followed by inverse q-power Frobenius. Pullback uniqueness gives the square.
This records the canonical structural equality, not an extra assumption on the sheaf. -/
theorem frobeniusSquare (j₀ : U₀ ⟶ C₀) :
    CommSq (D.geometricFrobenius U₀).hom (geometricMap D j₀)
      (geometricMap D j₀) (D.geometricFrobenius C₀).hom := by
  sorry

/-- The ordinary module direct image; for a lisse sheaf on a smooth curve it is j_*F.
Source: latest blueprint, displayed middle-extension definition
(blueprint: def-wf-middle-extension). -/
abbrev middleImage (j₀ : U₀ ⟶ C₀) :=
  CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) (geometricMap D j₀)

/-- Ordinary sheaf direct image put in degree zero and shifted by one.
Source: latest blueprint, final shift convention (blueprint: def-wf-middle-extension). -/
def shiftedMiddleImage (j₀ : U₀ ⟶ C₀) :=
  middleImage D l j₀ ⋙ DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ (1 : ℤ)

/-- Frobenius base change is invertible because both Frobenius arrows are isomorphisms.
Source: latest blueprint, the induced Weil structure (blueprint: def-wf-middle-extension).
Proof: use the module upper/lower-star base-change isomorphism for a commutative square
whose two horizontal Frobenius maps are isomorphisms. Its inverse is the mate for the
inverse Frobenius square; naturality and the two adjunction triangle identities show
that the two composites are identities. The existing isIso_lowerStarBaseChange_of_isIso
instance is precisely this natural-transformation statement. -/
theorem middleBaseChange_isIso (j₀ : U₀ ⟶ C₀) :
    IsIso (CondensedRing.lowerStarBaseChange (Profinite.padicAlgClRingObj l)
      (frobeniusSquare D j₀)) := by
  sorry

/-- The induced Weil structure is the canonical Frobenius base-change mate followed by
j_* of the given Weil structure. Invertibility uses the two Frobenius automorphisms.
Source: latest blueprint, ordinary middle image with its Weil structure
(blueprint: def-wf-middle-extension). -/
@[irreducible] def middleWeilImage (j₀ : U₀ ⟶ C₀) (M : WeilModule D l U₀) : WeilModule D l C₀ :=
  (CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso
    (@asIso _ _ _ _
      (CondensedRing.lowerStarBaseChange (Profinite.padicAlgClRingObj l)
        (frobeniusSquare D j₀)) (middleBaseChange_isIso D l j₀))).obj M

end WeilConjectures.NativeL2

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.FiniteSmoothCoefficientArrows
import all Sheaf.AlgebraicGeometry.OrdinaryFiniteTwistTransportUniqueness
import Sheaf.Paper.FiniteSmoothRootDerivedNormalization

/-! # Composition of normalized ordinary derived root comparisons

Source: smooth-purity reduction compatibilities, part (3).
(blueprint: lem-pur-finite-smooth-root-derived-composition).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local instance 10000] SheafExactDegreeZero.scalarWeakSheafify
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.mapDerivedCategory
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

private theorem quotient_comp (ell : ℕ) {r m n : ℕ}
    (hmr : m ≤ r) (hnm : n ≤ m) :
    FiniteReduction.quotient.{u} ell (hnm.trans hmr) =
      (FiniteReduction.quotient ell hnm).comp (FiniteReduction.quotient ell hmr) := by
  exact RingHom.ext (fun x ↦
    congrArg (fun y : ZMod (ell ^ n) ↦ (⟨⟨y⟩⟩ : FiniteReduction.Coeff.{u} ell n))
      (DFunLike.congr_fun
        (Subsingleton.elim
          (ZMod.castHom (pow_dvd_pow ell (hnm.trans hmr)) (ZMod (ell ^ n)))
          ((ZMod.castHom (pow_dvd_pow ell hnm) (ZMod (ell ^ n))).comp
            (ZMod.castHom (pow_dvd_pow ell hmr) (ZMod (ell ^ m))))) x.down.down))

private theorem root_comp
    (ell : ℕ) [Fact ell.Prime] (T : Scheme.{u})
    {r m n : ℕ} (hmr : m ≤ r) (hnm : n ≤ m)
    (a : CoefficientLineComparison (FiniteReduction.quotient ell hmr)
      (ell ^ r) (ell ^ m) (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) T)
    (b : CoefficientLineComparison (FiniteReduction.quotient ell hnm)
      (ell ^ m) (ell ^ n) (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) T)
    (c : CoefficientLineComparison (FiniteReduction.quotient ell (hnm.trans hmr))
      (ell ^ r) (ell ^ n) (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) T) :
    a.roots ≫ b.roots = c.roots := by
  apply (cancel_mono (kernel.ι ((ell ^ n) • 𝟙 T.gmSheaf))).1
  rw [Category.assoc, b.roots_power, Preadditive.comp_nsmul, a.roots_power,
    c.roots_power, smul_smul]
  congr 1
  rw [Nat.pow_div hnm (Fact.out : ell.Prime).pos,
    Nat.pow_div hmr (Fact.out : ell.Prime).pos,
    Nat.pow_div (hnm.trans hmr) (Fact.out : ell.Prime).pos,
    ← pow_add]
  congr 1
  omega

private theorem root_insertion_comp
    (ell : ℕ) [Fact ell.Prime] (T : Scheme.{u})
    {r m n : ℕ} (hmr : m ≤ r) (hnm : n ≤ m)
    (a : CoefficientLineComparison (FiniteReduction.quotient ell hmr)
      (ell ^ r) (ell ^ m) (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) T)
    (b : CoefficientLineComparison (FiniteReduction.quotient ell hnm)
      (ell ^ m) (ell ^ n) (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) T)
    (c : CoefficientLineComparison (FiniteReduction.quotient ell (hnm.trans hmr))
      (ell ^ r) (ell ^ n) (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) T) :
    (ProEtale.etaleSheafExtendScalarsAdjunction
        (FiniteReduction.quotient ell (hnm.trans hmr)) T).homEquiv _ _ c.sheafIso.hom =
      (ProEtale.etaleSheafExtendScalarsAdjunction
          (FiniteReduction.quotient ell hmr) T).homEquiv _ _ a.sheafIso.hom ≫
        (Sheaf.restrictScalars T.smallEtaleTopology (FiniteReduction.quotient ell hmr)).map
          ((ProEtale.etaleSheafExtendScalarsAdjunction
            (FiniteReduction.quotient ell hnm) T).homEquiv _ _ b.sheafIso.hom) ≫
        (Sheaf.restrictScalarsCompIso T.smallEtaleTopology
          (FiniteReduction.quotient ell hmr) (FiniteReduction.quotient ell hnm)
          (FiniteReduction.quotient ell (hnm.trans hmr)) (quotient_comp ell hmr hnm)).hom.app
          (Scheme.finiteEtaleTateLine T (ell ^ n) (coefficient ell n)
            (CharP.cast_eq_zero _ _)) := by
  apply (Scheme.lineHomEquiv T (ell ^ r) (coefficient ell r)
    (CharP.cast_eq_zero _ _) _).injective
  ext W z
  simp only [Scheme.lineHomEquiv_generator]
  change _ = ((ProEtale.etaleSheafExtendScalarsAdjunction
    (FiniteReduction.quotient ell hnm) T).homEquiv _ _ b.sheafIso.hom).hom.app W
      (((ProEtale.etaleSheafExtendScalarsAdjunction
        (FiniteReduction.quotient ell hmr) T).homEquiv _ _ a.sheafIso.hom).hom.app W
          (Scheme.finiteEtaleTateOneGenerator (coefficient ell r) (ell ^ r) T
            (CharP.cast_eq_zero _ _) W 1 z))
  rw [a.generators, b.generators, c.generators]
  simp only [map_one]
  have hr := congrArg (fun f ↦ f.hom.app W z) (root_comp ell T hmr hnm a b c)
  exact congrArg (Scheme.finiteEtaleTateOneGenerator (coefficient ell n) (ell ^ n) T
    (CharP.cast_eq_zero _ _) W 1) hr.symm

private theorem scalar_insertion_comp
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (T : Scheme.{u}) (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C)
    (hχ : χ = ψ.comp φ)
    {M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)}
    {P : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} C)}
    (η : M ⟶ (Sheaf.restrictScalars T.smallEtaleTopology φ).obj N)
    (θ : N ⟶ (Sheaf.restrictScalars T.smallEtaleTopology ψ).obj P)
    (ζ : M ⟶ (Sheaf.restrictScalars T.smallEtaleTopology χ).obj P)
    (hζ : ζ = η ≫ (Sheaf.restrictScalars T.smallEtaleTopology φ).map θ ≫
      (Sheaf.restrictScalarsCompIso T.smallEtaleTopology φ ψ χ hχ).hom.app P) :
    (ordinaryScalar ψ T).map
        (SheafExactDegreeZero.scalarAdjointInsertion T.smallEtaleTopology φ η) ≫
      SheafExactDegreeZero.scalarAdjointInsertion T.smallEtaleTopology ψ θ =
    (ProEtale.pbcFixedScalarExtensionComp T.smallEtaleTopology φ ψ χ hχ).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj M) ≫
      SheafExactDegreeZero.scalarAdjointInsertion T.smallEtaleTopology χ ζ := by
  subst χ
  exact SheafExactDegreeZero.scalarAdjointInsertion_comp T.smallEtaleTopology φ ψ η θ ζ hζ

/-- The normalized root-line comparisons compose in the ordinary derived categories.
Source: smooth-purity reduction compatibilities (3), root maps and degree-zero normalization.
(blueprint: lem-pur-finite-smooth-root-derived-composition).
Proof: compose with the monic root-kernel inclusion and multiply the power exponents.
The Tate-line universal property detects the ordinary adjuncts on generators.
The exact scalar insertion formula and its composition law transport this equality
to the canonical derived scalar associator. -/
theorem ordinaryRootDerivedComp
    (ell : ℕ) [Fact ell.Prime] (T : Scheme.{u})
    {r m n : ℕ} (hmr : m ≤ r) (hnm : n ≤ m)
    (a : CoefficientLineComparison (FiniteReduction.quotient ell hmr)
      (ell ^ r) (ell ^ m) (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) T)
    (b : CoefficientLineComparison (FiniteReduction.quotient ell hnm)
      (ell ^ m) (ell ^ n) (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) T)
    (c : CoefficientLineComparison (FiniteReduction.quotient ell (hnm.trans hmr))
      (ell ^ r) (ell ^ n) (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) T) :
    (ordinaryScalar (FiniteReduction.quotient ell hnm) T).map a.derivedIso.hom ≫
      b.derivedIso.hom =
    (ordinaryAssociator T ell hmr hnm).hom.app
      (ordinaryFiniteLine (coefficient ell r) (ell ^ r) (CharP.cast_eq_zero _ _) T) ≫
      c.derivedIso.hom := by
  rw [a.derived_eq_scalarInsertion, b.derived_eq_scalarInsertion, c.derived_eq_scalarInsertion]
  exact scalar_insertion_comp T _ _ _ (quotient_comp ell hmr hnm) _ _ _
    (root_insertion_comp ell T hmr hnm a b c)


end AlgebraicGeometry.Etale.FiniteSmoothPurity

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CondensedOrdinaryCompactSections
public import WeilConjectures.SmoothPurity.CondensedWeilModules
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.AlgebraicGeometry.Compactification.PureDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

import WeilConjectures.WeilSheaf.CurveLatticeCompactComparison
import WeilConjectures.WeilSheaf.CurveLatticeReductionVanishing
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAddCommGrp
import WeilConjectures.CategoryTheory.ModuleObjects.SequentialLimitEpi
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Degree-zero compact cohomology of a lisse condensed Weil sheaf

Source: latest blueprint lem-a1-affine-hc0 and its proof. The integral model and
finite reductions precede the Milnor argument and the final flat scalar comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures

attribute [local instance] IsAlgClosure.isAlgClosed

private theorem zero_homology_of_complete
    (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    (X : Scheme.{u}) (K : DerivedCategory (AdicCompletion.Modules ell E X))
    (hK : AlgebraicGeometry.ProEtale.IsDerivedComplete ell E X K)
    (hneg : ∀ n, IsZero ((DerivedCategory.homologyFunctor _ (-1)).obj
      (AdicCompletion.integralLevel ell E X K n)))
    (hzero : ∀ n, IsZero ((DerivedCategory.homologyFunctor _ 0).obj
      (AdicCompletion.integralLevel ell E X K n))) :
    IsZero ((DerivedCategory.homologyFunctor _ 0).obj K) := by
  let A := AdicCompletion.Modules ell E X
  let : CountableAB4Star A := .of_epi_π_app_zero
    (Mod.epiπAppZeroOfEpi Scheme.ProEt.epi_π_app_zero_of_epi_addCommGrpCat)
  obtain ⟨hProducts, _, hH⟩ := derivedCategory_countableProducts_core.{0} A
  let := hProducts
  obtain ⟨P, hP, ⟨e⟩, hη⟩ := hK
  let := hη
  obtain ⟨p, δ, hT, _⟩ := AdicCompletion.roos_isDerivedLimit ell E X K P hP e
  have hz (q : ℤ)
      (hq : ∀ n, IsZero ((DerivedCategory.homologyFunctor A q).obj
        (AdicCompletion.integralLevel ell E X K n))) :
      IsZero ((DerivedCategory.homologyFunctor A q).obj
        (∏ᶜ (AdicCompletion.integralLevel ell E X K))) := by
    let := hH ℕ q
    apply (isLimitOfPreserves (DerivedCategory.homologyFunctor A q)
      (productIsProduct (AdicCompletion.integralLevel ell E X K))).isZero_pt
    apply Functor.isZero
    intro n
    exact hq n.as
  have he := DerivedCategory.HomologySequence.exact₁
    (Triangle.mk p (towerTransitionEndomorphism (AdicCompletion.integralStep ell E X K)) δ)
    hT (-1) 0 (by decide)
  have hroos := he.isZero_X₂
    ((hz (-1) hneg).eq_of_src _ _) ((hz 0 hzero).eq_of_tgt _ _)
  exact hroos.of_iso ((DerivedCategory.homologyFunctor A 0).mapIso
    (e.symm ≪≫ asIso (DerivedCategory.Q.map (AdicCompletion.augmentation ell E X P))))

/-- A lisse Weil sheaf on a smooth geometrically connected affine curve has zero H_c^0.
The assertion holds for every compactification used in the recorded construction.

Source: latest blueprint lem-a1-affine-hc0.md and lem-a1-affine-hc0.proof.md
(blueprint: lem-a1-affine-hc0).

Proof: choose a lisse integral lattice. Constructibility, compact-image stability and
the integral criterion give a derived-complete integral compact image. Scalar-six
identifies its reductions with the finite-level compact images. At each finite level,
negative cohomology vanishes; a nonzero section would have full support on the connected
nonproper curve, contradicting proper support, so H^0 also vanishes. The Milnor triangle
and exact countable products give zero integral H^0 before point evaluation. Finally
flat scalar extension to Qbar and exact evaluation identify the claimed group with
that zero object's image. -/
theorem isZero_condensed_affineCurveHcZero
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p)
    (U₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom] [IsSeparated U₀.hom]
    [Smooth U₀.hom] [IsAffine U₀.left] [Nonempty U₀.left]
    (hDim : U₀.left.IsPureDimension 1)
    (hConnected : ConnectedSpace (D.geometricFiber U₀).left)
    (F : condensedWeilModules (Profinite.padicAlgClRingObj ell)
      (D.geometricFrobenius U₀).hom)
    (hF : IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell) F.carrier)
    (c : Compactification (D.geometricFiber U₀).hom) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (PadicAlgCl ell)) 0).obj
      ((condensedQbarCompactSections ell D.k c).obj
        ((DerivedCategory.singleFunctor _ 0).obj F.carrier))) := by
  obtain ⟨E, hE, hA, hfin, b, hmon, L, hL, _, hcomplete, hcompare⟩ :=
    exists_curveLatticeCompactComparison D ell hEll U₀ hDim hConnected F.carrier hF c
  let := hE
  let := hA
  let := hfin
  let := hmon
  have hlevels := curveLatticeReductionVanishing D ell hEll U₀
    hDim hConnected E L hL c
  have hz := zero_homology_of_complete ell E (Spec (.of D.k)) _ hcomplete
    (fun n ↦ (hlevels n).1) (fun n ↦ (hlevels n).2)
  obtain ⟨e⟩ := hcompare 0
  exact ((Mod.extendScalars (coefficientMap b (Spec (.of D.k))) ⋙
    CondensedQbarGeometricEvaluation.fieldFiber D.k ell).map_isZero hz).of_iso e

end WeilConjectures

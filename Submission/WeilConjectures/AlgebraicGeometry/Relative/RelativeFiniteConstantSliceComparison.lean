/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Relative.RelativeFiniteCoefficientTransport
public import Submission.WeilConjectures.CategoryTheory.LocallyConstantFiniteTypeModules
public import Submission.WeilConjectures.CategoryTheory.ConstantCoefficientScalarExtension
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRings
public import Submission.WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageSupplement
public import Mathlib.RingTheory.Finiteness.Defs
public import Submission.WeilConjectures.ConstructibleSheaf.Defs
import Submission.WeilConjectures.AlgebraicGeometry.Relative.RelativeFiniteModelSliceEquivalence
import Submission.WeilConjectures.AlgebraicGeometry.Relative.RelativeFiniteConstantModelIdentification

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Constant module comparisons on each slice of the equivalent small site -/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The explicit small-site coefficient transport identifies constant local models
on each slice, keeping the same coefficient module. No finiteness assumption is needed.

Source: Stacks Project, Modules on Sites, Tags 03CY and 093U; Sites, Tag 03A0.
(blueprint: lem-weil-pbc-relative-finite-constant-slice-comparison)

Proof: the canonical inverse-image constant-section isomorphism identifies the
inverse image of the sheafification of the constant M-valued presheaf with the
constant M-module on Y. Indeed, both sheafifications represent maps from the same
constant presheaf, and their units agree after coefficient restriction. The same
argument applies after restriction to any slice. Precomposition with AsSmall.down
induces an equivalence on the slices over V and AsSmall.down(V); the inverse is
precomposition with AsSmall.up and the unit and counit give the identifications.
Under these equivalences sheafification commutes with precomposition, since its
universal bijections on maps do. Hence relativeFiniteModelModules sends the
inverse-image constant module on this slice to constantCoefficientModule with the
same M, including its scalar action. The slice functor is fully faithful, so mapping
a local isomorphism forward, and lifting one back, are inverse operations on their
existence. This also handles the empty slice and the zero coefficient ring. -/
theorem relativeFiniteConstantSliceComparison {X Y : Scheme.{u}} (g : Y ⟶ X)
    (B : Type (u + 1)) [CommRing B]
    (F : pbcModules Y ((adicTowerInverseImage g).obj (adicLisseConstantRing X B)))
    (M : ModuleCat.{u + 1} B) (V : proEtaleSiteModel Y) :
    Nonempty (F.over (AsSmall.down.obj V) ≅
      ((proEtaleModuleInverseImage g (adicLisseConstantRing X B)).obj
        ((adicLisseConstantModules X B).obj M)).over (AsSmall.down.obj V)) ↔
    Nonempty (((relativeFiniteModelModules g B).obj F).over V ≅
      ((SheafOfModules.constantCoefficientModule
        (proEtaleModelTopology Y) B).obj M).over V) := by
  let G := (proEtaleModuleInverseImage g (adicLisseConstantRing X B)).obj
    ((adicLisseConstantModules X B).obj M)
  have hslice := relativeFiniteModelSliceEquivalence g B F G V
  have hconst := relativeFiniteConstantModelIdentification g B M V
  constructor
  · intro h
    obtain ⟨e⟩ := h
    obtain ⟨e'⟩ := hslice.mp ⟨e⟩
    obtain ⟨c⟩ := hconst
    exact ⟨e' ≪≫ c⟩
  · intro h
    obtain ⟨e⟩ := h
    obtain ⟨c⟩ := hconst
    apply hslice.mpr
    exact ⟨e ≪≫ c.symm⟩

end AlgebraicGeometry.Scheme

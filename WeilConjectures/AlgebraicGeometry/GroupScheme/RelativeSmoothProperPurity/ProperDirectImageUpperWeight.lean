/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.CharP.CharAndCard
public import WeilConjectures.AlgebraicGeometry.GroupScheme.RelativeCurve.RelativeCurvePunctual
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights

/-! # Upper weights for native proper direct image

Source: latest blueprint, relative smooth-proper purity proof, Step 2.
(blueprint: lem-zl-native-proper-direct-image-upper-weight)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.RelativeSmoothProperPurity
open CondensedRing

/-- The upper half of the weight estimate for a proper direct image.
Smoothness and constant relative dimension are not assumed.

Source: latest blueprint, prop-zl-smooth-proper-relative-purity.proof.md, Step 2
(blueprint: lem-zl-native-proper-direct-image-upper-weight).

Proof: regard the pure constructible input as mixed of weights at most w. Apply the
compact-support sheaf weight bound cor-zl-rfshriek-sheaf in the pulled-back condensed
coefficient model. Proper coincidence identifies this compact-support image with the
ordinary image, with its independent proper-exchange Weil map. The canonical inclusion
comparisons identify the ambient and bounded constructible carriers. Exact point sections
and Frobenius-equivariant proper base change identify the local operators with the fibre
cohomology operators. The mixed weight bound in degree i gives the displayed inequality.
For negative i, right-derived direct image of a heart object has zero cohomology, so no
eigenvalue occurs. No lower bound or lissity conclusion is asserted here. -/
theorem native_proper_direct_image_upper_weight
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    [Fact (ringChar D.k).Prime] [Fact (ringChar D.k ≠ ell)]
    (X₀ Y₀ : Over (Spec (.of D.k₀)))
    [IsSeparated X₀.hom] [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated Y₀.hom] [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [IsSeparated (D.geometricFiber X₀).hom]
    [LocallyOfFiniteType (D.geometricFiber X₀).hom]
    [QuasiCompact (D.geometricFiber X₀).hom]
    [IsSeparated (D.geometricFiber Y₀).hom]
    [LocallyOfFiniteType (D.geometricFiber Y₀).hom]
    [QuasiCompact (D.geometricFiber Y₀).hom]
    (f₀ : X₀ ⟶ Y₀) [IsProper f₀.left]
    (ι : PadicAlgCl ell →+* ℂ) (M : NativeL2.WeilModule D ell X₀)
    (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell) M.carrier)
    (hK : boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ell) (D.geometricFiber X₀).left)
      ((DerivedCategory.singleFunctor _ 0).obj M.carrier))
    (w : ℝ) (hw : NativeL2.Pure D ell X₀ M ι w) (i : ℤ) :
    let f : D.geometricFiber X₀ ⟶ D.geometricFiber Y₀ := (Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀
    let K := (Endofunctor.IsoAlgebra.mapOfNatIso
      ((upperStar (Profinite.padicAlgClRingObj ell)
        (D.geometricFrobenius X₀).hom).mapDerivedCategorySingleFunctor 0)).obj M
    let sq : CommSq (D.geometricFrobenius X₀).hom f.left f.left
        (D.geometricFrobenius Y₀).hom :=
      ⟨(D.frobenius_square_cartesian X₀ Y₀ f₀).2.2.2.2.1⟩
    let S := exStarLift ell f (D.geometricFrobenius X₀) (D.geometricFrobenius Y₀) sq K hK
    let N := (Endofunctor.IsoAlgebra.mapOfNatIso
      ((upperStar (Profinite.padicAlgClRingObj ell)
        (D.geometricFrobenius Y₀).hom).mapDerivedCategoryHomologyFunctorIso i)).obj S
    ∀ (x : {x : Y₀.left // x ∈ closedPoints Y₀.left})
      (j : Y₀.left.residueField x.val →+* D.k)
      (hj : j.comp (Y₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
      (α : ULift.{u + 1} (PadicAlgCl ell)),
      Module.End.HasEigenvalue (NativeL2.closedOperator D ell Y₀ N x j hj).hom α →
      ‖ι α.down‖ ≤ (Nat.card (Y₀.left.residueField x.val) : ℝ) ^ ((w + (i : ℝ)) / 2) := by sorry

end WeilConjectures.RelativeSmoothProperPurity

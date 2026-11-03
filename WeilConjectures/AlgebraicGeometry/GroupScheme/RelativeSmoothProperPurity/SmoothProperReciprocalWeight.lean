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

/-! # Reciprocal weight bound for smooth proper direct image

Source: latest blueprint, relative smooth-proper purity proof, Step 3.
(blueprint: lem-zl-native-smooth-proper-reciprocal-weight)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.RelativeSmoothProperPurity
open CondensedRing

/-- The bound on inverses of eigenvalues, obtained from complementary fibre cohomology.
This is the duality half of the relative-purity argument.

Source: latest blueprint, prop-zl-smooth-proper-relative-purity.proof.md, Step 3
(blueprint: lem-zl-native-smooth-proper-reciprocal-weight).

Proof: the internal lisse dual is finite locally free, and its local operator is the
inverse transpose. Its Tate twist by d has weight -w-2d. For a closed point y, use the
Frobenius-equivariant proper geometric-fibre formula. Apply the disconnected-fibre
Poincare pairing to the smooth proper fibre over the finite residue field. The normalized
perfect invariant pairing identifies degree 2d-i cohomology of the twisted dual with
the contragredient of degree i cohomology of the original coefficient. Thus every inverse
eigenvalue occurs in complementary cohomology. The upper compact-support weight bound
there is (-w-2d)+(2d-i)=-w-i and gives the stated inequality. The componentwise normalized
trace includes disconnected fibres; zero fibres and out-of-range degrees have no
eigenvalues. This statement asserts neither the forward inequality nor lissity. -/
theorem native_smooth_proper_reciprocal_weight
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
    (d : ℕ) [SmoothOfRelativeDimension d f₀.left]
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
      ‖ι α.down⁻¹‖ ≤ (Nat.card (Y₀.left.residueField x.val) : ℝ) ^ (-(w + (i : ℝ)) / 2) := by sorry

end WeilConjectures.RelativeSmoothProperPurity

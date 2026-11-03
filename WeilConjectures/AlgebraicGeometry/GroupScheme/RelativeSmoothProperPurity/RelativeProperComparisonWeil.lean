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

/-! # Weil equivariance of the canonical proper comparison

Source: latest blueprint, relative smooth-proper purity proof, Step 1.
(blueprint: lem-zl-relative-proper-comparison-weil)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.RelativeSmoothProperPurity
open CondensedRing

/-- The canonical bounded proper comparison intertwines the two independently
specified derived Weil structures, before taking any cohomology.

Source: latest blueprint, prop-zl-smooth-proper-relative-purity.proof.md, Step 1
(blueprint: lem-zl-relative-proper-comparison-weil).

Proof: apply proper compactification coincidence to the model compactification and its
Frobenius automorphism square. The normalized comparison from this presentation to the
identity compactification identifies proper/open exchange with the proper mate.
Identify its restriction with the published common-refinement comparison Iso'_padicAlgCl:
for each of the two refinement maps, expand the interchange exchange, the identity
pushforward comparison and the direct-image compositor. The adjunction mate pasting
identities give the same normalized refinement. The cocycle identity cancels the common
refinement, so the identity-model comparison is the published bounded proper comparison.
Naturality at K.str identifies the two resulting Weil composites. Finally conjugate by
the two bounded-to-ambient inclusion comparisons used in exShriekLift and exStarLift.
This argument uses only properness and bounded constructibility, with no smoothness,
weight, lissity, or single-degree assumption. -/
theorem relative_proper_comparison_weil
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
    (K : Endofunctor.IsoAlgebra
      (upperStar (Profinite.padicAlgClRingObj ell)
        (D.geometricFrobenius X₀).hom).mapDerivedCategory)
    (hK : boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ell) (D.geometricFiber X₀).left)
      K.carrier) :
    let f : D.geometricFiber X₀ ⟶ D.geometricFiber Y₀ := (Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀
    letI : IsProper f.left := MorphismProperty.overPullbackMap
      (P := @IsProper) (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) f₀ inferInstance
    let A : BoundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ell) (D.geometricFiber X₀).left) :=
      ⟨K.carrier, hK⟩
    let c₀ := compactificationOverField f₀
    let C := exShriekLift ell f (RelativeCurve.geometricCompactification D f₀ c₀)
      (RelativeCurve.exchange D ell f₀ c₀) K hK
    let sq : CommSq (D.geometricFrobenius X₀).hom f.left f.left
        (D.geometricFrobenius Y₀).hom :=
      ⟨(D.frobenius_square_cartesian X₀ Y₀ f₀).2.2.2.2.1⟩
    let S := exStarLift ell f (D.geometricFrobenius X₀) (D.geometricFrobenius Y₀) sq K hK
    let a := ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ell f).hom.app A).hom
    (upperStar (Profinite.padicAlgClRingObj ell)
      (D.geometricFrobenius Y₀).hom).mapDerivedCategory.map a ≫ S.str.hom =
        C.str.hom ≫ a := by sorry

end WeilConjectures.RelativeSmoothProperPurity

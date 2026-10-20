/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.AlgebraicGeometry.FiniteFreeDirectImageData
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-! # Finite-free basis columns of the direct-image coefficient comparison

Source: Stacks Project, Tags 0B56 and 0944.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.FiniteFreeDirectImage

/-- In finite-free coordinates the restricted canonical mate has the direct images
of the basis inclusions as its columns. This does not assert invertibility.
Source: Stacks Project, sites-cohomology.tex, Tags 0B56 and 0944.
(blueprint: lem-sp-finite-free-direct-image-columns).

Proof: choose the given basis of S_W over R_W and pull it back using the specified
coefficient identifications to obtain the basis on Z. On module sheaves the maps
(x_i) to sum e_i tensor x_i and e_i tensor x to the i-th coordinate are inverse
by the tensor balancing relations. They are natural in the module, respect
restrictions, and yield the isomorphisms after passing to complexes and localizing:
finite sums preserve quasi-isomorphisms, so these compute the universal scalar
extensions on every unbounded complex. This includes rank zero.
The balancing map in the definition is the conjugate of the actual restriction
comparison. The tensor-unit normalization of the scalar adjunctions and the
identity-on-sections normalization of the restriction comparison identify it with
the balanced pullback map. Apply the scalar-restriction adjunct identity of
proEtaleRingSheafChangeAdjunction to the defining transpose of comparison.
On the i-th basis summand that transpose is the R-counit followed by the i-th
basis inclusion on Z: both send a local pure tensor to its counit image tensor e_i.
The naturality of the R-adjunction identifies its adjunct with Rq of that inclusion.
These are equations of actual module-derived maps before forgetting any further
scalars; no faithfulness on derived Hom sets is used. -/
theorem finiteFreeDirectImage_columns {Z W : Scheme.{u}} (q : Z ⟶ W)
    (sW : ScalarModel W) (sZ : ScalarModel Z)
    (R S : Coefficients q) (a : CoefficientMap R S) (d : ℕ)
    (hfree : Nonempty ((proEtaleRingRestrictScalars a.target).obj
            (SheafOfModules.unit ((sheafCompose (ProEt.topology W)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S.target)) ≅
          SheafOfModules.free (R := (sheafCompose (ProEt.topology W)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R.target)
            (ULift.{u + 1} (Fin d))))
    (M : DerivedCategory (proEtaleRingModules Z R.source)) :
    ∃ (eW : (⨁ fun _ : Fin d ↦
        (proEtaleRingDerivedDirectImage q R.target R.source R.identification).obj M) ≅
        (proEtaleRingRestrictScalars a.target).mapDerivedCategory.obj
          ((sW.presentation a.target).derived.obj
            ((proEtaleRingDerivedDirectImage q R.target R.source R.identification).obj M)))
      (eZ : (⨁ fun _ : Fin d ↦ M) ≅
        (proEtaleRingRestrictScalars a.source).mapDerivedCategory.obj
          ((sZ.presentation a.source).derived.obj M)),
      ∀ i : Fin d,
        biproduct.ι _ i ≫ eW.hom ≫
          (proEtaleRingRestrictScalars a.target).mapDerivedCategory.map
            ((comparison sW sZ a).app M) ≫
          (proEtaleRingRestrictionDerivedDirectImage q R.target S.target R.source S.source
            a.target a.source R.identification S.identification a.comm).hom.app
              ((sZ.presentation a.source).derived.obj M) =
        (proEtaleRingDerivedDirectImage q R.target R.source R.identification).map
          (biproduct.ι _ i ≫ eZ.hom) := by
  sorry

end AlgebraicGeometry.Scheme.FiniteFreeDirectImage

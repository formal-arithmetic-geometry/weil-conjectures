/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A8
-/
module

public import Sheaf.AlgebraicGeometry.CondensedScalarRealization
public import WeilConjectures.RingTheory.ProEtale.WContractible

/-!
# Ordinary scalar extension evaluated on a w-contractible affine

Source: Hemo–Richarz–Scholbach, Section 3, equation (3.2) and Remark 3.2,
and Proposition 4.3(1).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- The coefficient comparison and the ordinary, module-valued scalar comparison.
This assertion concerns modules in degree zero, without derived categories or
truncation bounds. Scalar extension uses the actual ordinary functor in the fixed
change-of-rings model.

Source: Hemo–Richarz–Scholbach, equation (3.2), Remark 3.2 and Proposition 4.3(1).
(blueprint: lem-zl-condensed-affine-ordinary-scalar-sections).

Proof: the point-basis evaluation theorem identifies the section ring of the
inverse image of Λ on Spec A with Λ(pi_0 Spec A). The comparison is constructed
in commutative rings, hence preserves the constant scalar map from Λ(*).
For an R-module M, send b tensor m to b times the image of its constant section.
This balanced map is natural and is the identity on the free rank-one module.
Ordinary scalar extension, inverse image and both module equivalences preserve
colimits. Evaluation on the affine preserves colimits by weak contractibility.
Thus the comparison is an isomorphism on arbitrary free modules, by coproducts,
and on every module, by taking a free presentation and its cokernel. Transport
along the coefficient-ring isomorphism gives precisely the displayed B-linear
comparison. This argument includes the empty affine and zero coefficient rings:
all modules over the zero section ring are zero. No flatness is assumed. -/
theorem condensed_affine_ordinary_scalar_sections
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) (A : Type u) [CommRing A] [IsWContractibleRing A]
    (f : Spec (CommRingCat.of A) ⟶ X) [WeaklyEtale f] :
    ∃ e :
      (InternalAbelianSheafModule.sectionRingSheaf (Scheme.ProEt.topology X)
        (condensedRingObj Λ X)).obj.obj (op (Scheme.ProEt.mk f)) ≅
      (condensedSectionRing Λ).obj.obj
        (op (Profinite.of (ConnectedComponents (PrimeSpectrum A)))),
      Nonempty
        ((commutativeSiteConstantModuleFunctor (coherentTopology Profinite.{u})
            (condensedScalarRing Λ) ⋙ (condensedScalarExtensionModel Λ).E) ⋙
          (InternalAbelianSheafModule.sectionModuleEquivalence
            (coherentTopology Profinite.{u}) Λ).inverse ⋙
          (upperStarFromPoint X).mapMod Λ ⋙
          (InternalAbelianSheafModule.sectionModuleEquivalence
            (Scheme.ProEt.topology X) (condensedRingObj Λ X)).functor ⋙
          SheafOfModules.evaluation _ (op (Scheme.ProEt.mk f)) ⋙
          ModuleCat.restrictScalars.{u + 1} e.inv.hom ≅
          ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
            ((condensedSectionRing Λ).obj.map
              (terminal.from (Profinite.of
                (ConnectedComponents (PrimeSpectrum A)))).op).hom) := by
  sorry

end AlgebraicGeometry.ProEtale

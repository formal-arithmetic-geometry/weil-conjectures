/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q139
-/
module

public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.BifunctorShift
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
public import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.ScalarInternalHomAdjunction
/-! # Normalized tensor comparison for scalar extension

Source: Stacks Project, Tags 07A4 and 08J9.
(blueprint: lem-sf-ringed-finite-free-tensor-data). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace CategoryTheory

section Site
variable {C : Type c} [Category.{v} C]
  (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S)

/-- A pure scalar-extension section, transported along the specified object equality.
It is the sheafification unit applied to s tensor x; no basis is used.
Source: Stacks 03EK, 08J9
(blueprint: lem-sf-ringed-finite-free-hom-base-change). -/
def ringedFiniteFreeScalarSection
    (E : SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R) ⥤ SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S))
    (h : ∀ M, E.obj M = SheafOfModules.changeOfRings φ M)
    (M : SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R))
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    (E.obj M).val.obj U :=
  (eqToHom (h M).symm).val.app U
    ((((PresheafOfModules.sheafificationAdjunction
      (𝟙 (SheafOfModules.derivedChangeRingIndependentCoefficients J S).obj)).unit.app
        (SheafOfModules.changeOfRingsPresheaf φ M)).app U)
      (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))


/-- The actual scalar tensor comparison on complexes and preservation of K-flatness.
Source: Stacks Project, sites-cohomology.tex, Tags 07A4, 06YT and 08J9.
(blueprint: lem-sf-ringed-finite-free-tensor-complex).

Proof: on sheafified pure tensors send s tensor (x tensor y) to
(s tensor x) tensor (1 tensor y). The inverse multiplies the scalars.
Balanced relations make both maps well-defined, and sheafification extends them.
Naturality in both factors gives a map on total complexes: the two tensor
differentials are preserved separately, including the sign on the second one.
Extension is a left adjoint and preserves the coproducts in each total degree,
so these mutually inverse maps assemble to a natural chain isomorphism.
For an acyclic S-complex F, restriction is exact and U(F) is acyclic.
The cancellation isomorphism U(F tensor_S E(P)) = U(F) tensor_R P
identifies the signed total differentials. K-flatness of P makes the right side
acyclic. Faithful exact restriction detects acyclicity, proving E(P) K-flat.
The generator formula is the same pure-tensor formula at scalar 1.
The argument includes the zero algebra and all unbounded complexes. -/
theorem ringedFiniteFreeHomBaseChange_complex
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R))]
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S))]
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel.{c, v, max c v r, w, w} φ) :
    ∃ (κ : WeilConjectures.coefficientTotalTensor.{r, c, v} J R ⋙
          D.E.mapHomologicalComplex (ComplexShape.up ℤ) ≅
        (D.E.mapHomologicalComplex (ComplexShape.up ℤ)).prod
          (D.E.mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
            WeilConjectures.coefficientTotalTensor.{r, c, v} J S),
      (∀ (P Q : CochainComplex (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ)
        (p q : ℤ) (U : Cᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        ((κ.hom.app (P, Q)).f (p + q)).val.app U
          (ringedFiniteFreeScalarSection.{c, v, r} J φ D.E D.obj_eq
            (((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q)).X (p + q))
            U 1 (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R
              P Q p q (p + q) rfl U x y)) =
        WeilConjectures.coefficientTensorGenerator.{r, c, v} J S
          ((D.E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          ((D.E.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) p q (p + q) rfl U
          (ringedFiniteFreeScalarSection.{c, v, r} J φ D.E D.obj_eq (P.X p) U 1 x)
          (ringedFiniteFreeScalarSection.{c, v, r} J φ D.E D.obj_eq (Q.X q) U 1 y)) ∧
      (∀ (P : CochainComplex (SheafOfModules.{max c v r}
        (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ),
        CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
          CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
            ((D.E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) := by
  sorry

end Site
end CategoryTheory

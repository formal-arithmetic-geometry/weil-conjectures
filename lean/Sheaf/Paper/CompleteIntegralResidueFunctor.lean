/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q92
-/
module

public import Sheaf.SixFunctors.ProEtale.DerivedCompletion
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import Sheaf.Paper.CompletionTriangleComparison
import Sheaf.Paper.ContinuousSetDescentComponents
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.InternalSectionTensorComparison
import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.Order.CompletePartialOrder

/-! # Exact residue reduction on complete integral complexes

Source: blueprint main-20261015, sec-six-functors-basics,
sk-lem-int-integral-heart/sk-lem-int-integral-heart-triangulated.proof.md, (1);
sec-proetale-coefficients, sk-lem-pe-derived-nakayama-first-reduction.proof.md, Cones.
Stacks Tags 014A, 06YY and 093I.
(blueprint: lem-sfb-complete-integral-residue-functor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open scoped CategoryTheory.Obj ZeroObject

namespace AlgebraicGeometry.ProEtale.CompleteIntegralResidue

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- The residue scalar ring, lifted to the coefficient universe of the fixed site.
Source: blueprint (1), kappa = O_E/pi_E
(blueprint: lem-sfb-complete-integral-residue-functor). -/
abbrev Scalar := ULift.{u + 1} (Padic.coefficientExtensionRing l E 1)

/-- Sheafification of continuous functions on the quotient space of components.
The finite residue field has its discrete topology.
Source: blueprint (1), finite residue coefficients; Stacks 093I
(blueprint: lem-sfb-complete-integral-residue-functor). -/
abbrev continuousRing : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1} :=
  letI := Padic.finite_coefficientExtensionRing l E 1 (Nat.le_refl 1)
  letI : TopologicalSpace (Scalar l E) := ⊥
  letI : DiscreteTopology (Scalar l E) := ⟨rfl⟩
  finiteCoefficientRingSheaf X (Scalar l E)

/-- The sheafification of the constant residue-ring presheaf.
Source: blueprint (1), finite residue coefficients; Stacks 093I
(blueprint: lem-sfb-complete-integral-residue-functor). -/
abbrev constantRing : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1} :=
  (constantSheaf (Scheme.ProEt.topology X) RingCat.{u + 1}).obj (RingCat.of (Scalar l E))

/-- The constant-function morphism, extended by the sheafification adjunction.
Source: blueprint (1), finite residue coefficients; Stacks 093I
(blueprint: lem-sfb-complete-integral-residue-functor). -/
def constantToContinuous : constantRing l E X ⟶ continuousRing l E X :=
  letI := Padic.finite_coefficientExtensionRing l E 1 (Nat.le_refl 1)
  letI : TopologicalSpace (Scalar l E) := ⊥
  letI : DiscreteTopology (Scalar l E) := ⟨rfl⟩
  ((sheafificationAdjunction (Scheme.ProEt.topology X) RingCat.{u + 1}).homEquiv
    _ (continuousRing l E X)).symm (finiteCoefficientScalarMap X (Scalar l E))

/-- The ordinary ring sheaf of sections of the actual pulled-back residue ring S_X.
Source: blueprint (1), section-action coefficient identification
(blueprint: lem-sfb-complete-integral-residue-functor). -/
abbrev sectionRing : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1} :=
  (sheafCompose (Scheme.ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X)
      (AdicCompletion.finiteRing l E X 0))

/-- Canonical constant scalars in the actual pulled-back residue ring. The topology here
is the quotient topology inherited from the specified spectral absolute value on E.
Source: blueprint (1), scalar-normalized finite discrete comparison
(blueprint: lem-sfb-complete-integral-residue-functor). -/
abbrev pulledBackConstants :
    (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj
      (AddCommGrpCat.of (Scalar l E)) ⟶ AdicCompletion.finiteRing l E X 0 :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  FiniteDiscreteOrdinary.canonicalAbelianMap (Padic.coefficientExtensionRing l E 1) X

/-- Section-action followed by scalar relabelling through the inverse ring isomorphism.
This fixes the forward functor, including the action on every morphism.
Source: blueprint (1), coefficient relabelling; Stacks 00YV and 06YY
(blueprint: lem-sfb-complete-integral-residue-functor). -/
def relabel (e : sectionRing l E X ≅ continuousRing l E X) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (AdicCompletion.finiteRing l E X 0) ⥤
        SheafOfModules.{u + 1} (continuousRing l E X) :=
  (InternalAbelianSheafModule.sectionModuleEquivalence (Scheme.ProEt.topology X)
    (AdicCompletion.finiteRing l E X 0)).functor ⋙ SheafOfModules.restrictScalars e.inv

/-- Complete integral complexes form a strictly full triangulated subcategory, and actual
residue extension, with its residue action retained and normalized on constant scalars,
is an exact functor into the continuous finite-coefficient module derived category.
Source: blueprint integral-heart triangulated proof (1), first two sentences, and
Nakayama first-reduction proof, Cones; Stacks 014A, 06YY and 093I
(blueprint: lem-sfb-complete-integral-residue-functor).

Proof plan:
1. Use lem-pe-completion-triangle-comparison: the actual completion maps are the components
   of a natural transformation id to an additive exact completion functor. At zero the
   component is invertible. Naturality gives invariance under isomorphisms; its specified
   shift equation gives the equivalence for every integer shift.
2. The same comparison gives a morphism of distinguished triangles. By
   lem-sf-triangle-morphism-iso, invertibility at any two vertices implies it at the third.
   Thus the complete property is isomorphism closed and triangulated; its full inclusion
   has the inherited exact structure (def-weil-triangulated-subcategory).
3. A continuous function to the discrete residue field factors continuously through the
   quotient of connected components. This is natural and preserves ring operations.
   lem-sfb-continuous-set-descent-components and
   lem-pc-sites-sheafification-underlying-sets identify the constant-function map with
   an isomorphism of ring sheaves, including on non-quasi-compact objects.
4. Apply lem-sf-module-object-ordinary-coefficient-equivalence and its normalized encoding
   to kappa. The coefficient isomorphism b sends every constant scalar to its actual
   pulled-back value. Define e by b inverse followed by constantToContinuous; hence the
   square commutes. The sheafification universal property fixes the comparison uniquely.
5. lem-pur-derived-change-of-rings gives the actual everywhere-defined derived extension
   along the quotient, retaining the residue action. On a K-flat representative it is
   tensor with S_X. lem-pc-kflat-resolution and lem-pe-internal-section-tensor-comparison
   identify this with the relative derived tensor convention, naturally in the input.
6. Relabelling through e inverse keeps underlying additive sheaves and maps, so it is an
   exact additive equivalence. Its termwise derived functor is triangulated by
   lem-sf-exact-functor-derived-triangulated. Compose it with actual derived reduction.
   The composite preserves zero, isomorphisms, shifts and triangles; compose with the
   exact full inclusion for its restriction. No boundedness or geometric finiteness
   assumption was used. -/
theorem complete_integral_residue_functor :
    IsDerivedComplete l E X (0 : DerivedCategory (AdicCompletion.Modules l E X)) ∧
    (∀ (K : DerivedCategory (AdicCompletion.Modules l E X)) (r : ℤ),
      IsDerivedComplete l E X (K⟦r⟧) ↔ IsDerivedComplete l E X K) ∧
    ∃ (_hclosed : ObjectProperty.IsClosedUnderIsomorphisms (IsDerivedComplete l E X))
      (_htri : ObjectProperty.IsTriangulated (IsDerivedComplete l E X)),
      IsIso (constantToContinuous l E X) ∧
      ∃ (b : constantRing l E X ≅ sectionRing l E X)
        (e : sectionRing l E X ≅ continuousRing l E X),
        b.hom ≫ e.hom = constantToContinuous l E X ∧
        (∀ (U : X.ProEtᵒᵖ) (a : Scalar l E),
          b.hom.hom.app U
            ((toSheafify (Scheme.ProEt.topology X)
              ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of (Scalar l E)))).app U a) =
          (pulledBackConstants l E X).hom.app U
            ((toSheafify (Scheme.ProEt.topology X)
              ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (Scalar l E)))).app U a)) ∧
        ∃ (A : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (AdicCompletion.finiteRing l E X 0) ≌
              SheafOfModules.{u + 1} (continuousRing l E X))
          (_hA : A.functor.Additive),
          A.functor = relabel l E X e ∧
          Nonempty (AdicCompletion.derivedReduction l E X 0 ⋙
            AdicCompletion.restrict l E X 0 ≅
              (CondensedRing.derivedTensor (DerivedNakayama.integerRing l E) X).flip.obj
                ((DerivedCategory.singleFunctor _ 0).obj (AdicCompletion.finiteModule l E X 0))) ∧
          ∃ (T₁ : DerivedCategory (AdicCompletion.Modules l E X) ⥤
              DerivedCategory (SheafOfModules.{u + 1} (continuousRing l E X)))
            (_sT₁ : T₁.CommShift ℤ),
            T₁ = AdicCompletion.derivedReduction l E X 0 ⋙ A.functor.mapDerivedCategory ∧
            T₁.IsTriangulated ∧ IsZero (T₁.obj 0) ∧
            (ObjectProperty.ι (IsDerivedComplete l E X) ⋙ T₁).IsTriangulated := by
  sorry

end AlgebraicGeometry.ProEtale.CompleteIntegralResidue

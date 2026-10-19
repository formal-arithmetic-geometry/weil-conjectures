/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleSupportedExteriorProduct
public import Sheaf.Paper.SupportedCohomologyHom
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.Algebra.Homology.BoundedBelowInjectiveResolution
import Sheaf.CategoryTheory.Abelian.RHomDerivedRoof
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Sheaf.AlgebraicGeometry.SupportCohomology

/-!
# The normalized supported-Hom map and the adjunction transpose

Source: blueprint `sec-smooth-purity/sk-thm-regular`, proof Step 5
(blueprint: lem-pur-supported-hom-adjunction-transpose).

The normalization is specified on every bounded-below injective complex. Naturality
then specifies it on every bounded-below object, independently of a resolution.
The degree-a single object is the canonical presentation of A[-a].
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

namespace AlgebraicGeometry.ProEtale

/-- Finiteness of the already defined coefficient ring, with its standard size lift.
Source: purity conventions and the finite coefficient quotient construction
(blueprint: lem-pur-supported-hom-adjunction-transpose). -/
noncomputable instance supportedHomCoefficientFinite (P : WeilConjectures.PurityFiniteSetting.{u}) :
    Finite P.Coefficient :=
  Equiv.ulift.finite_iff.mpr
    (Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos)

variable (A : Type (u + 1)) [CommRing A] [Finite A]
variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- Supported cohomology, as an additive-group-valued functor on D+.
Source: the definition of H^a RΓ_Z (blueprint: lem-pur-supported-hom-adjunction-transpose). -/
noncomputable def supportedHomCohomologyFunctor (a : ℤ) :
    DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ⥤
      AddCommGrpCat.{u + 1} :=
  DerivedCategory.Plus.ι ⋙ supportedSectionsDerived A i ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) a ⋙
      forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}

/-- Morphisms from i_*A_Z in degree zero into the shifted bounded-below object.
Source: supported-Hom identification (blueprint: lem-pur-supported-hom-adjunction-transpose). -/
noncomputable def supportedHomMorphismFunctor (a : ℤ) :
    DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ⥤
      AddCommGrpCat.{u + 1} :=
  DerivedCategory.Plus.ι ⋙
    shiftFunctor (DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) a ⋙
    preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) 0).obj
        ((supportedCoefficients A i).obj (ModuleCat.of A A))))

/-- The actual derived unit on a cochain representative, with the canonical localization
comparison on its source. Source: Stacks Tags 05TH, 05TI and the prescribed injective
normalization (blueprint: lem-pur-supported-hom-adjunction-transpose). -/
noncomputable def supportedHomDerivedUnit
    (I : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ℤ) :
    DerivedCategory.Q.obj
        (((supportSections i A).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ⟶
      (supportedSectionsDerived A i).obj
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I)) :=
  (DerivedCategory.quotientCompQhIso (ModuleCat.{u + 1} A)).inv.app _ ≫
    (supportSections i A).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj I)

/-- The class of an abstract cycle of Γ_Z(I), transported by the actual derived unit.
Source: Stacks Tags 05TH, 05TI (blueprint: lem-pur-supported-hom-adjunction-transpose). -/
noncomputable def supportedHomCycleClass
    (I : CochainComplex.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (a : ℤ)
    (s : (((supportSections i A).mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj).cycles a) :
    (supportedHomCohomologyFunctor A i a).obj (DerivedCategory.Plus.Q.obj I) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) a).map
    (supportedHomDerivedUnit A i I.obj)
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u + 1} A) a).inv.app _
      ((((supportSections i A).mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj).homologyπ a s))

/-- Evaluation at 1 on the degree-a cohomology of a map A[-a] → RΓ_Z(F).
This is the inverse of the cocycle-to-morphism identification in the statement.
Source: the specified cocycle convention
(blueprint: lem-pur-supported-hom-adjunction-transpose). -/
noncomputable def supportedHomClassOfMorphism
    (F : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (a : ℤ)
    (f : (DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) a).obj (ModuleCat.of A A) ⟶
      (supportedSectionsDerived A i).obj F.obj) :
    (supportedHomCohomologyFunctor A i a).obj F :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) a).map f
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u + 1} A) a).inv.app
      (ModuleCat.of A A) (1 : A))

variable [IsLocallyNoetherian X]

/-- The adjoint of A[-a] → RΓ_Z(F), shifted by a. The two comparison isomorphisms
identify C_i(A[-a])[a] with C_i(A)[0]. Source: the cochain shift convention and the
normalized supported adjunction (blueprint: lem-pur-supported-hom-adjunction-transpose). -/
noncomputable def supportedHomShiftedTranspose
    (F : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (a : ℤ)
    (f : (DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) a).obj (ModuleCat.of A A) ⟶
      (supportedSectionsDerived A i).obj F.obj) :
    (supportedHomMorphismFunctor A i a).obj F :=
  ((DerivedCategory.singleFunctors
    (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))).shiftIso a 0 a
      (add_zero a)).inv.app ((supportedCoefficients A i).obj (ModuleCat.of A A)) ≫
    (((supportedCoefficients A i).mapDerivedCategorySingleFunctor a).inv.app
      (ModuleCat.of A A))⟦a⟧' ≫
    (((supportedCoefficientDerivedAdjunction A i).homEquiv _ _).symm f)⟦a⟧'

/-- The supported-Hom isomorphism has exactly the evaluation normalization on injectives.
For a cocycle f, its supported section is the ordinary adjoint evaluated at 1; the
ordinary quotient normalization identifies this with f_X(q_i(1)). The right side is
precisely the derived-Hom cocycle formula. Source: Stacks Tags 06XR, 070I
(blueprint: lem-pur-supported-hom-adjunction-transpose). -/
def SupportedHomEvaluationNormalization (a : ℤ)
    (χ : supportedHomCohomologyFunctor A i a ≅ supportedHomMorphismFunctor A i a) : Prop :=
  ∀ (I : CochainComplex.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (_hi : ∀ r : ℤ, Injective (I.obj.X r))
    (f : (supportedCoefficients A i).obj (ModuleCat.of A A) ⟶ I.obj.X a)
    (hf : f ≫ I.obj.d a (a + 1) = 0)
    (s : (((supportSections i A).mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj).cycles a),
    (((supportSections i A).mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj).iCycles a s =
      ((supportedCoefficientAdjunction A i).homEquiv _ _ f) 1 →
    χ.hom.app (DerivedCategory.Plus.Q.obj I) (supportedHomCycleClass A i I a s) =
      (DerivedCategory.singleFunctorIsoCompQ _ 0).hom.app
          ((supportedCoefficients A i).obj (ModuleCat.of A A)) ≫
        ShiftedHom.map (Cocycle.equivHomShift.symm
          (Cocycle.fromSingleMk f (zero_add a) (a + 1) rfl hf)) DerivedCategory.Q ≫
        ((DerivedCategory.quotientCompQhIso _).inv.app I.obj)⟦a⟧'

/-- The canonical, evaluation-normalized supported-Hom isomorphism equals the shifted
transpose under the supported adjunction. Source: blueprint sk-thm-regular, proof Step 5
(blueprint: lem-pur-supported-hom-adjunction-transpose).

Proof:
1. Put P=C_i(A) and G=Γ_Z. The quotient normalization of
   def-pur-proetale-supported-exterior-product identifies the ordinary adjoint b of f
   by f_X(q_i(1))=b(1). Evaluation at 1 identifies Hom_A(A,G(M)) with G(M), naturally.
2. On the chosen small pro-etale site, prop-pur-kinjective-resolutions-exist and
   lem-sp-grothendieck-enough-injectives supply injectives. By
   lem-sc-bounded-below-injective-resolution choose F→I, bounded below, termwise
   injective and K-injective. The derived unit computes RG there, by
   lem-weil-pbc-right-derived-plus-injective.
3. The ordinary evaluation bijection is a natural additive isomorphism. Apply it
   degreewise to I and derive its inverse. Uniqueness of the right-derived extension
   identifies the result on I with its termwise map, sending s to its ordinary adjoint f_s.
4. By lem-sc-p1-rhom-hom-derived-roof, f_s represents the derived morphism
   P[0]→I[a]→F[a]. This gives χ, its naturality, and the displayed normalization.
5. By lem-sc-derived-adjunction-from-underived the derived counit on I is the
   localized ordinary counit. Hence the transpose of the map taking 1 to s is
   P[-a]→I→F, with degree-a component f_s.
6. Shift by a, using (K[a])^r=K^(r+a). Components of a degree-zero map do not change,
   so this is the same map as in step 4. Boundaries give homotopies with component
   (-1)^a f_t after shifting. Naturality transports both formulas from I to F.
   Every cohomology class is represented by a map A[-a]→RG(F), because A is free of
   rank one. Thus the quantified formula is χ(x)=x^flat[a] for every class x. -/
theorem supportedHom_adjunction_transpose (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X] (a : ℤ) :
    ∃ χ : supportedHomCohomologyFunctor P.Coefficient i a ≅
        supportedHomMorphismFunctor P.Coefficient i a,
      SupportedHomEvaluationNormalization P.Coefficient i a χ ∧
      ∀ (F : DerivedCategory.Plus
          (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
        (f : (DerivedCategory.singleFunctor (ModuleCat.{u + 1} P.Coefficient) a).obj
            (ModuleCat.of P.Coefficient P.Coefficient) ⟶
          (supportedSectionsDerived P.Coefficient i).obj F.obj),
        χ.hom.app F (supportedHomClassOfMorphism P.Coefficient i F a f) =
          supportedHomShiftedTranspose P.Coefficient i F a f := by
  sorry

end AlgebraicGeometry.ProEtale

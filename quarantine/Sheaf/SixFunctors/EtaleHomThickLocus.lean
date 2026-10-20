/- 
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.EtaleDerivedScalarTensor
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
import Sheaf.Algebra.Homology.DerivedScalarExtensionCounitShift
import WeilConjectures.Algebra.Homology.HomComplex
import WeilConjectures.Algebra.Homology.HomTensorTotal
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses

/-! # Scalar extension and the derived internal-Hom comparison

Source: blueprint `thm-coef-finite-hom`, proof paragraph 2; Stacks 06YY, 07A4,
08J9 and 08JC (blueprint: `lem-coef-etale-hom-thick-locus`).

The scalar extension functor and the derived internal Hom are the published étale
constructions.  The comparison is specified by its tensor--Hom transpose, so that
the statement retains the actual evaluation map and does not choose an unrelated
map between the two Hom objects.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v w w₁ w₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
open CategoryTheory.Pretriangulated.Opposite Opposite

namespace AlgebraicGeometry.Etale

variable {A B : Type (u + 1)} [CommRing A] [CommRing B]

/-- Scalar extension of Hom, contravariant in K.
Source: blueprint thm-coef-finite-hom, proof paragraph 2
(blueprint: lem-coef-etale-hom-thick-locus). -/
abbrev EtaleHomLeft (X : Scheme.{u}) (φ : A →+* B)
    (M : DerivedCategoryModule A X) :
    (DerivedCategoryModule A X)ᵒᵖ ⥤ DerivedCategoryModule B X :=
  (derivedHom (ModuleCat.{u + 1} A) X).flip.obj M ⋙ scalarExtension φ X

/-- Hom of scalar extensions, contravariant in K.
Source: blueprint thm-coef-finite-hom, proof paragraph 2
(blueprint: lem-coef-etale-hom-thick-locus). -/
abbrev EtaleHomRight (X : Scheme.{u}) (φ : A →+* B)
    (M : DerivedCategoryModule A X) :
    (DerivedCategoryModule A X)ᵒᵖ ⥤ DerivedCategoryModule B X :=
  (scalarExtension φ X).op ⋙
    (derivedHom (ModuleCat.{u + 1} B) X).flip.obj ((scalarExtension φ X).obj M)

/-- Type of binary tensor comparisons; canonicity is imposed below.
Source: Stacks 07A4, tensor compatibility
(blueprint: lem-coef-etale-hom-thick-locus). -/
abbrev EtaleHomTensorComparison (X : Scheme.{u}) (φ : A →+* B) : Type _ :=
  ∀ K L : DerivedCategoryModule A X,
    ((derivedTensor (ModuleCat.{u + 1} B) X).obj ((scalarExtension φ X).obj K)).obj
        ((scalarExtension φ X).obj L) ≅
      (scalarExtension φ X).obj
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj K).obj L)

section TensorNormalization

variable (C : Type w₁) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [MonoidalClosed C] [SymmetricCategory C] [Abelian.HasFunctorialFlatResolution C]
  (D : Type w₂) [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
  [MonoidalClosed D] [SymmetricCategory D] [Abelian.HasFunctorialFlatResolution D]
  (X : Scheme.{u})

/-- The binary derived comparison is normalized by the ordinary oplax tensorator.
The equation is imposed on K-flat complexes with flat terms. Its bottom arrow is
ordinary scalar balancing, inverse to (x tensor b) tensor (y tensor c) ↦
(x tensor y) tensor bc. The comparison maps r are the derived-extension counit.
Source: Stacks 06YY and 07A4, proof step 1 of the node
(blueprint: lem-coef-etale-hom-thick-locus). -/
def EtaleHomTensorModelNormalization
    (E : Sheaf X.smallEtaleTopology C ⥤ Sheaf X.smallEtaleTopology D) [E.Additive] [E.IsLeftAdjoint]
    [E.OplaxMonoidal]
    (F : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology D))
    (r : ∀ P : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ,
      F.obj (_root_.DerivedCategory.Q.obj P) ⟶
      _root_.DerivedCategory.Q.obj ((E.mapHomologicalComplex (.up ℤ)).obj P))
    (μ : ∀ K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C),
      ((derivedTensor D X).obj (F.obj K)).obj (F.obj L) ≅
        F.obj (((derivedTensor C X).obj K).obj L)) : Prop :=
  ∀ P Q : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ,
    (HomologicalComplex.quasiIso (Sheaf X.smallEtaleTopology C) (.up ℤ)).kFlat P →
    (HomologicalComplex.quasiIso (Sheaf X.smallEtaleTopology C) (.up ℤ)).kFlat Q →
    (∀ i : ℤ, ObjectProperty.flat (P.X i)) → (∀ i : ℤ, ObjectProperty.flat (Q.X i)) →
    F.map (Functor.LaxMonoidal.μ _root_.DerivedCategory.Q P Q) ≫ r (P ⊗ Q) ≫
        _root_.DerivedCategory.Q.map
          (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) E).app P).app Q) =
      (μ (_root_.DerivedCategory.Q.obj P) (_root_.DerivedCategory.Q.obj Q)).inv ≫
        (r P ⊗ₘ r Q) ≫
        Functor.LaxMonoidal.μ _root_.DerivedCategory.Q
          ((E.mapHomologicalComplex (.up ℤ)).obj P)
          ((E.mapHomologicalComplex (.up ℤ)).obj Q)

end TensorNormalization

/-- Naturality in both tensor variables and the flat-term K-flat normalization.
The ordinary oplax structure is the mate of the fixed lax restriction-of-scalars
structure, so it cannot be twisted by per-object automorphisms.
Source: Stacks 07A4, proof step 1 of the node
(blueprint: lem-coef-etale-hom-thick-locus). -/
def IsEtaleHomTensorCanonical (X : Scheme.{u}) (φ : A →+* B)
    (μ : EtaleHomTensorComparison X φ) : Prop :=
  (∀ {K K' : DerivedCategoryModule A X} (f : K ⟶ K') (L : DerivedCategoryModule A X),
    ((derivedTensor (ModuleCat.{u + 1} B) X).map ((scalarExtension φ X).map f)).app
        ((scalarExtension φ X).obj L) ≫ (μ K' L).hom =
      (μ K L).hom ≫ (scalarExtension φ X).map
        (((derivedTensor (ModuleCat.{u + 1} A) X).map f).app L)) ∧
  (∀ (K : DerivedCategoryModule A X) {L L' : DerivedCategoryModule A X} (g : L ⟶ L'),
    ((derivedTensor (ModuleCat.{u + 1} B) X).obj ((scalarExtension φ X).obj K)).map
        ((scalarExtension φ X).map g) ≫ (μ K L').hom =
      (μ K L).hom ≫ (scalarExtension φ X).map
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj K).map g)) ∧
  (letI := (ProEtale.etaleSheafExtendScalarsAdjunction φ X).isLeftAdjoint
   letI := (ProEtale.etaleSheafExtendScalarsAdjunction φ X).leftAdjointOplaxMonoidal
   EtaleHomTensorModelNormalization (ModuleCat.{u + 1} A) (ModuleCat.{u + 1} B) X
     (ProEtale.etaleSheafExtendScalars φ X)
     (scalarExtension φ X) (scalarExtensionRepresentative φ X) μ)

/-- The canonical binary tensor comparison exists uniquely.
Source: Stacks 06YY and 07A4, proof step 1 of the node
(blueprint: lem-coef-etale-hom-thick-locus).
Proof: on two flat-term K-flat resolutions, termwise scalar balancing is the
isomorphism (x tensor b) tensor (y tensor c) ↦ (x tensor y) tensor bc.
The total differential is preserved because the coefficients have degree zero.
The displayed counit equation expresses this map after localization. Naturality
of balancing permits descent along quasi-isomorphisms between K-flat models.
Every object has such a model, and naturality along its resolution determines
every component, proving uniqueness. No flatness of B over A is needed. -/
theorem etaleHomTensorComparison_existsUnique (X : Scheme.{u}) (φ : A →+* B) :
    ∃! μ : EtaleHomTensorComparison X φ, IsEtaleHomTensorCanonical X φ μ := by
  sorry

/-- The uniquely normalized binary comparison, used in the evaluation transpose.
Source: Stacks 07A4, proof step 1 of the node
(blueprint: lem-coef-etale-hom-thick-locus). -/
def etaleHomTensorComparison (X : Scheme.{u}) (φ : A →+* B) :
    EtaleHomTensorComparison X φ :=
  (etaleHomTensorComparison_existsUnique X φ).choose

/-- The defining evaluation-transpose equation for the canonical comparison.
Source: blueprint thm-coef-finite-hom, proof paragraph 2
(blueprint: lem-coef-etale-hom-thick-locus). -/
def IsEtaleHomTranspose (X : Scheme.{u}) (φ : A →+* B)
    (M : DerivedCategoryModule A X)
    (v : EtaleHomLeft X φ M ⟶ EtaleHomRight X φ M) : Prop :=
  ∀ K : DerivedCategoryModule A X,
    (etaleHomTensorComparison X φ K
        (((derivedHom (ModuleCat.{u + 1} A) X).flip.obj M).obj (op K))).hom ≫
        (scalarExtension φ X).map
          ((derivedTensorHomAdjunction (ModuleCat.{u + 1} A) (X := X) K).counit.app M) =
      ((derivedTensorHomAdjunction (ModuleCat.{u + 1} B) (X := X)
          ((scalarExtension φ X).obj K)).homEquiv _ _).symm (v.app (op K))

/-- Naturality of the family of evaluation transposes in the second variable.
Source: blueprint thm-coef-finite-hom, proof paragraph 2
(blueprint: lem-coef-etale-hom-thick-locus). -/
def IsEtaleHomNaturalInM (X : Scheme.{u}) (φ : A →+* B)
    (v : ∀ M : DerivedCategoryModule A X,
      EtaleHomLeft X φ M ⟶ EtaleHomRight X φ M) : Prop :=
  ∀ {M N : DerivedCategoryModule A X} (g : M ⟶ N)
    (K : DerivedCategoryModule A X),
    (scalarExtension φ X).map
        (((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).map g) ≫
        (v N).app (op K) =
      (v M).app (op K) ≫
        ((derivedHom (ModuleCat.{u + 1} B) X).obj (op ((scalarExtension φ X).obj K))).map
          ((scalarExtension φ X).map g)

section HomShiftNormalization

variable (C : Type w) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [MonoidalClosed C] [SymmetricCategory C] [Abelian.HasFunctorialFlatResolution C]
  (X : Scheme.{u})

/-- Canonical cancellation of the two opposite tensor shifts, with the tensor signs.
Source: Stacks 08JC and the tensor-shift calculation in proof step 4
(blueprint: lem-coef-etale-hom-thick-locus). -/
def etaleHomTensorShiftCancellation
    (K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C)) (n : ℤ) :
    ((derivedTensor C X).obj (K⟦-n⟧)).obj (L⟦n⟧) ⟶ ((derivedTensor C X).obj K).obj L :=
  (((curriedTensor _).flip.obj (L⟦n⟧)).commShiftIso (-n)).hom.app K ≫
    ((((curriedTensor _).obj K).commShiftIso n).hom.app L)⟦-n⟧' ≫
    (shiftFunctorCompIsoId _ n (-n) (add_neg_cancel n)).hom.app _

/-- The canonical contravariant Hom shift is fixed by evaluation and tensor shifts.
This equation determines the shift, since its transpose is fixed and shifting is
an equivalence. In complex notation it is the signed reindexing of Hom. With the
tensor shifts composed as in `etaleHomTensorShiftCancellation`, the Hom shift carries
the explicit factor `((n * (n + 1)) / 2).negOnePow`; on Hom complexes it is then
f ↦ (-1)^(n*j + n*(n+1)/2) f in degree j, the sign of Mathlib's `Cochain.leftShift`
by -n. The factor is -1 for n = 1, as the cone triangle's connecting morphism in
the opposite triangulated convention requires. It satisfies
ε(a+b) = (-1)^(a*b) ε(a) ε(b), which compensates c(a+b) = (-1)^(a*b) c(a) c(b) for the
cancellations, so the normalized family obeys the `CommShift` addition axiom
(a multiplicative factor such as `n.negOnePow` would not). It applies to both
coefficient Hom functors.
Source: Stacks 08JC, proof steps 4 and 5
(blueprint: lem-coef-etale-hom-thick-locus). -/
def EtaleHomShiftNormalization
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C))
    (s : ((derivedHom C X).flip.obj M).CommShift ℤ) : Prop :=
  letI := s
  ∀ (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C)) (n : ℤ),
    ((derivedTensor C X).obj (K⟦-n⟧)).map
        (((n * (n + 1)) / 2).negOnePow •
          ((((derivedHom C X).flip.obj M).commShiftIso n).hom.app (op K))) ≫
      etaleHomTensorShiftCancellation C X K (((derivedHom C X).flip.obj M).obj (op K)) n ≫
      (derivedTensorHomAdjunction C (X := X) K).counit.app M =
    (derivedTensorHomAdjunction C (X := X) (K⟦-n⟧)).counit.app M

end HomShiftNormalization

/-- The scalar shift is the canonical adjoint mate of exact restriction's shift.
This is the counit-compatible shift, hence on K-flat models the termwise shift.
Source: Stacks 05SU and 06YY, proof step 1
(blueprint: lem-coef-etale-hom-thick-locus). -/
@[instance_reducible]
def etaleHomScalarCommShift (X : Scheme.{u}) (φ : A →+* B) :
    (scalarExtension φ X).CommShift ℤ :=
  (Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)).leftAdjointCommShift ℤ

/-- Exactness with the evaluation-normalized Hom shifts and the fixed scalar shift.
The two component equations are chi_Phi = F(s_A) followed by sigma and
chi_Psi = H_B(sigma inverse,1) followed by s_B. The very same structures make
both functors triangulated and v a shift-compatible natural transformation;
therefore its third triangle square includes the connecting map and its sign.
Source: Stacks 08JC, proof steps 4--6
(blueprint: lem-coef-etale-hom-thick-locus). -/
def IsEtaleHomReversedExact (X : Scheme.{u}) (φ : A →+* B)
    (M : DerivedCategoryModule A X)
    (v : EtaleHomLeft X φ M ⟶ EtaleHomRight X φ M) : Prop :=
  letI := etaleHomScalarCommShift X φ
  ∃ (sA : ((derivedHom (ModuleCat.{u + 1} A) X).flip.obj M).CommShift ℤ)
    (sB : ((derivedHom (ModuleCat.{u + 1} B) X).flip.obj
      ((scalarExtension φ X).obj M)).CommShift ℤ)
    (_chiPhi : (EtaleHomLeft X φ M).CommShift ℤ)
    (_chiPsi : (EtaleHomRight X φ M).CommShift ℤ),
    EtaleHomShiftNormalization (ModuleCat.{u + 1} A) X M sA ∧
    EtaleHomShiftNormalization (ModuleCat.{u + 1} B) X ((scalarExtension φ X).obj M) sB ∧
    (∀ (K : DerivedCategoryModule A X) (n : ℤ),
      ((EtaleHomLeft X φ M).commShiftIso n).hom.app (op K) =
        (scalarExtension φ X).map ((sA.commShiftIso n).hom.app (op K)) ≫
          ((scalarExtension φ X).commShiftIso n).hom.app
            (((derivedHom (ModuleCat.{u + 1} A) X).flip.obj M).obj (op K))) ∧
    (∀ (K : DerivedCategoryModule A X) (n : ℤ),
      ((EtaleHomRight X φ M).commShiftIso n).hom.app (op K) =
        ((derivedHom (ModuleCat.{u + 1} B) X).flip.obj
            ((scalarExtension φ X).obj M)).map
          ((((scalarExtension φ X).commShiftIso (-n)).inv.app K).op) ≫
        (sB.commShiftIso n).hom.app (op ((scalarExtension φ X).obj K))) ∧
    (EtaleHomLeft X φ M).IsTriangulated ∧
    (EtaleHomRight X φ M).IsTriangulated ∧ NatTrans.CommShift v ℤ

/-- The isomorphism locus and its thick-subcategory closure properties.
Source: blueprint thm-coef-finite-hom, proof paragraph 2
(blueprint: lem-coef-etale-hom-thick-locus). -/
def IsEtaleHomThickIsoLocus (X : Scheme.{u}) (φ : A →+* B)
    (M : DerivedCategoryModule A X)
    (v : EtaleHomLeft X φ M ⟶ EtaleHomRight X φ M) : Prop :=
  (∀ (K : (DerivedCategoryModule A X)ᵒᵖ), IsZero K → IsIso (v.app K)) ∧
  (∀ {K L : (DerivedCategoryModule A X)ᵒᵖ} (_e : K ≅ L),
    IsIso (v.app K) ↔ IsIso (v.app L)) ∧
  (∀ (K : (DerivedCategoryModule A X)ᵒᵖ) (n : ℤ), IsIso (v.app K) →
    IsIso (v.app (K⟦n⟧))) ∧
  (∀ (T : Triangle ((DerivedCategoryModule A X)ᵒᵖ)), T ∈ distTriang _ →
    IsIso (v.app T.obj₁) → IsIso (v.app T.obj₂) → IsIso (v.app T.obj₃)) ∧
  (∀ {K L : (DerivedCategoryModule A X)ᵒᵖ} (i : K ⟶ L) (r : L ⟶ K),
    i ≫ r = 𝟙 K → IsIso (v.app L) → IsIso (v.app K))

/--
For every coefficient map and every fixed coefficient object, scalar extension of the
derived internal Hom admits the evaluation-defined comparison with the internal Hom of
the scalar extensions.  The comparison is natural in both variables, its two
contravariant functors are exact with their canonical shifts (hence carry every
distinguished triangle to the reversed triangle, including the connecting sign), and
its isomorphism locus is thick: zero, isomorphisms, all integer shifts, cones, and
retracts.  No flatness assumption on `φ` is made.

Source: blueprint thm-coef-finite-hom, proof paragraph 2 (localization reduction),
and Stacks 06YY, 07A4, 08J9, 08JC; expanded proof steps 1--9 of this node.

Proof:
1. The canonical comparison on flat-term K-flat models is coefficient multiplication;
   use its uniqueness theorem above. The scalar shift is its counit-compatible one.
2. Transpose scalar extension of the evaluation counit along the B tensor-Hom
   adjunction. K-injective target models compute the given internal Hom.
3. Naturality of evaluation, scalar balancing and the adjunction gives naturality in
   K and M on all derived morphisms, by injectivity of transposition.
4. On Hom complexes the source-shift map is f ↦ (-1)^a f in degree a (node's H ⊗ K
   order, shift one). In the library's K ⊗ H order, for shift n it is
   f ↦ (-1)^(n*j + n*(n+1)/2) f in degree j, and the tensor cancellation has the sign
   (-1)^(p*n) on K^p. Their evaluation equation is precisely
   EtaleHomShiftNormalization. K-flat/K-injective models descend this equation.
5. Transpose the shift square. Both sides reduce to the evaluation equation in step 4
   and the degree-preserving scalar balancing formula in step 1. Iterate for all integers.
6. The cone calculation gives the reversed distinguished triangles. Naturality gives
   their first two squares; the shift square gives their third, retaining its reversal sign.
7. Exact functors preserve zero; naturality preserves invertibility under isomorphisms;
   the normalized shift square preserves invertibility under every integer shift.
8. Two-out-of-three for the resulting morphism of triangles gives closure under cones.
9. For i : K → L and r : L → K with ri = 1, the inverse at K is
   Phi(i) v_L inverse Psi(r). Naturality verifies both inverse identities, giving retract
   closure. No flatness, boundedness, or idempotent-completeness hypothesis is used.
(blueprint: lem-coef-etale-hom-thick-locus)
-/
theorem etaleHomComparison_thickLocus (X : Scheme.{u}) (φ : A →+* B) :
    ∃ (v : ∀ M : DerivedCategoryModule A X,
      EtaleHomLeft X φ M ⟶ EtaleHomRight X φ M),
      (∀ M : DerivedCategoryModule A X,
        IsEtaleHomTranspose X φ M (v M) ∧
          IsEtaleHomReversedExact X φ M (v M) ∧
          IsEtaleHomThickIsoLocus X φ M (v M)) ∧
        IsEtaleHomNaturalInM X φ v := by
  sorry

end AlgebraicGeometry.Etale

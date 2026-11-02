/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedCurvePerverse.CondensedCurvePerverseStatement
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativeL2MiddleImage
public import Mathlib.CategoryTheory.Simple

import WeilConjectures.AlgebraicGeometry.FundamentalGroup.DenseOpenNormal
import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Construction
import WeilConjectures.WeilSheaf.DenseOpen
import WeilConjectures.WeilSheaf.RealSheaves.Setup.RealSheavesSetup
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.ConstructibleSheaf.NormalOpenLowerStar
import WeilConjectures.ConstructibleSheaf.DenseOpenUnitNormal
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.Compactification.GeometricallyConnectedAlgebraicClosure
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import WeilConjectures.RingTheory.ProperBaseChange.NormalRingFieldExtensionDescent
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Mathlib.AlgebraicGeometry.Properties
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartClosure
import WeilConjectures.AlgebraicGeometry.FiniteEtaleLocallyFreeModels
import WeilConjectures.AlgebraicGeometry.SixFunctors.StratificationGenericNeighborhood
import WeilConjectures.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends
import WeilConjectures.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity
import WeilConjectures.Mathlib.Topology.Sober
import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import WeilConjectures.CategoryTheory.Triangulated.TStructure.CohomologyComparisonPasting
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.EndoFunctor
import Mathlib.CategoryTheory.Limits.Creates
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebraComp
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenClosed
import WeilConjectures.AlgebraicGeometry.CoefficientHeartGeneralStatement
import WeilConjectures.AlgebraicGeometry.ProEtaleOpenRestriction.ProEtaleOpenRestrictionCounit
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartCommonStratification
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartCurveLisseDescent
import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.AlgebraicGeometry.CondensedCurvePerverse.GeometricSimpleClassification
public import WeilConjectures.AlgebraicGeometry.CondensedCurvePerverse.GeometricSimpleNoPunctual
public import WeilConjectures.AlgebraicGeometry.CondensedCurvePerverse.WeilSimpleClassification
public import WeilConjectures.AlgebraicGeometry.CondensedCurvePerverse.WeilSimpleNoPunctual
public import WeilConjectures.AlgebraicGeometry.CondensedWeilDenseLisseOpen

/-! # Simple objects of the condensed curve perverse hearts

Source: latest blueprint, sec-deligne-laumon-a1/sk-lem-wft-curve-simples/_section.md,
with prop-a1-curve-perverse-simples.proof.md in that directory.
(blueprint: sk-lem-wft-curve-simples).

Both hearts are the recorded geometric heart and its Frobenius-pair heart. Ordinary
middle extension uses the actual module direct image. In the Weil case its structure
is transported by the canonical base-change isomorphism. Irreducibility of a lisse
object is simplicity within the lisse full subcategory, not among all module sheaves.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedCurvePerverse

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- A punctual perverse complex is a punctual constructible sheaf in degree zero.
Source: latest blueprint, sk-lem-wft-curve-simples, punctual-object clause
(blueprint: sk-lem-wft-curve-simples). -/
def IsPunctualPerverse (C : Scheme.{u}) (P : DerivedCategory (Modules Λ C)) : Prop :=
  ∃ F : Modules Λ C, IsPunctual Λ C F ∧
    Nonempty (P ≅ (DerivedCategory.singleFunctor _ 0).obj F)

/-- Presentation as the shifted ordinary image of a nonzero irreducible lisse sheaf.
Simplicity is tested only against lisse subobjects, and includes nonzeroness.
Source: latest blueprint, sk-lem-wft-curve-simples, middle-extension clause
(blueprint: sk-lem-wft-curve-simples). -/
def IsGeometricSimpleMiddle (C : Scheme.{u}) (P : DerivedCategory (Modules Λ C)) : Prop :=
  ∃ (U : Scheme.{u}) (j : U ⟶ C), IsOpenImmersion j ∧ DenseRange j ∧
    ∃ (M : Modules Λ U) (hM : IsLisseCoefficientModule Λ M),
      Simple (⟨M, hM⟩ : ObjectProperty.FullSubcategory (IsLisseCoefficientModule Λ)) ∧
      Nonempty (P ≅ ((DerivedCategory.singleFunctor _ 0).obj
        ((CondensedRing.lowerStar Λ j).obj M))⟦(1 : ℤ)⟧)

/-- The two geometric kinds, with irreducibility in the constructible sheaf category
for the punctual kind. Source: latest blueprint, sk-lem-wft-curve-simples
(blueprint: sk-lem-wft-curve-simples). -/
def GeometricSimpleKinds (C : Scheme.{u}) (P : DerivedCategory (Modules Λ C)) : Prop :=
  (∃ F : ConstantModelConstructible Λ C, Simple F ∧ IsPunctual Λ C F.obj ∧
    Nonempty (P ≅ (DerivedCategory.singleFunctor _ 0).obj F.obj)) ∨
    IsGeometricSimpleMiddle Λ C P

/-- All geometric clauses, including exclusion of punctual subobjects and quotients.
The mono and epi tests are in the actual perverse heart, not in the derived category.
Source: latest blueprint, sk-lem-wft-curve-simples, both sentences
(blueprint: sk-lem-wft-curve-simples). -/
def GeometricSimpleAssertions (C : Scheme.{u}) : Prop :=
  (∀ P : (heart Λ C).FullSubcategory, Simple P ↔ GeometricSimpleKinds Λ C P.obj) ∧
  (∀ P : (heart Λ C).FullSubcategory, IsGeometricSimpleMiddle Λ C P.obj →
    ∀ Q : (heart Λ C).FullSubcategory, IsPunctualPerverse Λ C Q.obj →
      (∀ f : Q ⟶ P, Mono f → IsZero Q) ∧ (∀ f : P ⟶ Q, Epi f → IsZero Q))

/-- Canonical placement of a Weil module in degree zero followed by shift n.
The structure is the exact inverse-image/single-complex comparison followed by the
canonical shift comparison. No structure isomorphism is chosen.
Source: latest blueprint, sk-lem-wft-curve-simples, degree-zero and shifted objects
(blueprint: sk-lem-wft-curve-simples). -/
def weilPlaced {C : Scheme.{u}} (g : C ≅ C) (n : ℤ) :
    WeilConjectures.condensedWeilModules Λ g.hom ⥤
      Endofunctor.IsoAlgebra (CondensedRing.upperStar Λ g.hom).mapDerivedCategory :=
  Endofunctor.IsoAlgebra.mapOfNatIso
    (Functor.associator (DerivedCategory.singleFunctor _ 0) (shiftFunctor _ n)
        (CondensedRing.upperStar Λ g.hom).mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft (DerivedCategory.singleFunctor _ 0)
        ((CondensedRing.upperStar Λ g.hom).mapDerivedCategory.commShiftIso n) ≪≫
      (Functor.associator (DerivedCategory.singleFunctor _ 0)
        (CondensedRing.upperStar Λ g.hom).mapDerivedCategory (shiftFunctor _ n)).symm ≪≫
      Functor.isoWhiskerRight
        ((CondensedRing.upperStar Λ g.hom).mapDerivedCategorySingleFunctor 0)
        (shiftFunctor _ n) ≪≫
      Functor.associator (CondensedRing.upperStar Λ g.hom)
        (DerivedCategory.singleFunctor _ 0) (shiftFunctor _ n))

/-- Weil-equivariant presentation as a shifted ordinary middle extension on actual
finite-field models. The existing middleWeilImage supplies its canonical Frobenius
base-change mate; the isomorphism is in the category of Frobenius pairs.
Simplicity is in lisse Weil sheaves, without imposing geometric irreducibility.
Source: latest blueprint, sk-lem-wft-curve-simples, Weil middle-extension clause
(blueprint: sk-lem-wft-curve-simples). -/
def IsWeilSimpleMiddle (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (C₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom]
    (P : Endofunctor.IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ell)
        (D.geometricFrobenius C₀).hom).mapDerivedCategory) : Prop :=
  ∃ U₀ : Over (Spec (.of D.k₀)),
    Exists fun [_hft : LocallyOfFiniteType U₀.hom] ↦
      Exists fun [_hqc : QuasiCompact U₀.hom] ↦
        ∃ j₀ : U₀ ⟶ C₀, IsOpenImmersion j₀.left ∧ DenseRange j₀.left ∧
          ∃ (M : WeilConjectures.NativeL2.WeilModule D ell U₀)
            (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell) M.carrier),
            Simple (⟨M, hM⟩ : ObjectProperty.FullSubcategory
              (fun N : WeilConjectures.NativeL2.WeilModule D ell U₀ ↦
                IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell) N.carrier)) ∧
            Nonempty (P ≅ (weilPlaced (Profinite.padicAlgClRingObj ell)
              (D.geometricFrobenius C₀) 1).obj
                (WeilConjectures.NativeL2.middleWeilImage D ell j₀ M))

/-- The two Weil kinds. Punctual irreducibility is tested in the existing constructible
Weil-sheaf category, whereas the middle-extension clause tests lisse Weil subobjects.
Every comparison is an isomorphism of Frobenius pairs.
Source: latest blueprint, sk-lem-wft-curve-simples, Weil classification
(blueprint: sk-lem-wft-curve-simples). -/
def WeilSimpleKinds (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (C₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom]
    (P : Endofunctor.IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ell)
        (D.geometricFrobenius C₀).hom).mapDerivedCategory) : Prop :=
  (∃ F : WeilConjectures.condensedConstructibleWeilSheaves
      (Profinite.padicAlgClRingObj ell) (D.geometricFrobenius C₀).hom,
    Simple F ∧ IsPunctual (Profinite.padicAlgClRingObj ell) (D.geometricFiber C₀).left
      F.obj.carrier ∧
      Nonempty (P ≅ (weilPlaced (Profinite.padicAlgClRingObj ell)
        (D.geometricFrobenius C₀) 0).obj F.obj)) ∨ IsWeilSimpleMiddle D ell C₀ P

/-- All Weil clauses in the recorded Frobenius-pair heart. Punctual subobjects and
quotients are tested by equivariant arrows in that heart; zero support is geometric.
Source: latest blueprint, sk-lem-wft-curve-simples, both sentences
(blueprint: sk-lem-wft-curve-simples). -/
def WeilSimpleAssertions (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (C₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom] : Prop :=
  (∀ P : WeilHeart (Profinite.padicAlgClRingObj ell) (D.geometricFrobenius C₀),
    Simple P ↔ WeilSimpleKinds D ell C₀ P.obj) ∧
  (∀ P : WeilHeart (Profinite.padicAlgClRingObj ell) (D.geometricFrobenius C₀),
    IsWeilSimpleMiddle D ell C₀ P.obj →
    ∀ Q : WeilHeart (Profinite.padicAlgClRingObj ell) (D.geometricFrobenius C₀),
      IsPunctualPerverse (Profinite.padicAlgClRingObj ell) (D.geometricFiber C₀).left
        Q.obj.carrier →
        (∀ f : Q ⟶ P, Mono f → IsZero Q) ∧ (∀ f : P ⟶ Q, Epi f → IsZero Q))

end AlgebraicGeometry.ProEtale.CondensedCurvePerverse

namespace AlgebraicGeometry.ProEtale.CondensedCurvePerverse

/-- Classification of geometric simple perverse sheaves and the absence of nonzero
punctual subobjects or quotients of the listed middle extensions.
Source: latest blueprint, sk-lem-wft-curve-simples/_section.md and
prop-a1-curve-perverse-simples.proof.md (blueprint: sk-lem-wft-curve-simples).

Proof: (1) The coefficient heart gives constructible kernels and cokernels. Common
stratifications, generic neighborhoods and lisse descent give a common dense lisse
open for finitely many sheaves; its complement on the curve is finite. Open adjunction
identifies j^*j_*M with M, and localization identifies supported sheaves with sheaves
on their finite closed support. Sheaf exact sequences give distinguished triangles.
(2) For constructible F, the kernel F_p of F → j_*j^*F is its largest punctual
subsheaf, and F/F_p has no punctual subsheaf. Lisse sheaves and j_*M have none.
(3) In a perverse subobject sequence of a punctual sheaf, the ordinary cohomology
sequence forces the degree -1 terms to vanish. Subobjects are exactly sheaf
subobjects. Thus punctual irreducibility is equivalent to perverse simplicity.
(4) For P=(j_*M)[1], a perverse exact sequence gives
0 → H^-1 Q → j_*M → H^-1 R → H^0 Q → 0. Shrink to a common dense lisse open.
Dense-open fundamental-group surjectivity preserves irreducibility. If H^-1 Q
vanishes there it vanishes globally. The unit from H^-1 R to its dense-open direct
image is monic, and its composite with j_*M is the lisse unit isomorphism. Hence
H^0 Q=0 and Q=0. In the other case H^-1 R is punctual and zero, so R=0.
(5) The ordinary truncation perverse exact sequence makes a simple object either
punctual in degree zero or F[1]. In the punctual case decomposition over the finite
support leaves one irreducible punctual summand.
(6) In the second case F → j_*M is monic with punctual cokernel T. Rotation gives
0 → T[0] → F[1] → (j_*M)[1] → 0. The last term is nonzero, so simplicity kills T.
(7) If M has a proper nonzero lisse subsheaf M', take C=coker(j_*M' → j_*M),
remove its punctual part to obtain C'', and set F'=ker(j_*M → C''). Shifting the
resulting sequence gives a nontrivial perverse subobject, since its two restrictions
are M' and M/M'. This contradiction proves lisse irreducibility.
(8) A nonzero punctual subobject or quotient of a listed middle extension would,
by simplicity, equal it. But punctual complexes have H^-1=0, whereas its H^-1 is
j_*M and restricts to the nonzero M. This proves the last clause. -/
theorem curve_perverse_simples (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [PerfectField k] (_hEll : IsUnit (ell : k))
    (C : Over (Spec (.of k))) [Smooth C.hom] [QuasiCompact C.hom]
    [IsSeparated C.hom] (_hPure : C.left.IsPureDimension 1) :
    GeometricSimpleAssertions (Profinite.padicAlgClRingObj ell) C.left := by
  constructor
  · exact geometric_simple_classification ell k _hEll C _hPure
  · exact geometric_simple_no_punctual ell k _hEll C _hPure

/-- Classification of simple perverse Weil sheaves, with Weil irreducibility, and the
absence of nonzero punctual equivariant subobjects or quotients of middle extensions.
Source: latest blueprint, sk-lem-wft-curve-simples/_section.md and
prop-a1-curve-perverse-simples.proof.md (blueprint: sk-lem-wft-curve-simples).

Proof: Follow steps (1)--(8) of the preceding proof in the Weil heart. The common
lisse opens can be chosen over the finite field by the condensed Weil dense-lisse-open
lemma and finite intersection. The forgetful functor creates kernels and cokernels
and reflects exactness. The punctual kernel, quotient by punctual torsion, units,
and the saturation F' therefore inherit their actual Frobenius structures. On a
stable dense open, dense-open Weil-group surjectivity preserves Weil irreducibility;
no geometric irreducibility is asserted. The two cases in step (4), truncation in
step (5), rotated sequence in step (6), and saturated subobject in step (7) all use
equivariant arrows. The ordinary direct image carries precisely the base-change
structure of NativeL2.middleWeilImage, and degree-zero placement and shift carry the
single-complex and shift comparisons of weilPlaced. Finally step (8) applies after
forgetting the punctual subobject or quotient, since the underlying middle extension
has nonzero degree -1 cohomology. These are the eight steps of the DAG proof. -/
theorem curve_perverse_weil_simples (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (_hEll : ell ≠ D.p)
    (C₀ : Over (Spec (.of D.k₀))) [Smooth C₀.hom] [QuasiCompact C₀.hom]
    [IsSeparated C₀.hom] (_hPure : C₀.left.IsPureDimension 1) :
    WeilSimpleAssertions D ell C₀ := by
  constructor
  · exact weil_simple_classification D ell _hEll C₀ _hPure
  · exact weil_simple_no_punctual D ell _hEll C₀ _hPure

end AlgebraicGeometry.ProEtale.CondensedCurvePerverse

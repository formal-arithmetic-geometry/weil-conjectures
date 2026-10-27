/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q160
-/
module

public import Sheaf.CategoryTheory.CondensedEquivariantBarData
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.CategoryTheory.DoubleComplexTotal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroFlat
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.Algebra.Homology.SliceScalarHomChainAdjunction
import Sheaf.Algebra.Homology.ScalarInternalHomAdjunction
import Sheaf.SixFunctors.ResolvingDerivedAdjunction
import Sheaf.CategoryTheory.CondensedSplitCosetInduction
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import WeilConjectures.Algebra.Homology.FirstQuadrantTotalComparison
import WeilConjectures.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

/-! # Evaluation-normalized scalar comparison of condensed bar resolutions

Source: main-20261015 blueprint, direct-images proof paragraph (3), formal internal
condensed bar expansion (blueprint: lem-sfb-condensed-bar-scalar-resolution-comparison).
The specified comparisons retain the actual derived units and chain augmentations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace CategoryTheory.CondensedBar

/-- Cache the published tensor structure on complexes of internal modules. The value is
exactly the existing instance, not a second tensor product.
Source: ordinary internal tensor complexes, step 1
(blueprint: lem-sfb-condensed-bar-scalar-resolution-comparison). -/
instance scalarComplexMonoidal (A : Ring.{u}) :
    MonoidalCategory (CochainComplex (Modules A) ℤ) :=
  Mod.monoidalCategoryCochainComplex

/-- The existing free-parameter construction on maps of profinite sets.
Source: free linearization, step 2
(blueprint: lem-sfb-condensed-bar-scalar-resolution-comparison). -/
def scalarFreeMap (A : Ring.{u}) {P Q : Profinite.{u}} (f : P ⟶ Q) :
    freeParameter A P ⟶ freeParameter A Q :=
  (Sheaf.composeAndSheafify (coherentTopology Profinite.{u}) AddCommGrpCat.free.{u + 1} ⋙
    Mod.free A.toMon.X).map
      ((GrothendieckTopology.uliftYoneda.{u + 1} (coherentTopology Profinite.{u})).map f)

/-- The actual unit generator of a free internal module, over an arbitrary test space.
Source: the free adjunction, step 2
(blueprint: lem-sfb-condensed-bar-scalar-resolution-comparison). -/
def scalarFreeGenerator (A : Ring.{u}) (P T : Profinite.{u}) (f : T ⟶ P) :
    sections A (freeParameter A P) T :=
  (((Profinite.CondensedAction.InternalBar.freeAdjunction A.toMon).unit.app
    ((GrothendieckTopology.uliftYoneda.{u + 1} (coherentTopology Profinite.{u})).obj P)).hom.app
      (op T)) (ULift.up f)

/-- The section-module version of the free representable presheaf, followed by its
actual sheafification. At T its presheaf is the direct sum of A(T) indexed by T to P.
Source: step 1, the j-shriek description
(blueprint: lem-sfb-condensed-bar-scalar-resolution-comparison). -/
def scalarFreeSheaf (A : Ring.{u}) (P : Profinite.{u}) :=
  (PresheafOfModules.sheafification.{u + 1}
    (𝟙 ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf (coherentTopology Profinite.{u}) A.X)).obj)).obj
    (PresheafOfModules.freeObj.{u + 1}
      (((GrothendieckTopology.uliftYoneda.{u + 1} (coherentTopology Profinite.{u})).obj P).obj))

/-- Pullback in the parameter, transported along the recorded internal-Hom identification.
Source: naturality in the parameter, steps 2--5
(blueprint: lem-sfb-condensed-bar-scalar-resolution-comparison). -/
def scalarHomPre {A : Ring.{u}} (F : InternalFunctions A) {P Q : Profinite.{u}}
    (f : P ⟶ Q) : F.functor Q ⟶ F.functor P :=
  (F.internalHom Q).hom ≫ Mod.ihomMap (scalarFreeMap A f) ≫ (F.internalHom P).inv

/-- The functorial K-injective resolution supplies the exact arbitrary-quasi-isomorphism
hypothesis of the recorded ordinary right-derived functor.
Source: Grothendieck K-injective resolutions, steps 1 and 8
(blueprint: lem-sfb-condensed-bar-scalar-resolution-comparison). -/
abbrev scalarEnoughKInjectives (A : Ring.{u}) :
    ∀ K : CochainComplex (Modules A) ℤ,
      ∃ (I : CochainComplex (Modules A) ℤ) (f : K ⟶ I), I.IsKInjective ∧ QuasiIso f :=
  fun K ↦ ⟨(CochainComplex.kInjectiveResolutionFunctor (Modules A)).obj K,
    (CochainComplex.toKInjectiveResolution (Modules A)).app K, inferInstance,
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app (Modules A) K).2⟩

/-- Second-variable derived internal functions, using the dependency's ordinary total
right-derived functor, not a bounded-below category.
Source: step 4 (blueprint: lem-sfb-condensed-bar-scalar-resolution-comparison). -/
def scalarRHom {A : Ring.{u}} [HasDerivedCategory.{u + 2} (Modules A)]
    (F : InternalFunctions A) (P : Profinite.{u}) :
    DerivedCategory (Modules A) ⥤ DerivedCategory (Modules A) :=
  (F.functor P).rightDerivedFunctorOfQuasiIsoResolutions (scalarEnoughKInjectives A)

/-- Parameter pullback on the recorded derived functors, defined by the inverse of
its universal bijection. This choice is unique among unit-compatible transformations.
Source: parameter naturality in steps 2--5
(blueprint: lem-sfb-condensed-bar-scalar-resolution-comparison). -/
def scalarRHomPre {A : Ring.{u}} [HasDerivedCategory.{u + 2} (Modules A)]
    (F : InternalFunctions A) {P Q : Profinite.{u}} (f : P ⟶ Q) :
    scalarRHom F Q ⟶ scalarRHom F P :=
  (Equiv.ofBijective
    (fun β ↦ (F.functor Q).rightDerivedFunctorOfQuasiIsoResolutionsUnit
      (scalarEnoughKInjectives A) ≫ Functor.whiskerLeft DerivedCategory.Qh β)
    ((F.functor Q).rightDerivedFunctorOfQuasiIsoResolutions_universal
      (scalarEnoughKInjectives A) (scalarRHom F P))).symm
        (Functor.whiskerRight (NatTrans.mapHomotopyCategory (scalarHomPre F f) (.up ℤ))
          DerivedCategory.Qh ≫
            (F.functor P).rightDerivedFunctorOfQuasiIsoResolutionsUnit
              (scalarEnoughKInjectives A))

/-- The actual unit from localized internal functions to their second-variable derivation.
Source: the comparison u in steps 4 and 8
(blueprint: lem-sfb-condensed-bar-scalar-resolution-comparison). -/
def scalarHomUnit {A : Ring.{u}} [HasDerivedCategory.{u + 2} (Modules A)]
    (F : InternalFunctions A) (P : Profinite.{u}) (L : CochainComplex (Modules A) ℤ) :
    DerivedCategory.Q.obj (((F.functor P).mapHomologicalComplex (.up ℤ)).obj L) ⟶
      (scalarRHom F P).obj (DerivedCategory.Q.obj L) :=
  ((F.functor P).rightDerivedFunctorOfQuasiIsoResolutionsUnit
    (scalarEnoughKInjectives A)).app ((HomotopyCategory.quotient _ (.up ℤ)).obj L)

/-- Flatness, K-flatness, and the actual representable sheafification description.
These are properties of the existing free object, not replacement definitions.
Source: step 1 (blueprint: lem-sfb-condensed-bar-scalar-resolution-comparison). -/
def ScalarFreeProperties (A : Ring.{u}) : Prop :=
  ∀ P : Profinite.{u},
    Nonempty ((sectionsFunctor A).obj (freeParameter A P) ≅ scalarFreeSheaf A P) ∧
    ObjectProperty.flat (freeParameter A P) ∧
    (HomologicalComplex.quasiIso (Modules A) (.up ℤ)).kFlat
      ((HomologicalComplex.single (Modules A) (.up ℤ) 0).obj (freeParameter A P))

section Comparison
variable {A A' : Ring.{u}} (a : A ⟶ A')
  [HasDerivedCategory.{u + 2} (Modules A)] [HasDerivedCategory.{u + 2} (Modules A')]

/-- The free scalar-extension and scalar-Hom comparisons, with unit and evaluation
normalizations on all generalized sections and all complexes. Naturality in modules
is encoded by natural isomorphisms; parameter naturality is retained explicitly.
Source: steps 2--5 and equation (*)
(blueprint: lem-sfb-condensed-bar-scalar-resolution-comparison). -/
structure ScalarParameterComparison (F : InternalFunctions A) (F' : InternalFunctions A') where
  free : ∀ P : Profinite.{u},
    (Mod.extendScalars a.hom.hom).obj (freeParameter A P) ≅ freeParameter A' P
  free_natural : ∀ {P Q : Profinite.{u}} (f : P ⟶ Q),
    (Mod.extendScalars a.hom.hom).map (scalarFreeMap A f) ≫ (free Q).hom =
      (free P).hom ≫ scalarFreeMap A' f
  free_unit : ∀ (P T : Profinite.{u}) (f : T ⟶ P),
    (((Mod.extendRestrictAdjunction a.hom.hom).unit.app (freeParameter A P) ≫
      (Mod.comap a.hom.hom).map (free P).hom).hom.hom.app (op T))
        (scalarFreeGenerator A P T f) = scalarFreeGenerator A' P T f
  derived_free : ∀ P : Profinite.{u},
    IsIso ((Mod.extendScalars a.hom.hom).leftDerivedFunctorCounit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        ((HomologicalComplex.single (Modules A) (.up ℤ) 0).obj (freeParameter A P))))
  hom : ∀ P : Profinite.{u},
    F'.functor P ⋙ Mod.comap a.hom.hom ≅ Mod.comap a.hom.hom ⋙ F.functor P
  evaluation : ∀ (P T V : Profinite.{u}) (f : V ⟶ T) (g : C(V, P))
    (N : Modules A') (x : sections A' ((F'.functor P).obj N) T),
    (F.evaluate P T ((Mod.comap a.hom.hom).obj N)
      (((hom P).hom.app N).hom.hom.app (op T) x)).val V f g =
        (F'.evaluate P T N x).val V f g
  parameter : ∀ {P Q : Profinite.{u}} (f : P ⟶ Q) (N : Modules A'),
    (Mod.comap a.hom.hom).map ((scalarHomPre F' f).app N) ≫ (hom P).hom.app N =
      (hom Q).hom.app N ≫ (scalarHomPre F f).app ((Mod.comap a.hom.hom).obj N)
  derived : ∀ P : Profinite.{u},
    (Mod.comap a.hom.hom).mapDerivedCategory ⋙ scalarRHom F P ≅
      scalarRHom F' P ⋙ (Mod.comap a.hom.hom).mapDerivedCategory
  derived_parameter : ∀ {P Q : Profinite.{u}} (f : P ⟶ Q)
    (N : DerivedCategory (Modules A')),
    (scalarRHomPre F f).app ((Mod.comap a.hom.hom).mapDerivedCategory.obj N) ≫
        (derived P).hom.app N =
      (derived Q).hom.app N ≫
        (Mod.comap a.hom.hom).mapDerivedCategory.map ((scalarRHomPre F' f).app N)
  normalization : ∀ (P : Profinite.{u}) (L : CochainComplex (Modules A') ℤ),
    DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (hom P) (.up ℤ)).hom.app L) ≫
      scalarHomUnit F P (((Mod.comap a.hom.hom).mapHomologicalComplex (.up ℤ)).obj L) ≫
      (scalarRHom F P).map ((Mod.comap a.hom.hom).mapDerivedCategoryFactors.inv.app L) ≫
      (derived P).hom.app (DerivedCategory.Q.obj L) =
    (Mod.comap a.hom.hom).mapDerivedCategoryFactors.inv.app
        (((F'.functor P).mapHomologicalComplex (.up ℤ)).obj L) ≫
      (Mod.comap a.hom.hom).mapDerivedCategory.map (scalarHomUnit F' P L)

end Comparison

section Resolutions
variable {A A' : Ring.{u}} {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [ActionAbelian A G] [ActionAbelian A' G]
  [IsGrothendieckAbelian.{u + 1} (Equivariant A G)]
  [IsGrothendieckAbelian.{u + 1} (Equivariant A' G)]
  [HasDerivedCategory.{u + 2} (Equivariant A G)]
  [HasDerivedCategory.{u + 2} (Equivariant A' G)]
  [HasDerivedCategory.{u + 2} (Modules A)] [HasDerivedCategory.{u + 2} (Modules A')]
  (a : A ⟶ A') {M : Model A G} {M' : Model A' G} (s : ScalarModel a M M')

/-- The additional clauses of the scalar resolution comparison on the recorded bar
models. The computation field retains existence of strict lifts, all column, total and
invariant quasi-isomorphisms, and the square after inverting augmentations. The remaining
fields retain the actual chain square, its derived-unit identification and independence
under every augmentation-preserving change of the two resolutions.
Source: steps 5 and 7--12
(blueprint: lem-sfb-condensed-bar-scalar-resolution-comparison). -/
structure ScalarResolutionComparison
    (c : ScalarParameterComparison a M.functions M'.functions) where
  computation : ScalarComputation a s
  cosimplicial : ∀ N : Equivariant A' G,
    M.bar.diagram.obj (s.restriction.functor.obj N) ≅
      M'.bar.diagram.obj N ⋙ Mod.comap a.hom.hom
  cochain_terms : ∀ (N : Equivariant A' G) (n : ℕ),
    (cosimplicial N).hom.app (SimplexCategory.mk n) = (s.bar.hom.app N).f n
  cosimplicial_term : ∀ (N : Equivariant A' G) (n : ℕ),
    (cosimplicial N).hom.app (SimplexCategory.mk n) ≫
        (Mod.comap a.hom.hom).map (M'.bar.term N n).hom ≫
          (c.hom (power G n)).hom.app N.module =
      (M.bar.term (s.restriction.functor.obj N) n).hom ≫
        (M.functions.functor (power G n)).map (s.restriction.underlying.hom.app N)
  lift_quasiIso : ∀ (N : Equivariant A' G)
    (I : InjectiveResolution (s.restriction.functor.obj N)) (J : InjectiveResolution N)
    (β : (s.restriction.functor.mapHomologicalComplex (.up ℕ)).obj J.cocomplex ⟶
      I.cocomplex) (_hβ : s.restriction.functor.map (J.ι.f 0) ≫ β.f 0 = I.ι.f 0),
    QuasiIso β
  restricted_unit : ∀ (N : Equivariant A' G) (J : InjectiveResolution N)
    (P : Profinite.{u}),
    IsIso (scalarHomUnit M.functions P
      (extend (((forgetAction (A := A) (G := G)).mapHomologicalComplex (.up ℕ)).obj
        ((s.restriction.functor.mapHomologicalComplex (.up ℕ)).obj J.cocomplex))))
  target_unit : ∀ (N : Equivariant A G) (I : InjectiveResolution N)
    (P : Profinite.{u}),
    IsIso (scalarHomUnit M.functions P
      (extend (((forgetAction (A := A) (G := G)).mapHomologicalComplex (.up ℕ)).obj
        I.cocomplex)))
  restricted_augmentation : ∀ (N : Equivariant A' G) (J : InjectiveResolution N),
    QuasiIso (((Mod.comap a.hom.hom).mapHomologicalComplex (.up ℕ)).map
      (M'.totalAugmentation.map.app J.cocomplex))
  chain_square : ∀ (N : Equivariant A' G)
    (I : InjectiveResolution (s.restriction.functor.obj N)) (J : InjectiveResolution N)
    (β : (s.restriction.functor.mapHomologicalComplex (.up ℕ)).obj J.cocomplex ⟶
      I.cocomplex) (_hβ : s.restriction.functor.map (J.ι.f 0) ≫ β.f 0 = I.ι.f 0),
    scalarInvariantChain a s J.cocomplex I.cocomplex β ≫
        M.totalAugmentation.map.app I.cocomplex =
      ((Mod.comap a.hom.hom).mapHomologicalComplex (.up ℕ)).map
          (M'.totalAugmentation.map.app J.cocomplex) ≫
        scalarTotalChain a s J.cocomplex I.cocomplex β
  independent : ∀ (N : Equivariant A' G)
    (I₁ I₂ : InjectiveResolution (s.restriction.functor.obj N))
    (J₁ J₂ : InjectiveResolution N)
    (j : J₁.cocomplex ⟶ J₂.cocomplex) (_hj : J₁.ι ≫ j = J₂.ι)
    (i : I₁.cocomplex ⟶ I₂.cocomplex) (_hi : I₁.ι ≫ i = I₂.ι)
    (β₁ : (s.restriction.functor.mapHomologicalComplex (.up ℕ)).obj J₁.cocomplex ⟶
      I₁.cocomplex)
    (_hβ₁ : s.restriction.functor.map (J₁.ι.f 0) ≫ β₁.f 0 = I₁.ι.f 0)
    (β₂ : (s.restriction.functor.mapHomologicalComplex (.up ℕ)).obj J₂.cocomplex ⟶
      I₂.cocomplex)
    (_hβ₂ : s.restriction.functor.map (J₂.ι.f 0) ≫ β₂.f 0 = I₂.ι.f 0),
    DerivedCategory.Q.map (HomologicalComplex.extendMap
        (((Mod.comap a.hom.hom).mapHomologicalComplex (.up ℕ)).map
          ((M'.invariants.functor.mapHomologicalComplex (.up ℕ)).map j))
        ComplexShape.embeddingUpNat) ≫
      DerivedCategory.Q.map (HomologicalComplex.extendMap
        (scalarInvariantChain a s J₂.cocomplex I₂.cocomplex β₂)
        ComplexShape.embeddingUpNat) =
    DerivedCategory.Q.map (HomologicalComplex.extendMap
        (scalarInvariantChain a s J₁.cocomplex I₁.cocomplex β₁)
        ComplexShape.embeddingUpNat) ≫
      DerivedCategory.Q.map (HomologicalComplex.extendMap
        ((M.invariants.functor.mapHomologicalComplex (.up ℕ)).map i)
        ComplexShape.embeddingUpNat) ∧
    DerivedCategory.Q.map (HomologicalComplex.extendMap
        (((Mod.comap a.hom.hom).mapHomologicalComplex (.up ℕ)).map
          ((totalCochains M'.bar).map j)) ComplexShape.embeddingUpNat) ≫
      DerivedCategory.Q.map (HomologicalComplex.extendMap
        (scalarTotalChain a s J₂.cocomplex I₂.cocomplex β₂)
        ComplexShape.embeddingUpNat) =
    DerivedCategory.Q.map (HomologicalComplex.extendMap
        (scalarTotalChain a s J₁.cocomplex I₁.cocomplex β₁)
        ComplexShape.embeddingUpNat) ≫
      DerivedCategory.Q.map (HomologicalComplex.extendMap
        ((totalCochains M.bar).map i) ComplexShape.embeddingUpNat)
end Resolutions

/-- All coefficients and all ring maps are quantified, and all abelian structures and
bar models are conclusions. No flatness of the coefficient map or injectivity of a
restricted resolution is an input. The existential models use exactly the dependency's
normalized data; no object is chosen from an undetermined existence theorem.
Source: the full scalar-resolution statement
(blueprint: lem-sfb-condensed-bar-scalar-resolution-comparison). -/
def ScalarResolutionAssertion (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] : Prop := by
  refine ∃ h : ∀ A : Ring.{u}, ActionAbelian A G, ?_
  letI (A : Ring.{u}) : ActionAbelian A G := h A
  refine ∃ g : ∀ A : Ring.{u}, IsGrothendieckAbelian.{u + 1} (Equivariant A G), ?_
  letI (A : Ring.{u}) : IsGrothendieckAbelian.{u + 1} (Equivariant A G) := g A
  letI (A : Ring.{u}) : HasDerivedCategory.{u + 2} (Equivariant A G) :=
    HasDerivedCategory.standard (Equivariant A G)
  letI (A : Ring.{u}) : HasDerivedCategory.{u + 2} (Modules A) :=
    HasDerivedCategory.standard (Modules A)
  exact (∀ A : Ring.{u}, ScalarFreeProperties A) ∧
    ∃ models : ∀ A : Ring.{u}, Model A G,
      ∀ (A A' : Ring.{u}) (a : A ⟶ A'),
        ∃ (s : ScalarModel a (models A) (models A'))
          (c : ScalarParameterComparison a (models A).functions (models A').functions),
          Nonempty (ScalarResolutionComparison a s c)

/-- Scalar restriction compares the specified internal profinite bar resolutions with
all free-parameter, internal-Hom, augmentation and resolution-independence normalizations.
Source: main-20261015 direct-images proof paragraph (3), formal bar expansion
(blueprint: lem-sfb-condensed-bar-scalar-resolution-comparison).

Proof:
1. Transport through the underlying-sheaf-preserving internal/section module equivalence.
   Its tensor comparison transports the closed adjunction. The actual free module is
   the sheafification of the representable free presheaf, hence j-shriek of the slice
   unit. Extension-by-zero flatness and bounded-flat K-flatness give ScalarFreeProperties.
2. The free and scalar adjunctions identify A' tensor A[P] with A'[P], sending a' tensor
   a[p] to a' phi(a)[p]. The inverse sends [p] to 1 tensor [p]. K-flatness makes the
   left-derived counit invertible. These maps commute with every parameter map.
3. The slice scalar-Hom chain adjunction identifies internal functions on every test
   space. It sends f to the function [p] maps to f([p]); the inverse extends A'-linearly.
4. Apply the derived scalar-Hom adjunction. Transposing with the flat degree-zero A[P]
   shows that both composites in normalization are restricted evaluation preceded by
   the scalar unit. Uniqueness of transposes gives equality for every complex.
5. Evaluate on every generalized tuple. The first face acts by g1, interior faces
   multiply adjacent coordinates, the last drops its entry, and degeneracies insert 1.
   The evaluation identification commutes with all these operations.
6. The action and module categories are Grothendieck abelian. Split-coset induction
   for the trivial subgroup is exact left adjoint to forgetting, which therefore
   preserves injectives. Restriction is exact and invariants are left exact.
7. The restricted augmentation of J is a monomorphic quasi-isomorphism. Lift it into
   I, a bounded-below complex of injectives. Every augmentation-preserving lift beta
   is a quasi-isomorphism by two-out-of-three.
8. Underlying J and I are bounded-below injective complexes, hence K-injective. Their
   derived units are invertible. The normalization of step 4 makes the unit on Res J
   invertible too, without asserting injectivity of its terms. Naturality of this
   unit proves the column quasi-isomorphisms and their specified derived identities.
9. First-quadrant column comparison makes the total map a quasi-isomorphism. Scalar
   restriction commutes with the finite diagonal sums and their signed differential.
10. Exact augmented bar rows for equivariant injectives make the two total
    augmentations quasi-isomorphisms. Exact restriction preserves the J augmentation.
11. Naturality of the augmentation for arbitrary chain maps gives chain_square:
    both paths send an invariant section m in degree q to beta(m) in bidegree (0,q),
    with zero higher-bar components. Two-out-of-three gives the invariant quasi-iso.
    Localize and invert augmentations to obtain ScalarComputation.square.
12. Two lifts agreeing on the augmentation are equivariantly homotopic. Invariants
    preserve this homotopy; on bar column p totalization uses (-1)^p times it. For
    changes j and i of resolutions, i beta1 and beta2 Res j agree on the augmentation,
    so the same argument proves independent, including independence of beta by taking
    the identity changes. Localizing the chain square preserves these identifications.
-/
theorem condensed_bar_scalar_resolution_comparison (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    ScalarResolutionAssertion G := by
  sorry

end CategoryTheory.CondensedBar

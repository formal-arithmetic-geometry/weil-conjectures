/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q56
-/
module

public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.Algebra.Homology.HomComplexProjections
public import Sheaf.CategoryTheory.ScalarLocalization
public import Sheaf.NumberTheory.Padics.IntegersLocalizationUniformizer
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Sheaf.CategoryTheory.ScalarLocalizationDerivedHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Sheaf.Algebra.Homology.RingedSiteBoundedFreeRHomModel
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.Algebra.Homology.HomComplex

-- The high-priority successor-universe sheafification instance gets stuck on coefficient-universe goals.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

/-!
# Rational degree-zero sheaf Hom comparison

Source: Stacks Project, Cohomology on Sites, Tag 08JI, extended to scalar-localized
retractions as in the proof of the current blueprint `prop-sf-dualizable`.
(blueprint: lem-sf-rational-term-hom-comparison).
The degree-zero identification is normalized by the product projection of the existing
Hom complex. The comparison is explicitly postcomposition with the given resolution.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.RationalTermHom

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})

/-- The degree-zero complex of a module sheaf. Source: Stacks, Tag 08JI
(blueprint: lem-sf-rational-term-hom-comparison). -/
abbrev single
    (F : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
  (CochainComplex.singleFunctor _ (0 : ℤ)).obj F

/-- The coefficient sheaf as a module over itself. Source: Stacks, Tag 08JI
(blueprint: lem-sf-rational-term-hom-comparison). -/
abbrev coefficients :=
  SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)

/-- The complex B(F) = Hom(F,R)[0]. Source: Stacks, Tag 08JI
(blueprint: lem-sf-rational-term-hom-comparison). -/
abbrev ordinary
    (F : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
  single R (SheafOfModules.homObj (R := R) F (coefficients R))

/-- The complex T(F) = Hom-complex(F[0],I). Source: Stacks, Sections 08J7 and 0A8X
(blueprint: lem-sf-rational-term-hom-comparison). -/
abbrev resolved
    (I : CochainComplex
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (F : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
  homComplex (R := R) (single R F) I

/-- Precomposition on B. Source: Stacks, Section 0A8X
(blueprint: lem-sf-rational-term-hom-comparison). -/
def ordinaryMap
    {F G : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : F ⟶ G) : ordinary R G ⟶ ordinary R F :=
  (CochainComplex.singleFunctor _ (0 : ℤ)).map
    (SheafOfModules.homObjMap (R := R) f (𝟙 (coefficients R)))

/-- Precomposition on T. Source: Stacks, Section 0A8X
(blueprint: lem-sf-rational-term-hom-comparison). -/
def resolvedMap
    (I : CochainComplex
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    {F G : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : F ⟶ G) : resolved R I G ⟶ resolved R I F :=
  ((homComplexFunctor (R := R)).map
    ((CochainComplex.singleFunctor _ (0 : ℤ)).map f).op).app I

/-- Projection to the (0,0) factor of the existing Hom complex. Its product projections
are those in the specification of `homComplexFunctor`. Source: Stacks, Section 0A8X
(blueprint: lem-sf-rational-term-hom-comparison). -/
def zeroProjection
    (F : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    (resolved R (single R (coefficients R)) F).X 0 ⟶
      SheafOfModules.homObj (R := R) ((single R F).X 0)
        ((single R (coefficients R)).X 0) :=
  Classical.choose
    (homComplex_projections_exists.{u, u, u, u} (C := C) (J := J) (R := R))
      (single R F) (single R (coefficients R)) 0 0 0 rfl

/-- The normalized degree-zero identification with the Hom complex. Source: Stacks,
Section 0A8X (blueprint: lem-sf-rational-term-hom-comparison).
The displayed projection is the identity on ordinary local linear maps, transported
through the canonical degree-zero isomorphisms of the single complexes. -/
def IsNormalized
    (e : ∀ F : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R),
      ordinary R F ≅ resolved R (single R (coefficients R)) F) : Prop :=
  ∀ F, (e F).hom.f 0 ≫ zeroProjection R F =
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (SheafOfModules.homObj (R := R) F (coefficients R))).hom ≫
        SheafOfModules.homObjMap (R := R)
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (coefficients R)).inv

/-- Postcomposition with j, following the normalized identification. Source: Stacks,
Tag 08JI (blueprint: lem-sf-rational-term-hom-comparison). -/
def comparison
    (e : ∀ F : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R),
      ordinary R F ≅ resolved R (single R (coefficients R)) F)
    {I : CochainComplex
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ}
    (j : single R (coefficients R) ⟶ I)
    (F : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    ordinary R F ⟶ resolved R I F :=
  (e F).hom ≫ ((homComplexFunctor (R := R)).obj (op (single R F))).map j

variable [HasDerivedCategory.{w}
  (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]

/-- The image of a complex in the scalar localization of D(R). Source: blueprint,
scalar rationalization (blueprint: lem-sf-rational-term-hom-comparison). -/
def localizedObject (A : Type v) [CommRing A]
    (t : A) (K : CochainComplex
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ) :
    ScalarLocalization A (DerivedCategory (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) t :=
  ⟨DerivedCategory.Q.obj K⟩

/-- The image of a chain map in the scalar localization of D(R). Source: blueprint,
scalar rationalization (blueprint: lem-sf-rational-term-hom-comparison). -/
def localizedMap (A : Type v) [CommRing A]
    [Linear A
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    (t : A) {K L : CochainComplex
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ}
    (f : K ⟶ L) : localizedObject R A t K ⟶ localizedObject R A t L :=
  TensorProduct.tmul A (1 : Localization.Away t) (DerivedCategory.Q.map f)

/-- A finite free retract after scalar localization has the expected ordinary dual and
Hom comparison. Source: Stacks, Tag 08JI and the scalar-retraction extension used in
blueprint `prop-sf-dualizable` (blueprint: lem-sf-rational-term-hom-comparison).

Proof:
1. The product Hom formula has only the (0,0) factor for two single complexes.
   Projection to it is an isomorphism; e is its inverse, uniquely normalized above.
   Composing e.hom with Hom(F[0],j) is exactly postcomposition with j.
2. For E = R^m, evaluation on the standard basis identifies c_E with m copies of j.
   Hence it is invertible in D(R), also for m=0; alternatively specialize
   lem-weil-pbc-ringed-site-bounded-free-rhom-model to bounds 0,0.
3. Precomposition commutes with postcomposition with j, so c is natural under every
   module map. Both precomposition actions are A-linear. The A-linear derived Q
   (lem-weil-linear-abelian-derived-category) preserves these equations.
   Full faithfulness of the degree-zero embedding
   (lem-weil-pbc-derived-single-fully-faithful) identifies every degree-zero derived
   map with a module map. Tensoring its Hom maps with A[1/t] therefore extends both
   actions linearly and the naturality square holds on every localized morphism.
4. Apply these contravariant actions to i,p. Naturality and p i = 1 show that
   B(i) c_E^{-1} T(p) is a two-sided inverse of c_F. Similarly B(p),B(i) exhibit
   B(F) as a retract of B(E); the standard-basis duality B(E) ≅ E transports this
   to the asserted retract of the very same free object. No complementary object
   or idempotent completeness is assumed. -/
theorem rational_term_hom_comparison (A : Type v) [CommRing A]
    (a : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)) (t : A)
    (I : CochainComplex
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    [I.IsKInjective] (j : single R (coefficients R) ⟶ I) [QuasiIso j] :
    (fun [_linear : Linear A
        (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))] ↦
      ∃ e : ∀ F : ringedSiteModules.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R),
          ordinary R F ≅ resolved R (single R (coefficients R)) F,
        IsNormalized R e ∧
        (∀ (F G : ringedSiteModules.{u}
            ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (f : F ⟶ G),
          ordinaryMap R f ≫ comparison R e j F =
            comparison R e j G ≫ resolvedMap R I f) ∧
        (∀ (F : ringedSiteModules.{u}
            ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (m : ℕ)
          (i : localizedObject R A t (single R F) ⟶
            localizedObject R A t (single R (SheafOfModules.free
              (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (ULift.{u} (Fin m)))))
          (p : localizedObject R A t (single R (SheafOfModules.free
              (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (ULift.{u} (Fin m)))) ⟶
            localizedObject R A t (single R F)),
          i ≫ p = 𝟙 _ →
            IsIso (localizedMap R A t (comparison R e j F)) ∧
            ∃ i' : localizedObject R A t (ordinary R F) ⟶
                localizedObject R A t (single R (SheafOfModules.free
                  (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
                  (ULift.{u} (Fin m)))),
              ∃ p' : localizedObject R A t (single R (SheafOfModules.free
                  (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
                  (ULift.{u} (Fin m)))) ⟶ localizedObject R A t (ordinary R F),
                i' ≫ p' = 𝟙 _) ∧
        ∃ b : ∀ F G : ringedSiteModules.{u}
            ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R),
            (localizedObject R A t (single R F) ⟶ localizedObject R A t (single R G)) →ₗ[
              Localization.Away t]
              (localizedObject R A t (ordinary R G) ⟶ localizedObject R A t (ordinary R F)),
          ∃ z : ∀ F G : ringedSiteModules.{u}
              ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R),
              (localizedObject R A t (single R F) ⟶ localizedObject R A t (single R G)) →ₗ[
                Localization.Away t]
                (localizedObject R A t (resolved R I G) ⟶
                  localizedObject R A t (resolved R I F)),
            (∀ (F G : ringedSiteModules.{u}
                ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (f : F ⟶ G),
              b F G (localizedMap R A t ((CochainComplex.singleFunctor _ 0).map f)) =
                localizedMap R A t (ordinaryMap R f) ∧
              z F G (localizedMap R A t ((CochainComplex.singleFunctor _ 0).map f)) =
                localizedMap R A t (resolvedMap R I f)) ∧
            (∀ (F G : ringedSiteModules.{u}
                ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
              (f : localizedObject R A t (single R F) ⟶ localizedObject R A t (single R G)),
              b F G f ≫ localizedMap R A t (comparison R e j F) =
                localizedMap R A t (comparison R e j G) ≫ z F G f))
      (_linear := scalarLocalizationCoefficientLinear A R a) := by
  sorry

end CategoryTheory.RationalTermHom

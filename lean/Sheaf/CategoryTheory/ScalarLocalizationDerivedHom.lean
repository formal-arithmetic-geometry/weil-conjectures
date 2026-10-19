/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Sheaf.CategoryTheory.RingedSectionLocalizationRing
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.BoundedBelowCountableHomContinuity
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Module.LocalizedModule.Basic
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.CategoryTheory.SequenceRelativeHomTelescope
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Mathlib.RingTheory.Flat.Localization
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel

/-!
# Scalar localization of shifted derived Hom

Source: Bhatt–Scholze, The pro-étale topology for schemes, Lemma 6.8.12 and
Proposition 6.8.14(2), with the abstract bounded-below telescope argument
(blueprint: lem-weil-pbc-scalar-localization-derived-hom).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w x y

open CategoryTheory CategoryTheory.Limits Opposite DirectSum

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

/-- Image of a compatible coefficient family is again compatible.
Source: Bhatt–Scholze, Proposition 6.8.14(2)
(blueprint: lem-weil-pbc-scalar-localization-derived-hom).
Proof: commute each restriction with the ring-sheaf morphism, and then use the
restriction compatibility of the original family. -/
theorem scalarLocalizationSectionsMap_mem {R S : Sheaf J CommRingCat.{u}}
    (f : R ⟶ S) (a : RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)) :
    (fun U ↦ f.hom.app U (a.val U)) ∈
      RingCat.sectionsSubring (S.obj ⋙ forget₂ CommRingCat RingCat) := by
  intro U V g
  change S.obj.map g (f.hom.app U (a.val U)) = f.hom.app V (a.val V)
  have h := ConcreteCategory.congr_hom (f.hom.naturality g) (a.val U)
  change f.hom.app V (R.obj.map g (a.val U)) =
    S.obj.map g (f.hom.app U (a.val U)) at h
  rw [← h]
  exact congrArg (f.hom.app V) (a.property g)

/-- The map of global coefficient rings induced by a ring-sheaf morphism.
Source: Bhatt–Scholze, Proposition 6.8.14(2)
(blueprint: lem-weil-pbc-scalar-localization-derived-hom). -/
def scalarLocalizationSectionsMap {R S : Sheaf J CommRingCat.{u}} (f : R ⟶ S) :
    RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat) →+*
      RingCat.sectionsSubring (S.obj ⋙ forget₂ CommRingCat RingCat) :=
  (RingHom.pi (fun U ↦ (f.hom.app U).hom.comp
    ((Pi.evalRingHom (fun V ↦ R.obj.obj V) U).comp
      (RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)).subtype))).codRestrict
    (RingCat.sectionsSubring (S.obj ⋙ forget₂ CommRingCat RingCat))
    (scalarLocalizationSectionsMap_mem f)

/-- The usual coefficient action on module-sheaf Homs, by restriction from global sections.
Source: Bhatt–Scholze, Proposition 6.8.14(2)
(blueprint: lem-weil-pbc-scalar-localization-derived-hom). -/
@[instance_reducible]
def scalarLocalizationCoefficientLinear (A : Type v) [CommRing A]
    (R : Sheaf J CommRingCat.{u})
    (a : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)) :
    Linear A (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
  letI : Linear (RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat))
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
    SheafOfModules.homLinear R.obj
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).property
  { homModule := fun M N ↦ Module.compHom (M ⟶ N) a
    smul_comp := fun M N P r f g ↦ Linear.smul_comp M N P (a r) f g
    comp_smul := fun M N P f r g ↦ Linear.comp_smul M N P f (a r) g }

/-- The induced coefficient action on the ordinary derived category.
Source: Bhatt–Scholze, Proposition 6.8.14(2)
(blueprint: lem-weil-pbc-scalar-localization-derived-hom). -/
@[instance_reducible]
def scalarLocalizationDerivedLinear (A : Type v) [CommRing A]
    (R : Sheaf J CommRingCat.{u})
    (a : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat))
    [HasDerivedCategory.{w}
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))] :
    Linear A (DerivedCategory
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) :=
  letI := scalarLocalizationCoefficientLinear A R a
  DerivedCategory.instLinear A _

/-- The localized coefficient is a unit in the ring of sections of R[1/t].
Source: Bhatt–Scholze, Proposition 6.8.14(2)
(blueprint: lem-weil-pbc-scalar-localization-derived-hom).
Proof: the sectionwise image of t is a unit by localization. Its inverses commute
with restriction by uniqueness of inverses. Apply sheafification to this section
and its inverse; their products remain one, also for the zero ring and empty site. -/
theorem scalarLocalizationSections_isUnit (A : Type v) [CommRing A]
    (R : Sheaf J CommRingCat.{u})
    (a : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)) (t : A) :
    IsUnit ((scalarLocalizationSectionsMap
      (ringedLocalizationRingUnit R (a t))).comp a t) := by
  classical
  let b := (scalarLocalizationSectionsMap (ringedLocalizationRingUnit R (a t))).comp a t
  have hu (U : Cᵒᵖ) : IsUnit (b.val U) := by
    change IsUnit ((toSheafify J (ringedLocalizationRingPresheaf R (a t))).app U
      (algebraMap (R.obj.obj U) (ringedSectionLocalizationCarrier R (a t) U)
        ((a t).val U)))
    exact (IsLocalization.Away.algebraMap_isUnit (R := R.obj.obj U)
      (S := ringedSectionLocalizationCarrier R (a t) U) ((a t).val U)).map
        ((toSheafify J (ringedLocalizationRingPresheaf R (a t))).app U).hom
  choose c hc using fun U ↦ (hu U).exists_right_inv
  let d : RingCat.sectionsSubring
      ((ringedLocalizationRing R (a t)).obj ⋙ forget₂ CommRingCat RingCat) :=
    ⟨c, by
      intro U V g
      let ρ := (((ringedLocalizationRing R (a t)).obj ⋙
        forget₂ CommRingCat RingCat).map g).hom
      change ρ (c U) = c V
      apply (hu V).mul_left_cancel
      have hb : ρ (b.val U) = b.val V := b.property g
      calc
        b.val V * ρ (c U) = ρ (b.val U * c U) := by rw [← hb, map_mul]
        _ = 1 := by rw [hc, map_one]
        _ = b.val V * c V := (hc V).symm⟩
  exact IsUnit.of_mul_eq_one d (by ext U; exact hc U)

/-- The canonical A[1/t]-algebra structure of the localized ring sheaf.
Source: Bhatt–Scholze, Proposition 6.8.14(2)
(blueprint: lem-weil-pbc-scalar-localization-derived-hom). -/
def scalarLocalizationCoefficientMap (A : Type v) [CommRing A]
    (R : Sheaf J CommRingCat.{u})
    (a : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)) (t : A) :
    Localization.Away t →+* RingCat.sectionsSubring
      ((ringedLocalizationRing R (a t)).obj ⋙ forget₂ CommRingCat RingCat) :=
  IsLocalization.Away.lift t
    (g := (scalarLocalizationSectionsMap (ringedLocalizationRingUnit R (a t))).comp a)
    (scalarLocalizationSections_isUnit A R a t)

/-- Linear equivalences from the existing fraction quotient, using its canonical
localized scalar action. This only installs Mathlib's module structure in the type.
Source: Stacks Project, algebra.tex, Tags 07JZ and 07K0
(blueprint: lem-weil-pbc-scalar-localization-derived-hom). -/
abbrev scalarLocalizationHomEquiv (A : Type v) [CommRing A] (t : A)
    (M : Type w) [AddCommGroup M] [Module A M]
    (N : Type w) [AddCommGroup N] [Module (Localization.Away t) N] :=
  (fun [_localizedModule : Module (Localization.Away t) (LocalizedModule.Away t M)] ↦
    LocalizedModule.Away t M ≃ₗ[Localization.Away t] N)
    (_localizedModule := LocalizedModule.moduleOfIsLocalization
      (S := Submonoid.powers t) (T := Localization.Away t) (M := M))

/-- Scalar localization of module sheaves is additive and exact.
Source: Bhatt–Scholze, Proposition 6.8.14(2), and Stacks Tags 00HT and 015F
(blueprint: lem-weil-pbc-scalar-localization-derived-hom).
Proof: the sheaf tensor is the sheafification of sectionwise localization, by
lem-pc-sites-module-sheafification-tensor. Kernels of sheaf modules are sectionwise;
localization is flat (lem-weil-pbc-localization-flat), and module sheafification
preserves monomorphisms (lem-weil-pbc-ringed-site-module-sheafification-exact).
Tensor is an additive left adjoint (lem-pc-sheaf-modules-tensor-closed), hence
preserves cokernels and finite colimits. Restriction of scalars is exact and
faithful and detects exactness. Thus the functor valued in R[1/t]-modules is exact.
The object and map equations pin E to this actual sheafified tensor functor. -/
theorem scalarLocalization_exact (R : Sheaf J CommRingCat.{u})
    (s : (R.obj ⋙ forget CommRingCat).sections)
    (E : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        (ringedLocalizationRing R s)))
    (hE : ∀ M, E.obj M = SheafOfModules.changeOfRings (ringedLocalizationRingUnit R s) M)
    (hmap : ∀ {M N} (f : M ⟶ N), E.map f = eqToHom (hE M) ≫
      SheafOfModules.changeOfRingsHom (ringedLocalizationRingUnit R s) M f ≫
        eqToHom (hE N).symm) :
    E.Additive ∧ PreservesFiniteLimits E ∧ PreservesFiniteColimits E := by
  sorry

/-- The full localized-Hom comparison: linear equivalences on all fractions,
contravariant/covariant naturality, identity, composition and simultaneous shift.
The predicates P and B specify respectively the allowed sources and targets;
the theorem below substitutes the actual continuity and lower-bound predicates.
Source: Bhatt–Scholze, Lemma 6.8.12 and Proposition 6.8.14(2)
(blueprint: lem-weil-pbc-scalar-localization-derived-hom). -/
def scalarLocalizationHomComparison (A : Type v) [CommRing A] (t : A)
    {D : Type x} [Category.{w} D] [Preadditive D] [HasShift D ℤ] [Linear A D]
    {T : Type y} [Category.{w} T] [Preadditive T] [HasShift T ℤ]
    [Linear (Localization.Away t) T] (F : D ⥤ T) [F.CommShift ℤ]
    (P B : D → Prop) : Prop :=
  ∃ e : ∀ (K : D),
    P K →
    ∀ (L : D),
    B L → ∀ q : ℤ,
      scalarLocalizationHomEquiv A t (K ⟶ L⟦q⟧)
        (F.obj K ⟶ (F.obj L)⟦q⟧),
    (∀ K hK L hL q (f : K ⟶ L⟦q⟧) (n : ℕ),
      (e K hK L hL q).toFun (LocalizedModule.mk f ⟨t ^ n, ⟨n, rfl⟩⟩) =
        (IsLocalization.Away.invSelf t : Localization.Away t) ^ n •
          (F.map f ≫ (F.commShiftIso q).hom.app L)) ∧
    (∀ K K' hK hK' L L' hL hL' q (f : K' ⟶ K) (g : L ⟶ L')
      (u : K ⟶ L⟦q⟧) (n : ℕ),
      (e K' hK' L' hL' q).toFun (LocalizedModule.mk (f ≫ u ≫ g⟦q⟧') ⟨t ^ n, ⟨n, rfl⟩⟩) =
        F.map f ≫
          (e K hK L hL q).toFun (LocalizedModule.mk u ⟨t ^ n, ⟨n, rfl⟩⟩) ≫
            (F.map g)⟦q⟧') ∧
    (∀ K hK hL,
      (e K hK K hL 0).toFun
        (LocalizedModule.mk ((shiftFunctorZero _ ℤ).inv.app K) 1) =
          (shiftFunctorZero _ ℤ).inv.app (F.obj K)) ∧
    (∀ K L M hK hL hLc hM p q (f : K ⟶ L⟦q⟧) (g : L ⟶ M⟦p⟧) (n m : ℕ),
      (e K hK M hM (p + q)).toFun
        (LocalizedModule.mk
          (f ≫ g⟦q⟧' ≫ (shiftFunctorAdd _ p q).inv.app M)
          ⟨t ^ (n + m), ⟨n + m, rfl⟩⟩) =
        (e K hK L hL q).toFun (LocalizedModule.mk f ⟨t ^ n, ⟨n, rfl⟩⟩) ≫
          ((e L hLc M hM p).toFun (LocalizedModule.mk g ⟨t ^ m, ⟨m, rfl⟩⟩))⟦q⟧' ≫
            (shiftFunctorAdd _ p q).inv.app (F.obj M)) ∧
    (∀ K hK L hL p q hKq hLq (f : K ⟶ L⟦p⟧) (n : ℕ),
      (e (K⟦q⟧) hKq (L⟦q⟧) hLq p).toFun
        (LocalizedModule.mk
          (f⟦q⟧' ≫ (shiftFunctorComm _ p q).hom.app L) ⟨t ^ n, ⟨n, rfl⟩⟩) =
        (F.commShiftIso q).hom.app K ≫
          ((e K hK L hL p).toFun (LocalizedModule.mk f ⟨t ^ n, ⟨n, rfl⟩⟩))⟦q⟧' ≫
            (shiftFunctorComm _ p q).hom.app (F.obj L) ≫
              ((F.commShiftIso q).inv.app L)⟦p⟧')

/-- Shifted derived Hom from a countably bounded-below Hom-continuous source
localizes under the actual exact scalar-extension functor. The family of linear
equivalences is normalized on every fraction; the following equations express
naturality on all fractions, the identity, and composition. Commutation with
shifts uses the canonical `mapDerivedCategory` shift structure in every formula.

Source: Bhatt–Scholze, Lemma 6.8.12 and Proposition 6.8.14(2)
(blueprint: lem-weil-pbc-scalar-localization-derived-hom).

Proof:
1. scalarLocalization_exact proves exactness of sheafified section localization.
Use lem-weil-pbc-exact-functor-derived-functor for the termwise derived functor.
Uniqueness of the left derived functor identifies it with the K-flat change of
rings of lem-pur-derived-change-of-rings, compatibly with the identity on K-flat
representatives. Transport lem-pur-sheaf-ring-derived-coefficient-adjunction;
its unit is the termwise map x ↦ 1 tensor x, and it respects the canonical shifts.
2. lem-weil-pbc-scalar-localization-underlying-telescope identifies restriction
of the localized bounded-below L with the telescope of multiplication by t on L.
Its nth leg is the scalar-extension unit followed by t to the power minus n.
This identification remains valid after any integer shift.
3. Apply lem-weil-pbc-sequence-relative-hom-telescope to the constant family
L[q] with transition t. The source condition supplies the two coproduct
comparisons, for L[q] and L[q+1], since both families have common lower bounds.
It gives the colimit of Hom(K,L[q]) under multiplication by t.
4. Compose with the derived adjunction. The nth leg sends u to t^(-n) F(u):
this follows from naturality of the unit and the triangle identities.
5. The fraction relation of def-weil-pbc-module-localization-away identifies this
colimit with LocalizedModule.Away t Hom(K,L[q]). The target action comes from
the canonical A[1/t]-algebra structure of R[1/t]. The resulting equivalences
are linear over A[1/t]. Naturality, shift compatibility, identities and
composition follow from the normalized fraction formula, naturality of the
adjunction and telescope legs, and bilinearity of composition. Every element
is a fraction, so the equations below cover all elements, including t=0. -/
theorem scalarLocalization_derivedHom (A : Type v) [CommRing A]
    (R : Sheaf J CommRingCat.{u})
    (a : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)) (t : A)
    [HasDerivedCategory.{w}
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [HasDerivedCategory.{w}
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        (ringedLocalizationRing R (a t))))]
    (E : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        (ringedLocalizationRing R (a t))))
    (hE : ∀ M, E.obj M =
      SheafOfModules.changeOfRings (ringedLocalizationRingUnit R (a t)) M)
    (hmap : ∀ {M N} (f : M ⟶ N), E.map f = eqToHom (hE M) ≫
      SheafOfModules.changeOfRingsHom (ringedLocalizationRingUnit R (a t)) M f ≫
        eqToHom (hE N).symm)
    [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E] :
    (fun [_iA : Linear A (DerivedCategory
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))]
      [_iT : Linear (Localization.Away t) (DerivedCategory
        (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
          (ringedLocalizationRing R (a t)))))] ↦
      scalarLocalizationHomComparison A t E.mapDerivedCategory
        DerivedCategory.CountableBoundedBelowHomContinuous
        (fun L ↦ ∃ b : ℤ, L.IsGE b))
      (_iA := scalarLocalizationDerivedLinear A R a)
      (_iT := scalarLocalizationDerivedLinear (Localization.Away t)
        (ringedLocalizationRing R (a t)) (scalarLocalizationCoefficientMap A R a t)) := by
  sorry

end CategoryTheory

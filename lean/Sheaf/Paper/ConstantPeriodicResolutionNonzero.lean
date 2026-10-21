/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O1
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Subobject.Limits
public import Sheaf.Algebra.Homology.KFlatCoefficientUniverse
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Sheaf.CategoryTheory.SiteConstantModuleFunctorGeneral
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.CategoryTheory.FiniteTypeConstantExact
import Sheaf.CategoryTheory.SiteConstantModuleUnit

/-! # The constant periodic resolution and its nonzero quotient

Source: blueprint main-20261015, sec-proetale-coefficients,
sk-def-localizing-closure-ctf-equals-bc.proof.md, "The examples";
Stacks Project, Tags 093J, 03CY and 06YQ.
(blueprint: lem-sfb-constant-periodic-resolution-nonzero).

The resolution is specified by its term identifications and all its differentials.
The augmentation is fixed in every degree, including its quotient component in degree zero.
The sized constant-module helpers belong to this realization; the landed general
constant-module dependency and its record are preserved without changes.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe r u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  (J : GrothendieckTopology C) (Λ : Type w) [CommRing Λ]

/-- Ring sheafification transported from the small model in the coefficient universe.
Source: Stacks Tag 03CY (blueprint: lem-sfb-constant-periodic-resolution-nonzero). -/
instance siteConstantSizedRingSheafify : HasSheafify J RingCat.{w} :=
  hasSheafifyEssentiallySmallSite J RingCat.{w}

/-- Commutative ring sheafification on the same small model.
Source: Stacks Tag 03CY (blueprint: lem-sfb-constant-periodic-resolution-nonzero). -/
instance siteConstantSizedCommRingSheafify : HasSheafify J CommRingCat.{w} :=
  hasSheafifyEssentiallySmallSite J CommRingCat.{w}

/-- Limits needed to transport ring sheafification from the small model.
Source: Stacks Tag 03CY (blueprint: lem-sfb-constant-periodic-resolution-nonzero). -/
instance siteConstantSizedRingStructuredLimits :
    ∀ X : Cᵒᵖ, Limits.HasLimitsOfShape
      (StructuredArrow X (equivSmallModel.{w} C).inverse.op) RingCat.{w} :=
  fun _ ↦ hasLimitsOfShape_of_essentiallySmall.{w} _ _

/-- The analogous limits for commutative rings.
Source: Stacks Tag 03CY (blueprint: lem-sfb-constant-periodic-resolution-nonzero). -/
instance siteConstantSizedCommRingStructuredLimits :
    ∀ X : Cᵒᵖ, Limits.HasLimitsOfShape
      (StructuredArrow X (equivSmallModel.{w} C).inverse.op) CommRingCat.{w} :=
  fun _ ↦ hasLimitsOfShape_of_essentiallySmall.{w} _ _

/-- The local description of ring sheafification transported from the small model.
Source: Stacks Tag 03CY (blueprint: lem-sfb-constant-periodic-resolution-nonzero). -/
instance siteConstantSizedRingLocallyBijective : J.WEqualsLocallyBijective RingCat.{w} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall J

/-- The constant module presheaf, with the original scalar action and identity restrictions.
Source: Stacks Tags 03CY and 093T (blueprint: lem-sfb-constant-periodic-resolution-nonzero). -/
def siteConstantModulePresheafSized : ModuleCat.{w} Λ ⥤
    PresheafOfModules.{w} ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)) where
  obj M := { obj := fun _ ↦ M, map := fun _ ↦ ModuleCat.ofHom LinearMap.id }
  map f := { app := fun _ ↦ f }

/-- Module sheafification of the constant module presheaf over the constant ring sheaf.
Source: Stacks Tags 03CY and 093T (blueprint: lem-sfb-constant-periodic-resolution-nonzero). -/
def siteConstantModuleFunctorSized : ModuleCat.{w} Λ ⥤ SheafOfModules.{w}
    ((constantSheaf J RingCat.{w}).obj (RingCat.of Λ)) :=
  siteConstantModulePresheafSized (C := C) Λ ⋙ PresheafOfModules.sheafification
    (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)))

set_option backward.isDefEq.respectTransparency false in
/-- The canonical coefficient isomorphism, commuting sheafification with forgetting
commutativity. Source: Stacks Tag 03CY (blueprint: lem-sfb-constant-periodic-resolution-nonzero). -/
def siteConstantSizedRingIso :
    (constantSheaf J RingCat.{w}).obj (RingCat.of Λ) ≅
      (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj
        ((constantSheaf J CommRingCat.{w}).obj (CommRingCat.of Λ)) :=
  letI : ((equivSmallModel.{w} C).inverse.inducedTopology J).PreservesSheafification
      (forget₂ CommRingCat.{w} RingCat.{w}) :=
    GrothendieckTopology.instPreservesSheafification
      ((equivSmallModel.{w} C).inverse.inducedTopology J)
      (forget₂ CommRingCat.{w} RingCat.{w})
      (FD := fun A B : CommRingCat.{w} ↦ A →+* B)
      (CD := fun A : CommRingCat.{w} ↦ A)
      (FE := fun A B : RingCat.{w} ↦ A →+* B)
      (CE := fun A : RingCat.{w} ↦ A)
  letI : J.PreservesSheafification (forget₂ CommRingCat.{w} RingCat.{w}) :=
    GrothendieckTopology.PreservesSheafification.transport (A := CommRingCat.{w}) J
      ((equivSmallModel.{w} C).inverse.inducedTopology J)
      (equivSmallModel.{w} C).inverse RingCat.{w}
      (forget₂ CommRingCat.{w} RingCat.{w})
  (sheafComposeNatIso J (forget₂ CommRingCat.{w} RingCat.{w})
    (sheafificationAdjunction J CommRingCat.{w})
    (sheafificationAdjunction J RingCat.{w})).app
      ((Functor.const Cᵒᵖ).obj (CommRingCat.of Λ))

/-- The same constant module sheaf over the underlying constant commutative ring sheaf.
Source: Stacks Tags 03CY and 093T (blueprint: lem-sfb-constant-periodic-resolution-nonzero). -/
def siteConstantCommModuleFunctorSized : ModuleCat.{w} Λ ⥤ SheafOfModules.{w}
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj
      ((constantSheaf J CommRingCat.{w}).obj (CommRingCat.of Λ))) :=
  siteConstantModuleFunctorSized J Λ ⋙
    SheafOfModules.pushforward (F := 𝟭 C) (siteConstantSizedRingIso J Λ).inv

/-- The additive sheafification unit after the canonical coefficient isomorphism.
Source: Stacks Tag 03CY (blueprint: lem-sfb-constant-periodic-resolution-nonzero). -/
def siteConstantCommModuleUnitSized (M : ModuleCat.{w} Λ) :
    (Functor.const Cᵒᵖ).obj ((forget₂ (ModuleCat Λ) AddCommGrpCat).obj M) ⟶
      ((siteConstantCommModuleFunctorSized J Λ).obj M).val.presheaf :=
  toSheafify J ((siteConstantModulePresheafSized (C := C) Λ).obj M).presheaf

end CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The fixed small pro-etale site is essentially small in the coefficient universe.
Source: the size convention in the blueprint's pro-etale site
(blueprint: lem-sfb-constant-periodic-resolution-nonzero). -/
instance constantPeriodicSiteSmall (V : Scheme.{u}) :
    EssentiallySmall.{max r (u + 1)} V.ProEt := essentiallySmallSelf _

/-- Constant module sheafification after the canonical coefficient-universe lift.
The last functor generalizes the recorded constant module construction to the coefficient size,
then transports along the canonical isomorphism of ring sheafifications.
Source: Stacks Tags 03CY and 093J, and blueprint "The examples"
(blueprint: lem-sfb-constant-periodic-resolution-nonzero). -/
def constantPeriodicModuleFunctor (R : Type r) [CommRing R] (V : Scheme.{u}) :=
  ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} R ≃+* R).toRingHom ⋙
    ModuleCat.uliftFunctor.{u + 1, r} (ULift.{u + 1} R) ⋙
      siteConstantCommModuleFunctorSized (ProEt.topology V) (ULift.{u + 1} R)

/-- The constant multiplication-by-`t` endomorphism on the rank-one constant module.
Source: blueprint "The examples", periodic differential; Stacks Tag 093J
(blueprint: lem-sfb-constant-periodic-resolution-nonzero). -/
def constantPeriodicScalar (R : Type r) [CommRing R] (t : R) (V : Scheme.{u}) :=
  (constantPeriodicModuleFunctor R V).map (ModuleCat.ofHom (LinearMap.mulLeft R t))

/-- The constant quotient map to `R/(t)`, with its prescribed quotient scalar action.
Source: blueprint "The examples", augmentation; Stacks Tag 03CY
(blueprint: lem-sfb-constant-periodic-resolution-nonzero). -/
def constantPeriodicQuotientMap (R : Type r) [CommRing R] (t : R) (V : Scheme.{u}) :=
  (constantPeriodicModuleFunctor R V).map
    (ModuleCat.ofHom (Ideal.span ({t} : Set R)).mkQ)

/-- The actual constant-section map at the terminal pro-etale object `V`.
Source: Stacks Tag 03CY, sheafification unit, and blueprint "The examples"
(blueprint: lem-sfb-constant-periodic-resolution-nonzero). -/
def constantPeriodicSection (R : Type r) [CommRing R] (V : Scheme.{u})
    (M : ModuleCat.{r} R) (x : M) :=
  (siteConstantCommModuleUnitSized (ProEt.topology V) (ULift.{u + 1} R)
    ((ModuleCat.uliftFunctor.{u + 1, r} (ULift.{u + 1} R)).obj
      ((ModuleCat.restrictScalars
        (ULift.ringEquiv : ULift.{u + 1} R ≃+* R).toRingHom).obj M))).app
          (op (ProEt.mk (𝟙 V))) (ULift.up x)

/-- The constant periodic complex is a termwise flat K-flat resolution, with the
canonical quotient as its cokernel and injective constants on any nonempty base.
Source: blueprint main-20261015, sec-proetale-coefficients,
sk-def-localizing-closure-ctf-equals-bc.proof.md, "The examples";
Stacks Tags 093J, 03CY and 06YQ
(blueprint: lem-sfb-constant-periodic-resolution-nonzero).

Proof:
1. Algebraically multiplication by t has image (t) and, by the annihilator hypothesis,
   kernel (t). The quotient map is surjective with kernel (t). Its cokernel is R/(t),
   t squared is zero, and t acts as zero on R/(t); this includes the zero ring.
2. Apply the exact constant module functor of def-sf-site-constant-module-functor,
   using lem-weil-pbc-finite-type-constant-exact. It preserves kernels, cokernels and
   therefore images. Its prescribed scalar action gives precisely the constant
   multiplication and quotient maps used here.
3. Apply lem-sfb-exact-scalar-periodic-resolution to the constant ring sheaf and t.
   Its cokernel is canonically the constant quotient by step 2. This gives the
   augmented exact sequence, all term identifications and differentials, termwise
   flatness, and the K-flat augmentation. The cutoff is above degree zero.
4. If V is nonempty, local injectivity of the constant-module unit
   (lem-sf-constant-module-unit-locally-bijective) makes equal constant sections equal
   on a covering sieve. A pro-etale cover of a nonempty scheme has a nonempty member,
   where the constant-presheaf restriction is the identity, so the constants agree.
5. A nonzero element of R/(t) consequently has a nonzero constant section. A zero
   sheaf has only zero sections. No nonvanishing assertion is made for empty V. -/
theorem constant_periodic_resolution_nonzero (R : Type r) [CommRing R]
    (t : R) (ht : t ^ 2 = 0)
    (hann : ∀ a : R, t * a = 0 ↔ a ∈ Ideal.span ({t} : Set R)) (V : Scheme.{u}) :
    kernelSubobject (constantPeriodicScalar R t V) =
      imageSubobject (constantPeriodicScalar R t V) ∧
    (∃ e : cokernel (constantPeriodicScalar R t V) ≅
        (constantPeriodicModuleFunctor R V).obj
          (ModuleCat.of R (R ⧸ Ideal.span ({t} : Set R))),
      cokernel.π (constantPeriodicScalar R t V) ≫ e.hom =
        constantPeriodicQuotientMap R t V) ∧
    (∃ P : CochainComplex (SheafOfModules.{max r (u + 1)}
        ((sheafCompose (ProEt.topology V)
          (forget₂ CommRingCat.{max r (u + 1)} RingCat.{max r (u + 1)})).obj
            ((constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).obj
              (CommRingCat.of (ULift.{u + 1} R))))) ℤ,
      ∃ e : ∀ (i : ℤ), i ≤ 0 →
          (P.X i ≅ (constantPeriodicModuleFunctor R V).obj (ModuleCat.of R R)),
        (∀ (i : ℤ), 0 < i → IsZero (P.X i)) ∧
        (∀ (i : ℤ) (hi : i < 0) (hi' : i + 1 ≤ 0),
          P.d i (i + 1) ≫ (e (i + 1) hi').hom =
            (e i (le_of_lt hi)).hom ≫ constantPeriodicScalar R t V) ∧
        (∀ i : ℤ,
          SheafOfModules.IsFlatOnSite.{u + 1, u, max r (u + 1), max r (u + 1)}
            (J := ProEt.topology V)
            (R := (constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).obj
              (CommRingCat.of (ULift.{u + 1} R))) (P.X i)) ∧
        (∃ ε : P ⟶ (HomologicalComplex.single _ (.up ℤ) 0).obj
            ((constantPeriodicModuleFunctor R V).obj
              (ModuleCat.of R (R ⧸ Ideal.span ({t} : Set R)))),
          ε.f 0 ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).hom =
            (e 0 (le_refl 0)).hom ≫ constantPeriodicQuotientMap R t V ∧
          (∀ i : ℤ, i ≠ 0 → ε.f i = 0) ∧
          CochainComplex.IsKFlatResolutionIndependentCoefficients.{u + 1, u, max r (u + 1)}
            (R := (constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).obj
              (CommRingCat.of (ULift.{u + 1} R))) ε)) ∧
    (constantPeriodicModuleFunctor R V).map
      (t • 𝟙 (ModuleCat.of R (R ⧸ Ideal.span ({t} : Set R)))) = 0 ∧
    (Nonempty V → Function.Injective
      (constantPeriodicSection R V (ModuleCat.of R (R ⧸ Ideal.span ({t} : Set R))))) ∧
    (Nontrivial (R ⧸ Ideal.span ({t} : Set R)) → Nonempty V →
      ¬ IsZero ((constantPeriodicModuleFunctor R V).obj
        (ModuleCat.of R (R ⧸ Ideal.span ({t} : Set R))))) := by
  sorry

end AlgebraicGeometry.Scheme

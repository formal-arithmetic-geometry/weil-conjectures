/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PodCtfAdjunctions
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.PoincareDuality.Abstract
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingInputs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection

/-!
# Pointwise projection and exceptional-adjunction Hom bijection

The operations are restrictions of the ordinary derived module operations. The exceptional
adjunction is restricted from the localizing adjunction at the specified boundary compactification.
The projection arrow is the canonical proper/open composite, rather than an input isomorphism.

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-tensor-hom/
sk-thm-sf-tensor-hom.proof.md, first Hom chain, second equality, and final paragraph
(blueprint: lem-sf-exceptional-integral-scalar-mates-data-reduction-pointwise).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace WeilConjectures

open AlgebraicGeometry AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing

/-- Restriction membership proofs and the specified localizing exceptional adjunction.
These are precisely the preservation data of ctf-stability-direct-images and the localizing
adjunction of podGeneralCtfAdjunctions clause (3). No tensor, pullback, lower-shriek, or braiding
is a field of this structure: those operations are constructed from the recorded ambient ones.
Source: the first Hom chain, with ctf-stability-adjunctions (3)
(blueprint: lem-sf-exceptional-integral-scalar-mates-data-reduction-pointwise). -/
structure ExceptionalPointwiseRestrictions
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification.BoundaryCompactification f) where
  /-- Pullback preservation from direct-images clause (1). -/
  pullPreservation : ∀ K : ConstantModelConstructibleFiniteTor Λ Y,
    (constantModelBoundedConstructible Λ X ⊓
      fun M ↦ _root_.DerivedCategory.finiteTorAmplitude _ M) (L((f)^*⟦Λ⟧).obj K.obj)
  /-- Tensor preservation on the source. -/
  tensorPreservationX : ∀ K M : ConstantModelConstructibleFiniteTor Λ X,
    (constantModelBoundedConstructible Λ X ⊓
      fun B ↦ _root_.DerivedCategory.finiteTorAmplitude _ B)
      (((derivedTensor Λ X).obj K.obj).obj M.obj)
  /-- Tensor preservation on the target. -/
  tensorPreservationY : ∀ K M : ConstantModelConstructibleFiniteTor Λ Y,
    (constantModelBoundedConstructible Λ Y ⊓
      fun B ↦ _root_.DerivedCategory.finiteTorAmplitude _ B)
      (((derivedTensor Λ Y).obj K.obj).obj M.obj)
  /-- The specified compactification lower-shriek preserves ctf. -/
  supportPreservation : ∀ K : ConstantModelConstructibleFiniteTor Λ X,
    (constantModelBoundedConstructible Λ Y ⊓
      fun M ↦ _root_.DerivedCategory.finiteTorAmplitude _ M)
      ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K.obj)
  /-- The same lower-shriek preserves the localizing closures. -/
  localizingPreservation : ∀ K, localizingClosureProEtale Λ X K →
    localizingClosureProEtale Λ Y
      ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K)
  /-- The localizing exceptional inverse image, determined by its adjunction. -/
  localizingRight : (localizingClosureProEtale Λ Y).FullSubcategory ⥤
    (localizingClosureProEtale Λ X).FullSubcategory
  /-- The adjunction for the actual localizing lower-shriek. -/
  localizingAdjunction : localizingLowerShriek Λ c.obj.obj localizingPreservation ⊣
    localizingRight
  /-- Compatibility required in podGeneralCtfAdjunctions clause (3). -/
  compatible : podCompatibleRestriction localizingAdjunction
    (ObjectProperty.ιOfLE (fun K hK _P _hP hSP ↦ hSP K hK) :
      ConstantModelConstructibleFiniteTor Λ X ⥤
        (localizingClosureProEtale Λ X).FullSubcategory)
    (ObjectProperty.ιOfLE (fun K hK _P _hP hSP ↦ hSP K hK) :
      ConstantModelConstructibleFiniteTor Λ Y ⥤
        (localizingClosureProEtale Λ Y).FullSubcategory)
  /-- The exceptional right adjoint preserves ctf, as in direct-images clause (4). -/
  rightPreservation : ∀ L : ConstantModelConstructibleFiniteTor Λ Y,
    (constantModelBoundedConstructible Λ X ⊓
      fun M ↦ _root_.DerivedCategory.finiteTorAmplitude _ M)
      (localizingRight.obj ⟨L.obj, fun _P _hP hSP ↦ hSP L.obj L.property⟩).obj

namespace ExceptionalPointwiseRestrictions

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification.BoundaryCompactification f}
  (d : ExceptionalPointwiseRestrictions Λ c)

/-- The actual restricted derived upper star. Source: ctf-stability-direct-images (1)
(blueprint: lem-sf-exceptional-integral-scalar-mates-data-reduction-pointwise). -/
def pullback : ConstantModelConstructibleFiniteTor Λ Y ⥤
    ConstantModelConstructibleFiniteTor Λ X :=
  (constantModelBoundedConstructible Λ X ⊓
    fun M ↦ _root_.DerivedCategory.finiteTorAmplitude _ M).lift
    ((constantModelBoundedConstructible Λ Y ⊓
      fun M ↦ _root_.DerivedCategory.finiteTorAmplitude _ M).ι ⋙ L((f)^*⟦Λ⟧))
    d.pullPreservation

/-- The restriction of `Rr_* D(j_!)` for the specified compactification.
Source: module-derived-lower-shriek and ctf-stability-direct-images (3)
(blueprint: lem-sf-exceptional-integral-scalar-mates-data-reduction-pointwise). -/
def lowerShriek : ConstantModelConstructibleFiniteTor Λ X ⥤
    ConstantModelConstructibleFiniteTor Λ Y :=
  (constantModelBoundedConstructible Λ Y ⊓
    fun M ↦ _root_.DerivedCategory.finiteTorAmplitude _ M).lift
    ((constantModelBoundedConstructible Λ X ⊓
      fun M ↦ _root_.DerivedCategory.finiteTorAmplitude _ M).ι ⋙
        rightDerivedLowerShriekOfCompactification Λ c.obj.obj)
    d.supportPreservation

/-- The restriction of the localizing exceptional right adjoint, using the canonical inclusion.
Source: ctf-stability-adjunctions (3)
(blueprint: lem-sf-exceptional-integral-scalar-mates-data-reduction-pointwise). -/
def upperShriek : ConstantModelConstructibleFiniteTor Λ Y ⥤
    ConstantModelConstructibleFiniteTor Λ X :=
  (constantModelBoundedConstructible Λ X ⊓
    fun M ↦ _root_.DerivedCategory.finiteTorAmplitude _ M).lift
    ((ObjectProperty.ιOfLE (fun K hK _P _hP hSP ↦ hSP K hK) :
      ConstantModelConstructibleFiniteTor Λ Y ⥤
        (localizingClosureProEtale Λ Y).FullSubcategory) ⋙
          d.localizingRight ⋙ (localizingClosureProEtale Λ X).ι)
    d.rightPreservation

/-- The specified localizing adjunction restricted along the canonical full inclusions.
Its unit, counit, and Hom bijection are therefore the restricted localizing ones.
Source: podGeneralCtfAdjunctions clause (3), via Adjunction.restrictFullyFaithful
(blueprint: lem-sf-exceptional-integral-scalar-mates-data-reduction-pointwise). -/
def adjunction : d.lowerShriek ⊣ d.upperShriek :=
  d.localizingAdjunction.restrictFullyFaithful
    (ObjectProperty.fullyFaithfulιOfLE (fun K hK _P _hP hSP ↦ hSP K hK))
    (ObjectProperty.fullyFaithfulιOfLE (fun K hK _P _hP hSP ↦ hSP K hK))
    (Iso.refl _) (Iso.refl _)

/-- The ordinary relative derived tensor restricted in its second argument on X.
Source: derived-tensor-hom and ctf-stability-direct-images (1)
(blueprint: lem-sf-exceptional-integral-scalar-mates-data-reduction-pointwise). -/
def tensorX (K : ConstantModelConstructibleFiniteTor Λ X) :
    ConstantModelConstructibleFiniteTor Λ X ⥤ ConstantModelConstructibleFiniteTor Λ X :=
  (constantModelBoundedConstructible Λ X ⊓
    fun M ↦ _root_.DerivedCategory.finiteTorAmplitude _ M).lift
    ((constantModelBoundedConstructible Λ X ⊓
      fun M ↦ _root_.DerivedCategory.finiteTorAmplitude _ M).ι ⋙ (derivedTensor Λ X).obj K.obj)
    (d.tensorPreservationX K)

/-- The ordinary relative derived tensor restricted in its second argument on Y.
Source: derived-tensor-hom and ctf-stability-direct-images (1)
(blueprint: lem-sf-exceptional-integral-scalar-mates-data-reduction-pointwise). -/
def tensorY (N : ConstantModelConstructibleFiniteTor Λ Y) :
    ConstantModelConstructibleFiniteTor Λ Y ⥤ ConstantModelConstructibleFiniteTor Λ Y :=
  (constantModelBoundedConstructible Λ Y ⊓
    fun M ↦ _root_.DerivedCategory.finiteTorAmplitude _ M).lift
    ((constantModelBoundedConstructible Λ Y ⊓
      fun M ↦ _root_.DerivedCategory.finiteTorAmplitude _ M).ι ⋙ (derivedTensor Λ Y).obj N.obj)
    (d.tensorPreservationY N)

/-- Tensor's first-variable action on X, restricted from derivedTensor.
Source: naturality in the first Hom chain
(blueprint: lem-sf-exceptional-integral-scalar-mates-data-reduction-pointwise). -/
def tensorXMapLeft {K K' : ConstantModelConstructibleFiniteTor Λ X} (a : K ⟶ K')
    (M : ConstantModelConstructibleFiniteTor Λ X) :
    (d.tensorX K).obj M ⟶ (d.tensorX K').obj M :=
  ObjectProperty.homMk (((derivedTensor Λ X).map a.hom).app M.obj)

/-- Tensor's first-variable action on Y, restricted from derivedTensor.
Source: naturality in the first Hom chain
(blueprint: lem-sf-exceptional-integral-scalar-mates-data-reduction-pointwise). -/
def tensorYMapLeft {N N' : ConstantModelConstructibleFiniteTor Λ Y} (a : N ⟶ N')
    (M : ConstantModelConstructibleFiniteTor Λ Y) :
    (d.tensorY N).obj M ⟶ (d.tensorY N').obj M :=
  ObjectProperty.homMk (((derivedTensor Λ Y).map a.hom).app M.obj)

/-- The source symmetry is the derived Koszul braiding, restricted by full inclusion.
Source: derived-tensor-hom and podGeneralCtfAdjunctions clause (2)
(blueprint: lem-sf-exceptional-integral-scalar-mates-data-reduction-pointwise). -/
def symmetryX (K M : ConstantModelConstructibleFiniteTor Λ X) :
    (d.tensorX K).obj M ≅ (d.tensorX M).obj K :=
  ObjectProperty.isoMk _
    (@BraidedCategory.braiding _ _ _ (_root_.DerivedCategory.braidedCategory' _) K.obj M.obj)

/-- The target symmetry is the derived Koszul braiding, restricted by full inclusion.
Source: derived-tensor-hom and podGeneralCtfAdjunctions clause (2)
(blueprint: lem-sf-exceptional-integral-scalar-mates-data-reduction-pointwise). -/
def symmetryY (N M : ConstantModelConstructibleFiniteTor Λ Y) :
    (d.tensorY N).obj M ≅ (d.tensorY M).obj N :=
  ObjectProperty.isoMk _
    (@BraidedCategory.braiding _ _ _ (_root_.DerivedCategory.braidedCategory' _) N.obj M.obj)

/-- The canonical proper/open projection arrow restricted to ctf objects.
The underlying map is exceptionalProjectionMorphismOfCompactification: properProjectionMorphism,
the inverse openImmersionProjectionComparison, and leftDerivedUpperStarCompactificationIso.
No invertibility assumption is used to define this arrow.
Source: the second step of the pointwise Hom calculation
(blueprint: lem-sf-exceptional-integral-scalar-mates-data-reduction-pointwise). -/
def projection (K : ConstantModelConstructibleFiniteTor Λ X)
    (N : ConstantModelConstructibleFiniteTor Λ Y) :
    (d.tensorY (d.lowerShriek.obj K)).obj N ⟶
      d.lowerShriek.obj ((d.tensorX K).obj (d.pullback.obj N)) :=
  ObjectProperty.homMk
    (exceptionalProjectionMorphismOfCompactification Λ c.obj.obj K.obj N.obj)

/-- The specified comparison π: source symmetry, inverse canonical projection, target symmetry.
The IsIso input concerns the actual projection arrow, not an arbitrary supplied isomorphism.
Source: step 2 and the displayed π formula
(blueprint: lem-sf-exceptional-integral-scalar-mates-data-reduction-pointwise). -/
def projectionPi
    (hPF : ∀ (K : ConstantModelConstructibleFiniteTor Λ X)
      (N : ConstantModelConstructibleFiniteTor Λ Y), IsIso (d.projection K N))
    (N : ConstantModelConstructibleFiniteTor Λ Y)
    (K : ConstantModelConstructibleFiniteTor Λ X) :
    d.lowerShriek.obj ((d.tensorX (d.pullback.obj N)).obj K) ≅
      (d.tensorY N).obj (d.lowerShriek.obj K) :=
  letI := hPF K N
  d.lowerShriek.mapIso (d.symmetryX (d.pullback.obj N) K) ≪≫
    (asIso (d.projection K N)).symm ≪≫ d.symmetryY (d.lowerShriek.obj K) N

end ExceptionalPointwiseRestrictions

/-- **Blueprint lem-sf-exceptional-integral-scalar-mates-data-reduction-pointwise.**
The fixed-coefficient pointwise Hom bijection on the actual constructible finite-Tor categories.

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-tensor-hom/
sk-thm-sf-tensor-hom.proof.md, first Hom chain, second equality, and final paragraph
(blueprint: lem-sf-exceptional-integral-scalar-mates-data-reduction-pointwise).

Proof steps:
1. Obtain pullback, tensor, lower-shriek and exceptional preservation from
ctf-stability-direct-images. Use podGeneralCtfAdjunctions clause (3) at c, and the
compactification-coherence transport implicit in that clause, to restrict the specified
localizing exceptional adjunction with its unit, counit and Hom bijection.
2. The named restricted projection is the proper projection, inverse open-immersion projection,
and pullback compositor. The coefficient-specific proper projection theorem makes it invertible;
the source and target Koszul braidings then give exactly π.
3. Precompose with π and apply the restricted adjunction Hom equivalence. Its unit and counit
formulas give the two displayed formulas, including the stated inverse.
4. The two triangle identities give the counit normalization and inverse laws. Applying the
inverse adjunction bijection proves uniqueness; the naturality of projection and adjunction
proves contravariance in N and K and covariance in L. No coefficient transport is used.
-/
theorem exceptionalIntegralScalarMates_data_reduction_pointwise
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime]
    [Fact (ringChar k ≠ ell)]
    (hcd : AlgebraicGeometry.ProEtale.BaseFieldFiniteCD ell k)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (c : Compactification.BoundaryCompactification f)
    (hΛ : IsLocalizingAdmissibleCoefficient ell Λ) :
    ∃ d : ExceptionalPointwiseRestrictions Λ c,
    (∀ (K : ConstantModelConstructibleFiniteTor Λ X)
      (N : ConstantModelConstructibleFiniteTor Λ Y), IsIso (d.projection K N)) ∧
    ∀ (hPF : ∀ (K : ConstantModelConstructibleFiniteTor Λ X)
      (N : ConstantModelConstructibleFiniteTor Λ Y), IsIso (d.projection K N)),
    ∃ (Φ : ∀ (N : ConstantModelConstructibleFiniteTor Λ Y)
      (K : ConstantModelConstructibleFiniteTor Λ X) (L : ConstantModelConstructibleFiniteTor Λ Y),
      ((d.tensorY N).obj (d.lowerShriek.obj K) ⟶ L) ≃
        ((d.tensorX (d.pullback.obj N)).obj K ⟶ d.upperShriek.obj L)),
      (∀ (N : ConstantModelConstructibleFiniteTor Λ Y)
        (K : ConstantModelConstructibleFiniteTor Λ X) (L : ConstantModelConstructibleFiniteTor Λ Y)
        (h : (d.tensorY N).obj (d.lowerShriek.obj K) ⟶ L),
        Φ N K L h = d.adjunction.unit.app ((d.tensorX (d.pullback.obj N)).obj K) ≫
          d.upperShriek.map ((d.projectionPi hPF N K).hom ≫ h)) ∧
      (∀ (N : ConstantModelConstructibleFiniteTor Λ Y)
        (K : ConstantModelConstructibleFiniteTor Λ X) (L : ConstantModelConstructibleFiniteTor Λ Y)
        (a : (d.tensorX (d.pullback.obj N)).obj K ⟶ d.upperShriek.obj L),
        (Φ N K L).symm a =
          (d.projectionPi hPF N K).inv ≫ d.lowerShriek.map a ≫ d.adjunction.counit.app L) ∧
      (∀ {N N' : ConstantModelConstructibleFiniteTor Λ Y}
        (u : N' ⟶ N) (K : ConstantModelConstructibleFiniteTor Λ X)
        (L : ConstantModelConstructibleFiniteTor Λ Y)
        (h : (d.tensorY N).obj (d.lowerShriek.obj K) ⟶ L),
        Φ N' K L (d.tensorYMapLeft u (d.lowerShriek.obj K) ≫ h) =
          d.tensorXMapLeft (d.pullback.map u) K ≫ Φ N K L h) ∧
      (∀ (N : ConstantModelConstructibleFiniteTor Λ Y)
        {K K' : ConstantModelConstructibleFiniteTor Λ X} (v : K' ⟶ K)
        (L : ConstantModelConstructibleFiniteTor Λ Y)
        (h : (d.tensorY N).obj (d.lowerShriek.obj K) ⟶ L),
        Φ N K' L ((d.tensorY N).map (d.lowerShriek.map v) ≫ h) =
          (d.tensorX (d.pullback.obj N)).map v ≫ Φ N K L h) ∧
      (∀ (N : ConstantModelConstructibleFiniteTor Λ Y)
        (K : ConstantModelConstructibleFiniteTor Λ X)
        {L L' : ConstantModelConstructibleFiniteTor Λ Y} (w : L ⟶ L')
        (h : (d.tensorY N).obj (d.lowerShriek.obj K) ⟶ L),
        Φ N K L' (h ≫ w) = Φ N K L h ≫ d.upperShriek.map w) ∧
      (∀ (N : ConstantModelConstructibleFiniteTor Λ Y)
        (K : ConstantModelConstructibleFiniteTor Λ X) (L : ConstantModelConstructibleFiniteTor Λ Y)
        (h : (d.tensorY N).obj (d.lowerShriek.obj K) ⟶ L),
        d.lowerShriek.map (Φ N K L h) ≫ d.adjunction.counit.app L =
          (d.projectionPi hPF N K).hom ≫ h) ∧
      (∀ (Ψ : ∀ (N : ConstantModelConstructibleFiniteTor Λ Y)
        (K : ConstantModelConstructibleFiniteTor Λ X) (L : ConstantModelConstructibleFiniteTor Λ Y),
        ((d.tensorY N).obj (d.lowerShriek.obj K) ⟶ L) ≃
          ((d.tensorX (d.pullback.obj N)).obj K ⟶ d.upperShriek.obj L)),
        (∀ (N : ConstantModelConstructibleFiniteTor Λ Y)
          (K : ConstantModelConstructibleFiniteTor Λ X)
          (L : ConstantModelConstructibleFiniteTor Λ Y)
          (h : (d.tensorY N).obj (d.lowerShriek.obj K) ⟶ L),
          d.lowerShriek.map (Ψ N K L h) ≫ d.adjunction.counit.app L =
            (d.projectionPi hPF N K).hom ≫ h) →
        ∀ (N : ConstantModelConstructibleFiniteTor Λ Y)
          (K : ConstantModelConstructibleFiniteTor Λ X)
          (L : ConstantModelConstructibleFiniteTor Λ Y)
          (h : (d.tensorY N).obj (d.lowerShriek.obj K) ⟶ L),
          Ψ N K L h = Φ N K L h) := by
  sorry

end WeilConjectures

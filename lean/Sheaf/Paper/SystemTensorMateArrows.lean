/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q68
-/
module

public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.SixFunctors.OpenTensorNormalization
public import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.FiniteFieldFiber

/-!
# Canonical tensor and proper/open arrows for varying coefficient systems

Source: Stacks Project, Tags 0941, 0F7B, 0E8I and 0B56; the simultaneous
system construction of Zheng, Construction 4.1 and Lemma 4.10
(blueprint: def-pur-system-tensor-mate-arrows).

The site is the published vertical sequence site. Level `n` means exponent `n+1`.
All derived categories are ordinary unbounded localizations of module systems.
The choices below are universal constructions: adjoints to specified sectionwise
functors, or unique section-normalized maps. In particular no transformation is
chosen merely because its source and target are isomorphic.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.SemilinearSections

namespace WeilConjectures.SystemTensorMate

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The original pro-etale site is small in the coefficient universe.
Source: the published size convention (blueprint: def-pur-system-tensor-mate-arrows). -/
instance proEtSmall (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

/-- The vertical sequence site retains the site's distinct object and morphism sizes.
Source: Stacks 0941 (blueprint: def-pur-system-tensor-mate-arrows). -/
instance sequenceSmall (X : Scheme.{u}) : EssentiallySmall.{u + 1} (ℕ × X.ProEt) :=
  essentiallySmallSelf.{0, u, u + 1} _

/-- The actual varying commutative coefficient ring on the vertical sequence site.
Source: Stacks 0941 (blueprint: def-pur-system-tensor-mate-arrows). -/
abbrev R (X : Scheme.{u}) := coefficientSequenceCommRingSheaf l E X

/-- Strict semilinear module systems, with the published quotient transitions.
Source: Zheng 4.1; Stacks 0941 (blueprint: def-pur-system-tensor-mate-arrows). -/
abbrev S (X : Scheme.{u}) :=
  @SemilinearSections.Mod.{u + 1, u, u + 1} _ _ (essentiallySmallSelf.{0, u, u + 1} _)
    (coefficientSequenceTopology (Scheme.ProEt.topology X)) (R l E X)

/-- The ordinary unbounded derived category of these systems.
Source: Stacks 05RU, 0941 (blueprint: def-pur-system-tensor-mate-arrows). -/
abbrev D (X : Scheme.{u}) :=
  @SemilinearSections.D.{u + 1, u, u + 1} _ _ (essentiallySmallSelf.{0, u, u + 1} _)
    (coefficientSequenceTopology (Scheme.ProEt.topology X)) (R l E X)

/-- The dependency's canonical abelian structure, at the original site universes.
Source: Stacks 03D1 (blueprint: def-pur-system-tensor-mate-arrows). -/
instance systemAbelian (X : Scheme.{u}) : Abelian (S l E X) :=
  @SemilinearSections.moduleAbelian.{u + 1, u, u + 1} _ _ (essentiallySmallSelf.{0, u, u + 1} _)
    (coefficientSequenceTopology (Scheme.ProEt.topology X)) (R l E X)

/-- The dependency's standard unbounded localization instance.
Source: Stacks 05RU (blueprint: def-pur-system-tensor-mate-arrows). -/
instance systemDerived (X : Scheme.{u}) : HasDerivedCategory.{u + 2} (S l E X) :=
  HasDerivedCategory.standard _

/-- A constant scalar section at positive exponent `n+1`.
Source: Stacks 0H7J (blueprint: def-pur-system-tensor-mate-arrows). -/
def scalar (X : Scheme.{u}) (n : ℕ) (U : X.ProEt) :
    ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)) →
      (R l E X).obj.obj (op (n, U)) :=
  letI : HasSheafify (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
    integralCoefficientRingSheafify.{u, u + 1} X
  (toSheafify (Scheme.ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj
      (CommRingCat.of.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).app (op U)

/-- Base change keeps the coefficient index.
Source: Stacks 0941, 09A5 (blueprint: def-pur-system-tensor-mate-arrows). -/
def base {X Y : Scheme.{u}} (f : X ⟶ Y) : ℕ × Y.ProEt ⥤ ℕ × X.ProEt :=
  (𝟭 ℕ).prod (Scheme.proEtaleBaseChange f)

/-- Base change is continuous for vertical coverings.
Source: Stacks 0941, 09A5 (blueprint: def-pur-system-tensor-mate-arrows).
Proof: restrict a system sheaf to a vertical slice. Pro-etale base change is
continuous there. The horizontal maps retain their index and commute with the
same vertical restrictions, giving the system sheaf condition. -/
theorem base_continuous {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (base f).IsContinuous (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (coefficientSequenceTopology (Scheme.ProEt.topology X)) := by
  sorry

attribute [instance] base_continuous

/-- The ring map on the diagram site is uniquely fixed by constant sections.
Source: Stacks 0H7J, 0941 (blueprint: def-pur-system-tensor-mate-arrows).
Proof: on slice n use proEtaleConstantDirectImageMap for the ring A_(n+1).
Naturality of that map in the coefficient ring proves compatibility with the
quotient transitions, so the maps assemble. Uniqueness follows slice by slice
from the constant-presheaf sheafification universal property. -/
theorem coefficient_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! c : R l E Y ⟶ ((base f).sheafPushforwardContinuous CommRingCat.{u + 1}
      (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (coefficientSequenceTopology (Scheme.ProEt.topology X))).obj (R l E X),
      ∀ (n : ℕ) (U : Y.ProEt)
        (a : ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))),
        c.hom.app (op (n, U)) (scalar l E Y n U a) =
          scalar l E X n ((Scheme.proEtaleBaseChange f).obj U) a := by
  sorry

/-- The unique constant-section-preserving structural ring map.
Source: Stacks 0H7J, 0941 (blueprint: def-pur-system-tensor-mate-arrows). -/
def coefficient {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (coefficient_existsUnique l E f).choose

/-- Actual sectionwise system direct image with its specified scalar action.
Source: Stacks 03D7, 0941 (blueprint: def-pur-system-tensor-mate-arrows). -/
def direct {X Y : Scheme.{u}} (f : X ⟶ Y) : S l E X ⥤ S l E Y :=
  SheafOfModules.pushforward.{u + 1} (F := base f)
    (S := (sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (R l E Y))
    (R := (sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology X))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (R l E X))
    ⟨Functor.whiskerRight (coefficient l E f).hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

/-- Sectionwise direct image is additive.
Source: Stacks 03D7 (blueprint: def-pur-system-tensor-mate-arrows).
Proof: restrictions and scalar restriction leave addition of maps unchanged,
so the equality holds on every section, including the horizontal restrictions. -/
theorem direct_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (direct l E f).Additive := by
  sorry

/-- The actual system category has K-injective resolutions.
Source: Stacks 079P; semilinearDerivedSections
(blueprint: def-pur-system-tensor-mate-arrows).
Proof: semilinearDerivedSections makes this module category on the small
vertical ringed site Grothendieck abelian. Apply K-injective existence for a
Grothendieck abelian category, in the recorded standard derived universe. -/
theorem system_kInjective (X : Scheme.{u}) :
    Abelian.HasKInjectiveResolutions (S l E X) := by
  sorry

attribute [instance] direct_additive system_kInjective

/-- Total right derived sectionwise direct image of actual systems.
Source: Stacks 07A4 (blueprint: def-pur-system-tensor-mate-arrows). -/
abbrev pushDerived {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (direct l E f).rightDerivedFunctor

/-- The lax tensor map of sectionwise direct image has its usual pure-tensor formula.
Source: Stacks 03EK, 0B56 (blueprint: def-pur-system-tensor-mate-arrows).
Proof: on every object the map sends x tensor y to x tensor y over the pulled
back ring. It is bilinear over the structural ring map, commutes with both
vertical and horizontal restrictions, and therefore sheafifies. Pure tensors
locally generate the sheaf tensor, proving uniqueness. -/
theorem laxTensor_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) (M N : S l E X) :
    ∃! t : ordinaryTensor.{u + 1, u, u + 1}
        (coefficientSequenceTopology (Scheme.ProEt.topology Y)) (R l E Y)
        ((direct l E f).obj M) ((direct l E f).obj N) ⟶
      (direct l E f).obj
        (ordinaryTensor.{u + 1, u, u + 1}
          (coefficientSequenceTopology (Scheme.ProEt.topology X)) (R l E X) M N),
      ∀ (V : (ℕ × Y.ProEt)ᵒᵖ)
        (x : ((direct l E f).obj M).val.obj V)
        (y : ((direct l E f).obj N).val.obj V),
        t.val.app V
          (tensorSection.{u + 1, u, u + 1}
            (coefficientSequenceTopology (Scheme.ProEt.topology Y)) (R l E Y)
            ((direct l E f).obj M) ((direct l E f).obj N) V x y) =
          tensorSection.{u + 1, u, u + 1}
            (coefficientSequenceTopology (Scheme.ProEt.topology X)) (R l E X)
            M N ((base f).op.obj V) x y := by
  sorry

/-- The normalized lax tensor map, used to fix inverse-image tensor comparison.
Source: Stacks 03EK, 0B56 (blueprint: def-pur-system-tensor-mate-arrows). -/
def laxTensor {X Y : Scheme.{u}} (f : X ⟶ Y) (M N : S l E X) :=
  (laxTensor_existsUnique l E f M N).choose

/-- Sectionwise direct-image composition is the fibre-product pasting map.
Source: Stacks 0D6D (blueprint: def-pur-system-tensor-mate-arrows).
Proof: restrict sections along pullbackComp, keeping the coefficient index.
The constant-section normalization makes this linear. Its inverse is restriction
along the inverse pasting map. Naturality and uniqueness are checked on sections. -/
theorem directComp_existsUnique {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∃! e : direct l E f ⋙ direct l E g ≅ direct l E (f ≫ g),
      ∀ (M : S l E X) (n : ℕ) (U : Z.ProEt)
        (x : ((direct l E f ⋙ direct l E g).obj M).val.obj (op (n, U))),
        (e.hom.app M).val.app (op (n, U)) x =
          M.val.map (CategoryTheory.Prod.mkHom (𝟙 n)
            ((MorphismProperty.Over.pullbackComp f g (f ≫ g) rfl).hom.app U)).op x := by
  sorry

/-- The unique section-normalized direct-image compositor.
Source: Stacks 0D6D (blueprint: def-pur-system-tensor-mate-arrows). -/
def directComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  (directComp_existsUnique l E f g).choose

/-- Universal geometric operations on the actual varying-ring system categories.
Tensor comparisons retain both their ordinary unit formula and their complete
K-flat total-summand normalization. Open extension is the exact left adjoint to
inverse image; its canonical identification with sectionwise extension is the
unique adjunction-compatible identification.
Source: Zheng 4.1, 4.10; Stacks 03DI, 07A4, 0E8I
(blueprint: def-pur-system-tensor-mate-arrows). -/
structure Operations where
  systems : ∀ X : Scheme.{u}, @Data.{u + 1, u, u + 1} _ _
    (Scheme.ProEt.topology X) (essentiallySmallSelf.{0, u, u + 1} _)
    (integralCoefficientCommRingSheaf.{u, u + 1} l E X)
    (coefficientSequenceCommRingTransition.{u, u + 1} l E X)
  pull : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → S l E Y ⥤ S l E X
  adj : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), pull f ⊣ direct l E f
  [pullAdditive : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), (pull f).Additive]
  [pullLimits : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), PreservesFiniteLimits (pull f)]
  [pullColimits : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), PreservesFiniteColimits (pull f)]
  extension : ∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j], S l E U ⥤ S l E X
  openAdj : ∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j], extension j ⊣ pull j
  [extensionAdditive : ∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j],
    (extension j).Additive]
  [extensionLimits : ∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j],
    PreservesFiniteLimits (extension j)]
  [extensionColimits : ∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j],
    PreservesFiniteColimits (extension j)]

attribute [instance] Operations.pullAdditive Operations.pullLimits Operations.pullColimits
  Operations.extensionAdditive
  Operations.extensionLimits Operations.extensionColimits

namespace Operations
variable {l E}
variable (o : Operations l E)

/-- Inverse-image composition is the conjugate of sectionwise direct-image pasting.
Source: Stacks 0D6D, 07A7 (blueprint: def-pur-system-tensor-mate-arrows). -/
def pullComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    o.pull g ⋙ o.pull f ≅ o.pull (f ≫ g) :=
  Adjunction.leftAdjointCompIso (o.adj g) (o.adj f) (o.adj (f ≫ g))
    (directComp l E f g)

/-- Exact system pullback on the ordinary derived category.
Source: Stacks 07A4 (blueprint: def-pur-system-tensor-mate-arrows). -/
abbrev P {X Y : Scheme.{u}} (f : X ⟶ Y) := (o.pull f).mapDerivedCategory

/-- The canonical derived adjunction of the actual ordinary adjunction.
Source: Stacks 07A4 (blueprint: def-pur-system-tensor-mate-arrows). -/
def derivedAdj {X Y : Scheme.{u}} (f : X ⟶ Y) : o.P f ⊣ pushDerived l E f :=
  (o.adj f).mapDerivedCategoryRightDerivedAdjunction

/-- Exact open extension on complexes and their ordinary localization.
Source: Stacks 03DI, 07A4 (blueprint: def-pur-system-tensor-mate-arrows). -/
abbrev J {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  (o.extension j).mapDerivedCategory

/-- The exact derived open adjunction, with the ordinary unit normalization.
Source: Stacks 03DI, 07A4 (blueprint: def-pur-system-tensor-mate-arrows). -/
def derivedOpenAdj {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] : o.J j ⊣ o.P j :=
  SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction (o.openAdj j)

/-- Tensor is the dependency's K-flat modeled closed tensor on systems.
Source: Stacks 06YS, 08J9 (blueprint: def-pur-system-tensor-mate-arrows). -/
abbrev T (X : Scheme.{u}) := (o.systems X).closed.tensor

/-- The derived pullback compositor is localized from the actual ordinary one.
Source: Stacks 07A4 (blueprint: def-pur-system-tensor-mate-arrows). -/
def pComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    o.P g ⋙ o.P f ≅ o.P (f ≫ g) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (o.pullComp f g)

/-- The pullback-square comparison, oriented from the top/right to bottom/left route.
Source: Stacks 07A7 (blueprint: def-pur-system-tensor-mate-arrows). -/
def square {A B C F : Scheme.{u}} (k : A ⟶ B) (r : A ⟶ C)
    (p : B ⟶ F) (i : C ⟶ F) (h : k ≫ p = r ≫ i) :
    o.P p ⋙ o.P k ≅ o.P i ⋙ o.P r :=
  o.pComp k p ≪≫ eqToIso (congrArg (fun f ↦ o.P f) h) ≪≫ (o.pComp r i).symm

end Operations

/-- Canonical system tensor comparisons, fixed on ordinary units and K-flat total
summands. This extends universal operations, rather than postulating arbitrary
isomorphisms between tensor expressions.
Source: Stacks 07A4, 0B56 (blueprint: def-pur-system-tensor-mate-arrows). -/
structure TensorOperations extends Operations l E where
  mu : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    toOperations.T Y ⋙ toOperations.P f ≅
      ((toOperations.P f).prod (toOperations.P f)) ⋙ toOperations.T X
  model : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    TensorComparisonModel.{u + 1, u, u + 1}
      (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (coefficientSequenceTopology (Scheme.ProEt.topology X)) (R l E Y) (R l E X)
      (pull f) (systems Y).closed (systems X).closed
      (systems Y).tensorModels (systems X).tensorModels (mu f)
  ordinary_unit : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (M N : S l E Y),
    (adj f).homEquiv _ _ ((model f).ordinary M N).hom =
      ordinaryTensorHom.{u + 1, u, u + 1}
        (coefficientSequenceTopology (Scheme.ProEt.topology Y)) (R l E Y)
        ((adj f).unit.app M) ((adj f).unit.app N) ≫
          laxTensor l E f ((pull f).obj M) ((pull f).obj N)

/-- Universal presentations of the canonical system operations exist.
Source: Zheng 4.1, 4.10; Stacks 03DI, 07A4, 0E8I, 0941
(blueprint: def-pur-system-tensor-mate-arrows).
Proof: use semilinearDerivedSections for each actual quotient sequence. On the
vertical site form the module inverse image left adjoint to direct. The constant
section map identifies its coefficient ring with the given quotient sequence,
so this inverse image is exact. Open localization has the direct-sum and
sheafification extension, which is exact and left adjoint to this inverse image.
Their universal properties give the ordinary adjunctions. Derive on the ordinary
system category, using its Grothendieck abelianness and K-injectives. The ordinary
tensor inverse-image comparison is the transpose of laxTensor after the two
units. It is invertible for inverse image of constant coefficients. Its inverse
on every total summand gives the chain comparison; localize on flat-term K-flat
systems to get mu and its TensorComparisonModel, precisely as in the geometric
part of semilinearDerivedSections. No equalities are inferred from evaluation. -/
theorem tensorOperations_nonempty : Nonempty (TensorOperations l E) := by
  sorry

namespace Operations
variable {l E}
variable (o : Operations l E)

/-- The ordinary pullback square induced by the section-normalized compositors.
Source: Stacks 07A7 (blueprint: def-pur-system-tensor-mate-arrows). -/
def ordinarySquare {A B C F : Scheme.{u}} (k : A ⟶ B) (r : A ⟶ C)
    (p : B ⟶ F) (i : C ⟶ F) (h : k ≫ p = r ≫ i) :
    o.pull p ⋙ o.pull k ≅ o.pull i ⋙ o.pull r :=
  o.pullComp k p ≪≫ eqToIso (congrArg (fun f ↦ o.pull f) h) ≪≫
    (o.pullComp r i).symm

/-- The open unit is an isomorphism already on strict module systems.
Source: Stacks 03DI, 0941 (blueprint: def-pur-system-tensor-mate-arrows).
Proof: compare the universal left adjoints with extension on the localized
vertical site. Over an object in the open the extension presheaf has exactly
its original summand; sheafification retains it. Thus the unit is invertible.
Transport by the unique adjunction-compatible comparison to the supplied
universal presentation. -/
theorem ordinaryOpenUnit_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (o.openAdj j).unit := by
  sorry

/-- The inverse open unit is fixed by its two inverse identities.
Source: Stacks 03DI (blueprint: def-pur-system-tensor-mate-arrows). -/
def ordinaryOpenUnitInv {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  @inv _ _ _ _ (o.openAdj j).unit (o.ordinaryOpenUnit_isIso j)

/-- The intrinsic ordinary proper/open map is uniquely determined by its open
restriction. This characterization specifies exactly the clopen projection
composite, including the noncartesian and refinement cases.
Source: Stacks 0F7B, 09AE (blueprint: def-pur-system-tensor-mate-arrows).
Proof: form B_C and s=(k,r). Use squareLift_clopen from the recorded strict-tower
calculus, whose geometric conclusion is independent of coefficients. On module
systems, open base change is the transpose of the open unit. Follow it with the
projection which is identity on s(A) and zero on its complementary open, then
with open and inverse-image composition. This gives alpha and its displayed
restriction equation. A morphism of module sheaves with target extended by zero
is determined by its restriction to that open: on the complement its target is
zero, and the two opens cover. Hence the equation determines every component of
alpha uniquely. All constructions take place on the vertical site, so commute
with the quotient transitions before passing to derived categories. -/
theorem alpha_existsUnique {A B C F : Scheme.{u}} (k : A ⟶ B) (r : A ⟶ C)
    (p : B ⟶ F) (i : C ⟶ F) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    ∃! a : o.extension i ⋙ o.pull p ⟶ o.pull r ⋙ o.extension k,
      ∀ N : S l E C,
        (o.pull k).map (a.app N) =
          (o.ordinarySquare k r p i h).hom.app ((o.extension i).obj N) ≫
            (o.pull r).map ((o.ordinaryOpenUnitInv i).app N) ≫
              (o.openAdj k).unit.app ((o.pull r).obj N) := by
  sorry

/-- The actual ordinary clopen-projection transformation, chosen by a unique
section-level characterization, not from existence of an arbitrary arrow.
Source: Stacks 0F7B, 09AE (blueprint: def-pur-system-tensor-mate-arrows). -/
def ordinaryAlpha {A B C F : Scheme.{u}} (k : A ⟶ B) (r : A ⟶ C)
    (p : B ⟶ F) (i : C ⟶ F) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :=
  (o.alpha_existsUnique k r p i h).choose

/-- Localize the actual clopen-projection composite termwise on complexes.
Source: Stacks 0F7B, 07A4 (blueprint: def-pur-system-tensor-mate-arrows). -/
def alpha {A B C F : Scheme.{u}} (k : A ⟶ B) (r : A ⟶ C)
    (p : B ⟶ F) (i : C ⟶ F) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : o.J i ⋙ o.P p ⟶ o.P r ⋙ o.J k :=
  (Functor.mapDerivedCategoryCompIso _ _).inv ≫
    Localization.liftNatTrans DerivedCategory.Q
      (HomologicalComplex.quasiIso (S l E C) (.up ℤ))
      (((o.extension i ⋙ o.pull p).mapHomologicalComplex (.up ℤ)) ⋙ DerivedCategory.Q)
      (((o.pull r ⋙ o.extension k).mapHomologicalComplex (.up ℤ)) ⋙ DerivedCategory.Q)
      (o.extension i ⋙ o.pull p).mapDerivedCategory
      (o.pull r ⋙ o.extension k).mapDerivedCategory
      (Functor.whiskerRight
        (NatTrans.mapHomologicalComplex (o.ordinaryAlpha k r p i h) (.up ℤ))
        DerivedCategory.Q) ≫
      (Functor.mapDerivedCategoryCompIso _ _).hom

/-- The proper-adjunction mate of the clopen-projection composite. Equivalently
this is eta_p followed by R_p(alpha R_r), then R_p(k_! epsilon_r).
Source: Stacks 0F7B, 07A7 (blueprint: def-pur-system-tensor-mate-arrows). -/
def gamma {A B C F : Scheme.{u}} (k : A ⟶ B) (r : A ⟶ C)
    (p : B ⟶ F) (i : C ⟶ F) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : pushDerived l E r ⋙ o.J i ⟶ o.J k ⋙ pushDerived l E p :=
  mateEquiv (o.derivedAdj r) (o.derivedAdj p) (o.alpha k r p i h)

end Operations

namespace TensorOperations
variable {l E}
variable (o : TensorOperations l E)

/-- The counit-defined projection morphism on arbitrary unbounded systems.
Source: Stacks 0B56 (blueprint: def-pur-system-tensor-mate-arrows). -/
def projection {X Y : Scheme.{u}} (f : X ⟶ Y) (M : D l E X) (N : D l E Y) :
    (o.T Y).obj ((pushDerived l E f).obj M, N) ⟶
      (pushDerived l E f).obj ((o.T X).obj (M, (o.P f).obj N)) :=
  (o.derivedAdj f).homEquiv _ _
    ((o.mu f).hom.app ((pushDerived l E f).obj M, N) ≫
      (o.T X).map (Prod.mkHom ((o.derivedAdj f).counit.app M) (𝟙 _)))

/-- The inverse open tensor comparison is the open-unit transpose under the
canonical restriction/tensor identification.
Source: Stacks 0E8I (blueprint: def-pur-system-tensor-mate-arrows). -/
def deltaInv {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : D l E U) (N : D l E X) :
    (o.J j).obj ((o.T U).obj (M, (o.P j).obj N)) ⟶
      (o.T X).obj ((o.J j).obj M, N) :=
  ((o.derivedOpenAdj j).homEquiv _ _).symm
    ((o.T U).map (Prod.mkHom ((o.derivedOpenAdj j).unit.app M) (𝟙 _)) ≫
      (o.mu j).inv.app ((o.J j).obj M, N))

/-- The specified open tensor map is invertible for arbitrary unbounded inputs.
Source: Stacks 0E8I; lem-sf-open-tensor-normalization
(blueprint: def-pur-system-tensor-mate-arrows).
Proof: compare universal operations with localized module extension/restriction.
The ordinary tensor comparison is fixed by its unit formula, so is the ordinary
sectionwise comparison. Its total K-flat normalization is model. Thus the map
is the gamma-inverse of openTensorNormalization on the ringed diagram topos,
under the unique compatible comparisons of universal presentations. That theorem
applies with arbitrary coefficient transitions and arbitrary unbounded inputs. -/
theorem deltaInv_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : D l E U) (N : D l E X) : IsIso (o.deltaInv j M N) := by
  sorry

/-- The canonical open tensor isomorphism, oriented toward extension of tensor.
Source: Stacks 0E8I (blueprint: def-pur-system-tensor-mate-arrows). -/
def delta {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : D l E U) (N : D l E X) :
    (o.T X).obj ((o.J j).obj M, N) ≅
      (o.J j).obj ((o.T U).obj (M, (o.P j).obj N)) :=
  (@asIso _ _ _ _ (o.deltaInv j M N) (o.deltaInv_isIso j M N)).symm

end TensorOperations

end WeilConjectures.SystemTensorMate

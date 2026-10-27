module

public import Sheaf.Paper.PodMixedSupportCupProduct
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.PointSectionsDerivedReduction

/-! # Coefficient comparisons for the mixed-support cup

Source: current blueprint, sec-six-functors/sk-thm-sf-package,
def-pod-mixed-support-cup-product, final coefficient compatibility sentence
(blueprint: def-sf-mixed-cup-coefficient-passages).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.MonoidalCategory
namespace WeilConjectures.MixedCupCoefficientChange

/-- The standard Grothendieck localization in the coefficient-module hom universe.
Source: coefficient complexes (blueprint: def-sf-mixed-cup-coefficient-passages). -/
@[instance_reducible]
def moduleDerived (R : Type u) [Ring R] :
    HasDerivedCategory.{u} (ModuleCat.{u} R) :=
  HasDerivedCategory.ofIsGrothendieckAbelian _

attribute [scoped instance 10000] moduleDerived

variable {D : FiniteFieldDatum.{u}} (C : D.CoefficientDatum)

/-- The four coefficient stages, indexed by the existing finite subextensions.
The finite index n denotes the positive exponent n+1.
Source: blueprint final coefficient compatibility sentence
(blueprint: def-sf-mixed-cup-coefficient-passages). -/
inductive Stage where
  | finite (F : Padic.FiniteCoefficientFields C.l C.Qbar) (n : ℕ)
  | integral (F : Padic.FiniteCoefficientFields C.l C.Qbar)
  | rational (F : Padic.FiniteCoefficientFields C.l C.Qbar)
  | closed

/-- The existing small model of a finite coefficient field.
Source: blueprint final coefficient compatibility sentence
(blueprint: def-sf-mixed-cup-coefficient-passages). -/
abbrev FieldAt (F : Padic.FiniteCoefficientFields C.l C.Qbar) :=
  AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar F

/-- The actual coefficient ring, in the common section universe.
Source: blueprint final coefficient compatibility sentence
(blueprint: def-sf-mixed-cup-coefficient-passages). -/
def ring : Stage C → CommRingCat.{u + 1}
  | .finite F n => .of (ULift.{u + 1, u}
      (Padic.coefficientExtensionRing C.l (FieldAt C F) (n + 1)))
  | .integral F => .of (ULift.{u + 1, u}
      (Padic.coefficientExtensionIntegers C.l (FieldAt C F)))
  | .rational F => .of (ULift.{u + 1, u} (FieldAt C F))
  | .closed => .of (ULift.{u + 1, u} C.Qbar)

/-- The existing ambient stage categories; the finite-Tor domains are recorded below.
Source: blueprint final coefficient compatibility sentence
(blueprint: def-sf-mixed-cup-coefficient-passages). -/
def ambient (W : Scheme.{u}) : Stage C → Type (u + 2)
  | .finite F n => proEtaleDerivedCategory W
      (Padic.coefficientExtensionRing C.l (FieldAt C F) (n + 1))
  | .integral F => sfIntegralConstructibleCategory C.l (FieldAt C F) W
  | .rational F => sfRationalConstructibleCategory C.l (FieldAt C F) W
  | .closed => generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar W

/-- The inherited category structures, with no universe identification.
Source: blueprint final coefficient compatibility sentence
(blueprint: def-sf-mixed-cup-coefficient-passages). -/
instance ambientCategory (W : Scheme.{u}) (a : Stage C) : Category.{u + 2} (ambient C W a) :=
  match a with
  | .finite F n => inferInstanceAs (Category (proEtaleDerivedCategory W
      (Padic.coefficientExtensionRing C.l (FieldAt C F) (n + 1))))
  | .integral F => inferInstanceAs
      (Category (sfIntegralConstructibleCategory C.l (FieldAt C F) W))
  | .rational F => inferInstanceAs
      (Category (sfRationalConstructibleCategory C.l (FieldAt C F) W))
  | .closed => inferInstanceAs
      (Category (generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar W))

/-- Exactly the finite-Tor domain at each stage.
Source: blueprint final coefficient compatibility sentence
(blueprint: def-sf-mixed-cup-coefficient-passages). -/
def domain (W : Scheme.{u}) : (a : Stage C) → ObjectProperty (ambient C W a)
  | .finite F n => finiteTorConstructible C.l (FieldAt C F) (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) W
  | .integral F => fun K ↦ finiteTorConstructibleIntegral C.l (FieldAt C F) W K.obj
  | .rational _ => ⊤
  | .closed => ⊤

/-- The actual admissible elementary coefficient passages. No field-to-quotient
constructor exists. Identities and successive passages are included explicitly.
Source: blueprint final coefficient compatibility sentence
(blueprint: def-sf-mixed-cup-coefficient-passages). -/
inductive Passage : Stage C → Stage C → Type (u + 1) where
  | finite {F G : Padic.FiniteCoefficientFields C.l C.Qbar} {n m : ℕ}
      (φ : Padic.coefficientExtensionRing C.l (FieldAt C F) (n + 1) →+*
        Padic.coefficientExtensionRing C.l (FieldAt C G) (m + 1)) :
      Passage (.finite F n) (.finite G m)
  | reduction (F : Padic.FiniteCoefficientFields C.l C.Qbar) (n : ℕ) :
      Passage (.integral F) (.finite F n)
  | integral {F G : Padic.FiniteCoefficientFields C.l C.Qbar} (h : F ≤ G) :
      Passage (.integral F) (.integral G)
  | rational {F G : Padic.FiniteCoefficientFields C.l C.Qbar} (h : F ≤ G) :
      Passage (.rational F) (.rational G)
  | localization (F : Padic.FiniteCoefficientFields C.l C.Qbar) :
      Passage (.integral F) (.rational F)
  | closure (F : Padic.FiniteCoefficientFields C.l C.Qbar) :
      Passage (.rational F) .closed
  | identity (a : Stage C) : Passage a a
  | comp {a b c : Stage C} (f : Passage a b) (g : Passage b c) : Passage a c

/-- The prescribed coefficient-ring homomorphism of a passage.
Source: blueprint final coefficient compatibility sentence
(blueprint: def-sf-mixed-cup-coefficient-passages). -/
def coefficientMap : {a b : Stage C} → Passage C a b → ((ring C a) ⟶ (ring C b))
  | _, _, .finite φ => CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} φ)
  | _, _, .reduction F n => CommRingCat.ofHom (pointReductionQuotient C.l (FieldAt C F) n)
  | _, _, .integral (F := F) (G := G) h => CommRingCat.ofHom (RingHom.ulift
      (integralScalarIntegerInclusion C.l (FieldAt C F) (FieldAt C G)
        (AlgebraicallyClosedCoefficients.coefficientInclusion C.l C.Qbar F G h)))
  | _, _, .rational (F := F) (G := G) h => CommRingCat.ofHom (RingHom.ulift
      (AlgebraicallyClosedCoefficients.coefficientInclusion C.l C.Qbar F G h).toRingHom)
  | _, _, .localization F => CommRingCat.ofHom (RingHom.ulift
      (algebraMap (Padic.coefficientExtensionIntegers C.l (FieldAt C F)) (FieldAt C F)))
  | _, _, .closure F => CommRingCat.ofHom (RingHom.ulift (pointTensorStageEmbedding C.l C.Qbar F))
  | _, _, .identity _ => 𝟙 _
  | _, _, .comp f g => coefficientMap f ≫ coefficientMap g

/-- The prescribed site scalar functor, including completed integral extension
and the existing raw rationalization and common-stage inclusion.
Source: blueprint final coefficient compatibility sentence
(blueprint: def-sf-mixed-cup-coefficient-passages). -/
def siteChange (W : Scheme.{u}) : {a b : Stage C} → Passage C a b →
    ambient C W a ⥤ ambient C W b
  | _, _, .finite φ => pbcDerivedExtend
      ((constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} φ)))
  | _, _, .reduction F n => (sfIntegralConstructible C.l (FieldAt C F) W).ι ⋙
      scalarReductionDerivedExtension C.l (FieldAt C F) W n
  | _, _, .integral (F := F) (G := G) h =>
      GeneralAlgebraicallyClosedCoefficients.integralTransition C.l C.Qbar W F G h
  | _, _, .rational (F := F) (G := G) h =>
      GeneralAlgebraicallyClosedCoefficients.transition C.l C.Qbar W F G h
  | _, _, .localization F => sfRationalConstructibleLocalization C.l (FieldAt C F) W
  | _, _, .closure F => GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := C.l) (Ω := C.Qbar) (Y := W) F
  | _, _, .identity _ => 𝟭 _
  | _, _, .comp f g => siteChange W f ⋙ siteChange W g

/-- Derived scalar extension on coefficient complexes, along the actual ring map.
For completed integral cohomology this computes completed tensor because the
cohomology modules are bounded and finitely generated and the extension is finite free.
Source: blueprint final coefficient compatibility sentence
(blueprint: def-sf-mixed-cup-coefficient-passages). -/
def pointChange {a b : Stage C} (f : Passage C a b) :=
  ModuleCat.ordinaryDerivedExtendScalars (coefficientMap C f).hom

end WeilConjectures.MixedCupCoefficientChange

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q02
-/
module

public import Sheaf.Paper.ProEtaleTateTwists
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Sheaf.Paper.CartesianCoefficientsFiniteFree
import Sheaf.NumberTheory.Padics.LocalFieldIntegralBasis
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import Sheaf.CategoryTheory.SheafTensor
import Sheaf.CategoryTheory.SheafTensorClosed
import Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Sheaf.CategoryTheory.ModuleObjects.LiftExact
import Sheaf.Paper.CartesianCoefficientTwists
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

/-!
# Cartesian coefficient sheaves

Source: blueprint main-20261015, sec-proetale-coefficients,
`sk-prop-sfb-cartesian-coefficients/_section.md`, assertions (1), (2), and the final paragraph
(blueprint: sk-prop-sfb-cartesian-coefficients).

The assertions below use the published coefficient comparison and module pullback.
The inverse-image lift and its comparison with extension of scalars are actual constructions.
The signed lines are the recorded Tate twists, including their sectionwise module encoding.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable {X Y : Scheme.{u}}

/-- The inverse-image lift with action transported through the inverse of alpha_f.
Its underlying objects and arrows are literally those of abelian inverse image.
Source: blueprint final paragraph (blueprint: sk-prop-sfb-cartesian-coefficients). -/
def cartesianCoefficientLift
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (f : X ⟶ Y) :=
  (upperStar AddCommGrpCat.{u + 1} f).mapMod (condensedRingObj Λ Y) ⋙
    Mod.comap (inv (condensedPullbackHom Λ f))

/-- The canonical comparison: extension along alpha is restriction along its inverse.
This is the uniqueness-of-left-adjoints comparison of the published scalar adjunctions.
Source: blueprint final paragraph (blueprint: sk-prop-sfb-cartesian-coefficients). -/
def cartesianCoefficientPullbackIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (f : X ⟶ Y) :
    CondensedRing.upperStar Λ f ≅ cartesianCoefficientLift Λ f :=
  Functor.isoWhiskerLeft
    ((upperStar AddCommGrpCat.{u + 1} f).mapMod (condensedRingObj Λ Y))
    (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f))

/-- The untwisted assertions for one specified condensed coefficient ring.
The first conjunct concerns the canonical ring-object morphism, whose ring structure
is recorded by isMonHom_condensedPullbackHom; the lift comparison is the actual
cartesianCoefficientPullbackIso above. The last equality retains the whole underlying
functor, on objects and morphisms.
Source: blueprint (1) and final paragraph (blueprint: sk-prop-sfb-cartesian-coefficients). -/
def CartesianCoefficientProperty
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (f : X ⟶ Y) : Prop :=
  IsIso (condensedPullbackHom Λ f) ∧
    PreservesFiniteLimits (CondensedRing.upperStar Λ f) ∧
    PreservesFiniteColimits (CondensedRing.upperStar Λ f) ∧
    cartesianCoefficientLift Λ f ⋙ Mod.forget (condensedRingObj Λ X) =
      Mod.forget (condensedRingObj Λ Y) ⋙ upperStar AddCommGrpCat.{u + 1} f

/-- Finite coefficients have the discrete topology, fixed here rather than supplied
as an extra hypothesis. This is the recorded continuous-function condensed ring.
Source: blueprint coefficient list (blueprint: sk-prop-sfb-cartesian-coefficients). -/
abbrev cartesianFinitePointRing (A : Type u) [CommRing A] :
    Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1} :=
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := discreteTopology_bot A
  Profinite.continuousCoefficientRingObj A

/-- Exactly the admissible untwisted coefficient list. Z_ell and Q_ell are included
explicitly, in addition to all finite intermediate extensions and their integer rings.
Qbar is the finite-subextension-valued condensed ring, not all continuous functions.
Source: blueprint (1) (blueprint: sk-prop-sfb-cartesian-coefficients). -/
def CartesianUntwistedAssertions (ℓ : ℕ) [Fact ℓ.Prime] (f : X ⟶ Y) : Prop :=
  (∀ (A : Type u) [CommRing A] [Finite A],
    CartesianCoefficientProperty (cartesianFinitePointRing A) f) ∧
  CartesianCoefficientProperty (Profinite.continuousMapRingObj (PadicInt ℓ)) f ∧
  CartesianCoefficientProperty (Profinite.continuousMapRingObj (Padic ℓ)) f ∧
  (∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
    CartesianCoefficientProperty (Profinite.padicIntegersRingObj ℓ E.1) f ∧
    CartesianCoefficientProperty (Profinite.continuousMapRingObj E.1) f) ∧
  CartesianCoefficientProperty (Profinite.padicAlgClRingObj ℓ) f

/-- The underlying abelian sheaf of a signed line, retaining the recorded powers and duals.
Source: blueprint twist clause (blueprint: sk-prop-sfb-cartesian-coefficients). -/
abbrev cartesianSignedAb (Z : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology Z) CommRingCat.{u + 1})
    (L : SheafOfModules.{u + 1} (Scheme.purTwistRing Z R)) (d : ℤ) :=
  (SheafOfModules.toSheaf _).obj (WeilConjectures.coefficientTwistLine Z L d)

/-- Direct-image maps on all signed lines. Their inverse-image mates are the comparisons.
Source: blueprint twist clause (blueprint: sk-prop-sfb-cartesian-coefficients). -/
abbrev CartesianSignedMaps (f : X ⟶ Y)
    (RX : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (RY : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (LX : SheafOfModules.{u + 1} (Scheme.purTwistRing X RX))
    (LY : SheafOfModules.{u + 1} (Scheme.purTwistRing Y RY)) :=
  ∀ d : ℤ, cartesianSignedAb Y RY LY d ⟶
    (lowerStar AddCommGrpCat.{u + 1} f).obj (cartesianSignedAb X RX LX d)

/-- Zero, linearity, positive tensor, and negative evaluation normalizations.
The first-line normalization is supplied separately for each coefficient construction.
All equations are on sections over a test object and its actual fibre product.
Source: blueprint powers and duals paragraph
(blueprint: sk-prop-sfb-cartesian-coefficients). -/
def CartesianSignedNormalization (f : X ⟶ Y)
    (RX : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (RY : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (LX : SheafOfModules.{u + 1} (Scheme.purTwistRing X RX))
    (LY : SheafOfModules.{u + 1} (Scheme.purTwistRing Y RY))
    (ρ : cartesianSignedAb Y RY LY 0 ⟶
      (lowerStar AddCommGrpCat.{u + 1} f).obj (cartesianSignedAb X RX LX 0))
    (c : CartesianSignedMaps f RX RY LX LY) : Prop :=
  c 0 = ρ ∧
  (∀ (d : ℤ) (V : Y.ProEt) (a : RY.obj.obj (Opposite.op V))
    (x : (WeilConjectures.coefficientTwistLine Y LY d).val.obj (Opposite.op V)),
    (c d).hom.app (Opposite.op V) (a • x) =
      @SMul.smul (RX.obj.obj (Opposite.op ((Scheme.proEtaleBaseChange f).obj V)))
        ((WeilConjectures.coefficientTwistLine X LX d).val.obj
          (Opposite.op ((Scheme.proEtaleBaseChange f).obj V))) inferInstance
        (ρ.hom.app (Opposite.op V) a) ((c d).hom.app (Opposite.op V) x)) ∧
  (∀ (n : ℕ) (V : Y.ProEt)
    (x : (WeilConjectures.coefficientTwistPower Y LY (n + 1)).val.obj (Opposite.op V))
    (y : LY.val.obj (Opposite.op V)),
    (c (Int.ofNat (n + 2))).hom.app (Opposite.op V)
        (SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
          (A := RY) _ _ (Opposite.op V) x y) =
      SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1} (A := RX) _ _
        (Opposite.op ((Scheme.proEtaleBaseChange f).obj V))
        ((c (Int.ofNat (n + 1))).hom.app (Opposite.op V) x)
        ((c 1).hom.app (Opposite.op V) y)) ∧
  ∀ (n : ℕ) (V : Y.ProEt)
    (q : (WeilConjectures.coefficientTwistLine Y LY (Int.negSucc n)).val.obj
      (Opposite.op V))
    (x : (WeilConjectures.coefficientTwistPower Y LY (n + 1)).val.obj (Opposite.op V)),
    (((c (Int.negSucc n)).hom.app (Opposite.op V) q).app
        (Opposite.op (Over.mk (𝟙 ((Scheme.proEtaleBaseChange f).obj V)))))
          ((c (Int.ofNat (n + 1))).hom.app (Opposite.op V) x) =
      ρ.hom.app (Opposite.op V) ((q.app (Opposite.op (Over.mk (𝟙 V)))) x)

/-- The section-module model of an internal coefficient line.
Source: the recorded internal/sectionwise equivalence
(blueprint: sk-prop-sfb-cartesian-coefficients). -/
abbrev cartesianSectionLine (Z : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1})
    [MonObj R] [IsCommMonObj R]
    (L : Mod (Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1}) R) :=
  (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology Z) R).functor.obj L

/-- The reconstructed ring sheaf, with exactly the recorded internal multiplication.
Source: the recorded internal/sectionwise equivalence
(blueprint: sk-prop-sfb-cartesian-coefficients). -/
abbrev cartesianSectionRing (Z : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1})
    [MonObj R] [IsCommMonObj R] :=
  InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    (Scheme.ProEt.topology Z) R

/-- Signed direct-image maps for one fixed condensed coefficient and its actual first lines.
Source: blueprint twist clause (blueprint: sk-prop-sfb-cartesian-coefficients). -/
abbrev CartesianInternalSignedMaps
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (f : X ⟶ Y)
    (LX : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
      (condensedRingObj Λ X))
    (LY : Mod (Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1})
      (condensedRingObj Λ Y)) :=
  CartesianSignedMaps f (cartesianSectionRing X (condensedRingObj Λ X))
    (cartesianSectionRing Y (condensedRingObj Λ Y))
    (cartesianSectionLine X _ LX) (cartesianSectionLine Y _ LY)

/-- Canonical scalar and signed-power normalization for the internal coefficient model.
Source: blueprint twist clause, compatibility with alpha_f
(blueprint: sk-prop-sfb-cartesian-coefficients). -/
def CartesianInternalSignedNormalization
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (f : X ⟶ Y)
    (LX : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
      (condensedRingObj Λ X))
    (LY : Mod (Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1})
      (condensedRingObj Λ Y))
    (c : CartesianInternalSignedMaps Λ f LX LY) : Prop :=
  CartesianSignedNormalization f _ _ (cartesianSectionLine X _ LX)
    (cartesianSectionLine Y _ LY) (condensedPushforwardHom Λ f) c

/-- The full family of candidate comparisons, before any isomorphism is asserted.
Source: blueprint twist proof, roots, finite, integral, rational, colimit, powers and duals
(blueprint: sk-prop-sfb-cartesian-coefficients). -/
structure CartesianTwistMaps (ℓ : ℕ) [Fact ℓ.Prime] (f : X ⟶ Y) where
  /-- Roots comparison, as an inverse-image map. -/
  roots (n : ℕ) :
    (upperStar AddCommGrpCat.{u + 1} f).obj
        (Scheme.proEtaleRootsOfUnitySheaf Y (ℓ ^ (n + 1))) ⟶
      Scheme.proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1))
  /-- Finite signed maps, in the recorded constant coefficient presentation. -/
  finite (A : Type u) [CommRing A] [Finite A] (r : ℕ)
      (hA : (ℓ ^ (r + 1) : ULift.{u + 1} A) = 0) :
    CartesianSignedMaps f (Scheme.tateFiniteCoefficient X (ULift.{u + 1} A))
      (Scheme.tateFiniteCoefficient Y (ULift.{u + 1} A))
      (spFiniteTwist X ℓ (ULift.{u + 1} A) r hA)
      (spFiniteTwist Y ℓ (ULift.{u + 1} A) r hA)
  /-- Integral signed maps, in the recorded pulled-back coefficient presentation. -/
  integral (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    CartesianInternalSignedMaps (Profinite.padicIntegersRingObj ℓ E.1) f
      (spIntegralTwist X ℓ E) (spIntegralTwist Y ℓ E)
  /-- Rational signed maps, in the recorded pulled-back coefficient presentation. -/
  rational (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    CartesianInternalSignedMaps (Profinite.continuousMapRingObj E.1) f
      (spRationalTwist X ℓ E) (spRationalTwist Y ℓ E)
  /-- Algebraic-closure signed maps for finite-subextension-valued coefficients. -/
  qbar : CartesianInternalSignedMaps (Profinite.padicAlgClRingObj ℓ) f
    (spQbarTwist X ℓ) (spQbarTwist Y ℓ)

/-- The actual inverse-image mate of a direct-image abelian sheaf map.
Source: the recorded inverse-image adjunction
(blueprint: sk-prop-sfb-cartesian-coefficients). -/
abbrev cartesianTwistMate (f : X ⟶ Y)
    {M : Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1}}
    {N : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}}
    (c : M ⟶ (lowerStar AddCommGrpCat.{u + 1} f).obj N) :=
  ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv M N).symm c

/-- Pull back units by the actual fibre-product projection, on each test object.
Source: blueprint roots paragraph (blueprint: sk-prop-sfb-cartesian-coefficients). -/
def cartesianUnitsBaseChange (f : X ⟶ Y) (V : Y.ProEt) :=
  (forget₂ CommRingCat.{u} CommMonCat.{u} ⋙ CommMonCat.units ⋙
    CommGrpCat.toAddCommGrp ⋙ AddCommGrpCat.uliftFunctor.{u + 1}).map
      (Scheme.Γ.map (pullback.fst V.hom f).op)

/-- The finite-level comparison is the tensor of the specified quotient-coefficient
comparison and roots comparison, using the actual strong monoidal tensorator.
Source: blueprint finite-level integral twist paragraph
(blueprint: sk-prop-sfb-cartesian-coefficients). -/
def cartesianTwistLevelMap (ℓ : ℕ) [Fact ℓ.Prime] (f : X ⟶ Y)
    (c : CartesianTwistMaps ℓ f) (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
    (upperStar AddCommGrpCat.{u + 1} f).obj (spIntegralTwistLevel Y ℓ E n).X ⟶
      (spIntegralTwistLevel X ℓ E n).X :=
  (Functor.Monoidal.μIso (upperStar AddCommGrpCat.{u + 1} f) _ _).inv ≫
    (condensedPullbackHom (spEllPointRingObj ℓ E n) f ⊗ₘ c.roots n)

/-- The unique unital quotient map to the finite coefficient ring, in its section universe.
Source: blueprint finite first-line formula (blueprint: sk-prop-sfb-cartesian-coefficients). -/
abbrev cartesianFiniteQuotientHom (ℓ : ℕ) (A : Type u) [CommRing A] (r : ℕ)
    (hA : (ℓ ^ (r + 1) : ULift.{u + 1} A) = 0) :
    ZMod (ℓ ^ (r + 1)) →+* ULift.{u + 1} A :=
  letI : CharP (ULift.{u + 1} A) (ringChar (ULift.{u + 1} A)) :=
    ringChar.charP (R := ULift.{u + 1} A)
  ZMod.castHom
    (ringChar.dvd (R := ULift.{u + 1} A) (by simpa only [Nat.cast_pow] using hA))
    (ULift.{u + 1} A)

/-- The normalization which uniquely determines every comparison. The roots equation
uses the literal structural map on units; the first integral maps are determined by
all projections, rational maps by the balanced-tensor quotient, and Qbar by all finite
field coprojections. Signed tensor and dual equations fix every other degree.
Source: the six paragraphs of the blueprint Tate-twist comparison proof
(blueprint: sk-prop-sfb-cartesian-coefficients). -/
def CartesianTwistNormalization (ℓ : ℕ) [Fact ℓ.Prime] (f : X ⟶ Y)
    (c : CartesianTwistMaps ℓ f) : Prop :=
  (∀ (n : ℕ) (V : Y.ProEt),
    (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _
        (c.roots n)).hom.app (Opposite.op V)) ≫
        (Scheme.proEtaleRootsOfUnityInclusion X (ℓ ^ (n + 1))).hom.app
          (Opposite.op ((Scheme.proEtaleBaseChange f).obj V)) =
      (Scheme.proEtaleRootsOfUnityInclusion Y (ℓ ^ (n + 1))).hom.app (Opposite.op V) ≫
        cartesianUnitsBaseChange f V) ∧
  (∀ (A : Type u) [CommRing A] [Finite A] (r : ℕ)
    (hA : (ℓ ^ (r + 1) : ULift.{u + 1} A) = 0),
    CartesianSignedNormalization f _ _
      (spFiniteTwist X ℓ (ULift.{u + 1} A) r hA)
      (spFiniteTwist Y ℓ (ULift.{u + 1} A) r hA)
      ((sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).map
          (Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
            (CommRingCat.of (ULift.{u + 1} A)))) (c.finite A r hA)) ∧
  (∀ (A : Type u) [CommRing A] [Finite A] (r : ℕ)
    (hA : (ℓ ^ (r + 1) : ULift.{u + 1} A) = 0) (V : Y.ProEt)
    (b : (Scheme.tateFiniteCoefficient Y (ULift.{u + 1} A)).obj.obj (Opposite.op V))
    (x : (Scheme.proEtaleRootsOfUnitySheaf Y (ℓ ^ (r + 1))).obj.obj (Opposite.op V)),
    (c.finite A r hA 1).hom.app (Opposite.op V)
        (Scheme.tateFiniteTensor Y ℓ (ULift.{u + 1} A) r
          (cartesianFiniteQuotientHom ℓ A r hA) V b x) =
      Scheme.tateFiniteTensor X ℓ (ULift.{u + 1} A) r
        (cartesianFiniteQuotientHom ℓ A r hA)
        ((Scheme.proEtaleBaseChange f).obj V)
        ((Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
          (CommRingCat.of (ULift.{u + 1} A))).hom.app (Opposite.op V) b)
        ((((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _
          (c.roots r))).hom.app (Opposite.op V) x)) ∧
  (∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
    CartesianInternalSignedNormalization (Profinite.padicIntegersRingObj ℓ E.1) f
      (spIntegralTwist X ℓ E) (spIntegralTwist Y ℓ E) (c.integral E) ∧
    CartesianInternalSignedNormalization (Profinite.continuousMapRingObj E.1) f
      (spRationalTwist X ℓ E) (spRationalTwist Y ℓ E) (c.rational E)) ∧
  (∀ (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ),
    cartesianTwistMate f (c.integral E 1) ≫
        (limit.π (spIntegralTwistSystem X ℓ E) (Opposite.op n)).hom =
      (upperStar AddCommGrpCat.{u + 1} f).map
          (limit.π (spIntegralTwistSystem Y ℓ E) (Opposite.op n)).hom ≫
        cartesianTwistLevelMap ℓ f c E n) ∧
  (∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
    (upperStar AddCommGrpCat.{u + 1} f).map
        (Mod.extendπ (padicIntegersToPadicSubfield Y ℓ E) (spIntegralTwist Y ℓ E)) ≫
          cartesianTwistMate f (c.rational E 1) =
      (Functor.Monoidal.μIso (upperStar AddCommGrpCat.{u + 1} f) _ _).inv ≫
        (condensedPullbackHom (Profinite.continuousMapRingObj E.1) f ⊗ₘ
          cartesianTwistMate f (c.integral E 1)) ≫
        Mod.extendπ (padicIntegersToPadicSubfield X ℓ E) (spIntegralTwist X ℓ E)) ∧
  CartesianInternalSignedNormalization (Profinite.padicAlgClRingObj ℓ) f
    (spQbarTwist X ℓ) (spQbarTwist Y ℓ) c.qbar ∧
  ∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
    (upperStar AddCommGrpCat.{u + 1} f).map
        (colimit.ι (spRationalTwistDiagram Y ℓ) E) ≫ cartesianTwistMate f (c.qbar 1) =
      cartesianTwistMate f (c.rational E 1) ≫ colimit.ι (spRationalTwistDiagram X ℓ) E

/-- There is exactly one family with these roots, scalar, tower, tensor and evaluation
normalizations. Its data are thus determined; this is not a choice of arbitrary maps.
Source: blueprint Tate-twist comparison proof, all paragraphs
(blueprint: sk-prop-sfb-cartesian-coefficients).
Proof: pull a root along the structural map on units and use the kernel property;
finite etale representability identifies this map with base change. Tensor its
finite comparison with the constant scalar map, using local pure tensor generation
for uniqueness. At each integral quotient use the strong tensorator, alpha and this
roots map. The root powers and scalar reductions commute, so these maps form a cone.
On a common compatible-root cover they identify with coefficient maps; the compatible
free tower comparison supplies the integral map, uniquely fixed by all projections.
Pass to rational scalar extension via its balanced coequalizer, and to Qbar via its
specified finite-subextension colimit. Both universal properties determine the maps.
They are semilinear for eta_f since all finite-level formulas are semilinear. At zero
use eta_f, at positive degrees tensor these maps, and at negative degrees use dual
evaluation on the pulled-back positive line. Local rank-one trivializations prove
existence and uniqueness of the dual map and all sheaf maps glue. No basis, cover,
or unnormalized isomorphism is chosen in the resulting family. -/
theorem cartesianTwistMaps_existsUnique (ℓ : ℕ) [Fact ℓ.Prime] (f : X ⟶ Y)
    (hX : ∀ x : X, Invertible (ℓ : X.residueField x))
    (hY : ∀ y : Y, Invertible (ℓ : Y.residueField y)) :
    ∃! c : CartesianTwistMaps ℓ f, CartesianTwistNormalization ℓ f c := by
  sorry

/-- The uniquely normalized canonical maps, defined by their determining universal
properties; the only postponed datum is the proof of their unique characterization.
Source: blueprint twist comparison (blueprint: sk-prop-sfb-cartesian-coefficients). -/
def cartesianTwistMaps (ℓ : ℕ) [Fact ℓ.Prime] (f : X ⟶ Y)
    (hX : ∀ x : X, Invertible (ℓ : X.residueField x))
    (hY : ∀ y : Y, Invertible (ℓ : Y.residueField y)) : CartesianTwistMaps ℓ f :=
  (cartesianTwistMaps_existsUnique ℓ f hX hY).exists.choose

/-- The isomorphism assertion for the specified normalized maps in every signed degree.
Linearity along alpha is part of their normalization, expressed on the adjoint maps
as semilinearity along eta. Adjointness gives exactly the transported alpha action.
Source: blueprint (1), twists (blueprint: sk-prop-sfb-cartesian-coefficients). -/
def CartesianTwistAssertions (ℓ : ℕ) [Fact ℓ.Prime] (f : X ⟶ Y) : Prop :=
  ∀ (hX : ∀ x : X, Invertible (ℓ : X.residueField x))
    (hY : ∀ y : Y, Invertible (ℓ : Y.residueField y)),
    (∀ (A : Type u) [CommRing A] [Finite A] (r : ℕ)
      (hA : (ℓ ^ (r + 1) : ULift.{u + 1} A) = 0) (d : ℤ),
      IsIso (cartesianTwistMate f ((cartesianTwistMaps ℓ f hX hY).finite A r hA d))) ∧
    (∀ (E : PadicAlgCl.FiniteIntermediateField ℓ) (d : ℤ),
      IsIso (cartesianTwistMate f ((cartesianTwistMaps ℓ f hX hY).integral E d)) ∧
      IsIso (cartesianTwistMate f ((cartesianTwistMaps ℓ f hX hY).rational E d))) ∧
    ∀ d : ℤ, IsIso (cartesianTwistMate f ((cartesianTwistMaps ℓ f hX hY).qbar d))

/-- Finite-free means isomorphic to a finite sum of copies of the regular module.
Both scalar restrictions are the coefficient maps induced by the given inclusion.
Source: blueprint (2) (blueprint: sk-prop-sfb-cartesian-coefficients). -/
def CartesianFiniteFreeAssertions (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) : Prop :=
  ∀ (E F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F),
    (∃ n : ℕ, Nonempty
      (Mod.finiteFree (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) n ≅
        (Mod.comap (coefficientMap (finiteCoefficientIntegersPointMap ℓ h) X)).obj
          (Mod.regular (condensedRingObj (Profinite.padicIntegersRingObj ℓ F.1) X)))) ∧
    ∃ n : ℕ, Nonempty
      (Mod.finiteFree (padicSubfieldRingObj X ℓ E) n ≅
        (Mod.comap (padicSubfieldRingObjMap X ℓ h)).obj
          (Mod.regular (padicSubfieldRingObj X ℓ F)))

/-- Cartesian coefficient sheaves, Tate twists, finite-free coefficient extensions,
and exact module pullback with its specified inverse-image lift.

Source: blueprint main-20261015, sk-prop-sfb-cartesian-coefficients/_section.md,
assertions (1), (2), final paragraph (blueprint: sk-prop-sfb-cartesian-coefficients).

Proof:
1. The component of the monoidal comparison f^-1 p_Y^* = p_X^* is alpha_f;
   sk-def-sfb-coefficient-morphisms and lem-sfb-alpha-iso make it a ring isomorphism.
2. On the domain of sk-def-sp-tate-twist apply the comparison of
   det-prop-sfb-cartesian-coefficients-twists. Pullback of roots is base change of
   their finite etale representing scheme, compatible with Kummer powers. Finite
   coefficient twists follow by scalar tensor. Integral twists follow by the
   compatible free root tower, rational twists by localization, and Qbar by the
   finite-subextension colimit. Strong monoidality gives positive powers; rank-one
   duality gives negative powers. The comparison is linear along the same alpha_f.
3. Choose an integral basis by lem-sfb-local-field-integral-basis and use
   det-prop-sfb-cartesian-coefficients-finite-free. Its two basis isomorphisms
   give finite free modules over the integral and rational lower coefficients.
4. On small pro-etale sites, lem-pur-ringed-site-grothendieck-abelian applied to Z
   gives abelian sheaves. sk-def-sfb-sheaf-tensor and det-def-sfb-sheaf-tensor-closed
   give additive, right-exact tensor; lem-sfb-modobj-abelian gives abelian modules.
5. def-sfb-module-upper-star is mapMod followed by extension along alpha_f.
   def-sfb-modobj-extension-along-iso identifies it with restriction along alpha_f^-1.
   def-sfb-modobj-restriction keeps underlying objects and maps unchanged, proving
   the functor equality. This is cartesianCoefficientPullbackIso, constructed above.
6. det-pe-topos-functoriality-inverse-image gives exact abelian inverse image.
   Finite-limit preservation gives zero objects and biproducts, hence additivity
   through h+k = codiagonal (h direct-sum k) diagonal. Apply
   det-prop-sfb-module-pullback-exact-lifted to the literal underlying-functor equality
   of step 5. Transfer exactness across cartesianCoefficientPullbackIso. No
   invertibility of ell on X or Y was used in the untwisted assertions.
-/
theorem cartesianCoefficients (ℓ : ℕ) [Fact ℓ.Prime] (f : X ⟶ Y) :
    CartesianUntwistedAssertions ℓ f ∧ CartesianTwistAssertions ℓ f ∧
      CartesianFiniteFreeAssertions ℓ X := by
  sorry

end AlgebraicGeometry.ProEtale

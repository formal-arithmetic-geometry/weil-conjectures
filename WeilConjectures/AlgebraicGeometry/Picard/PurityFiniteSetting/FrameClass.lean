/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCup
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineDatum
public import WeilConjectures.CategoryTheory.Sites.SmoothPurity.SupportLongExact
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonFiniteLevel
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.SixFunctors.ProEtale.OpenClosed.Sequence
public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.Abelian.AbelianEtaleProEtaleCohomologyComparison
import WeilConjectures.CategoryTheory.LeftModuleDerivedEvaluation.LeftModuleDerivedEvaluationForget
import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor
import WeilConjectures.AlgebraicGeometry.Picard.SiteDerivedTensorDescentIndependentCoefficients

/-! # The finite class of an étale frame

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-trace-map-of-affine-space/sk-prop-an/def-pur-frame-class.md
(blueprint: def-pur-frame-class).

Step 1 uses `coordinateKummer` over Spec k, retaining its standing hypothesis e | n,
and pulls it back along the actual unit-defined map to G_m with the cartesian twist map.
Step 2 applies the individual closed-open support boundary. Step 3 forms the ordered
supported cup using the published finite Tate sheaves and their tensor comparison.
Step 4 identifies the common zero support with Z times_V U. The empty product is the
unit, and the singleton is its own boundary. All coefficient and boundary maps have
real data; this module adds no postponed proof.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- The finite clause of the coefficient twists, in fixed-scalar coordinates.
This reuses the published finite Tate sheaves and exact comparison inverse image.
Source: def-coefficient-twists-detailed, finite twists and nonnegative powers;
def-pur-affine-line-datum, coefficient-identification paragraph
(blueprint: def-pur-frame-class). -/
def frameCoefficientTwist (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (X : Scheme.{u}) (d : ℕ) :
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient) :=
  (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).obj
    (Scheme.finiteEtaleTateTwist X P.exponent P.Coefficient
      (P.exponent_coefficient_eq_zero h) d)

/-- Multiplication of nonnegative finite twists, obtained from the published tensor
powers through the strong monoidal comparison. Degree zero uses its unit constraint.
Source: def-coefficient-twists-detailed, nonnegative powers
(blueprint: def-pur-frame-class). -/
def frameCoefficientTensorNext (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (X : Scheme.{u}) :
    (d : ℕ) → P.frameCoefficientTwist h X d ⊗ P.frameCoefficientTwist h X 1 ≅
      P.frameCoefficientTwist h X (d + 1)
  | 0 => by
    let ν := comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X
    let e : P.frameCoefficientTwist h X 0 ≅ 𝟙_ _ :=
      ν.mapIso (Functor.Monoidal.εIso
        (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))).symm ≪≫
        (Functor.Monoidal.εIso ν).symm
    exact tensorIso e (Iso.refl _) ≪≫ λ_ _
  | d + 1 => by
    exact Functor.Monoidal.μIso
      (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X)
      (Scheme.finiteEtaleTateTwist X P.exponent P.Coefficient
        (P.exponent_coefficient_eq_zero h) (d + 1))
      (Scheme.finiteEtaleTateLine X P.exponent P.Coefficient
        (P.exponent_coefficient_eq_zero h))

/-- The finite degree-one cartesian twist comparison. The map is the exact inverse image
of the canonical scalar-extension map on roots, including the site-comparison square.
Its inverse is the inverse of this specified isomorphism, with no existence choice.
Source: det-prop-sfb-cartesian-coefficients-twists, finite coefficients paragraph;
def-pur-affine-line-datum, canonical root pullback
(blueprint: def-pur-frame-class). -/
def frameCoefficientPullback (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : Y ⟶ Spec (.of P.field.k)) :
    (upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj
      (P.frameCoefficientTwist h Y 1) ≅ P.frameCoefficientTwist h X 1 := by
  letI := P.isIso_twistEtalePullback h f (P.exponent_isUnit Y a)
  exact (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} P.Coefficient) f).app
      (P.twistEtale h Y) ≪≫
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapIso
      (asIso (P.twistEtalePullback h f))

/-- The finite coefficient support connecting morphism in degree one. Its construction
is the Yoneda splice with the canonical localization sequence; it has degree two.
Source: thm-pur-with-support-exactness, finite-torsion pro-etale clause;
literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-the-trace-map-of-affine-space/sk-prop-an/def-pur-frame-class.md, step 2
(blueprint: def-pur-frame-class). -/
def frameSupportBoundary (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (f : Γ(X, ⊤))
    (L : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))
    (κ : Abelian.Ext
      ((openImmersionLowerShriek (ModuleCat.{u + 1} P.Coefficient) (X.basicOpen f).ι).obj
        ((upperStar (ModuleCat.{u + 1} P.Coefficient) (X.basicOpen f).ι).obj
          (P.constant X))) L 1) :
    Abelian.Ext ((lowerStar (ModuleCat.{u + 1} P.Coefficient)
      (X.zeroLocusSubschemeι {f})).obj (P.constant (X.zeroLocusSubscheme {f}))) L 2 := by
  let i := X.zeroLocusSubschemeι {f}
  let j := (X.basicOpen f).ι
  have hij : IsCompl (Set.range i.base) (Set.range j.base) := by
    dsimp only [i, j]
    rw [Scheme.range_zeroLocusSubschemeι_singleton, Scheme.Opens.range_ι]
    exact isCompl_compl.symm
  exact (Abelian.Ext.mk₀ ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).map
    (P.frameConstantPullback i).inv)).comp
      ((shortExact_openClosedShortComplex i j hij (P.constant X)).extClass.comp
        κ (rfl : 1 + 1 = 2)) (zero_add 2)

/-- The map defined by a unit to the punctured affine line over the coefficient base.
Its factorization through the coordinate basic open is the explicit frame map used
for the Kummer pullback.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-trace-map-of-affine-space/sk-prop-an/def-pur-frame-class.md,
step 1 (blueprint: def-pur-frame-class). -/
noncomputable def frameCoordinateMap (P : PurityFiniteSetting.{u}) {X : Scheme.{u}}
    (a : X ⟶ Spec (.of P.field.k)) (t : Γ(X, ⊤)ˣ) :
    X ⟶ Punctured (Spec (.of P.field.k)) := by
  let S := Spec (CommRingCat.of P.field.k)
  let q : X ⟶ AffineSpace (ULift.{u} (Fin 1)) S :=
    AffineSpace.homOfVector a (fun _ ↦ (t : Γ(X, ⊤)))
  let j := openImmersion S
  letI : IsOpenImmersion j := by
    dsimp [j, openImmersion]
    infer_instance
  have hpre : q ⁻¹ᵁ ((AffineSpace (ULift.{u} (Fin 1)) S).basicOpen
      (AffineSpace.coord S (ULift.up 0))) = ⊤ := by
    dsimp [q]
    rw [Scheme.preimage_basicOpen_top,
      AffineSpace.homOfVector_appTop_coord, X.basicOpen_of_isUnit t.isUnit]
  have hrange : Set.range q.base ⊆ Set.range j.base := by
    change Set.range q.base ⊆ Set.range
      (((AffineSpace (ULift.{u} (Fin 1)) S).basicOpen
        (AffineSpace.coord S (ULift.up 0))).ι.base)
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact hpre.ge trivial
  exact IsOpenImmersion.lift j q hrange

/-- Pull back the recorded affine-line datum's coordinate Kummer class along the unit's
map to G_m over Spec k. The cartesian twist comparison identifies its target with A(1).
The inherited divisibility hypothesis is the one required by `coordinateKummer`.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-trace-map-of-affine-space/sk-prop-an/def-pur-frame-class.md,
step 1 (blueprint: def-pur-frame-class). -/
def frameCoordinateKummer (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level)
    (X : Scheme.{u}) (a : X ⟶ Spec (.of P.field.k)) (t : Γ(X, ⊤)ˣ) :
    Abelian.Ext (P.constant X) (P.frameCoefficientTwist h X 1) 1 := by
  let S := Spec (CommRingCat.of P.field.k)
  let g := P.frameCoordinateMap a t
  let κg := (P.coordinateKummer h S (𝟙 S)).mapExactFunctor
    (upperStar (ModuleCat.{u + 1} P.Coefficient) g)
  exact (Abelian.Ext.mk₀ (P.frameConstantPullback g).inv).comp κg (zero_add 1) |>.comp
    (Abelian.Ext.mk₀ (P.frameCoefficientPullback h g (puncturedProjection S)).hom) (add_zero 1)

/-- The frame unit's Kummer class, namely g^* kappa(t) from the affine-line datum.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-trace-map-of-affine-space/sk-prop-an/def-pur-frame-class.md,
step 1 (blueprint: def-pur-frame-class). -/
def finiteFrameKummer (P : PurityFiniteSetting.{u}) (h : P.ramificationIndex ∣ P.level)
    (X : Scheme.{u}) (a : X ⟶ Spec (.of P.field.k)) (t : Γ(X, ⊤)ˣ) :
    Abelian.Ext (P.constant X) (P.frameCoefficientTwist h X 1) 1 :=
  P.frameCoordinateKummer h X a t

/-- The normalized twist counit for the individual complementary basic open.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-trace-map-of-affine-space/sk-prop-an/def-pur-frame-class.md,
step 2, restriction of A(1) and the open-immersion counit
(blueprint: def-pur-frame-class). -/
def finiteFrameTwistCounit (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (X : Scheme.{u})
    (a : X ⟶ Spec (.of P.field.k)) (f : Γ(X, ⊤)) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} P.Coefficient) (X.basicOpen f).ι).obj
      (P.frameCoefficientTwist h (X.basicOpen f).toScheme 1) ⟶ P.frameCoefficientTwist h X 1 :=
  (openImmersionLowerShriek (ModuleCat.{u + 1} P.Coefficient) (X.basicOpen f).ι).map
      (P.frameCoefficientPullback h (X.basicOpen f).ι a).inv ≫
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} P.Coefficient)
      (X.basicOpen f).ι).counit.app (P.frameCoefficientTwist h X 1)

/-- Extend the Kummer class by zero and apply the normalized twist counit.
The source is the first object of the canonical coefficient localization sequence.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-trace-map-of-affine-space/sk-prop-an/def-pur-frame-class.md,
step 2, extend the individual Kummer class by zero before the connecting map
(blueprint: def-pur-frame-class). -/
def finiteFrameOpenKummer (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (X : Scheme.{u})
    (a : X ⟶ Spec (.of P.field.k)) (f : Γ(X, ⊤)) :
    Abelian.Ext
      ((openImmersionLowerShriek (ModuleCat.{u + 1} P.Coefficient) (X.basicOpen f).ι).obj
        ((upperStar (ModuleCat.{u + 1} P.Coefficient) (X.basicOpen f).ι).obj
          (P.constant X))) (P.frameCoefficientTwist h X 1) 1 :=
  (Abelian.Ext.mk₀
    ((openImmersionLowerShriek (ModuleCat.{u + 1} P.Coefficient) (X.basicOpen f).ι).map
      (P.frameConstantPullback (X.basicOpen f).ι).hom)).comp
    (((P.finiteFrameKummer h (X.basicOpen f).toScheme ((X.basicOpen f).ι ≫ a)
      (X.basicOpenUnit f)).mapExactFunctor
        (openImmersionLowerShriek (ModuleCat.{u + 1} P.Coefficient) (X.basicOpen f).ι)).comp
          (Abelian.Ext.mk₀ (P.finiteFrameTwistCounit h X a f)) (add_zero 1)) (zero_add 1)

/-- The boundary for (X,V(f)), formed before intersecting any supports. Its Yoneda
splice with the canonical short exact localization sequence is the right-derived
support connecting map, with the usual positive boundary convention. A principal
basic-open immersion is affine, hence quasi-compact; no quasi-compactness assumption
on X is imposed. Constant pullback identifies the closed source with i_* A_D.
Source: thm-pur-with-support-exactness (blueprint: def-pur-frame-class). -/
def finiteFrameBoundary (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (X : Scheme.{u})
    (a : X ⟶ Spec (.of P.field.k)) (f : Γ(X, ⊤)) :
    cupSupportedHom P (X.zeroLocusSubschemeι {f})
      ((cupSingle P X).obj (P.frameCoefficientTwist h X 1)) 2 := by
  exact (P.frameSupportBoundary X f (P.frameCoefficientTwist h X 1)
    (P.finiteFrameOpenKummer h X a f)).hom

/-- The supported unit for the zero ideal. Its closed immersion is an isomorphism:
the inverse is the universal lift of the identity through the empty zero locus.
Pushforward composition, the identity comparison, and the constant-unit comparison
then give precisely 1 in H^0(X,A_X), including for an empty scheme.
Source: c=0, empty supported product (blueprint: def-pur-frame-class). -/
def finiteFrameEmptyClass (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (X : Scheme.{u})
    (f : Fin 0 → Γ(X, ⊤)) :
    cupSupportedHom P (X.zeroLocusSubschemeι (Set.range f))
      ((cupSingle P X).obj (P.frameCoefficientTwist h X 0)) 0 := by
  let c := X.zeroLocusSubschemeι (Set.range f)
  let r := Scheme.Hom.liftZeroLocusSubscheme (𝟙 X) (s := Set.range f) (fun t ht ↦ by
    obtain ⟨a, _⟩ := ht
    exact Fin.elim0 a)
  have hr : r ≫ c = 𝟙 X :=
    Scheme.Hom.liftZeroLocusSubscheme_zeroLocusSubschemeι _ _
  letI : IsIso c := ⟨⟨r, by
    apply (cancel_mono c).mp
    simp only [Category.assoc, hr, Category.comp_id, Category.id_comp], hr⟩⟩
  let e : (constantSheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} P.Coefficient)).obj (ModuleCat.of P.Coefficient P.Coefficient) ≅
      P.frameCoefficientTwist h X 0 := (cupConstantIso P X).symm
  exact (cupSingle P X).map
    ((P.finiteFrameClosedCoefficientIso c (𝟙 X) (asIso c) (Category.comp_id c)).hom ≫
      (lowerStarId (ModuleCat.{u + 1} P.Coefficient) X).hom.app (P.constant X) ≫
      (cupConstantIso P X).hom ≫ e.hom) ≫
    (shiftFunctorZero (CupDerivedCategory P X) ℤ).inv.app _

/-- Ordered supported product with explicit edge cases. For c=0 it is the unit;
for c=1 it is precisely the single principal boundary, after the tautological support
identification. For c>=2 append the last factor to the product of the prefix.
Source: latest blueprint displayed frame class (blueprint: def-pur-frame-class). -/
def finiteFrameBoundaryProduct (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (X : Scheme.{u})
    (a : X ⟶ Spec (.of P.field.k)) :
    (c : ℕ) → (f : Fin c → Γ(X, ⊤)) →
      cupSupportedHom P (X.zeroLocusSubschemeι (Set.range f))
        ((cupSingle P X).obj (P.frameCoefficientTwist h X c)) (2 * (c : ℤ))
  | 0, f => P.finiteFrameEmptyClass h X f
  | 1, f => by
    have hf : Set.range f = {f 0} := by
      ext t
      constructor
      · rintro ⟨k, rfl⟩
        exact congrArg f (Fin.eq_zero k)
      · intro ht
        exact ⟨0, (Set.mem_singleton_iff.mp ht).symm⟩
    rw [hf]
    simpa only [Nat.cast_one, mul_one] using P.finiteFrameBoundary h X a (f 0)
  | c + 2, f => P.finiteFrameCupNext h X a (c + 1) f
      (P.finiteFrameBoundaryProduct h X a (c + 1) (fun k ↦ f k.castSucc))

/-- The class of a scheme-theoretic étale frame in the fixed finite purity setting.
The affine-line datum's standing divisibility hypothesis is retained explicitly.
The frame's pullback square identifies its common zero support with Z times_V U;
e is any étale morphism, with no open-immersion requirement. The pointwise stalk
Krull-dimension condition expresses pure codimension c. Each factor is the
individual support boundary of the affine-line coordinate Kummer class;
the result has degree 2c and the recorded coefficient twist of order c on the pro-étale site.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-trace-map-of-affine-space/sk-prop-an/def-pur-frame-class.md
(blueprint: def-pur-frame-class). -/
def finiteFrameClass (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {B V Z : Scheme.{u}}
    (b : B ⟶ Spec (.of P.field.k)) (v : V ⟶ B)
    (n : ℕ) [SmoothOfRelativeDimension n v] (i : Z ⟶ V) [IsClosedImmersion i]
    [Smooth (i ≫ v)] (c : ℕ)
    (_hcodim : ∀ z : Z, ringKrullDim (V.presheaf.stalk (i z)) =
      ringKrullDim (Z.presheaf.stalk z) + (c : WithBot ℕ∞)) (F : i.EtaleFrame c) :
    cupSupportedHom P (F.U.zeroLocusSubschemeι (Set.range F.f))
      ((cupSingle P F.U).obj (P.frameCoefficientTwist h F.U c)) (2 * (c : ℤ)) :=
  P.finiteFrameBoundaryProduct h F.U (F.e ≫ v ≫ b) c F.f

end WeilConjectures.PurityFiniteSetting

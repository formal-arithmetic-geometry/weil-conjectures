module

public import Sheaf.Paper.AffineSpacePurityComparison
public import Sheaf.Paper.FiniteForwardProductSymmetry
public import Sheaf.Paper.FiniteProductCompactification
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.Paper.RelativeKunneth
import Sheaf.Paper.TwistPreservesFiniteness
import Sheaf.Paper.ProEtaleConstructibleOrigin
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TensorResolution

/-! # The last-coordinate compact-support product

Source: current blueprint sec-smooth-purity/sk-prop-an, integration paragraph,
and prop-pur-affine-space-composition-law, Steps 3--4
(blueprint: lem-pur-affine-space-last-factor-product).

The finite product is the specified six-arrow composite. All compactification
comparisons in its composition factor are the normalized etale-origin comparisons.
The displayed tensor identification presents T_(m+1) as q* T_m tensor r* T_1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.AffineSpaceLastFactorProduct
open AffineSpacePurity AffineLinePurity

section Square
variable (A : Type (u + 1)) [CommRing A] [Finite A]
  {B X Z W : Scheme.{u}} {p : X ⟶ B} {a : Z ⟶ B}
  {q : W ⟶ X} {r : W ⟶ Z}

/-- The displayed Cartesian model, retaining the existing product-geometry structure.
The auxiliary products are ordinary Mathlib pullbacks; W itself is unchanged.
Source: the common Cartesian model in proof Step 3
(blueprint: lem-pur-affine-space-last-factor-product). -/
def geometry (sq : IsPullback q r p a) (cp : Compactification p)
    (ca : Compactification a) : FiniteProductGeometry p a where
  cf := cp
  cg := ca
  P := W
  W := pullback p ca.g
  T := pullback cp.g ca.g
  p := q
  q := r
  s := pullback.fst p ca.g
  v := pullback.snd p ca.g
  r := pullback.fst cp.g ca.g
  t := pullback.snd cp.g ca.g
  sqP := sq
  sqW := IsPullback.of_hasPullback p ca.g
  sqT := IsPullback.of_hasPullback cp.g ca.g

variable [HasCompactification p] [HasCompactification a]
  [HasCompactification q] [HasCompactification r]
  [HasCompactification (q ≫ p)] [HasCompactification (r ≫ a)]
  [QuasiCompact p] [QuasiCompact a] [QuasiCompact q] [QuasiCompact r]
  (sq : IsPullback q r p a)
  (M : C A X) (N : C A Z)

/-- The actual finite Ex_! for the opposite product square. Its target uses precisely
ca base changed along p, the same compactification as the following inverse projection.
Source: E in the node's displayed formula
(blueprint: lem-pur-affine-space-last-factor-product). -/
def exchange :=
  (rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} A)
    sq.flip (HasCompactification.compactification a)).app N

/-- The two-symmetry inverse projection map, in the displayed order.
Source: Pi in the statement (blueprint: lem-pur-affine-space-last-factor-product). -/
def inverseProjection
    [IsIso (finiteForwardProjectionMap (ModuleCat.{u + 1} A)
      ((HasCompactification.compactification a).ofIsPullback sq.flip)
      ((inverseImage A r).obj N) M)] :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      ((HasCompactification.compactification a).ofIsPullback sq.flip)).obj
      (((tensor A W).obj ((inverseImage A q).obj M)).obj
        ((inverseImage A r).obj N)) ⟶
    ((tensor A X).obj M).obj
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        ((HasCompactification.compactification a).ofIsPullback sq.flip)).obj
          ((inverseImage A r).obj N)) :=
  (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      ((HasCompactification.compactification a).ofIsPullback sq.flip)).map
      (finiteForwardTensorSymmetry (ModuleCat.{u + 1} A) W
        ((inverseImage A q).obj M) ((inverseImage A r).obj N)) ≫
    inv (finiteForwardProjectionMap (ModuleCat.{u + 1} A)
      ((HasCompactification.compactification a).ofIsPullback sq.flip)
      ((inverseImage A r).obj N) M) ≫
    finiteForwardTensorSymmetry (ModuleCat.{u + 1} A) X _ M

/-- The specified binary relative-product forward map, in the common Cartesian model.
The copied final compactification has identical proper and open factors, so the target
is literally the chosen compact support for q followed by p.
Source: thm-sf-kunneth-relative's construction, proof Step 2 of this node
(blueprint: lem-pur-affine-space-last-factor-product). -/
def forward (hH : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) W
    (((tensor A W).obj ((inverseImage A q).obj M)).obj ((inverseImage A r).obj N))) :=
  finiteProductChosenForward
    (geometry sq (HasCompactification.compactification p)
      (HasCompactification.compactification a)) A
    (HasCompactification.compactification p) (HasCompactification.compactification a)
    ((HasCompactification.compactification (q ≫ p)).copy sq.w.symm) M N hH

/-- The normalized alpha for q followed by p, with exactly the compactification used
in E and Pi. Source: alpha in the statement and thm-sf-comp-composition
(blueprint: lem-pur-affine-space-last-factor-product). -/
def composition (hH : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) W
    (((tensor A W).obj ((inverseImage A q).obj M)).obj ((inverseImage A r).obj N))) :=
  finiteProductComposition A q p
    ((HasCompactification.compactification a).ofIsPullback sq.flip)
    (HasCompactification.compactification p) (HasCompactification.compactification (q ≫ p))
    (((tensor A W).obj ((inverseImage A q).obj M)).obj ((inverseImage A r).obj N)) hH

/-- All assumptions and the equality of actual maps, using explicit finite operations.
The domains are retained separately for the two orders. No six-functor datum occurs.
Source: the hypotheses and final displayed equality of the node
(blueprint: lem-pur-affine-space-last-factor-product). -/
def Equation : Prop :=
  ∀ (d : FiniteForwardProductDomain (ModuleCat.{u + 1} A) sq M N)
    (d' : FiniteForwardProductDomain (ModuleCat.{u + 1} A) sq.flip N M),
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) B
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) p).obj M) →
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) B
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) a).obj N) →
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) B
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) (q ≫ p)).obj
        (((tensor A W).obj ((inverseImage A q).obj M)).obj ((inverseImage A r).obj N))) →
    ∀ (_hPFq : IsIso (finiteForwardProjectionMap (ModuleCat.{u + 1} A)
        ((HasCompactification.compactification a).ofIsPullback sq.flip)
        ((inverseImage A r).obj N) M))
      (_hPFp : IsIso (finiteForwardProjectionMap (ModuleCat.{u + 1} A)
        (HasCompactification.compactification p) M
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) a).obj N)))
      (_hPFr : IsIso (finiteForwardProjectionMap (ModuleCat.{u + 1} A)
        ((HasCompactification.compactification p).ofIsPullback sq)
        ((inverseImage A q).obj M) N))
      (_hPFa : IsIso (finiteForwardProjectionMap (ModuleCat.{u + 1} A)
        (HasCompactification.compactification a) N
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) p).obj M)))
      (_hE : IsIso (exchange A sq N))
      (_hE' : IsIso ((rightDerivedLowerShriekOfCompactificationBaseChangeMap
        (ModuleCat.{u + 1} A) sq (HasCompactification.compactification p)).app M))
      (_hAlpha : IsIso (composition A sq M N d.external))
      (_hAlpha' : IsIso (composition A sq.flip N M d'.external))
      (kappa :
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (q ≫ p)).obj
          (((tensor A W).obj ((inverseImage A q).obj M)).obj ((inverseImage A r).obj N)) ≅
        ((tensor A B).obj ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) p).obj M)).obj
          ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) a).obj N)),
      kappa.inv = forward A sq M N d.external →
      kappa.hom =
        inv (composition A sq M N d.external) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) p).map
          (inverseProjection A sq M N) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) p).map
          (((tensor A X).obj M).map (inv (exchange A sq N))) ≫
        inv (finiteForwardProjectionMap (ModuleCat.{u + 1} A)
          (HasCompactification.compactification p) M
          ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) a).obj N))

end Square

/-- T_m=A(m)[2m] for m=d+1, in the recorded ordered shifted-line presentation.
It uses the existing signed derived tensor and the existing finite Tate line.
Source: T_j and the twist identifications of def-pur-affine-space-comparison
(blueprint: lem-pur-affine-space-last-factor-product). -/
def positiveTate (P : WeilConjectures.PurityFiniteSetting.{u}) (X : Scheme.{u}) (d : ℕ) :
    D P X :=
  (action ((tensor (Ring P) X).flip.obj (shiftedLine P X)) d).obj (shiftedLine P X)

/-- The node's complete finite-coefficient affine-space specialization. Here m=d+1,
p=p_m, a is the affine-line projection, q forgets the last coordinate, and r is the
functorial map of affine lines induced by p. T_(m+1) is written in the indicated
q* T_m tensor r* T_1 coordinates. Geometry instances come from the existing affine
projections and their base changes, and add no hypothesis.
Source: the affine-space setup of the node
(blueprint: lem-pur-affine-space-last-factor-product). -/
def Assertion (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (d : ℕ) : Prop :=
  let p := iteratedAffineLineProj Y (d + 1)
  let a := AffineSpace PUnit.{u + 1} Y ↘ Y
  let q := lastProjection Y (d + 1)
  let r := AffineSpace.map PUnit.{u + 1} p
  let sq := (AffineSpace.isPullback_map (n := PUnit.{u + 1}) p).flip
  letI : QuasiCompact r :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sq inferInstance
  letI : HasCompactification p := (projection_geometry Y (d + 1)).2
  letI : HasCompactification a := (affineTraceLineCompactification Y).hasCompactification
  letI : HasCompactification q :=
    ⟨⟨(HasCompactification.compactification a).ofIsPullback sq.flip⟩⟩
  letI : HasCompactification r :=
    ⟨⟨(HasCompactification.compactification p).ofIsPullback sq⟩⟩
  letI : HasCompactification (q ≫ p) := (projection_geometry Y (d + 2)).2
  letI : HasCompactification (r ≫ a) := HasCompactification.of_eq (f := q ≫ p) sq.w
  Equation (Ring P) sq
    (positiveTate P (iteratedAffineLine Y (d + 1)) d)
    (shiftedLine P (AffineSpace PUnit.{u + 1} Y))

/-- The supplied binary Kunneth comparison is the last-coordinate inverse product.
Source: current blueprint sec-smooth-purity/sk-prop-an, integration paragraph and
ancestor composition-law Steps 3--4
(blueprint: lem-pur-affine-space-last-factor-product).

Proof: (1) The finite shifted Tate powers are bounded constructible and of etale origin,
by prop-weil-twist-preserves and lem-sf-proetale-constructible-origin. The two displayed
forward-product domains retain all further tensor conditions.
(2) Unfold the prescribed construction of thm-sf-kunneth-relative: the hypothesis on
kappa says its inverse is exactly the existing six-arrow finite forward product.
(3) Apply lem-pur-finite-forward-product-symmetry to the same Cartesian model with its
legs interchanged. The scheme swap is the identity on this model, and its coefficient
map is the signed external tensor symmetry. Identity compositors are normalized by
thm-sf-comp-composition.
(4) Expand the opposite forward product. Cancel its two input symmetries, use naturality
of the normalized compositor to move the external symmetry inside, and use symmetry
naturality to move E past the tensor swap. This gives alpha Rp_!(B) Rp_!(1 tensor E) P_U,
where B=Rq_!(sigma_(R,Q)) PF_(q,R,M) sigma_(M,W).
(5) Cancel adjacent signed symmetries and the inverse projection pairs to identify
B inverse with inverseProjection. By lem-weil-derived-tensor-functorial, tensoring and
direct image preserve inverse pairs. Invert the composite in (4). Its four reversed
factors are exactly the stated equation. No integration map or purity permutation
invariance is used. -/
theorem affineSpace_lastFactor_product
    (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY] (d : ℕ) :
    Assertion P Y d := by
  sorry

end AlgebraicGeometry.ProEtale.AffineSpaceLastFactorProduct

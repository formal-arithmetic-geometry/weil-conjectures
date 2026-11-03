/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.PurityDiagonalDualizingData
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalOrientationRefinement
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrientationCounit.DiagonalCounitComparisonData
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalDncEtaleNaturality
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalDncAffineModel
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # The affine counit read on a diagonal DNC chart

Source: blueprint latest, sec-smooth-purity/sk-prop-sp-orientation,
thm-pur-diagonal-dualizing-object.proof.md, Steps 1--2 and canonicity paragraph.
(blueprint: lem-pur-diagonal-affine-counit-restriction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting
private theorem paste_naturality
    {A B : Type*} [Category A] [Category B] {F G : A ⥤ B}
    (c : F ≅ G) {K L : A} (m : K ⟶ L) {K' L' : B}
    (a : K' ⟶ G.obj K) (b : G.obj L ⟶ L') {z : K' ⟶ L'}
    (h : a ≫ c.inv.app K ≫ F.map m ≫ c.hom.app L ≫ b = z) :
    a ≫ G.map m ≫ b = z := by
  calc
    a ≫ G.map m ≫ b = a ≫ (c.inv.app K ≫ F.map m ≫ c.hom.app L) ≫ b := by
      rw [NatIso.naturality_1]
    _ = z := by simpa only [Category.assoc] using h

private theorem affine_projection_smooth (Y : Scheme.{u}) (d : ℕ) :
    SmoothOfRelativeDimension d (affineTraceProjection Y d) := by
  induction d with
  | zero =>
      change SmoothOfRelativeDimension 0 (𝟙 Y)
      infer_instance
  | succ d ih =>
      have : SmoothOfRelativeDimension 1
          (AffineSpace PUnit.{u + 1} (affineTraceTower Y d) ↘ affineTraceTower Y d) := by
        simpa only [Nat.card_unique] using
          (AffineSpace.smoothOfRelativeDimension_over PUnit.{u + 1} (affineTraceTower Y d))
      have := smoothOfRelativeDimension_comp
        (AffineSpace PUnit.{u + 1} (affineTraceTower Y d) ↘ affineTraceTower Y d)
        (affineTraceProjection Y d) (n := 1) (m := d)
      simpa only [affineTraceTower, affineTraceProjection, Nat.add_comm] using this

/-- On one affine target open, the coordinate counit is the inverse of the actual
four-factor DNC comparison. No global orientation or realization equation is assumed.
Source: blueprint diagonal-dualizing proof, Steps 1--2 and canonicity paragraph;
DNC invariance's standard-coordinate normalization; vector integration's frame equation
(blueprint: lem-pur-diagonal-affine-counit-restriction).

Proof:
Restrict the coordinate diagram to j^{-1}(f^{-1}V). The two pullback routes are
identified by OrientationCounit.restriction. The diagonal on the source-etale
coordinate neighbourhood is the component of the inverse image of the affine
coordinate diagonal containing the section. Restricting to that component does
not change its section invariant. The conormal map sends each coordinate
difference to the corresponding difference, with the order fixed. On the Rees
chart these are t times the normal coordinates. The family readings at one and
zero therefore identify the DNC delta with the standard identity, by the
normalization and uniqueness equation of existsUnique_dncInvariance.
Use the chart's vector model and BetaNormalized equation to replace beta inverse
by the zero-section restriction of the integration transpose. In the coordinate
model vector integration is the ordered affine counit: the frame equation fixes
its rank-one Kummer scalar and the empty tensor is the identity for d=0.
Pasting the exceptional adjunctions identifies alpha and rho with the inverse
source-etale locality and open base-change maps. The sum-extension counit equation
of tensorMateEtalePrecomp identifies the resulting transpose with diagonalAffineMate.
The two root-line coefficient comparisons are vectorIntegrationBaseCoefficientPullback;
site comparison gives tate and restriction, and the coefficient-unit conversion is
unitChange. This yields the displayed equality, for every normalized t, D and N.
This is a calculation on one affine target restriction; no global map gluing or
existence of an orientation is used. Empty opens give maps between zero objects. -/
theorem diagonalAffineCounitRestriction (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    [IsNoetherian X] [IsNoetherian Y] [HasCompactification f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (V : Y.affineOpens) (C : OrientationRefinement.Chart P f aY d V)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t T hT)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    (U : Scheme.{u}) [IsNoetherian U]
    (j : U ⟶ X) [Etale j] [IsSeparated j] [LocallyOfFiniteType j] [QuasiCompact j]
    (v : U ⟶ affineTraceTower Y d) [Etale v] [IsSeparated v]
    [LocallyOfFiniteType v] [QuasiCompact v]
    (w : v ≫ affineTraceProjection Y d = j ≫ f)
    [HasCompactification (j ≫ f)] [HasCompactification (v ≫ affineTraceProjection Y d)] :
    let W := f ⁻¹ᵁ V.1
    let νX := (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory
    let νU := (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory
    let R := OrientationRefinement.pull P W.ι
    let S := OrientationRefinement.pull P (j ∣_ W)
    let T := OrientationRefinement.pull P (j ⁻¹ᵁ W).ι
    let c := OrientationCounit.restriction P j W
    T.map (νU.map (OrientationCounit.coordinate P d f aY t D N U j v w)) =
      (c.app (P.diagonalTwistEtale X d)).inv ≫
        S.map ((OrientationRefinement.tate P W.ι (f ≫ aY) d).hom ≫
          (OrientationRefinement.theta P f aY d V C.geometry C.betaEtale).inv ≫
          R.map (νX.map (OrientationCounit.unitChange P f).hom)) ≫
        (c.app (P.diagonalOrdinaryDualizing f)).hom := by
  let := affineTraceNoetherian Y d
  let := affine_projection_smooth Y d
  obtain ⟨E, _⟩ := P.diagonalOrientationRefinement aY
    (affineTraceProjection Y d ≫ aY) (affineTraceProjection Y d) rfl d
  have hV : (V.1.ι ≫ aY).appTop.hom.FiniteType :=
    HasRingHomProperty.appTop @LocallyOfFiniteType (V.1.ι ≫ aY)
      C.geometry.baseFiniteType
  let W := f ⁻¹ᵁ V.1
  let Wp := (affineTraceProjection Y d) ⁻¹ᵁ V.1
  let O := j ⁻¹ᵁ W
  have hO : O ≤ v ⁻¹ᵁ Wp := by
    change j ⁻¹ᵁ (f ⁻¹ᵁ V.1) ≤ v ⁻¹ᵁ ((affineTraceProjection Y d) ⁻¹ᵁ V.1)
    change (j ≫ f) ⁻¹ᵁ V.1 ≤ (v ≫ affineTraceProjection Y d) ⁻¹ᵁ V.1
    rw [w]
  let vO := v.resLE Wp O hO
  have hj : (j ∣_ W) ≫ W.ι = O.ι ≫ j := by simp [O]
  have hv : vO ≫ Wp.ι = O.ι ≫ v := Scheme.Hom.resLE_comp_ι v hO
  let cv := OrientationCounit.restrictionAlong P v Wp O vO hv
  let m := P.diagonalAffineMate t D Y (P.diagonalExponent_isUnit aY) d
  have h := P.diagonalDncEtaleNaturality d f (affineTraceProjection Y d) aY V C
    (E V hV) t N U j v w O (j ∣_ W) vO hj hv
  dsimp only at h
  rw [P.diagonalDncAffineModel Y d aY V (E V hV) t D] at h
  let νU := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory
  let T := OrientationRefinement.pull P O.ι
  let a :=
    (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates t j (P.diagonalExponent_isUnit (f ≫ aY)) d).hom ≫
    (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates t v
        (P.diagonalExponent_isUnit (affineTraceProjection Y d ≫ aY)) d).inv
  let b := (P.diagonalEtaleLocality N v (affineTraceProjection Y d)).hom ≫
    (P.diagonalDualizingCongr w).hom ≫ (P.diagonalEtaleLocality N j f).inv
  have hc := paste_naturality cv m (T.map (νU.map a)) (T.map (νU.map b)) h
  simpa only [OrientationCounit.coordinate, OrientationCounit.localInverse,
    OrientationCounit.restrictionAlong, OrientationCounit.restriction,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp,
    Functor.comp_map, diagonalTwistEtale,
    Category.assoc, a, b, m, T, νU, O, W] using hc

end WeilConjectures.PurityFiniteSetting

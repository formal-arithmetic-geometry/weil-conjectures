/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedSmoothTrace
public import WeilConjectures.AlgebraicGeometry.CondensedSixFunctorOperationDatum
public import WeilConjectures.SixFunctors.CondensedCompactSupportCompositionData
public import WeilConjectures.AlgebraicGeometry.CondensedStrictWeilComplex
public import WeilConjectures.SecSmoothPurity.TransportUnits
public import WeilConjectures.SixFunctors.SchemeFrobeniusGeometry
public import WeilConjectures.SecSmoothPurity.DetPropSfCbc
public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.PoincareDuality.Abstract
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingInputs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
import WeilConjectures.SecSmoothPurity.TraceBasic
import WeilConjectures.SixFunctors.CtfStabilityDirectImages
import WeilConjectures.AlgebraicGeometry.CompactSupportProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius
import WeilConjectures.SixFunctors.CondensedSemilinearPurityFactors
import WeilConjectures.EtaleCohomology.Purity.Smooth.Normalization

/-! # Native condensed compact-support Künneth compatibilities

Source: literature/blueprint/latest/blueprint/sec-fourier-transform/
sk-lem-wft-compact-kunneth/lem-wft-kunneth-compatibilities.md, clauses (1)--(3)
(blueprint: lem-wft-kunneth-compatibilities).

The forward map uses only the specified proper/open projection morphisms, compact-support
exchange and compositor. Its inverse is therefore fixed, including the coordinate convention.
The finite-Tor objects used below are exactly Dbc at the two field coefficients, by
integral_ctf_equals_bc. All tensor symmetries are the named derived Koszul symmetries.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.CompactKunneth

variable (ell : ℕ) [Fact ell.Prime]

/-- The two native field coefficient presentations in the statement.
Source: clause (1), coefficient convention (blueprint: lem-wft-kunneth-compatibilities). -/
def FieldCoefficient (c : Coefficient ell) : Prop :=
  (∃ E : PadicAlgCl.FiniteIntermediateField ell, c = .rational E) ∨ c = .closure

/-- The Cartesian geometry and chosen compactifications. The coherent comparisons are the
normalized comparisons of the recorded composition theorem, including all its laws.
Source: clause (1), W and its projections (blueprint: lem-wft-kunneth-compatibilities). -/
structure Square (D : WeilConjectures.FiniteFieldDatum.{u}) (c : Coefficient ell) where
  S : SepFinType D.k
  X : SepFinType D.k
  Y : SepFinType D.k
  W : SepFinType D.k
  a : X ⟶ S
  b : Y ⟶ S
  u : W ⟶ X
  v : W ⟶ Y
  cartesian : IsPullback v.hom.left u.hom.left b.hom.left a.hom.left
  ca : Compactification a.hom.left
  cb : Compactification b.hom.left
  cu : Compactification u.hom.left
  cc : Compactification (u.hom.left ≫ a.hom.left)
  coherent : CompactSupportComposition.CoherentData (c.obj ell) D.k

variable {ell}

/-- The actual Koszul symmetry, with no unspecified braiding instance.
Source: clause (1), sigma (blueprint: lem-wft-kunneth-compatibilities). -/
def symmetry (c : Coefficient ell) (X : Scheme.{u}) (K L : c.derived ell X) :
    K ⊗ L ≅ L ⊗ K :=
  @BraidedCategory.braiding _ _ _ (DerivedCategory.braidedCategory' _) K L

/-- External product in the ordinary module-object derived category.
Source: clause (1), definition of boxtimes (blueprint: lem-wft-kunneth-compatibilities). -/
def external (c : Coefficient ell) {T X Y : Scheme.{u}} (u : T ⟶ X) (v : T ⟶ Y)
    (K : c.derived ell X) (L : c.derived ell Y) : c.derived ell T :=
  (moduleObjectDerivedPullback (c.obj ell) u).obj K ⊗
    (moduleObjectDerivedPullback (c.obj ell) v).obj L

/-- Pullback and tensor preserve the stated finite-Tor constructible domain.
Source: clause (1), domain check (blueprint: lem-wft-kunneth-compatibilities).
Proof: apply det-thm-sf-ctf-stability-direct-images to each pullback and to tensor.
The two finite Tor intervals add under tensor. This is step 1 of the node's proof. -/
theorem external_mem (D : WeilConjectures.FiniteFieldDatum.{u}) (c : Coefficient ell)
    (H : CompactSupportComposition.CoherentData (c.obj ell) D.k)
    {T X Y : SepFinType D.k} (u : T ⟶ X) (v : T ⟶ Y)
    (K : c.ctf ell X.obj.left) (L : c.ctf ell Y.obj.left) :
    property ell c T.obj.left (external c u.hom.left v.hom.left K.obj L.obj) := by
  sorry

/-- The same external product as an object of the existing Dctf full subcategory.
Source: clause (1), constructible domain (blueprint: lem-wft-kunneth-compatibilities). -/
def externalCtf (D : WeilConjectures.FiniteFieldDatum.{u}) (c : Coefficient ell)
    (H : CompactSupportComposition.CoherentData (c.obj ell) D.k)
    {T X Y : SepFinType D.k} (u : T ⟶ X) (v : T ⟶ Y)
    (K : c.ctf ell X.obj.left) (L : c.ctf ell Y.obj.left) : c.ctf ell T.obj.left :=
  ⟨external c u.hom.left v.hom.left K.obj L.obj, external_mem D c H u v K L⟩

variable {D : WeilConjectures.FiniteFieldDatum.{u}} {c : Coefficient ell}
  (Q : Square ell D c)

/-- The canonical beta, oriented from a* Rb! to Ru! v*.
Source: clause (1), beta_L (blueprint: lem-wft-kunneth-compatibilities). -/
def beta (L : c.ctf ell Q.Y.obj.left) :
    (moduleObjectDerivedPullback (c.obj ell) Q.a.hom.left).obj
        ((rightDerivedLowerShriekOfCompactification (c.obj ell) Q.cb).obj L.obj) ≅
      (rightDerivedLowerShriekOfCompactification (c.obj ell) Q.cu).obj
        ((moduleObjectDerivedPullback (c.obj ell) Q.v.hom.left).obj L.obj) :=
  (Q.coherent.exchange Q.cartesian Q.cb Q.cu).app ((inclusion ell c _).obj L)

/-- The forward Künneth map: projection for a, beta, coefficient-first projection for u,
and the normalized compositor. Its inverse is precisely the displayed kappa.
Source: clause (1), four-arrow composite (blueprint: lem-wft-kunneth-compatibilities). -/
def forward (K : c.ctf ell Q.X.obj.left) (L : c.ctf ell Q.Y.obj.left) :
    (rightDerivedLowerShriekOfCompactification (c.obj ell) Q.ca).obj K.obj ⊗
        (rightDerivedLowerShriekOfCompactification (c.obj ell) Q.cb).obj L.obj ⟶
      (rightDerivedLowerShriekOfCompactification (c.obj ell) Q.cc).obj
        (external c Q.u.hom.left Q.v.hom.left K.obj L.obj) :=
  exceptionalProjectionMorphismOfCompactification (c.obj ell) Q.ca K.obj _ ≫
    (rightDerivedLowerShriekOfCompactification (c.obj ell) Q.ca).map
      (K.obj ◁ (beta Q L).hom) ≫
    (rightDerivedLowerShriekOfCompactification (c.obj ell) Q.ca).map
      ((symmetry c Q.X.obj.left K.obj _).hom ≫
        exceptionalProjectionMorphismOfCompactification (c.obj ell) Q.cu
          ((moduleObjectDerivedPullback (c.obj ell) Q.v.hom.left).obj L.obj) K.obj ≫
        (rightDerivedLowerShriekOfCompactification (c.obj ell) Q.cu).map
          (symmetry c Q.W.obj.left _ _).hom) ≫
    (Q.coherent.comp Q.u Q.a Q.cu Q.ca Q.cc).hom.app
      ((inclusion ell c _).obj (externalCtf D c Q.coherent Q.u Q.v K L))

/-- The inverse-direction version of the relative recipe, with its independent middle
symmetry and ordered pair (b,L),(a,K), rather than a definition by conjugating kappa.
Source: clause (1), r_{L,K} recipe (blueprint: lem-wft-kunneth-compatibilities). -/
def relativeForward (K : c.ctf ell Q.X.obj.left) (L : c.ctf ell Q.Y.obj.left) :
    (rightDerivedLowerShriekOfCompactification (c.obj ell) Q.cb).obj L.obj ⊗
        (rightDerivedLowerShriekOfCompactification (c.obj ell) Q.ca).obj K.obj ⟶
      (rightDerivedLowerShriekOfCompactification (c.obj ell) Q.cc).obj
        (external c Q.v.hom.left Q.u.hom.left L.obj K.obj) :=
  (symmetry c Q.S.obj.left _ _).hom ≫
    exceptionalProjectionMorphismOfCompactification (c.obj ell) Q.ca K.obj _ ≫
    (rightDerivedLowerShriekOfCompactification (c.obj ell) Q.ca).map
      ((symmetry c Q.X.obj.left _ _).hom ≫ (beta Q L).hom ▷ K.obj) ≫
    (rightDerivedLowerShriekOfCompactification (c.obj ell) Q.ca).map
      (exceptionalProjectionMorphismOfCompactification (c.obj ell) Q.cu
        ((moduleObjectDerivedPullback (c.obj ell) Q.v.hom.left).obj L.obj) K.obj) ≫
    (Q.coherent.comp Q.u Q.a Q.cu Q.ca Q.cc).hom.app
      ((inclusion ell c _).obj (externalCtf D c Q.coherent Q.v Q.u L K))

/-- Both canonical forward maps are invertible on exactly the stated field domain.
Source: clause (1) (blueprint: lem-wft-kunneth-compatibilities).
Proof: by lem-integral-ctf-equals-bc this is the entire Dbc field domain. In step 1,
pullback, tensor and compact support preserve Dctf. Step 2 applies
fix-prop-projection-formula to a and u and det-prop-sf-cbc to the Cartesian square.
Each factor is an isomorphism; the compositor is sk-thm-sf-comp-composition. -/
theorem forward_isIso (_hEll : ell ≠ D.p) (_hc : FieldCoefficient ell c)
    (K : c.ctf ell Q.X.obj.left) (L : c.ctf ell Q.Y.obj.left) :
    IsIso (forward Q K L) ∧ IsIso (relativeForward Q K L) := by
  sorry

/-- Kappa is the unique inverse of its canonical four-factor forward map.
Source: clause (1), kappa (blueprint: lem-wft-kunneth-compatibilities). -/
def kappa (hEll : ell ≠ D.p) (hc : FieldCoefficient ell c)
    (K : c.ctf ell Q.X.obj.left) (L : c.ctf ell Q.Y.obj.left) :=
  letI := (forward_isIso Q hEll hc K L).1
  (asIso (forward Q K L)).symm

/-- The native relative Künneth recipe, as the unique inverse of relativeForward.
Source: clause (1), r_{L,K} (blueprint: lem-wft-kunneth-compatibilities). -/
def relative (hEll : ell ≠ D.p) (hc : FieldCoefficient ell c)
    (K : c.ctf ell Q.X.obj.left) (L : c.ctf ell Q.Y.obj.left) :=
  letI := (forward_isIso Q hEll hc K L).2
  (asIso (relativeForward Q K L)).symm

/-- Naturality of the displayed isomorphism and the coordinate-swapped relative comparison.
Source: clause (1) (blueprint: lem-wft-kunneth-compatibilities).
Proof: step 2 gives naturality of each projection, beta and compositor. Invert the
resulting naturality square. Expand the independent relative recipe: its output symmetry
cancels the external output symmetry, and naturality of symmetry across beta identifies
the two middle factors. The external input symmetry supplies the remaining Ru!(sigma).
No finite-coefficient Künneth assertion is applied to field coefficients. -/
theorem kappa_natural_relative (hEll : ell ≠ D.p) (hc : FieldCoefficient ell c)
    (K : c.ctf ell Q.X.obj.left) (L : c.ctf ell Q.Y.obj.left) :
    (∀ (K' : c.ctf ell Q.X.obj.left) (L' : c.ctf ell Q.Y.obj.left)
        (f : K ⟶ K') (g : L ⟶ L'),
      (rightDerivedLowerShriekOfCompactification (c.obj ell) Q.cc).map
          ((moduleObjectDerivedPullback (c.obj ell) Q.u.hom.left).map f.hom ⊗ₘ
            (moduleObjectDerivedPullback (c.obj ell) Q.v.hom.left).map g.hom) ≫
          (kappa Q hEll hc K' L').hom =
        (kappa Q hEll hc K L).hom ≫
          ((rightDerivedLowerShriekOfCompactification (c.obj ell) Q.ca).map f.hom ⊗ₘ
            (rightDerivedLowerShriekOfCompactification (c.obj ell) Q.cb).map g.hom)) ∧
    (kappa Q hEll hc K L).hom =
      (rightDerivedLowerShriekOfCompactification (c.obj ell) Q.cc).map
          (symmetry c Q.W.obj.left _ _).hom ≫
        (relative Q hEll hc K L).hom ≫ (symmetry c Q.S.obj.left _ _).hom := by
  sorry


/-- Descent coordinates for the four schemes and four arrows. Conjugating the recorded
model Frobenius by these coordinates fixes the geometric Frobenius on each scheme.
Source: clause (2), descent to k0 (blueprint: lem-wft-kunneth-compatibilities). -/
structure Descent where
  S₀ : Over (Spec (.of D.k₀))
  X₀ : Over (Spec (.of D.k₀))
  Y₀ : Over (Spec (.of D.k₀))
  W₀ : Over (Spec (.of D.k₀))
  eS : Q.S.obj ≅ D.purityFrobeniusFiber S₀
  eX : Q.X.obj ≅ D.purityFrobeniusFiber X₀
  eY : Q.Y.obj ≅ D.purityFrobeniusFiber Y₀
  eW : Q.W.obj ≅ D.purityFrobeniusFiber W₀
  a₀ : X₀ ⟶ S₀
  b₀ : Y₀ ⟶ S₀
  u₀ : W₀ ⟶ X₀
  v₀ : W₀ ⟶ Y₀
  a_eq : Q.a.hom.left ≫ eS.hom.left = eX.hom.left ≫ D.purityFrobeniusMap a₀
  b_eq : Q.b.hom.left ≫ eS.hom.left = eY.hom.left ≫ D.purityFrobeniusMap b₀
  u_eq : Q.u.hom.left ≫ eX.hom.left = eW.hom.left ≫ D.purityFrobeniusMap u₀
  v_eq : Q.v.hom.left ≫ eY.hom.left = eW.hom.left ≫ D.purityFrobeniusMap v₀

/-- The recorded model Frobenius transported through an explicit descent coordinate.
Source: clause (2), geometric Frobenius (blueprint: lem-wft-kunneth-compatibilities). -/
def modelAutomorphism (D : WeilConjectures.FiniteFieldDatum.{u})
    {T : Scheme.{u}} (T₀ : Over (Spec (.of D.k₀)))
    (e : T ≅ (D.purityFrobeniusFiber T₀).left) : T ≅ T :=
  e ≪≫ StrictWeil.modelFrobenius D T₀ ≪≫ e.symm

/-- The canonical geometric Frobenius on the base in these descent coordinates.
Source: clause (2) (blueprint: lem-wft-kunneth-compatibilities). -/
def Descent.gS (M : Descent Q) := modelAutomorphism D M.S₀ ((Over.forget _).mapIso M.eS)

/-- The canonical geometric Frobenius on X in these descent coordinates.
Source: clause (2) (blueprint: lem-wft-kunneth-compatibilities). -/
def Descent.gX (M : Descent Q) := modelAutomorphism D M.X₀ ((Over.forget _).mapIso M.eX)

/-- The canonical geometric Frobenius on Y in these descent coordinates.
Source: clause (2) (blueprint: lem-wft-kunneth-compatibilities). -/
def Descent.gY (M : Descent Q) := modelAutomorphism D M.Y₀ ((Over.forget _).mapIso M.eY)

/-- The canonical geometric Frobenius on W in these descent coordinates.
Source: clause (2) (blueprint: lem-wft-kunneth-compatibilities). -/
def Descent.gW (M : Descent Q) := modelAutomorphism D M.W₀ ((Over.forget _).mapIso M.eW)

/-- The five canonical geometric-Frobenius squares, including the composite c.
Source: clause (2) (blueprint: lem-wft-kunneth-compatibilities).
Proof: functoriality of geometric Galois pullback and the four descent equalities
give the commuting squares. Their horizontal maps are isomorphisms, hence each is
Cartesian. Compose the u and a equalities for c. This is the geometry in step 3. -/
theorem descent_squares (M : Descent Q) :
    IsPullback M.gX.hom Q.a.hom.left Q.a.hom.left M.gS.hom ∧
    IsPullback M.gY.hom Q.b.hom.left Q.b.hom.left M.gS.hom ∧
    IsPullback M.gW.hom Q.u.hom.left Q.u.hom.left M.gX.hom ∧
    IsPullback M.gW.hom Q.v.hom.left Q.v.hom.left M.gY.hom ∧
    IsPullback M.gW.hom (Q.u.hom.left ≫ Q.a.hom.left)
      (Q.u.hom.left ≫ Q.a.hom.left) M.gS.hom := by
  sorry

/-- Pullback of a strict Weil datum through the canonical commuting-square comparison.
The total-derived/exact-derived comparison identifies the recorded action P with Lg*.
Source: clause (2), product structure (blueprint: lem-wft-kunneth-compatibilities). -/
def pullStructure {T X : Scheme.{u}} (f : T ⟶ X) (gT : T ≅ T) (gX : X ≅ X)
    (w : gT.hom ≫ f = f ≫ gX.hom) (K : c.derived ell X)
    (phi : (StrictWeil.action (c.obj ell) gX).obj K ≅ K) :
    (StrictWeil.action (c.obj ell) gT).obj ((moduleObjectDerivedPullback (c.obj ell) f).obj K) ≅
      (moduleObjectDerivedPullback (c.obj ell) f).obj K :=
  (leftDerivedUpperStarIsoMapDerivedCategory (c.obj ell) gT.hom).symm.app _ ≪≫
    (leftDerivedUpperStarComp (c.obj ell) gT.hom f).symm.app K ≪≫
    (eqToIso (congrArg (fun h ↦ (moduleObjectDerivedPullback (c.obj ell) h).obj K) w)) ≪≫
    (leftDerivedUpperStarComp (c.obj ell) f gX.hom).app K ≪≫
    (moduleObjectDerivedPullback (c.obj ell) f).mapIso
      ((leftDerivedUpperStarIsoMapDerivedCategory (c.obj ell) gX.hom).app K ≪≫ phi)

/-- Compact support of a strict Weil datum through the specified compact-support exchange.
Source: clause (2), pushforward Weil structure (blueprint: lem-wft-kunneth-compatibilities). -/
def supportStructure {X Y : SepFinType D.k} (f : X ⟶ Y)
    (cf : Compactification f.hom.left) (gX : X.obj.left ≅ X.obj.left)
    (gY : Y.obj.left ≅ Y.obj.left)
    (sq : IsPullback gX.hom f.hom.left f.hom.left gY.hom)
    (K : c.ctf ell X.obj.left)
    (phi : (StrictWeil.action (c.obj ell) gX).obj K.obj ≅ K.obj) :
    (StrictWeil.action (c.obj ell) gY).obj
        ((rightDerivedLowerShriekOfCompactification (c.obj ell) cf).obj K.obj) ≅
      (rightDerivedLowerShriekOfCompactification (c.obj ell) cf).obj K.obj :=
  (leftDerivedUpperStarIsoMapDerivedCategory (c.obj ell) gY.hom).symm.app _ ≪≫
    (Q.coherent.exchange sq cf cf).app ((inclusion ell c _).obj K) ≪≫
    (rightDerivedLowerShriekOfCompactification (c.obj ell) cf).mapIso
      ((leftDerivedUpperStarIsoMapDerivedCategory (c.obj ell) gX.hom).app K.obj ≪≫ phi)

/-- The product Weil datum is pullback of the two data followed by the monoidal tensorator.
Source: clause (2), product Weil structure (blueprint: lem-wft-kunneth-compatibilities). -/
def externalStructure (M : Descent Q)
    (K : c.ctf ell Q.X.obj.left) (L : c.ctf ell Q.Y.obj.left)
    (phi : (StrictWeil.action (c.obj ell) M.gX).obj K.obj ≅ K.obj)
    (psi : (StrictWeil.action (c.obj ell) M.gY).obj L.obj ≅ L.obj) :
    (StrictWeil.action (c.obj ell) M.gW).obj
        (external c Q.u.hom.left Q.v.hom.left K.obj L.obj) ≅
      external c Q.u.hom.left Q.v.hom.left K.obj L.obj :=
  StrictWeil.tensorDatum (c.obj ell) M.gW
    (pullStructure Q.u.hom.left M.gW M.gX (descent_squares Q M).2.2.1.w K.obj phi)
    (pullStructure Q.v.hom.left M.gW M.gY (descent_squares Q M).2.2.2.1.w L.obj psi)

/-- Kappa is an isomorphism of strict Weil complexes with the product Weil structure.
The displayed equation is exactly the defining equation for morphisms of strict pairs;
the fully faithful Dctf inclusion does not change morphisms or their equality.
Source: clause (2) (blueprint: lem-wft-kunneth-compatibilities).
Proof: step 3 gives canonical Frobenius structures on both pullbacks, tensor products
and compact supports. The composition, exchange, projection and symmetry maps of step 2
are equivariant by lem-fix-weil-operations. Inverting an equivariant isomorphism preserves
its square. Compose the four inverse squares to obtain precisely the equation below. -/
theorem kappa_weil (hEll : ell ≠ D.p) (hc : FieldCoefficient ell c) (M : Descent Q)
    (K : c.ctf ell Q.X.obj.left) (L : c.ctf ell Q.Y.obj.left)
    (phi : (StrictWeil.action (c.obj ell) M.gX).obj K.obj ≅ K.obj)
    (psi : (StrictWeil.action (c.obj ell) M.gY).obj L.obj ≅ L.obj) :
    (StrictWeil.action (c.obj ell) M.gS).map (kappa Q hEll hc K L).hom ≫
        (StrictWeil.tensorDatum (c.obj ell) M.gS
          (supportStructure Q Q.a Q.ca M.gX M.gS (descent_squares Q M).1 K phi)
          (supportStructure Q Q.b Q.cb M.gY M.gS (descent_squares Q M).2.1 L psi)).hom =
      (supportStructure Q (Q.u ≫ Q.a) Q.cc M.gW M.gS
        (descent_squares Q M).2.2.2.2
        (externalCtf D c Q.coherent Q.u Q.v K L)
        (externalStructure Q M K L phi psi)).hom ≫ (kappa Q hEll hc K L).hom := by
  sorry


/-- The coefficient unit is in the recorded finite-Tor constructible category.
Source: clause (3), Lambda_S (blueprint: lem-wft-kunneth-compatibilities).
Proof: the regular module is a finite free constant local model. Its degree-zero
complex is bounded constructible and is flat, so its Tor interval is [0,0]. -/
theorem unit_mem (c : Coefficient ell) (X : Scheme.{u}) :
    property ell c X (unit ell c X) := by
  sorry

/-- The existing coefficient unit, bundled with only its membership proof.
Source: clause (3), Lambda_S (blueprint: lem-wft-kunneth-compatibilities). -/
def unitCtf (c : Coefficient ell) (X : Scheme.{u}) : c.ctf ell X :=
  ⟨unit ell c X, unit_mem c X⟩

/-- The native shifted Tate line is constructible finite-Tor on every standing scheme.
Source: clause (3), A and B (blueprint: lem-wft-kunneth-compatibilities).
Proof: ell is invertible because it differs from the characteristic of k. The root
tower is locally free of rank one, as are scalar extension and every tensor power.
The even shift preserves constructibility and translates its finite Tor interval. -/
theorem line_mem (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (c : Coefficient ell) (X : SepFinType D.k) (d : ℕ) :
    property ell c X.obj.left (c.derivedLine ell X.obj.left d) := by
  sorry

/-- The line Lambda(d)[2d] in the existing full subcategory.
Source: clause (3), A and B (blueprint: lem-wft-kunneth-compatibilities). -/
def lineCtf (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (c : Coefficient ell) (X : SepFinType D.k) (d : ℕ) : c.ctf ell X.obj.left :=
  ⟨c.derivedLine ell X.obj.left d, line_mem D hEll c X d⟩

/-- The canonical root-normalized Tate pullback is determined by its normalization fields.
Source: clause (3), canonical I (blueprint: lem-wft-kunneth-compatibilities).
Proof: invertibility of ell gives linePullCoordinates_nonempty. At every finite level
the tensor-adjunction normalization determines the map. Joint monicity of the root-tower
projections determines the integral map. Scalar extension fixes first; tensor recursion
fixes power, including power zero. Proof fields are proof-irrelevant. -/
theorem coordinates_existsUnique (D : WeilConjectures.FiniteFieldDatum.{u})
    (hEll : ell ≠ D.p) (c : Coefficient ell) {X Y : SepFinType D.k} (f : X ⟶ Y) :
    ∃! p : LinePullCoordinates ell c f.hom.left, True := by
  sorry

/-- The uniquely root-normalized pullback coordinates, never a bare existence choice.
Source: clause (3), canonical I (blueprint: lem-wft-kunneth-compatibilities). -/
def coordinates (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (c : Coefficient ell) {X Y : SepFinType D.k} (f : X ⟶ Y) :=
  (coordinates_existsUnique D hEll c f).choose

/-- Invertibility at every residue field, obtained from the stated characteristic condition.
Source: clause (3), Tate-line domain (blueprint: lem-wft-kunneth-compatibilities).
Proof: map primeUnit D ell hEll through the residue-field algebra map of the structure
morphism. Ring maps carry the inverse of a unit to the inverse of its image. -/
theorem primeUnitAt (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (X : SepFinType D.k) (x : X.obj.left) : IsUnit (ell : X.obj.left.residueField x) := by
  sorry

/-- The actual I: pull back both Tate lines, then multiply their shifted tensor powers.
The even-shift identification is derivedProduct, hence includes its prescribed signs.
Source: clause (3), I (blueprint: lem-wft-kunneth-compatibilities). -/
def lineProductComparison (hEll : ell ≠ D.p) (d e : ℕ) :
    external c Q.u.hom.left Q.v.hom.left
        (c.derivedLine ell Q.X.obj.left d) (c.derivedLine ell Q.Y.obj.left e) ≅
      c.derivedLine ell Q.W.obj.left (d + e) :=
  letI : ∀ x : Q.W.obj.left, Invertible (ell : Q.W.obj.left.residueField x) :=
    fun x ↦ (primeUnitAt D hEll Q.W x).invertible
  tensorIso ((coordinates D hEll c Q.u).derived ell d)
      ((coordinates D hEll c Q.v).derived ell e) ≪≫
    derivedProduct ell c Q.W.obj.left d e

/-- The intrinsic separated finite-type geometry of a morphism of standing schemes.
Source: clause (1), standing geometry (blueprint: lem-wft-kunneth-compatibilities).
Proof: factor its diagonal through the closed absolute diagonal of its source.
Finite type follows from finite type over k, and its Noetherian source makes it
quasi-compact. The Over morphism equation is exactly the k-morphism condition. -/
theorem morphism_geometry (D : WeilConjectures.FiniteFieldDatum.{u})
    {X Y : SepFinType D.k} (f : X ⟶ Y) :
    IsSeparated f.hom.left ∧ LocallyOfFiniteType f.hom.left ∧
      QuasiCompact f.hom.left ∧ f.hom.left.IsOver (Spec (.of D.k)) := by
  sorry

/-- The smooth trace index with the given geometry and compactification.
Source: clause (3), a and b (blueprint: lem-wft-kunneth-compatibilities). -/
def smoothIndex (D : WeilConjectures.FiniteFieldDatum.{u})
    {X Y : SepFinType D.k} (f : X ⟶ Y) (cf : Compactification f.hom.left)
    (d : ℕ) [SmoothOfRelativeDimension d f.hom.left] : SmoothDatum D :=
  letI := (morphism_geometry D f).1
  letI := (morphism_geometry D f).2.1
  letI := (morphism_geometry D f).2.2.1
  letI := (morphism_geometry D f).2.2.2
  { X := X.obj, Y := Y.obj, map := f.hom.left, dim := d, compactification := cf }

/-- The product is smooth of the sum of the two pure dimensions, also on an empty scheme.
Source: clause (3), c (blueprint: lem-wft-kunneth-compatibilities).
Proof: u is the base change of b along a, so is smooth of dimension e. Compose u
with a and apply dimension additivity, using lem-sbc-smooth-relative-dimension-permanence.
The empty source is permitted by the recorded SmoothOfRelativeDimension convention. -/
theorem product_smooth (d e : ℕ)
    [SmoothOfRelativeDimension d Q.a.hom.left] [SmoothOfRelativeDimension e Q.b.hom.left] :
    SmoothOfRelativeDimension e Q.u.hom.left ∧
      SmoothOfRelativeDimension (d + e) (Q.u.hom.left ≫ Q.a.hom.left) := by
  sorry

/-- The smooth c index, with the dimension supplied by the geometry rather than assumed.
Source: clause (3), c (blueprint: lem-wft-kunneth-compatibilities). -/
def smoothComposite (d e : ℕ)
    [SmoothOfRelativeDimension d Q.a.hom.left] [SmoothOfRelativeDimension e Q.b.hom.left] :
    SmoothDatum D :=
  letI : SmoothOfRelativeDimension (d + e) (Q.u ≫ Q.a).hom.left :=
    (product_smooth Q d e).2
  smoothIndex D (Q.u ≫ Q.a) Q.cc (d + e)

/-- Trace on the displayed shifted Tate line, with the canonical J_f(1) identification.
The trace itself is exactly the delivered sk-def-sp-trace definition, using its actual
restricted counit and its integration-normalized purity comparison.
Source: clause (3), Tr_f(Lambda) (blueprint: lem-wft-kunneth-compatibilities). -/
def traceLine (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (c : Coefficient ell) (s : SmoothDatum D)
    (R : ScalarExceptionalAdjoint (c.bundled.{u} ell) s.compactification) :
    (rightDerivedLowerShriekOfCompactification (c.obj ell) s.compactification).obj
        (c.derivedLine ell s.X.left s.dim) ⟶ unit ell c s.Y.left :=
  (rightDerivedLowerShriekOfCompactification (c.obj ell) s.compactification).map
      (sourceUnit ell c s.map s.dim).inv ≫
    (PurityTransport.smoothTrace ell D hEll c s R (unitCtf c s.Y.left)).hom

/-- The coefficient-unit identification Lambda tensor Lambda = Lambda, at degree zero.
Source: clause (3), final unit identification (blueprint: lem-wft-kunneth-compatibilities). -/
def unitMultiply (c : Coefficient ell) (X : Scheme.{u}) :
    unit ell c X ⊗ unit ell c X ≅ unit ell c X :=
  tensorIso (DerivedCategory.singleFunctorObjUnitIso _) (DerivedCategory.singleFunctorObjUnitIso _)
    ≪≫ λ_ _ ≪≫ (DerivedCategory.singleFunctorObjUnitIso _).symm

/-- Smooth traces multiply under the canonical Künneth isomorphism and canonical I.
The three supplied right-adjoint models are used through their actual adjunctions;
canonicalPurity compares each to the same normalized family, so no orientation is assumed.
Source: clause (3) (blueprint: lem-wft-kunneth-compatibilities).
Proof: step 4 expands the coefficient trace with the tensor-transpose characterization
of lem-pur-condensed-semilinear-purity-factors, giving coefficient linearity. Step 5
applies thm-pur-trace-normalization-transitivity to u followed by a with the actual
sk-thm-sf-comp-composition compositor. Step 6 applies its trace base-change identity
to b along a, identifying its exchange with beta. The source comparisons compose to
I inverse; both shifts are even, so the interchange sign is one. Step 7 uses naturality
of the a projection formula in Tr_b, then recognizes the four factors defining kappa.
The coefficient-unit projection factor is the normalized unit identification. -/
theorem kappa_trace (hEll : ell ≠ D.p) (hc : FieldCoefficient ell c) (d e : ℕ)
    [SmoothOfRelativeDimension d Q.a.hom.left] [SmoothOfRelativeDimension e Q.b.hom.left]
    (Ra : ScalarExceptionalAdjoint (c.bundled.{u} ell) Q.ca)
    (Rb : ScalarExceptionalAdjoint (c.bundled.{u} ell) Q.cb)
    (Rc : ScalarExceptionalAdjoint (c.bundled.{u} ell) Q.cc) :
    (rightDerivedLowerShriekOfCompactification (c.obj ell) Q.cc).map
          (lineProductComparison Q hEll d e).hom ≫
        traceLine D hEll c (smoothComposite Q d e) Rc =
      (kappa Q hEll hc (lineCtf D hEll c Q.X d) (lineCtf D hEll c Q.Y e)).hom ≫
        (traceLine D hEll c (smoothIndex D Q.a Q.ca d) Ra ⊗ₘ
          traceLine D hEll c (smoothIndex D Q.b Q.cb e) Rb) ≫
        (unitMultiply c Q.S.obj.left).hom := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.CompactKunneth

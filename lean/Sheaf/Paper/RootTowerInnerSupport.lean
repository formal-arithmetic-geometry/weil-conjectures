/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.Paper.RootTowerBoundaryAcyclicity
public import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
public import Sheaf.Topology.ContinuousMapCondensedRing
public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.AlgebraicGeometry.Sites.Proetale

import Sheaf.Paper.RootTowerPunctureInvariance
import Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization
import Sheaf.Paper.RootTowerCoordinateFace
import Sheaf.AlgebraicGeometry.FiniteClosedCoverResolution
import Sheaf.Paper.SNCRootLimitNormalCharts

/-!
# Inner closed support of one parameter-root tower term

Source: blueprint main-20261015, direct-image stability proof, paragraph (3),
agent-formulated inner-support calculation (blueprint: lem-sfb-root-tower-inner-support).

The helpers construct the actual unit and its geometric exchange maps. Naturality is
expressed on whole derived objects, including entire profinite-parametrized schemes.
No root-cover descent or invariants enter this statement.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.RootInnerSupport

open RootBoundary

variable (F : Type u) [NormedField F]

/-- The ambient restricted direct image, functorial in the derived module on V.
Source: direct-image proof (3), s^*Ra_*K
(blueprint: lem-sfb-root-tower-inner-support). -/
def ambient {U V S : Scheme.{u}} (a : V ⟶ U) (s : S ⟶ U)
    (K : DerivedCategory (SiteMod F V)) : DerivedCategory (SiteMod F S) :=
  (pullD F s).obj ((pushD F a).obj K)

/-- The actual closed restriction followed by closed direct image.
Closed direct image is exact, so its total derived functor is the canonical derived
interpretation of h_* in the node's displayed formula.
Source: direct-image proof (3), h_*h^*K
(blueprint: lem-sfb-root-tower-inner-support). -/
def closed {V Z : Scheme.{u}} (h : Z ⟶ V)
    (K : DerivedCategory (SiteMod F V)) : DerivedCategory (SiteMod F V) :=
  (pushD F h).obj ((pullD F h).obj K)

/-- The supported object in the node's left-hand side.
Source: direct-image proof (3), s^*Ra_*h_*h^*K
(blueprint: lem-sfb-root-tower-inner-support). -/
def supported {U V Z S : Scheme.{u}} (a : V ⟶ U) (h : Z ⟶ V) (s : S ⟶ U)
    (K : DerivedCategory (SiteMod F V)) : DerivedCategory (SiteMod F S) :=
  ambient F a s (closed F h K)

/-- The actual closed adjunction unit, pushed to U and pulled to S.
Source: direct-image proof (3), delta_P
(blueprint: lem-sfb-root-tower-inner-support). -/
def delta {U V Z S : Scheme.{u}} (a : V ⟶ U) (h : Z ⟶ V) (s : S ⟶ U)
    (K : DerivedCategory (SiteMod F V)) :
    ambient F a s K ⟶ supported F a h s K :=
  (pullD F s).map ((pushD F a).map ((derivedAdjunction F h).unit.app K))

/-- Canonical restriction of an ambient direct image along a commuting square.
The map on K is the supplied module morphism; the other arrows are exchange mates.
Source: direct-image proof (3), naturality on entire test schemes
(blueprint: lem-sfb-root-tower-inner-support). -/
def ambientMap {U V S U' V' S' : Scheme.{u}}
    (a : V ⟶ U) (s : S ⟶ U) (a' : V' ⟶ U') (s' : S' ⟶ U')
    (g : U' ⟶ U) (v : V' ⟶ V) (z : S' ⟶ S)
    (wa : v ≫ a = a' ≫ g) (ws : z ≫ s = s' ≫ g)
    (K : DerivedCategory (SiteMod F V)) (K' : DerivedCategory (SiteMod F V'))
    (m : (pullD F v).obj K ⟶ K') :
    (pullD F z).obj (ambient F a s K) ⟶ ambient F a' s' K' :=
  (RootCoordinateFace.squareUpper (coefficients F) z s' s g ws).inv.app
      ((pushD F a).obj K) ≫
    (pullD F s').map
      ((RootCoordinateFace.exchange (coefficients F) v a' a g wa).app K ≫
        (pushD F a').map m)

/-- The canonical exchange map on the closed restriction/direct-image composite.
Its construction uses the closed counit mate and exact pullback composition; no
inverse of delta and no chosen supported comparison occurs here.
Source: direct-image proof (3), closed-unit naturality under base change
(blueprint: lem-sfb-root-tower-inner-support). -/
def closedMap {V Z V' Z' : Scheme.{u}}
    (h : Z ⟶ V) (h' : Z' ⟶ V') (v : V' ⟶ V) (c : Z' ⟶ Z)
    (wh : c ≫ h = h' ≫ v)
    (K : DerivedCategory (SiteMod F V)) (K' : DerivedCategory (SiteMod F V'))
    (m : (pullD F v).obj K ⟶ K') :
    (pullD F v).obj (closed F h K) ⟶ closed F h' K' :=
  (RootCoordinateFace.exchange (coefficients F) c h' h v wh).app
      ((pullD F h).obj K) ≫
    (pushD F h').map
      ((RootCoordinateFace.squareUpper (coefficients F) c h' h v wh).inv.app K ≫
        (pullD F h').map m)

/-- The actual geometric map between supported objects in a commuting diagram.
Source: direct-image proof (3), module, parameter and profinite-family naturality
(blueprint: lem-sfb-root-tower-inner-support). -/
def supportedMap {U V Z S U' V' Z' S' : Scheme.{u}}
    (a : V ⟶ U) (h : Z ⟶ V) (s : S ⟶ U)
    (a' : V' ⟶ U') (h' : Z' ⟶ V') (s' : S' ⟶ U')
    (g : U' ⟶ U) (v : V' ⟶ V) (c : Z' ⟶ Z) (z : S' ⟶ S)
    (wa : v ≫ a = a' ≫ g) (wh : c ≫ h = h' ≫ v) (ws : z ≫ s = s' ≫ g)
    (K : DerivedCategory (SiteMod F V)) (K' : DerivedCategory (SiteMod F V'))
    (m : (pullD F v).obj K ⟶ K') :
    (pullD F z).obj (supported F a h s K) ⟶ supported F a' h' s' K' :=
  ambientMap F a s a' s' g v z wa ws (closed F h K) (closed F h' K')
    (closedMap F h h' v c wh K K' m)

/-- Naturality of a normalized supported comparison, on entire schemes.
Here alpha is the ambient boundary comparison after composition transport. The last
premise is its naturality square, supplied by boundary acyclicity for the actual module,
parameter, base-change or family map. The conclusion is the supported square for the
actual exchange map above. Both the closed-unit square and the sigma square are included.
For profinite families the primed schemes are the entire parametrized terms, so this
assertion never reduces to testing points.
Source: direct-image proof (3), last clause
(blueprint: lem-sfb-root-tower-inner-support). -/
def NaturalComparison {U V Z S : Scheme.{u}}
    (a : V ⟶ U) (h : Z ⟶ V) (s : S ⟶ U)
    (K : DerivedCategory (SiteMod F V)) (B : DerivedCategory (SiteMod F S))
    (α : ambient F a s K ≅ B) (σ : supported F a h s K ≅ B) : Prop :=
  ∀ {U' V' Z' S' : Scheme.{u}}
    (a' : V' ⟶ U') (h' : Z' ⟶ V') (s' : S' ⟶ U')
    (g : U' ⟶ U) (v : V' ⟶ V) (c : Z' ⟶ Z) (z : S' ⟶ S)
    (wa : v ≫ a = a' ≫ g) (wh : c ≫ h = h' ≫ v) (ws : z ≫ s = s' ≫ g)
    (K' : DerivedCategory (SiteMod F V')) (m : (pullD F v).obj K ⟶ K')
    (B' : DerivedCategory (SiteMod F S')) (β : (pullD F z).obj B ⟶ B')
    (α' : ambient F a' s' K' ≅ B') (σ' : supported F a' h' s' K' ≅ B'),
    delta F a' h' s' K' ≫ σ'.hom = α'.hom →
    ambientMap F a s a' s' g v z wa ws K K' m ≫ α'.hom =
      (pullD F z).map α.hom ≫ β →
    ((pullD F z).map (delta F a h s K) ≫
        supportedMap F a h s a' h' s' g v c z wa wh ws K K' m =
      ambientMap F a s a' s' g v z wa ws K K' m ≫ delta F a' h' s' K') ∧
    (supportedMap F a h s a' h' s' g v c z wa wh ws K K' m ≫ σ'.hom =
      (pullD F z).map σ.hom ≫ β)

variable (p : ℕ) {R : Type u} [CommRing R] {r : ℕ} (t : Fin r → R)

/-- The base open obtained by inverting precisely the outer parameters.
Source: direct-image proof (3), V (blueprint: lem-sfb-root-tower-inner-support). -/
def outerOpen (out : Finset (Fin r)) : (Spec (.of R)).Opens :=
  PrimeSpectrum.basicOpen (∏ i ∈ out, t i)

/-- The full boundary complement on the base.
Source: direct-image proof (3), W (blueprint: lem-sfb-root-tower-inner-support). -/
def allOpen : (Spec (.of R)).Opens := PrimeSpectrum.basicOpen (∏ i, t i)

/-- Derived N_P[0] from the existing punctured root-tower test construction.
Source: direct-image proof (3), N_P (blueprint: lem-sfb-root-tower-inner-support). -/
abbrev puncturedModule (N : SiteMod F (tower p t)) (P : Profinite.{u}) :=
  RootBoundary.pulledOpenModule F p t N P

/-- The actual inner-support term K_P on the outer open.
Source: direct-image proof (3), K_P (blueprint: lem-sfb-root-tower-inner-support). -/
def term {V : Scheme.{u}} (P : Profinite.{u})
    (f : (test (puncture p t) P).left ⟶ V) (N : SiteMod F (tower p t)) :=
  (pushD F f).obj (puncturedModule F p t N P)

/-- The canonical derived-composition identification with the boundary theorem's source.
The equality f followed by a = v_P fixes the structural factorization through the open;
it does not supply an arbitrary map in place of that factorization.
Source: direct-image proof (3), canonical composition inserted in the normalization
(blueprint: lem-sfb-root-tower-inner-support). -/
def composition {V : Scheme.{u}} (a : V ⟶ Spec (.of R))
    (N : SiteMod F (tower p t)) (P : Profinite.{u})
    (f : (test (puncture p t) P).left ⟶ V) (wf : f ≫ a = vP p t P) :
    ambient F a (stratumInclusion t) (term F p t P f N) ≅ openSource F p t N P :=
  (pullD F (stratumInclusion t)).mapIso
    ((pushComp F f a).app (puncturedModule F p t N P) ≪≫
      eqToIso (congrArg (fun v ↦ (pushD F v).obj (puncturedModule F p t N P)) wf))

/-- One coefficient's supported comparison with the specified restriction-of-sections map.
The inner set is the complement of out and is nonempty. V is the specified principal
open; the reduced closed immersion h has precisely the complementary support of W.
Every normalized boundary comparison is allowed and determines sigma by the displayed
unit equation; naturality is expressed with actual geometric exchange maps.
Source: direct-image proof (3), the isomorphism and all its compatibility clauses
(blueprint: lem-sfb-root-tower-inner-support). -/
def Assertion (E : Type u) [Field E] [Algebra E F] : Prop :=
  ∀ (out : Finset (Fin r)), (Finset.univ \ out).Nonempty →
  ∀ (V Z : Scheme.{u}) (a : V ⟶ Spec (.of R)) [IsOpenImmersion a]
    (h : Z ⟶ V) [IsClosedImmersion h] [IsReduced Z],
    Set.range a = (outerOpen t out : Set (Spec (.of R))) →
    Set.range h = {x : V | a x ∉ (allOpen t : Set (Spec (.of R)))} →
  ∀ (M : Type u) [AddCommGroup M] [Module E M] [FiniteDimensional E M]
    (N : SiteMod F (tower p t)), IsLisseCoefficientModule (coefficients F) N →
  ∀ (e : (CondensedRing.upperStar (coefficients F) (boundary p t)).obj N ≅
      (pointPull F (stratumScheme t)).obj (model F E M)) (P : Profinite.{u})
    (f : (test (puncture p t) P).left ⟶ V) (wf : f ≫ a = vP p t P),
    (∃ α : openSource F p t N P ≅ target F t (model F E M) P,
      Normalization F p t N (model F E M) e P α) ∧
    ∀ α : openSource F p t N P ≅ target F t (model F E M) P,
      Normalization F p t N (model F E M) e P α →
      ∃ σ : supported F a h (stratumInclusion t) (term F p t P f N) ≅
          target F t (model F E M) P,
        delta F a h (stratumInclusion t) (term F p t P f N) ≫ σ.hom =
          (composition F p t a N P f wf).hom ≫ α.hom ∧
        NaturalComparison F a h (stratumInclusion t) (term F p t P f N)
          (target F t (model F E M) P) (composition F p t a N P f wf ≪≫ α) σ

/-- The inner closed-support comparison for E and its normed algebraic closure.
Source: blueprint main-20261015, direct-image proof (3), agent-formulated input
(blueprint: lem-sfb-root-tower-inner-support).

Proof: (1) lem-sfb-root-tower-puncture-invariance first removes the inner punctures
and then the outer punctures. The inverse actual open units and
lem-sfb-derived-composition-adjunction-normalization identify Ra_*K_P with the
unpunctured tower image H_P, preserving the adjunction normalization.
(2) lem-sfb-root-tower-coordinate-face computes each nonempty inner intersection.
The regular-intersection condition in def-trf-strict-normal-crossings-boundary permits
puncture invariance on its remaining outer coordinates. The coordinate-face adjunct
formula identifies its pushed closed unit with the actual unit on H_P.
(3) The inner divisors cover Z. lem-sfb-snc-root-limit-normal-charts with no roots
makes their pro-etale pullbacks reduced, so their maps factor through reduced Z.
Their complementary opens are quasi-compact principal opens. Apply
lem-sfb-finite-closed-cover-resolution to the bounded-below K_P; its augmentation is
the actual closed unit. Apply the exact triangulated functor s^*Ra_* to its finite total.
(4) Every nonempty inner intersection contains S. The invertible closed counit from
lem-weil-pbc-proetale-ringed-open-closed and the triangle identity identify its restricted
unit and all face maps with identities on s^*H_P.
(5) Choose one inner index. Inserting it in alternating cochains contracts the augmented
simplex complex. Apply this on each cohomology sheaf of the finite filtration of the
total complex, rather than assuming a chain-level identification of derived terms.
The first page is exact and the finite filtration implies the augmentation is invertible.
Thus delta is invertible. The choice of index is used only to prove this fact.
(6) lem-sfb-root-tower-boundary-acyclicity supplies the normalized alpha with the same
extension and boundary identification. Put sigma = delta inverse followed by the
composition comparison and alpha. This is the required derived isomorphism and its
unit equation is the stated normalization.
(7) Naturality of the unit and exchange pasting give the first square in
NaturalComparison. Cancel the pulled invertible delta in this square and the boundary
comparison's naturality square to obtain the sigma square. Use the actual parameter
restriction maps, extension morphisms, pro-etale base changes, and entire Q-parametrized
family action maps. No evaluation at points is involved. Empty out leaves the identity
outer open; one inner branch gives a one-term resolution. Empty S and rank zero give
zero objects. No root nerve or group invariants are computed. -/
theorem rootTower_inner_support
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (k : Type u) [Field k] [CharP k p]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (Ω : Type u) [NormedField Ω] [NormedAlgebra E Ω] [IsAlgClosure E Ω]
    (Y : Scheme.{u}) (y : Y ⟶ Spec (.of k)) [LocallyOfFiniteType y] [QuasiCompact y]
    [IsSeparated y] (hY : IsRegularScheme Y)
    (A : Type u) [CommRing A] (b : Spec (.of A) ⟶ Y) [Etale b]
    (r : ℕ) (s : Fin r → A) (H : (Spec (.of A)).IdealSheafData)
    (hH : IsStrictNormalCrossingsBoundary H)
    (hproduct : H = Scheme.IdealSheafData.ofIdealTop
      (Ideal.span {(Scheme.ΓSpecIso (CommRingCat.of A)).inv (∏ i, s i)}))
    (hbranches : Set.range (fun i : Fin r ↦ PrimeSpectrum.zeroLocus ({s i} : Set A)) =
      Set.image (Set.image Subtype.val) (irreducibleComponents (H.support : Set (Spec (.of A)))))
    (R : Type u) [CommRing R]
    (a : A →+* R) [WeaklyEtale (Spec.map (CommRingCat.ofHom a))] :
    Assertion E p (fun i ↦ a (s i)) E ∧ Assertion Ω p (fun i ↦ a (s i)) E := by
  sorry

end AlgebraicGeometry.ProEtale.RootInnerSupport

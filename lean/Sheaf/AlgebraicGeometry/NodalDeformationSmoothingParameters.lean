/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q107
-/
module

public import Sheaf.AlgebraicGeometry.MarkedSchemeLifts
public import Sheaf.RingTheory.MarkedFlatAlgebraDeformations
public import Sheaf.AlgebraicGeometry.StableFiberCurve
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.Modules.Ext
public import WeilConjectures.AlgebraicGeometry.Modules.Linear
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Sheaf.RingTheory.CompleteLocalSmoothPowerSeries
import Sheaf.AlgebraicGeometry.CoherentZeroDimensionalSupport
import Sheaf.AlgebraicGeometry.LciCotangentPresentation
import Sheaf.AlgebraicGeometry.MarkedNodalInfinitesimalFields
import Sheaf.AlgebraicGeometry.NodalCurveNormalizationEuler
import Sheaf.AlgebraicGeometry.NodalPointLocalCriterion
import Sheaf.AlgebraicGeometry.SheafExtCoherent
import Sheaf.AlgebraicGeometry.SheafExtStalkLocalization
import Sheaf.AlgebraicGeometry.StablePointedCurve
import Sheaf.Paper.ExtSheafToGlobalSpectralSequence
import Sheaf.RingTheory.SeparableClosedPointFormalPresentation
import Sheaf.SixFunctors.TraceFormula.NodalFamilyFittingSingular
import WeilConjectures.AlgebraicGeometry.AffineMorphismCohomologyEdge
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
import WeilConjectures.AlgebraicGeometry.ThickeningAffineScheme
import WeilConjectures.AlgebraicGeometry.UnramifiedQuasiFinite
import WeilConjectures.RingTheory.CompletionFiniteExtension
import WeilConjectures.RingTheory.PowerSeriesFullCoordinatesField
import WeilConjectures.RingTheory.RegularSequenceKoszulRegular
import WeilConjectures.RingTheory.RelativeGlobalCompleteIntersectionLocalRegularSequence

/-! # Local-to-global node smoothing parameters

Source: Deligne--Mumford, The irreducibility of the space of curves of given genus,
Section 1, Lemmas 1.3--1.4, Proposition 1.5, Theorem 1.6 and Corollary 1.9,
printed pp.79--83, equal characteristic
(blueprint: lem-sfb-nodal-deformation-smoothing-parameters).

The deformation sets use the existing marked flat lifts and marked flat algebra
factorizations. Transport is specified by cartesian squares and tensor products.
Thus the naturality conditions below specify actual base change on isomorphism
classes without choosing representatives or a second deformation functor.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ArtinDeformation

namespace AlgebraicGeometry.NodalDeformation

variable {k : Type u} [Field k]

/-- Completion at the maximal ideal of a local ring. Source: Deligne--Mumford §1
(blueprint: lem-sfb-nodal-deformation-smoothing-parameters). -/
abbrev Completed (T : Type u) [CommRing T] [IsLocalRing T] :=
  AdicCompletion (IsLocalRing.maximalIdeal T) T

/-- The split ordinary node. Source: Deligne--Mumford p.81, node example
(blueprint: lem-sfb-nodal-deformation-smoothing-parameters). -/
abbrev Node (k : Type u) [Field k] :=
  MvPowerSeries (Fin 2) k ⧸ Ideal.span
    {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) * MvPowerSeries.X 1}

/-- The scalar map on a stalk over an affine base. Source: Deligne--Mumford §1
(blueprint: lem-sfb-nodal-deformation-smoothing-parameters). -/
def stalkScalar {R : Type u} [CommRing R] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of R)) (y : Y) : R →+* Y.presheaf.stalk y :=
  (StructureSheaf.toStalk R (f y) ≫ f.stalkMap y).hom

/-- Marked proper flat deformations, using the existing category of flat lifts.
Source: Deligne--Mumford p.79 (blueprint: lem-sfb-nodal-deformation-smoothing-parameters). -/
abbrev Proper {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) (R : TestCategory k k) :=
  {Y : SchemeDeformation.Lift f (Spec.map (CommRingCat.ofHom (residue R).toRingHom)) //
    IsProper Y.projection}

/-- The actual marked isomorphism classes; all isomorphisms fix the special fibre.
Source: Deligne--Mumford p.79 (blueprint: lem-sfb-nodal-deformation-smoothing-parameters). -/
def Global {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) (R : TestCategory k k) :=
  Quot (fun Y Z : Proper f R ↦ Nonempty (Y.val ≅ Z.val))

/-- The marked class of a proper deformation. Source: Deligne--Mumford §1
(blueprint: lem-sfb-nodal-deformation-smoothing-parameters). -/
def globalClass {C : Scheme.{u}} {f : C ⟶ Spec (.of k)} {R : TestCategory k k}
    (Y : Proper f R) : Global f R := Quot.mk _ Y

/-- Base change on proper marked isomorphism classes is specified by a cartesian square.
Source: Deligne--Mumford p.79 (blueprint: lem-sfb-nodal-deformation-smoothing-parameters). -/
def GlobalBC {C : Scheme.{u}} {f : C ⟶ Spec (.of k)} {R S : TestCategory k k}
    (p : R ⟶ S) (a : Global f R) (b : Global f S) : Prop :=
  ∃ (Y : Proper f R) (Z : Proper f S), globalClass Y = a ∧ globalClass Z = b ∧
    ∃ q : Z.val.space ⟶ Y.val.space,
      SchemeDeformation.IsBaseChange (Spec.map (CommRingCat.ofHom (map p).toRingHom))
        Y.val Z.val q

/-- Complete local marked algebra deformations, with the maximal-ideal-adic topology.
Source: Deligne--Mumford p.81 (blueprint: lem-sfb-nodal-deformation-smoothing-parameters). -/
abbrev LocalObject (R : TestCategory k k) :=
  {Q : Algebra.FlatDeformation.Groupoid (Node k) R //
    IsNoetherianRing (Algebra.FlatDeformation.algebra Q) ∧
      ∃ h : IsLocalRing (Algebra.FlatDeformation.algebra Q),
        IsAdicComplete (@IsLocalRing.maximalIdeal _ _ h) (Algebra.FlatDeformation.algebra Q)}

/-- Isomorphism classes of complete local deformations with their special-fibre marking.
An isomorphism of local rings is automatically adically continuous.
Source: Deligne--Mumford p.81 (blueprint: lem-sfb-nodal-deformation-smoothing-parameters). -/
def Local (R : TestCategory k k) :=
  Quot (fun Q Q' : LocalObject R ↦ Nonempty (Q.val ≅ Q'.val))

/-- Class of a complete marked local deformation. Source: Deligne--Mumford §1
(blueprint: lem-sfb-nodal-deformation-smoothing-parameters). -/
def localClass {R : TestCategory k k} (Q : LocalObject R) : Local R := Quot.mk _ Q

/-- Base change on local deformations uses the actual marked tensor comparison.
Source: Deligne--Mumford p.81 (blueprint: lem-sfb-nodal-deformation-smoothing-parameters). -/
def LocalBC {R S : TestCategory k k} (p : R ⟶ S) (a : Local R) (b : Local S) : Prop :=
  ∃ (Q : LocalObject R) (Q' : LocalObject S), localClass Q = a ∧ localClass Q' = b ∧
    ∃ j : Algebra.FlatDeformation.algebra Q.val →ₐ[k] Algebra.FlatDeformation.algebra Q'.val,
      Algebra.FlatDeformation.IsBaseChange p Q.val Q'.val j

/-- The equation xy=s and its coefficient ring. Source: Deligne--Mumford p.81
(blueprint: lem-sfb-nodal-deformation-smoothing-parameters). -/
abbrev Equation (R : Type u) [CommRing R] (s : R) :=
  MvPowerSeries (Fin 2) R ⧸ Ideal.span
    {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) * MvPowerSeries.X 1 - MvPowerSeries.C s}

/-- A node equation with its exact coefficient map and reduction marking.
Source: Deligne--Mumford p.81 (blueprint: lem-sfb-nodal-deformation-smoothing-parameters). -/
def HasEquation {R : TestCategory k k} (Q : LocalObject R) (s : ring R) : Prop :=
  ∃ e : Algebra.FlatDeformation.algebra Q.val ≃+* Equation (ring R) s,
    (∀ a : ring R, e (Algebra.FlatDeformation.scalar Q.val a) =
      Ideal.Quotient.mk _ (MvPowerSeries.C a)) ∧
    ∀ a : MvPowerSeries (Fin 2) (ring R),
      Algebra.FlatDeformation.marking Q.val (e.symm (Ideal.Quotient.mk _ a)) =
        Ideal.Quotient.mk _ (MvPowerSeries.map (residue R).toRingHom a)

/-- The restriction to a node is the completed local ring, including its scalar and
special-fibre maps. The latter is fixed at every ideal-power quotient.
Source: Deligne--Mumford pp.79--81
(blueprint: lem-sfb-nodal-deformation-smoothing-parameters). -/
def IsRestriction {C : Scheme.{u}} {f : C ⟶ Spec (.of k)} {R : TestCategory k k}
    (q : C) (eq : Completed (C.presheaf.stalk q) ≃+* Node k)
    (Y : Proper f R) (Q : LocalObject R) : Prop :=
  ∃ e : Algebra.FlatDeformation.algebra Q.val ≃+*
      Completed (Y.val.space.presheaf.stalk (Y.val.marking q)),
    (∀ a : ring R, e (Algebra.FlatDeformation.scalar Q.val a) =
      algebraMap _ _ (stalkScalar Y.val.projection (Y.val.marking q) a)) ∧
    Algebra.FlatDeformation.IsCompletionMap
      (IsLocalRing.maximalIdeal (Y.val.space.presheaf.stalk (Y.val.marking q)))
      (IsLocalRing.maximalIdeal (C.presheaf.stalk q))
      (Y.val.marking.stalkMap q).hom
      (eq.symm.toRingHom.comp ((Algebra.FlatDeformation.marking Q.val).toRingHom.comp
        e.symm.toRingHom))

/-- Relative formal smoothness tests every compatible pair across every square-zero
Artinian surjection. Source: Deligne--Mumford Proposition 1.5
(blueprint: lem-sfb-nodal-deformation-smoothing-parameters). -/
def RestrictionSmooth {C : Scheme.{u}} {f : C ⟶ Spec (.of k)} {d : ℕ}
    (ρ : ∀ R : TestCategory k k, Global f R → (Fin d → Local R)) : Prop :=
  ∀ (R R' : TestCategory k k) (p : R' ⟶ R),
    Function.Surjective (map p) → (RingHom.ker (map p).toRingHom) ^ 2 = ⊥ →
    ∀ (a : Global f R) (b : Fin d → Local R'),
      (∀ i : Fin d, LocalBC p (b i) (ρ R a i)) →
      ∃ a' : Global f R', GlobalBC p a' a ∧ ρ R' a' = b

/-- A local hull, including the xy=s family, naturality, the compatible lifting property,
and tangent bijectivity. No uniqueness of the node parameter is imposed.
Source: Deligne--Mumford p.81 (blueprint: lem-sfb-nodal-deformation-smoothing-parameters). -/
def IsNodeHull (B : CompleteLocalAlgebra k k)
    (eB : B.ring ≃ₐ[k] MvPowerSeries (Fin 1) k)
    (H : ∀ R : TestCategory k k, LocalMap B R → Local R) : Prop :=
  (∀ (R : TestCategory k k) (b : LocalMap B R),
    ∃ Q : LocalObject R, localClass Q = H R b ∧
      HasEquation Q (b.hom (eB.symm (MvPowerSeries.X 0)))) ∧
  (∀ (R S : TestCategory k k) (p : R ⟶ S) (b : LocalMap B R) (c : LocalMap B S),
    (map p).comp b.hom = c.hom → LocalBC p (H R b) (H S c)) ∧
  (∀ (R R' : TestCategory k k) (p : R' ⟶ R),
    Function.Surjective (map p) → (RingHom.ker (map p).toRingHom) ^ 2 = ⊥ →
    ∀ (b : LocalMap B R) (a' : Local R'), LocalBC p a' (H R b) →
      ∃ b' : LocalMap B R', (map p).comp b'.hom = b.hom ∧ H R' b' = a') ∧
  Function.Bijective (H (squareZeroTest (R := k) (k := k) k))


/-- All smoothing conclusions, with the chosen maps from the local hulls recorded.
The global equivalences are natural because the base-change relation is precisely
composition of the representing local maps. The local hull is only smooth and tangent
bijective. Source: Deligne--Mumford §1, pp.79--83
(blueprint: lem-sfb-nodal-deformation-smoothing-parameters). -/
structure Smoothing {C : Scheme.{u}} [C.Over (Spec (.of k))]
    [HasExt.{u} C.Modules] (d N : ℕ) (q : Fin d → C)
    (eq : ∀ i : Fin d, Completed (C.presheaf.stalk (q i)) ≃+* Node k) where
  ring : CompleteLocalAlgebra k k
  represents : ∀ R : TestCategory k k, LocalMap ring R ≃ Global (C ↘ Spec (.of k)) R
  natural : ∀ (R S : TestCategory k k) (p : R ⟶ S)
    (a : LocalMap ring R) (b : LocalMap ring S),
    GlobalBC p (represents R a) (represents S b) ↔ (map p).comp a.hom = b.hom
  unobstructed : ∀ (R R' : TestCategory k k) (p : R' ⟶ R),
    Function.Surjective (map p) → (RingHom.ker (map p).toRingHom) ^ 2 = ⊥ →
    ∀ a : Global (C ↘ Spec (.of k)) R,
      ∃ a' : Global (C ↘ Spec (.of k)) R', GlobalBC p a' a
  tangent : Global (C ↘ Spec (.of k)) (squareZeroTest (R := k) (k := k) k) ≃
    Scheme.Modules.Ext (C ↘ Spec (.of k)).relativeDifferentials (Scheme.Modules.unit C) 1
  tangent_zero : ∀ Y : Proper (C ↘ Spec (.of k)) (squareZeroTest (R := k) (k := k) k),
    SchemeDeformation.IsTrivial (C ↘ Spec (.of k)) (ModuleCat.of k k) Y.val ↔
      tangent (globalClass Y) = 0
  tangent_add : ∀ Y Z W : Proper (C ↘ Spec (.of k))
      (squareZeroTest (R := k) (k := k) k),
    SchemeDeformation.IsSum (C ↘ Spec (.of k)) (ModuleCat.of k k) Y.val Z.val W.val →
      tangent (globalClass W) = tangent (globalClass Y) + tangent (globalClass Z)
  tangent_smul : ∀ (c : k) (Y Z : Proper (C ↘ Spec (.of k))
      (squareZeroTest (R := k) (k := k) k)),
    (∃ j : Z.val.space ⟶ Y.val.space,
      SchemeDeformation.IsBaseChange
        (SchemeDeformation.directionMap
          (ModuleCat.ofHom (c • (LinearMap.id : k →ₗ[k] k)))) Y.val Z.val j) →
      tangent (globalClass Z) = c • tangent (globalClass Y)
  restriction : ∀ R : TestCategory k k,
    Global (C ↘ Spec (.of k)) R → (Fin d → Local R)
  completion : ∀ (R : TestCategory k k) (Y : Proper (C ↘ Spec (.of k)) R) (i : Fin d),
    ∃ Q : LocalObject R, localClass Q = restriction R (globalClass Y) i ∧
      IsRestriction (q i) (eq i) Y Q
  restriction_natural : ∀ (R S : TestCategory k k) (p : R ⟶ S)
    (a : Global (C ↘ Spec (.of k)) R) (b : Global (C ↘ Spec (.of k)) S),
    GlobalBC p a b → ∀ i : Fin d, LocalBC p (restriction R a i) (restriction S b i)
  restriction_smooth : RestrictionSmooth restriction
  localRing : CompleteLocalAlgebra k k
  localCoordinate : localRing.ring ≃ₐ[k] MvPowerSeries (Fin 1) k
  localHull : ∀ R : TestCategory k k, LocalMap localRing R → Local R
  hull : IsNodeHull localRing localCoordinate localHull
  localTangent : Local (squareZeroTest (R := k) (k := k) k) ≃ k
  localTangent_coordinate : ∀ b : LocalMap localRing (squareZeroTest (R := k) (k := k) k),
    localTangent (localHull _ b) =
      (b.hom (localCoordinate.symm (MvPowerSeries.X 0))).snd
  tangentRestriction :
    Scheme.Modules.Ext (C ↘ Spec (.of k)).relativeDifferentials
      (Scheme.Modules.unit C) 1 →ₗ[k] (Fin d → k)
  tangentRestriction_surjective : Function.Surjective tangentRestriction
  tangentRestriction_completion : ∀ a : Global (C ↘ Spec (.of k))
      (squareZeroTest (R := k) (k := k) k),
    ∀ i : Fin d, tangentRestriction (tangent a) i = localTangent (restriction _ a i)
  nodeBound : d ≤ N
  relativeTangentDimension : Module.finrank k tangentRestriction.ker = N - d
  hullBase : CompleteLocalAlgebra k k
  hullCoordinates : hullBase.ring ≃ₐ[k] MvPowerSeries (Fin d) k
  hullMap : hullBase.ring →ₐ[k] ring.ring
  smoothHullMap : ∀ (R R' : TestCategory k k) (p : R' ⟶ R),
    Function.Surjective (map p) → (RingHom.ker (map p).toRingHom) ^ 2 = ⊥ →
    ∀ (a : LocalMap ring R) (b : LocalMap hullBase R'),
      a.hom.comp hullMap = (map p).comp b.hom →
      ∃ a' : LocalMap ring R', (map p).comp a'.hom = a.hom ∧ a'.hom.comp hullMap = b.hom
  powerSeries : ring.ring ≃ₐ[k] MvPowerSeries (Fin (N - d)) (MvPowerSeries (Fin d) k)
  powerSeries_base : ∀ b : hullBase.ring,
    powerSeries (hullMap b) = MvPowerSeries.C (hullCoordinates b)
  powerSeries_continuous :
    @Continuous ring.ring _ (IsLocalRing.maximalIdeal ring.ring).adicTopology
      (IsLocalRing.maximalIdeal _).adicTopology powerSeries
  powerSeries_inverse_continuous :
    @Continuous _ ring.ring (IsLocalRing.maximalIdeal _).adicTopology
      (IsLocalRing.maximalIdeal ring.ring).adicTopology powerSeries.symm
  nodeMap : Fin d → (localRing.ring →ₐ[k] ring.ring)
  nodeMap_coordinates : ∀ (i : Fin d) (b : localRing.ring),
    powerSeries (nodeMap i b) = MvPowerSeries.C
      (MvPowerSeries.rename (fun _ : Fin 1 ↦ i) (localCoordinate b))
  nodeMap_restriction : ∀ (R : TestCategory k k) (a : LocalMap ring R) (i : Fin d),
    ∃ b : LocalMap localRing R, b.hom = a.hom.comp (nodeMap i) ∧
      restriction R (represents R a) i = localHull R b
  effective : ∀ (Y : Scheme.{u}) (g : Y ⟶ Spec (.of ring.ring))
    [LocallyOfFinitePresentation g] (j : C ⟶ Y), IsProper g → Flat g →
    HasNodalGeometricFibres g →
    IsPullback j (C ↘ Spec (.of k)) g
      (Spec.map (CommRingCat.ofHom (ring.residueEquiv.toAlgHom.comp
        (Ideal.Quotient.mkₐ k (IsLocalRing.maximalIdeal ring.ring))).toRingHom)) →
    (∀ (R : TestCategory k k) (a : LocalMap ring R) (Z : Proper (C ↘ Spec (.of k)) R)
      (v : Z.val.space ⟶ Y),
      IsPullback v Z.val.projection g (Spec.map (CommRingCat.ofHom a.hom.toRingHom)) →
      Z.val.marking ≫ v = j → globalClass Z = represents R a) →
    (∀ i : Fin d, ∃ e : Completed (Y.presheaf.stalk (j (q i))) ≃+*
        Equation ring.ring (hullMap (hullCoordinates.symm (MvPowerSeries.X i))),
      ∀ a : ring.ring,
        e (algebraMap _ _ (stalkScalar g (j (q i)) a)) =
          Ideal.Quotient.mk _ (MvPowerSeries.C a)) ∧
    ∀ (K : Type u) [Field K] (a : ring.ring →+* K),
      Smooth (pullback.snd g (Spec.map (CommRingCat.ofHom a))) ↔
        ∀ i : Fin d, a (hullMap (hullCoordinates.symm (MvPowerSeries.X i))) ≠ 0

/-- Local-to-global smoothing with independent node parameters; stable unpointed curves
have no infinitesimal automorphisms and tangent dimension 3g-3 in every characteristic.

Source: Deligne--Mumford §1, Lemmas 1.3--1.4, Proposition 1.5, Theorem 1.6,
Corollary 1.9, pp.79--83 (equal characteristic)
(blueprint: lem-sfb-nodal-deformation-smoothing-parameters).

Proof:
1. The nodal local criterion gives local complete-intersection presentations. The
regular-sequence and Koszul-regularity lemmas make the cotangent presentation valid.
On the smooth locus its augmentation is an isomorphism; at nodes its differential is
injective since the curve is reduced and generically smooth. Thus L equals Omega[0].
2. Apply lem-sfb-proper-scheme-deformation-hull. Vanishing derivations upgrades the
hull to prorepresentation. Lem-sfb-isolated-lci-curve-unobstructed lifts every Artinian
extension; properness reflects across nilpotent base change. The complete-local smooth
power-series theorem gives an absolutely smooth representing ring with Ext tangent.
3. By lem-sfb-formal-hypersurface-deformation-presentation, deform a node as xy-s+g.
Over a small kernel J, write g=c+xa+yb. The coordinate change x+b,y+a removes the mixed
terms since J squared is zero; replace s by s-c. Induct along small extensions. The
first-order cokernel k[[x,y]]/(xy,x,y) is k, proving the local hull assertion.
4. Use the isolated-curve two-affine cover. Affine thickening, the completed isolated
affine comparison and smooth-open gluing lift a prescribed global deformation with
all its prescribed node completions. Nilpotent properness reflection makes it proper.
Finite type over the Noetherian Artinian base implies finite presentation.
5. The completed differential resolution is 0 -> B -> B squared -> Omega -> 0,
with first map a -> (ay,ax). Dualizing gives local Ext-one k and higher Ext zero.
Faithful flatness of completion, coherent sheaf Ext and its stalk formula descend this.
6. The sheaf-Ext spectral sequence, cohomology vanishing above dimension one and
zero-dimensional-support vanishing give 0 -> H-one(T) -> Ext-one -> k^d -> 0 and
Ext-two zero. This edge map is restriction followed by completion, so the relative
tangent dimension is N-d and d is at most N.
7. Choose compatible representatives of the universal classes at all Artinian levels.
The hypersurface presentation gives compatible node equations xy-s_i. Their linear
classes are independent by step 6. Extend to a cotangent basis and apply the full
power-series-coordinate theorem; this gives the displayed relative presentation.
8. For a stable curve, the marked nodal vector-field theorem with no markings gives
zero infinitesimal automorphisms: every normalized component has 2g_a-2+b_a positive.
The elementary correspondence alpha=1+epsilon D identifies these with derivations.
9. Completed normalization and local derivation descent identify the tangent sheaf
with the pushforward of normalized vector fields vanishing at both branches.
10. Affine normalization cohomology, canonical degree and Riemann--Roch give
minus chi(T)=sum(3g_a-3)+2d. The normalization Euler formula makes this 3g-3-d.
Step 8 kills H-zero; adding the d local tangent directions gives N=3g-3.
11. For an effective nodal proper family, the first-Fitting singular subscheme is
proper and unramified, hence quasi-finite and finite. At each node its completed
ring is A/(s_i), since the relative Jacobian ideal of xy-s_i is (x,y).
12. Completion of finite modules and the complete local product decomposition
identify its finite algebra with the product of A/(s_i). Its image is exactly the
union V(s_i). The Fitting singular locus commutes with base change, proving precisely
the discriminant assertion. The empty product covers d=0. -/
theorem exists_smoothing (k : Type u) [Field k] [IsAlgClosed k]
    (C : Scheme.{u}) [C.Over (Spec (.of k))] [ConnectedSpace C] [IsReduced C]
    [IsHProjective (C ↘ Spec (.of k))] [HasExt.{u} C.Modules]
    (hdim : topologicalKrullDim C = 1) (d : ℕ) (q : Fin d → C)
    (hq : Function.Injective q)
    (hsmooth : ∀ x : C, x ∉ Set.range q →
      ∃ U : C.Opens, x ∈ U ∧ Smooth (U.ι ≫ (C ↘ Spec (.of k))))
    (eq : ∀ i : Fin d, Completed (C.presheaf.stalk (q i)) ≃+* Node k)
    (eq_scalar : ∀ (i : Fin d) (a : k),
      eq i (algebraMap _ _ (stalkScalar (C ↘ Spec (.of k)) (q i) a)) = algebraMap k _ a) :
    (Subsingleton ((C ↘ Spec (.of k)).relativeDifferentials ⟶ Scheme.Modules.unit C) →
      FiniteDimensional k
        (Scheme.Modules.Ext (C ↘ Spec (.of k)).relativeDifferentials (Scheme.Modules.unit C) 1) ∧
      Nonempty (Smoothing d
        (Module.finrank k (Scheme.Modules.Ext (C ↘ Spec (.of k)).relativeDifferentials
          (Scheme.Modules.unit C) 1)) q eq)) ∧
    (∀ (g : ℕ) (hg : 2 ≤ g)
      (M : StablePointedModuli.Fiber (Spec (.of k)) g 0 (Over.mk (𝟙 _))),
      Nonempty (StablePointedModuli.fiberCurve M ≅ Over.mk (C ↘ Spec (.of k))) →
      Subsingleton ((C ↘ Spec (.of k)).relativeDifferentials ⟶ Scheme.Modules.unit C) ∧
        Module.finrank k
          (Scheme.Modules.Ext (C ↘ Spec (.of k)).relativeDifferentials
            (Scheme.Modules.unit C) 1) = 3 * g - 3) := by
  sorry

end AlgebraicGeometry.NodalDeformation

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TwistedPullbackTowerDomainDefinitions
import WeilConjectures.AlgebraicGeometry.TwistedPullbackTowerBounds
import WeilConjectures.AlgebraicGeometry.TwistedPullbackTowerOrigins
import WeilConjectures.AlgebraicGeometry.TowerCompactSupportProjectionFormula
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantModuleConstructibility
import Mathlib.FieldTheory.Finite.Basic
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionGeneral
/-! # Twisted pullback bounds and the tower projection domain

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-tower-geometric/
sk-prop-sp-tower-geometric-gamma.proof.md, paragraph (2)
(blueprint: lem-sp-twisted-pullback-tower-domain).

Natural indices n denote the positive exponents n+1. The published section-preserving
realization is an equivalence of ordinary derived categories of strict varying-ring
towers. P uses the published ordered tensor presentation of the Tate twist and shift.
Only definitions from the gamma module are used; its purity theorem is not an input.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTwistedTowerDomain

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

private theorem support_of_torAmplitude (X : Scheme.{u}) (A : Type u) [CommRing A]
    (K : proEtaleDerivedCategory X A) (a b : ℤ)
    (h : HasProEtaleTorAmplitude X A K a b) :
    proEtaleCohomologicalSupport K ⊆ Set.Icc a b := by
  classical
  let R : Sheaf (ProEt.topology X) CommRingCat.{u + 1} := proEtaleConstantRing X A
  let C := SheafOfModules.{u + 1}
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{u} _
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{u + 1, u, u + 1} R
  let := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} R
  have := SheafOfModules.tensorPreadditive.{u + 1, u, u + 1} R
  have : (DerivedCategory.Q (C := C)).EssSurj :=
    Localization.essSurj _ (HomologicalComplex.quasiIso C (.up ℤ))
  let L := (DerivedCategory.Q (C := C)).objPreimage K
  let e : DerivedCategory.Q.obj L ≅ K :=
    (DerivedCategory.Q (C := C)).objObjPreimageIso K
  obtain ⟨P, f, hP, _, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionGeneral.{u + 1, u} (R := R) L
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso C f).2 hf
  let et : AlgebraicGeometry.Scheme.derivedTensor X A L
      ((HomologicalComplex.single C (.up ℤ) 0).obj (MonoidalCategory.tensorUnit C))
      P f hf hP ≅ K :=
    DerivedCategory.Q.mapIso (HomologicalComplex.rightUnitor P) ≪≫
      asIso (DerivedCategory.Q.map f) ≪≫ e
  intro i hi
  by_contra hout
  have hoff : i < a ∨ b < i := by
    change ¬ (a ≤ i ∧ i ≤ b) at hout
    omega
  have hz := h.2 L P ⟨e⟩ f hf hP (MonoidalCategory.tensorUnit C) i hoff
  exact hi (hz.of_iso ((DerivedCategory.homologyFunctor C i).mapIso et.symm))

private theorem tor_iso (T : Scheme.{u}) (A : Type u) [CommRing A]
    {M N : proEtaleDerivedCategory T A} (e : M ≅ N) (a z : ℤ)
    (h : HasProEtaleTorAmplitude T A M a z) : HasProEtaleTorAmplitude T A N a z := by
  refine ⟨h.1, ?_⟩
  intro L P hL f hf hP Q i hi
  obtain ⟨eL⟩ := hL
  exact h.2 L P ⟨eL ≪≫ e.symm⟩ f hf hP Q i hi

private theorem finite_ctf_iso (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    {M N : proEtaleDerivedCategory T A} (e : M ≅ N)
    (h : spFiniteConstructibleTor T A M) : spFiniteConstructibleTor T A N := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨a, z, haz, hz⟩ := h.1
    exact ⟨a, z, haz, fun i hi ↦ (hz i hi).of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso e).symm⟩
  · intro i
    have hc := h.2.1 i
    rw [proEtaleModuleRestriction_constructible_iff] at hc ⊢
    exact ProEtale.isConstructible_of_iso
      ((proEtaleModuleRestriction T A).mapIso
        ((DerivedCategory.homologyFunctor _ i).mapIso e)) hc
  · obtain ⟨a, z, hz⟩ := h.2.2
    exact ⟨a, z, tor_iso T A e a z hz⟩

private theorem support_iso (T : Scheme.{u}) (A : Type u) [CommRing A]
    {M N : proEtaleDerivedCategory T A} (e : M ≅ N) (a z : ℤ)
    (h : proEtaleCohomologicalSupport M ⊆ Set.Icc a z) :
    proEtaleCohomologicalSupport N ⊆ Set.Icc a z := by
  intro i hi
  apply h
  intro hz
  exact hi (hz.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e).symm)

private theorem bounds_iso (T : Scheme.{u}) {M N : SpTowerShriek.D l E T}
    (e : M ≅ N) (a z s t : ℤ) (h : SpChartAdmissibility.bounds l E T M a z s t) :
    SpChartAdmissibility.bounds l E T N a z s t := by
  intro n
  let en := (SpTowerShriek.Ev l E T n).mapIso e
  exact ⟨finite_ctf_iso T _ en (h n).1, support_iso T _ en a z (h n).2.1,
    tor_iso T _ en s t (h n).2.2⟩

private theorem tower_mem_iso (T : Scheme.{u})
    {M N : spDerivedCoefficientTowers l E T (q.abelian T)} (e : M ≅ N)
    (h : spConstructibleTorTowers l E T (q.abelian T) M) :
    spConstructibleTorTowers l E T (q.abelian T) N := by
  refine ⟨fun n ↦ finite_ctf_iso T _
    ((spDerivedCoefficientEvaluation l E T (q.abelian T) n).mapIso e) (h.1 n), ?_⟩
  obtain ⟨a, z, s, t, haz, hst, hb⟩ := h.2
  refine ⟨a, z, s, t, haz, hst, fun n ↦ ⟨?_, ?_⟩⟩
  · intro i hi
    exact ((hb n).1 i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso
      ((spDerivedCoefficientEvaluation l E T (q.abelian T) n).mapIso e)).symm
  · exact tor_iso T _ ((spDerivedCoefficientEvaluation l E T (q.abelian T) n).mapIso e)
      s t (hb n).2

private theorem bounds_mem (T : Scheme.{u}) (M : SpTowerShriek.D l E T)
    (a z s t : ℤ) (haz : a ≤ z) (hst : s ≤ t)
    (h : SpChartAdmissibility.bounds l E T M a z s t) :
    spConstructibleTorTowers l E T (q.abelian T)
      ((SpTowerCalculus.realization l E b T (q.abelian T)).inverse.obj M) := by
  let e := SpTowerCalculus.realization l E b T (q.abelian T)
  let N := e.inverse.obj M
  let en (n : ℕ) : (SpTowerShriek.Ev l E T n).obj M ≅
      (spDerivedCoefficientEvaluation l E T (q.abelian T) n).obj N :=
    (SpTowerShriek.Ev l E T n).mapIso (e.counitIso.app M).symm ≪≫
      (SpTowerCalculus.levelComparison l E b q T n).app N
  refine ⟨fun n ↦ finite_ctf_iso T _ (en n) (h n).1,
    a, z, s, t, haz, hst, fun n ↦ ⟨?_, tor_iso T _ (en n) s t (h n).2.2⟩⟩
  intro i hi
  by_contra hn
  have hs := support_iso T _ (en n) a z (h n).2.1 hn
  rcases hi with hi | hi
  · exact (not_lt_of_ge hs.1) hi
  · exact (not_lt_of_ge hs.2) hi

variable (D : FiniteFieldDatum.{u}) (X Y : Over (Spec (CommRingCat.of D.k)))
  [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  (f : X ⟶ Y) (c : Compactification f.left) (d : ℕ)
  (w : SpChartAdmissibility.Twists l E X.left)
  (hF : ∀ M : SpTowerCalculus.C l E b q X.left,
    spConstructibleTorTowers l E Y.left (q.abelian Y.left)
      ((SpTowerCalculus.F l E b o q c).obj M.obj))
  (G : SpTowerCalculus.C l E b q Y.left ⥤ SpTowerCalculus.C l E b q X.left)
  (adj : SpTowerGluing.support l E b o q c hF ⊣ G)
  (lv : SpTowerGluing.Levels l E b o q c hF G adj)
  (hU : spConstructibleTorTowers l E Y.left (q.abelian Y.left)
    (SpTowerGamma.originalUnit l E b q Y.left))

/-- Uniform twisted-pullback bounds and the exact domains of the specified projection
map and its counit transpose. K is an arbitrary object of the UNNORMALIZED full category.
The structural coordinate arguments are the given finite units, counits and evaluations;
DiagonalLevels states the hypothesis that a has the prescribed finite orientations.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-tower-geometric/
sk-prop-sp-tower-geometric-gamma.proof.md, paragraph (2)
(blueprint: lem-sp-twisted-pullback-tower-domain).

Proof:
1. The finite-type structure maps over a field make X and Y Noetherian by
   lem-weil-pbc-finite-type-over-noetherian, and qcqs by lem-weil-pbc-qcqs-over-affine.
   The DVR quotient at e(n+1) is finite by lem-weil-valued-dvr-finite-quotients.
   A finite ring is Noetherian, since every ideal is generated by its finite set.
2. Every open in Noetherian X is quasi-compact. Smooth f is locally finitely
   presented, hence locally finite type, so it is finite type. Apply
   lem-sf-pullback-tor-amplitude to each K_n at the identified coefficient e(n+1).
   Test its Tor interval with the unit to obtain cohomological bounds [a,z].
3. By lem-pur-twist-sheaf-locally-free, the first Tate line is finite locally constant
   and locally free of rank one. Its nonnegative powers have the same properties;
   the zeroth power is the coefficient unit. Its tensor is exact. The orientation
   therefore gives omega_n cohomological and Tor interval [-2d,-2d].
4. Exact tensor with that line preserves the constructible strata. Associativity
   computes every Tor test, and H^i(C[2d])=H^(i+2d)(C) gives both intervals
   [a-2d,z-2d]. The bounds are independent of n, so sk-def-sp-normalized-towers
   gives P in C_X. Tensor the given orientation to identify it with Q, which has
   the identical bounds and membership. This is exactly orientationMap.
5. Apply det-pe-finite-tor-comparison-noetherian on X and Y separately at each
   finite coefficient. Essential surjectivity gives bounded constructible etale
   origins; its interval equivalence retains [a,z] and [-2d,-2d]. No transitions
   between these witnesses are selected or required.
6. Exact evaluation computes tower cohomology componentwise by
   det-sp-coefficient-towers-abelian. A tower with zero levels is zero, so the
   level lower bounds give the genuine ambient lower bounds a and -2d.
7. Apply det-sp-tower-shriek-levels(2a) to omega and K, using steps 5 and 6 for
   BOTH inputs. The resulting isomorphism is the specified projection. Symmetry
   identifies its target with FQ. Lem-sp-compact-support-tower-reduction puts FQ
   and Fomega in C_Y. Thus its source and target lie there as well. Q_mem and
   K.property type the actual transpose under the GIVEN adjunction; its inverse
   projection/counit word is SpTowerGamma.projectionCounit and its transpose is
   SpTowerGamma.tensorMate, without lifting a family of evaluated morphisms.
-/
theorem twisted_pullback_tower_domain
    (_hl : l ≠ D.p) [IsSeparated f.left] [SmoothOfRelativeDimension d f.left]
    (roots : SpCoordinateAdjunction.RootLines l E X.left)
    (unitsX : ∀ n : ℕ, IsUnit ((l ^ (n + 1) : ℕ) : Γ(X.left, ⊤)))
    (cc : ∀ n : ℕ, SpTowerP1.CoefficientCoordinates l E n X.left (unitsX n))
    (tc : ∀ n : ℕ, SpTowerP1.TensorCoordinates l E n b X.left)
    (unitsY : ∀ n : ℕ, IsUnit ((l ^ (n + 1) : ℕ) : Γ(Y.left, ⊤)))
    (cy : ∀ n : ℕ, SpTowerP1.CoefficientCoordinates l E n Y.left (unitsY n))
    (orientation : SpTowerGamma.orderedLine l E b X.left w d ≅ omega l E b q G hU)
    (_hdiagonal : DiagonalLevels l E b o q D X Y f c d w hF G adj lv hU
      roots unitsX cc tc unitsY cy orientation)
    (K : SpTowerCalculus.C l E b q Y.left) (a z : ℤ) (_haz : a ≤ z)
    (_hTor : ∀ n : ℕ, HasProEtaleTorAmplitude Y.left (SpTowerShriek.R l E n)
      ((SpTowerShriek.Ev l E Y.left n).obj
        ((SpTowerGamma.realization l E b q Y.left).obj K)) a z) :
    Conclusion l E b o q D X Y f c d w G hU K a z orientation := by
  classical
  letI := isNoetherian_of_locallyOfFiniteType X.hom
  letI := isNoetherian_of_locallyOfFiniteType Y.hom
  have hcoeff (n : ℕ) : Finite (SpTowerShriek.R l E n) ∧
      IsNoetherianRing (SpTowerShriek.R l E n) := ⟨inferInstance, inferInstance⟩
  obtain ⟨hpull, hlines, hPb, hLb, hRev⟩ := pullback_ordered_tate_bounds
    l E b o q D _hl X Y f d w K a z _haz _hTor
  let ePQ : P l E b o q f.left w d K ≅ Q l E b o q f.left G hU K :=
    (SpTowerShriek.tensor l E b X.left).mapIso
      (Iso.prod (Iso.refl (B l E b o q f.left K)) orientation)
  have hQb := bounds_iso l E X.left ePQ _ _ _ _ hPb
  have hOb := bounds_iso l E X.left orientation _ _ _ _ hLb
  have hPmem := bounds_mem l E b q X.left _ _ _ _ _ (by omega) (by omega) hPb
  have hQmem := bounds_mem l E b q X.left _ _ _ _ _ (by omega) (by omega) hQb
  have hOmem := bounds_mem l E b q X.left _ _ _ _ _ le_rfl le_rfl hOb
  have hInput : SpChartAdmissibility.bounds l E Y.left
      ((SpTowerGamma.realization l E b q Y.left).obj K) a z a z := by
    intro n
    let e := (SpTowerCalculus.levelComparison l E b q Y.left n).app K.obj
    exact ⟨finite_ctf_iso Y.left _ e.symm (K.property.1 n),
      support_of_torAmplitude Y.left _ _ a z (_hTor n), _hTor n⟩
  obtain ⟨hInputOrigin, hInputLower⟩ := uniform_bounds_origin_lower l E b Y.left
    _ a z a z _haz _haz hInput
  obtain ⟨hDualOrigin, hDualLower⟩ := uniform_bounds_origin_lower l E b X.left
    _ (-2 * d) (-2 * d) (-2 * d) (-2 * d) le_rfl le_rfl hOb
  letI : Fintype D.k₀ := Fintype.ofFinite D.k₀
  letI : Fact D.p.Prime := ⟨D.prime⟩
  letI : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans
      (D.card_base.trans D.cardinality_eq))
  letI : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  have hKmem : SpTowerProjection.constructibleTor l E b Y.left (q.abelian Y.left)
      ((SpTowerGamma.realization l E b q Y.left).obj K) :=
    tower_mem_iso l E b q Y.left
      ((SpTowerCalculus.realization l E b Y.left (q.abelian Y.left)).unitIso.app K.obj)
      K.property
  have hpf := (SpTowerProjection.tower_compact_support_projection_formula l E b o
    D.k D.p _hl X Y f c (q.abelian X.left) (q.abelian Y.left)
    (omega l E b q G hU) ((SpTowerGamma.realization l E b q Y.left).obj K)
    hOmem hKmem).2.2.2.2
  letI := hpf
  let revOrientation := (SpTowerShriek.tensor l E b X.left).mapIso
    (Iso.prod orientation (Iso.refl (B l E b o q f.left K)))
  have hRevO := bounds_iso l E X.left revOrientation _ _ _ _ hRev
  have hRevMem := bounds_mem l E b q X.left _ _ _ _ _ (by omega) (by omega) hRevO
  let rev : SpTowerCalculus.C l E b q X.left := ⟨_, hRevMem⟩
  have hFrev := hF rev
  let eX := SpTowerCalculus.realization l E b X.left (q.abelian X.left)
  let eY := SpTowerCalculus.realization l E b Y.left (q.abelian Y.left)
  let F := SpTowerShriek.F l E b o c
  have hTarget : spConstructibleTorTowers l E Y.left (q.abelian Y.left)
      (eY.inverse.obj (F.obj ((SpTowerShriek.tensor l E b X.left).obj
        (omega l E b q G hU, B l E b o q f.left K)))) :=
    tower_mem_iso l E b q Y.left
      (eY.inverse.mapIso (F.mapIso (eX.counitIso.app _))) hFrev
  have hSource := tower_mem_iso l E b q Y.left
    (eY.inverse.mapIso (asIso (SpTowerShriek.projection l E b o c
      (omega l E b q G hU) ((SpTowerGamma.realization l E b q Y.left).obj K))).symm)
    hTarget
  exact
    { noetherianX := inferInstance
      noetherianY := inferInstance
      compactX := inferInstance
      compactY := inferInstance
      quasiSeparatedX := inferInstance
      quasiSeparatedY := inferInstance
      coefficients := hcoeff
      pullback_bounds := hpull
      lines := hlines
      P_mem := hPmem
      Q_mem := hQmem
      P_bounds := hPb
      Q_bounds := hQb
      orientation_iso := by change IsIso ePQ.hom; infer_instance
      input_origins := hInputOrigin
      dualizing_origins := hDualOrigin
      input_lower := hInputLower
      dualizing_lower := hDualLower
      projection_iso := hpf
      projection_source_mem := hSource
      projection_target_mem := hTarget }

end AlgebraicGeometry.ProEtale.SpTwistedTowerDomain

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

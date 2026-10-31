/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedTateIntegralTowerData
import WeilConjectures.AlgebraicGeometry.SingleDegreeUniformReconstruction
import WeilConjectures.AlgebraicGeometry.NormalizedTateTensorTower
import WeilConjectures.AlgebraicGeometry.FinitePuritySourceUnitReduction
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Reconstruction of the normalized finite smooth-purity tower

Source: current blueprint, sk-thm-purity-transport, proof Steps 1--2.
(blueprint: lem-pur-condensed-tate-integral-tower)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped TensorProduct
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

attribute [local irreducible] HasDerivedCategory.standard Functor.leftAdjoint
  SheafOfModules.monoidalCategory completedAdicDerivedChange

private theorem finite_concentrated (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (n d : ℕ) (q : ℤ) (hq : q ≠ -(2 * (d : ℤ))) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj (finiteTwist T ell n d)) := by
  let e : finiteTwist T ell n d ≅
      (_root_.DerivedCategory.singleFunctor _ (-(2 * (d : ℤ)))).obj
        (finiteSheaf T ell n d) :=
    (comparison (coefficient ell (n + 1)) T).mapIso
      (Etale.CoordinateCounitArrows.baseTateIso (coefficient ell (n + 1))
        (ell ^ (n + 1)) (pow_pos (Fact.out : ell.Prime).pos _)
        (CharP.cast_eq_zero _ _) T (by simpa using hT.pow (n + 1)) d) ≪≫
      ((comparison (coefficient ell (n + 1)) T).commShiftIso (2 * (d : ℤ))).app _ ≪≫
      (shiftFunctor _ (2 * (d : ℤ))).mapIso
        ((Functor.mapDerivedCategorySingleFunctor
          (ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} (coefficient ell (n + 1))) T) 0).app _) ≪≫
      ((_root_.DerivedCategory.singleFunctors _).shiftIso (2 * (d : ℤ))
        (-(2 * (d : ℤ))) 0 (by omega)).app _
  apply IsZero.of_iso _ ((_root_.DerivedCategory.homologyFunctor _ q).mapIso e)
  rcases lt_or_gt_of_ne hq with hq | hq
  · exact _root_.DerivedCategory.isZero_of_isGE _ _ _ hq
  · exact _root_.DerivedCategory.isZero_of_isLE _ _ _ hq
private theorem level_concentrated (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (d : ℕ) (M : AdicTower T (datum.{u} ell))
    (e : ∀ n : ℕ,
      M.level n ≅ (derivedRealization T ell n).obj (finiteTwist T ell n d))
    (n : ℕ) (q : ℤ) (hq : q ≠ -(2 * (d : ℤ))) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj (M.level n)) := by
  apply IsZero.of_iso _ ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
    (e n ≪≫ finiteModelIso T ell hT n d))
  rcases lt_or_gt_of_ne hq with hq | hq
  · exact _root_.DerivedCategory.isZero_of_isGE _ _ _ hq
  · exact _root_.DerivedCategory.isZero_of_isLE _ _ _ hq

private theorem gammaUnit_isIso (ell : ℕ) [Fact ell.Prime]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsSeparated f]
    (d n : ℕ) (s : Level ell (n + 1) f d) :
    IsIso (gammaUnit ell n f d s) := by
  have := (s.pro_purity (𝟙_ _) s.unit_ctf.1).2.2
  dsimp only [gammaUnit]
  infer_instance

private theorem identifiesExceptional_of_reconstructed (ell : ℕ) [Fact ell.Prime]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsSeparated f]
    (d : ℕ) (s : ∀ n : ℕ, Level ell (n + 1) f d)
    (r : ∀ (b a : ℕ) (hab : a ≤ b),
      ReductionData (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1))
        f d (s b) (s a))
    (M : AdicTower X (datum.{u} ell))
    (e : ∀ n : ℕ, M.level n ≅ (derivedRealization X ell n).obj (finiteTwist X ell n d))
    (hM : Reconstructed X ell (fun n ↦ finiteTwist X ell n d)
      (fun b a hab ↦ proTwistMap d (r b a hab).twist) (-(2 * (d : ℤ))) M e)
    (hsquare : ∀ (b a : ℕ) (hab : a ≤ b),
      (proScalar (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1)) X).map
          (gammaUnit ell b f d (s b)) ≫ exceptionalReduction ell f b a hab =
        proTwistMap d (r b a hab).twist ≫ gammaUnit ell a f d (s a)) :
    IdentifiesExceptional ell f d s M e := by
  rw [Reconstructed] at hM
  obtain ⟨_, _, hc, he, hnorm, _, _, _⟩ := hM
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    have := hc n
    have := gammaUnit_isIso ell f d n (s n)
    dsimp only [reconstructedGamma]
    infer_instance
  · intro b a hab
    have hn := (scalarComparison X ell b a hab).hom.naturality
      (gammaUnit ell b f d (s b))
    dsimp only [Functor.comp_map] at hn
    have hs := congrArg (derivedRealization X ell a).map (hsquare b a hab)
    simp only [Functor.map_comp] at hs
    dsimp only [reconstructedGamma]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% hn, hs]
    rw [reassoc_of% (he b a hab), reassoc_of% (hnorm b a hab)]
  · intro n q
    exact (s n).unit_ctf.2.2.1 q
  · intro n q hq
    exact ((s n).unit_degree q hq).2

private theorem gammaUnit_reduction (ell : ℕ) [Fact ell.Prime]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsSeparated f]
    (d b a : ℕ) (hab : a ≤ b) (sb : Level ell (b + 1) f d)
    (sa : Level ell (a + 1) f d)
    (r : ReductionData
      (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1)) f d sb sa) :
    (proScalar (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1)) X).map
        (gammaUnit ell b f d sb) ≫ exceptionalReduction ell f b a hab =
      proTwistMap d r.twist ≫ gammaUnit ell a f d sa := by
  have hp := (r.pro_purity (𝟙_ _) sb.unit_ctf.1).2
  have hn := sa.pro_natural _ _ (r.reduction_ctf Y _ sb.unit_ctf.1) sa.unit_ctf.1
    (unitReduction Y ell b a hab).hom
  dsimp only [gammaUnit, exceptionalReduction]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hp, ← hn]
  have hu := finitePuritySourceUnitReduction ell f d b a hab r.twist
  have h := congrArg (fun z ↦ z ≫ proGamma (coefficient ell (a + 1)) f
    (line (coefficient ell (a + 1)) (ell ^ (a + 1))
      (CharP.cast_eq_zero _ _) X d) sa.alpha (𝟙_ _)) hu
  simpa only [Category.assoc, finiteProSource] using h

private theorem fixedConstructible_of_iso
    (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] [Finite A]
    {F G : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} A)} (e : F ≅ G)
    (hF : IsConstructibleProEtaleFixedModuleSheaf T A F) :
    IsConstructibleProEtaleFixedModuleSheaf T A G := by
  obtain ⟨S, hn, hc, hs⟩ := hF
  refine ⟨S, hn, hc, fun i ↦ ?_⟩
  let e' := (ProEtale.upperStar (ModuleCat.{u + 1} A) (S.immersion i)).mapIso e
  obtain ⟨hl, hf⟩ := hs i
  constructor
  · obtain ⟨I, U, f, hcover, hm⟩ := hl
    refine ⟨I, U, f, hcover, fun j ↦ ?_⟩
    obtain ⟨P, ⟨ep⟩⟩ := hm j
    exact ⟨P, ⟨((ProEt.topology (S.domain i)).overPullback
      (ModuleCat.{u + 1} A) (U j)).mapIso e'.symm ≪≫ ep⟩⟩
  · intro Ω _ _ y
    let e'' := HasColimit.isoOfNatIso
      (Functor.isoWhiskerLeft (proEtaleGeometricNeighbourhoodForget y).op
        ((sheafToPresheaf _ _).mapIso e'))
    have := hf Ω y
    exact Finite.of_equiv (proEtaleGeometricFixedModuleStalk y A
      ((ProEtale.upperStar (ModuleCat.{u + 1} A) (S.immersion i)).obj F))
      (Equiv.ofBijective e''.hom (ConcreteCategory.bijective_of_isIso e''.hom))

private theorem reconstructed_of_uniform_model
    {k : Type u} [Field k] (T : Scheme.{u}) [IsNoetherian T]
    (fT : T ⟶ Spec (.of k)) (hT : LocallyOfFiniteType fT ∧ QuasiCompact fT)
    (ell : ℕ) [Fact ell.Prime]
    (N : ∀ n : ℕ, proCategory (coefficient ell (n + 1)) T)
    (tau : ∀ (b a : ℕ) (hab : a ≤ b),
      (proScalar (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1)) T).obj
        (N b) ⟶ N a)
    (degree : ℤ) (M : AdicTower T (datum.{u} ell))
    (e : ∀ n : ℕ, M.level n ≅ (derivedRealization T ell n).obj (N n))
    (S : Stratification T) (W : UniformAdicTowerData (datum.{u} ell) M S)
    (hl : W.lower = degree) (hu : W.upper = degree)
    (he : ∀ (b a : ℕ) (hab : a ≤ b),
      (pbcDerivedExtend (pbcAdicQuotient T (datum.{u} ell) b a hab)).map (e b).hom ≫
        (scalarComparison T ell b a hab).hom.app (N b) ≫
        (derivedRealization T ell a).map (tau b a hab) =
          (M.normalization b a hab).hom ≫ (e a).hom)
    (hc : ∀ (n : ℕ) (q : ℤ),
      @IsConstructibleProEtaleCoefficientModuleSheaf T
        (Ring.{u} ell ⧸ (datum.{u} ell).ideal ^ (n + 1)) _
        ((datum.{u} ell).quotientFinite n)
        ((pbcRestrict (pbcLevelConstantComparison T (datum.{u} ell) n).hom).obj
          ((_root_.DerivedCategory.homologyFunctor _ q).obj (M.level n))))
    (hN : ∀ (n : ℕ) (q : ℤ),
      IsConstructibleProEtaleFixedModuleSheaf T (coefficient ell (n + 1))
        ((_root_.DerivedCategory.homologyFunctor _ q).obj (N n)))
    (hz : ∀ (n : ℕ) (q : ℤ), q ≠ degree →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj (M.level n)))
    (hNz : ∀ (n : ℕ) (q : ℤ), q ≠ degree →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj (N n))) :
    Reconstructed T ell N tau degree M e := by
  obtain ⟨hcomplete, hcounit, hnorm, hbound⟩ :=
    singleDegreeUniformReconstruction T fT hT (datum ell) M S W degree hl hu hc hz
  rw [Reconstructed]
  refine ⟨?_, hcomplete, hcounit, he, hnorm, hN, hNz, hbound⟩
  refine ⟨W.lower, W.upper, W.bounds, S, fun i ↦ ?_⟩
  exact ⟨W.cover i, W.covering i, fun U f hf ↦ ⟨W.model i U f hf⟩⟩

/-- Retain finite smooth purity and reconstruct its normalized root and constant towers.
The quantified finite data are the already normalized data of the dependency: root
power maps, tensor balancing, diagonal/Kummer orientation, and actual counit mates.
Auxiliary geometric properties are retained as conclusions, rather than extra hypotheses.
Source: sk-thm-purity-transport, proof Steps 1--2
(blueprint: lem-pur-condensed-tate-integral-tower). -/
def ReconstructionResult (ell : ℕ) [Fact ell.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ)
    (hfq : QuasiCompact f) (hfs : IsSeparated f) (c : Compactification f)
    (hX : IsNoetherian X) (hY : IsNoetherian Y) : Prop :=
  letI := hfq
  letI := hfs
  have := c.hasCompactification
  have := hX
  have := hY
  FiniteSmoothSystem ell f d ∧
  ∀ (s : ∀ n : ℕ, Level ell (n + 1) f d)
    (r : ∀ (b a : ℕ) (hab : a ≤ b),
      ReductionData (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1))
        f d (s b) (s a)),
    ∃ (hXT : IsUnit (ell : Γ(X, ⊤))) (hYT : IsUnit (ell : Γ(Y, ⊤)))
      (M : AdicTower X (datum.{u} ell)) (L : AdicTower Y (datum.{u} ell))
      (eM : ∀ n : ℕ,
        M.level n ≅ (derivedRealization X ell n).obj (finiteTwist X ell n d))
      (eL : ∀ n : ℕ, L.level n ≅ (derivedRealization Y ell n).obj (𝟙_ _)),
      ∃ (hM : M.tower = strictDerivedTower X ell d)
        (hL : L.tower = strictDerivedTower Y ell 0),
      ProjectionNormalized X ell hXT d M eM hM ∧
      ProjectionNormalized Y ell hYT 0 L
        (fun n ↦ eL n ≪≫ (derivedRealization Y ell n).mapIso (finiteZeroIso Y ell n).symm)
        hL ∧
      Reconstructed X ell (fun n ↦ finiteTwist X ell n d)
        (fun b a hab ↦ proTwistMap d (r b a hab).twist) (-(2 * (d : ℤ))) M eM ∧
      Reconstructed Y ell (fun n ↦ (𝟙_ (proCategory (coefficient ell (n + 1)) Y)))
        (fun b a hab ↦ (unitReduction Y ell b a hab).hom) 0 L eL ∧
      IdentifiesExceptional ell f d s M eM

/-- Reconstruction of the normalized finite smooth-purity tower over any field of
positive characteristic different from ell, in completed Z_ell coefficients.

Source: current blueprint, sk-thm-purity-transport, proof Steps 1--2; normalized
Tate-unit case of adic reconstruction
(blueprint: lem-pur-condensed-tate-integral-tower).

Proof:
1. Finite-type schemes over k are Noetherian and finite-dimensional: finite affine
   covers and Noether normalization bound every chain of irreducible closed subsets.
   Ell is invertible. Z_ell with ideal (ell) satisfies the adic datum by the DVR
   property and the two-term free resolutions of its finite quotients.
2. The Tate-line lemma gives the inverse-limit root line over the completed ring.
   A common pro-etale cover with compatible primitive roots identifies its actual
   projections with finite roots. Completion modulo ell^n and tensor balancing give
   the d-fold quotient identification, with the constant line when d=0.
   On every local root generator this is exactly ProjectionBalanced: use the
   actual limit projection and the tensor sheafification unit. Regroup the finite
   shifts by finiteModelIso. Exact restriction/evaluation of single complexes
   gives ProjectionNormalized for eM together with M.evaluation, and for eL with
   L.evaluation. Local generators force these identifications, removing any
   freedom to rescale the resulting canonical reduction by a sign or unit.
3. Those lines are K-flat: on a trivializing cover tensor with the line is identity,
   restriction is exact and commutes with sheaf tensor, and vanishing descends.
   Ordinary quotient balancing therefore computes all the derived reductions.
4. The root-power maps and quotient maps are strict sheaf maps. Their balanced
   adjoints are the stated normalization isomorphisms; multiplying root exponents
   and scalar residues verifies the full quotient cocycle, including equal levels.
5. The single stratum and the common trivializing cover give one adic-lisse complex
   supported in degree -2d on X and degree zero on Y. Its finite cohomology is finite
   lisse. Thus the strict towers are uniformly bounded constructible.
6. Apply reconstructionUniformTower: its actual Rlim and projection-induced counits
   give derived completeness, the canonical quotient isomorphisms, normalization
   compatibility, and the single-degree integral bounds.
7. The finite-ring constructible-origin theorem gives bounded etale origins over
   arbitrary k. normalizedEtaleOriginWitnesses lifts the quotient normalizations
   uniquely, with unit and cocycle. Transport both these witnesses and the common
   local models along the canonical reduction isomorphisms; this proves membership
   in PbcIsBoundedConstructibleComplete, including its compatible-origin clause.
8. Finite smooth adjunction gives the diagonal/Kummer gamma and its coefficient
   square. Identify its twist lambda with the root-power normalization from Step 4.
   Compose with the canonical counits of Step 6. The resulting maps are exactly
   reconstructedGamma, and their square is IdentifiesExceptional. Transport the
   constructibility, degree bound and compatible origins along gamma. -/
theorem condensedTateIntegralTower
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k] [Fact (ringChar k ≠ ell)]
    (hchar : 0 < ringChar k)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (d : ℕ) [SmoothOfRelativeDimension d f] :
    ∃ (hfq : QuasiCompact f) (hfs : IsSeparated f) (c : Compactification f)
      (hX : IsNoetherian X) (hY : IsNoetherian Y),
      ReconstructionResult ell f d hfq hfs c hX hY := by
  classical
  have hcomp : f ≫ (Y ↘ Spec (.of k)) = X ↘ Spec (.of k) := by simp
  have : IsSeparated (f ≫ (Y ↘ Spec (.of k))) := hcomp.symm ▸ inferInstance
  have : QuasiCompact (f ≫ (Y ↘ Spec (.of k))) := hcomp.symm ▸ inferInstance
  have : LocallyOfFiniteType (f ≫ (Y ↘ Spec (.of k))) := hcomp.symm ▸ inferInstance
  have hfs : IsSeparated f := IsSeparated.of_comp f (Y ↘ Spec (.of k))
  have hfq : QuasiCompact f := QuasiCompact.of_comp f (Y ↘ Spec (.of k))
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f (Y ↘ Spec (.of k))
  obtain ⟨c, hX, hY, hs⟩ := finiteSmoothAdjunctionGeneralBase ell k f d
  have := c.hasCompactification
  have := hX
  have := hY
  refine ⟨hfq, hfs, c, hX, hY, hs, ?_⟩
  intro s r
  have hk : IsUnit (ell : k) := by
    by_cases hz : ringChar k = 0
    · exact False.elim ((Nat.ne_of_gt hchar) hz)
    · exact (CharP.cast_ne_zero_of_ne_of_prime k (Fact.out : ell.Prime)
        (Fact.out : ringChar k ≠ ell)).isUnit
  have hSpec : IsUnit (ell : Γ(Spec (.of k), ⊤)) := by
    simpa only [map_natCast] using hk.map (Scheme.ΓSpecIso (.of k)).inv.hom
  have hXT : IsUnit (ell : Γ(X, ⊤)) := by
    simpa only [map_natCast] using hSpec.map (X ↘ Spec (.of k)).appTop.hom
  have hYT : IsUnit (ell : Γ(Y, ⊤)) := by
    simpa only [map_natCast] using hSpec.map (Y ↘ Spec (.of k)).appTop.hom
  obtain ⟨M, eM, hM, hprojM, SX, WX, hlX, huX, heM, hcM, hNM, _⟩ :=
    normalizedTateTensorTower X ell hXT d
  obtain ⟨L, eL₀, hL, hprojL, SY, WY, hlY, huY, heL, hcL, hNL, heL₀⟩ :=
    normalizedTateTensorTower Y ell hYT 0
  let eL (n : ℕ) := eL₀ n ≪≫ (derivedRealization Y ell n).mapIso (finiteZeroIso Y ell n)
  have hrecM : Reconstructed X ell (fun n ↦ finiteTwist X ell n d)
      (fun b a hab ↦ proTwistMap d (r b a hab).twist) (-(2 * (d : ℤ))) M eM :=
    reconstructed_of_uniform_model X (X ↘ Spec (.of k)) ⟨inferInstance, inferInstance⟩
      ell _ _ _ M eM SX WX hlX huX
      (fun b a hab ↦ heM b a hab (r b a hab).twist) hcM hNM
      (level_concentrated X ell hXT d M eM) (finite_concentrated X ell hXT · d)
  have hrecL : Reconstructed Y ell
      (fun n ↦ (𝟙_ (proCategory (coefficient ell (n + 1)) Y)))
      (fun b a hab ↦ (unitReduction Y ell b a hab).hom) 0 L eL := by
    apply reconstructed_of_uniform_model Y (Y ↘ Spec (.of k))
      ⟨inferInstance, inferInstance⟩ ell _ _ _ L eL SY WY
      (by simpa using hlY) (by simpa using huY)
    · intro b a hab
      simpa only [eqToIso_refl, Iso.refl_trans] using heL₀ rfl b a hab
    · exact hcL
    · intro n q
      exact fixedConstructible_of_iso Y _
        ((_root_.DerivedCategory.homologyFunctor _ q).mapIso (finiteZeroIso Y ell n))
        (hNL n q)
    · intro n q hq
      exact level_concentrated Y ell hYT 0 L eL₀ n q (by simpa using hq)
    · intro n q hq
      exact (finite_concentrated Y ell hYT n 0 q (by simpa using hq)).of_iso
        ((_root_.DerivedCategory.homologyFunctor _ q).mapIso (finiteZeroIso Y ell n)).symm
  refine ⟨hXT, hYT, M, L, eM, eL, hM, hL, hprojM, ?_, hrecM, hrecL, ?_⟩
  · convert hprojL using 1
    funext n
    dsimp only [eL]
    simp only [Iso.trans_assoc, ← Functor.mapIso_trans, Iso.self_symm_id,
      Functor.mapIso_refl, Iso.trans_refl]
  · exact identifiesExceptional_of_reconstructed ell f d s r M eM hrecM
      (fun b a hab ↦ gammaUnit_reduction ell f d b a hab (s b) (s a) (r b a hab))

end AlgebraicGeometry.Scheme.PurityIntegralTower

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.AffineSpaceZeroSectionConstructions
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.AffineSpacePurity.AffineSpacePurityComparison
public import WeilConjectures.AlgebraicGeometry.AffineLinePurity.AffineLinePurityComparison
import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalOriginCompactSupportComposition
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTwistLine
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.SixFunctors.Etale.Derived.CoefficientsShift
import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOrigin

/-! # Normalization induction for the ordered affine coordinate tower

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
cor-pur-affine-space-zero-section-purity.proof.md, final paragraph
(blueprint: lem-pur-coordinate-tower-normalization-induction).

(blueprint: def-pur-coordinate-tower-normalization-data).

The existing zero-section module supplies only its canonical constructions here;
its purity statements are not invoked. The input orientations are arbitrary maps
satisfying the displayed affine-line evaluation identity. Positive coefficient
levels are indexed by n+1, including n=0. Every comparison is formed from the
recorded compact-support compositor and its pasted exceptional counits.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u v₁ v₂ w₁ w₂
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.CoordinateTowerNormalization
open AffineZeroPurity AffineSpacePurity VectorIntegrationSite

attribute [local irreducible] rightDerivedUpperShriek rightDerivedLowerShriek
  originCompositionAmbient derivedComparisonAdjunction

/-- The existing coefficient unit, with the canonical ambient category instance cached.
Source: A_B in the recurrence
(blueprint: lem-pur-coordinate-tower-normalization-induction). -/
@[implicit_reducible]
def coefficientUnit (P : PurityFiniteSetting.{u}) (n : ℕ) (T : Scheme.{u}) :
    AffineSpacePurity.C (setting P n).Coefficient T := AffineZeroPurity.unit P n T

/-- The existing ordered Tate target, with that same ambient category instance cached.
Source: W_r=A_X(r)[2r]
(blueprint: lem-pur-coordinate-tower-normalization-induction). -/
@[implicit_reducible]
def tatePower (P : PurityFiniteSetting.{u}) (n : ℕ) (T : Scheme.{u}) (r : ℕ) :
    AffineSpacePurity.C (setting P n).Coefficient T := AffineZeroPurity.target P n T r

/-- The last-coordinate zero section in the recorded ordered tower.
Source: s_r in the final paragraph
(blueprint: lem-pur-coordinate-tower-normalization-induction). -/
abbrev lastSection (B : Scheme.{u}) (r : ℕ) :=
  AffineSpace.zeroSection PUnit.{u + 1} (iteratedAffineLine B r)

/-- The successive zero vectors compose to the zero vector of the full tower.
Source: z_(r+1)=s_r z_r
(blueprint: lem-pur-coordinate-tower-normalization-induction).
Proof: toIteratedAffineLine is determined by its base map and all coordinates.
Both composites have identity base map and every coordinate zero. -/
theorem zero_successor (B : Scheme.{u}) (r : ℕ) :
    zero B r ≫ lastSection B r = zero B (r + 1) := by
  change zero B r ≫ AffineSpace.homOfVector (𝟙 _) (fun _ ↦ 0) =
    AffineSpace.homOfVector (zero B r) (fun _ ↦ 0)
  rw [AffineSpace.comp_homOfVector, Category.comp_id]
  congr 1
  funext i
  exact map_zero _

/-- The actual affine-line comparison at an arbitrary finite-Tor etale-origin input.
Source: the affine-line hypothesis of the final paragraph
(blueprint: lem-pur-coordinate-tower-normalization-induction). -/
@[irreducible]
def lineGamma (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (r : ℕ)
    (K : Plus (setting P n).Coefficient (iteratedAffineLine B r))
    (Ke : Etale.DerivedCategoryModule (setting P n).Coefficient (iteratedAffineLine B r))
    (hKe : etaleFiniteTor (setting P n).Coefficient (iteratedAffineLine B r) Ke)
    (eK : (comparison (setting P n).Coefficient (iteratedAffineLine B r)).obj Ke ≅ K.obj) :
    (lineSource (setting P n) (iteratedAffineLine B r)).obj K.obj ⟶
      (rightDerivedUpperShriek (setting P n).Coefficient
        (lastProjection B r)).obj K.obj :=
  letI : LocallyOfFiniteType (towerBase aB r) := (tower_geometry aB r).1
  letI : QuasiCompact (towerBase aB r) := (tower_geometry aB r).2.1
  letI : IsSeparated (towerBase aB r) := (tower_geometry aB r).2.2
  lineComparison (setting P n) (iteratedAffineLine B r) (towerBase aB r) K Ke hKe eK

/-- Naturality and invertibility on the stated input class, for just the c affine lines.
Source: the affine-line hypothesis, without a smooth-purity assumption
(blueprint: lem-pur-coordinate-tower-normalization-induction). -/
@[irreducible]
def LineLaw (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (c : ℕ) : Prop :=
  ∀ r : Fin c,
    (∀ (K : Plus (setting P n).Coefficient (iteratedAffineLine B r.val))
      (Ke : Etale.DerivedCategoryModule (setting P n).Coefficient (iteratedAffineLine B r.val))
      (hKe : etaleFiniteTor (setting P n).Coefficient (iteratedAffineLine B r.val) Ke)
      (eK : (comparison (setting P n).Coefficient (iteratedAffineLine B r.val)).obj Ke ≅ K.obj),
      IsIso (lineGamma P n B aB r.val K Ke hKe eK)) ∧
    (∀ (K L : Plus (setting P n).Coefficient (iteratedAffineLine B r.val))
      (Ke Le : Etale.DerivedCategoryModule
        (setting P n).Coefficient (iteratedAffineLine B r.val))
      (hKe : etaleFiniteTor (setting P n).Coefficient (iteratedAffineLine B r.val) Ke)
      (hLe : etaleFiniteTor (setting P n).Coefficient (iteratedAffineLine B r.val) Le)
      (eK : (comparison (setting P n).Coefficient (iteratedAffineLine B r.val)).obj Ke ≅ K.obj)
      (eL : (comparison (setting P n).Coefficient (iteratedAffineLine B r.val)).obj Le ≅ L.obj)
      (f : K.obj ⟶ L.obj),
      (lineSource (setting P n) (iteratedAffineLine B r.val)).map f ≫
          lineGamma P n B aB r.val L Le hLe eL =
        lineGamma P n B aB r.val K Ke hKe eK ≫
          (rightDerivedUpperShriek (setting P n).Coefficient
            (lastProjection B r.val)).map f)

/-- Canonical ordinary antecedent, using Rnu_* rather than choosing an origin witness.
Source: proof Step 1, the finite Tate tensor power
(blueprint: lem-pur-coordinate-tower-normalization-induction). -/
@[implicit_reducible]
def ordinaryTarget (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u}) (r : ℕ) :=
  (comparisonLowerStar (ModuleCat.{u + 1} (setting P n).Coefficient)
    (iteratedAffineLine B r)).rightDerivedFunctor.obj
      (tatePower P n (iteratedAffineLine B r) r)

section OriginProofs

attribute [local irreducible] Scheme.finiteEtaleTateLine
attribute [local irreducible] AffineSpacePurity.shiftedLine

-- A local basis on the localized site gives a finite locally constant etale sheaf.
private theorem finiteLine_properties (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (hT : IsUnit (N : Γ(T, ⊤))) :
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T
      ((Etale.ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧) := by
  classical
  have ht := Scheme.finite_etale_torsion_twist_line T N hN
    (fun x ↦ by
      simpa only [map_natCast] using hT.map (T.presheaf.germ ⊤ x (by trivial)).hom)
    A hA 1
  obtain ⟨cover, hc⟩ := ht.1
  have hlocal (i : cover.I₀) : Scheme.IsFiniteLocallyConstantSheaf
      ((Etale.upperStar (ModuleCat.{u + 1} A) (cover.f i)).obj
        (Scheme.finiteEtaleTateLine T N A hA)) := by
    let U := cover.etalePrecoverageToEtale i
    let E := Scheme.Etale.overSheafEquiv U (ModuleCat.{u + 1} A)
    let c := (Scheme.Etale.overEquiv U).constantSheafSheafCongrIso
      (T.smallEtaleTopology.over U) U.left.smallEtaleTopology (ModuleCat.{u + 1} A)
      Over.mkIdTerminal
    let e := (Scheme.overSheafEquivFunctorObjOverIso (ModuleCat.{u + 1} A) U
        (Scheme.finiteEtaleTateLine T N A hA)).symm ≪≫
      E.functor.mapIso (hc i).some ≪≫ c.app (ModuleCat.of A A)
    have : Scheme.IsFiniteLocallyConstantSheaf
        ((constantSheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
          (ModuleCat.of A A)) :=
      Etale.isFiniteLocallyConstantSheaf_constantSheaf (ModuleCat.of A A)
    apply Scheme.IsFiniteLocallyConstantSheaf.of_iso e.symm
  have := hlocal
  have hfinite := Scheme.IsFiniteLocallyConstantSheaf.of_cover cover
    (Scheme.finiteEtaleTateLine T N A hA)
  have := hfinite.isConstructibleSheaf
  have hflat : ObjectProperty.flat (Scheme.finiteEtaleTateLine T N A hA) :=
    (ObjectProperty.flat_iff_preservesFiniteLimits _).2 ht.2.2.1
  have hs : Etale.DerivedCategory.boundedConstructibleFiniteTor A T
      ((_root_.DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateLine T N A hA)) :=
    ⟨Etale.DerivedCategory.boundedConstructible_singleFunctor_obj _ 0,
      0, 0, _root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat hflat⟩
  exact Etale.DerivedCategory.boundedConstructibleFiniteTor.shift hs 2

-- Tensor stability and monoidal comparison, before specializing the coefficient ring.
private theorem tensorPowers_origin (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) (K L : Etale.DerivedCategoryModule A T)
    (hK : etaleFiniteTor A T K) (hL : etaleFiniteTor A T L)
    (M : AffineSpacePurity.C A T) (eM : (comparison A T).obj K ≅ M) (r : ℕ) :
    ∃ Q : Etale.DerivedCategoryModule A T, etaleFiniteTor A T Q ∧
      Nonempty ((comparison A T).obj Q ≅
        (action ((tensor A T).flip.obj ((comparison A T).obj L)) r).obj
          M) := by
  induction r with
  | zero => exact ⟨K, hK, ⟨eM⟩⟩
  | succ r ih =>
    obtain ⟨Q, hQ, ⟨e⟩⟩ := ih
    refine ⟨((Etale.derivedTensor (ModuleCat.{u + 1} A) T).obj Q).obj L,
      Etale.constructibleFiniteTor_tensor A T hQ hL, ⟨?_⟩⟩
    exact tensorComparison A T Q L ≪≫
      ((tensor A T).flip.obj ((comparison A T).obj L)).mapIso e

-- Cache the exact-comparison single isomorphism before specializing its ring.
private def comparedSingleIso (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  (Functor.mapDerivedCategorySingleFunctor
    (comparisonUpperStar (ModuleCat.{u + 1} A) T) 0).app F

-- Construct an etale origin by the same ordered tensor recursion as the target.
private theorem tatePower_origin (P : PurityFiniteSetting.{u}) (n : ℕ)
    (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k)) (r : ℕ) :
    ∃ K : Etale.DerivedCategoryModule (setting P n).Coefficient T,
      etaleFiniteTor (setting P n).Coefficient T K ∧
      Nonempty ((comparison (setting P n).Coefficient T).obj K ≅ tatePower P n T r) := by
  let A := (setting P n).Coefficient
  have : Finite (setting P n).Ring :=
    Padic.finite_coefficientExtensionRing (setting P n).coefficients.l
      (setting P n).extension (setting P n).level (setting P n).level_pos
  have : Finite A := Finite.of_equiv (setting P n).Ring Equiv.ulift.symm
  let L := (Etale.ordinaryFiniteLine A
    ((setting P n).coefficients.l ^ ((setting P n).level + 1))
    (annihilates (setting P n)) T)⟦(2 : ℤ)⟧
  have hL : etaleFiniteTor A T L := finiteLine_properties A T _
    (pow_pos (Fact.out : (setting P n).coefficients.l.Prime).pos _)
    (annihilates (setting P n)) (exponentUnit (setting P n) T aT)
  let eUnit := comparedSingleIso A T ((setting P n).constantEtale T) ≪≫
    (eqToIso (unit_single_eq P n T)).symm
  unfold tatePower AffineZeroPurity.target AffineSpacePurity.shiftedLine
  exact tensorPowers_origin A T
    ((_root_.DerivedCategory.singleFunctor _ 0).obj ((setting P n).constantEtale T))
    L (unit_finiteTor P n T) hL (unit P n T) eUnit r

-- Rnu_* preserves the constructible origin and comparison detects its Tor interval.
private theorem canonical_origin_properties (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) (K : AffineSpacePurity.C A T)
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T K) :
    etaleFiniteTor A T
      ((comparisonLowerStar (ModuleCat.{u + 1} A) T).rightDerivedFunctor.obj K) ∧
    IsIso ((derivedComparisonAdjunction (ModuleCat.{u + 1} A) T).counit.app K) := by
  have hi := (DerivedCategory.plusEtaleOrigin_iff K).mp hK.plusEtaleOrigin
  have := hi.2
  refine ⟨?_, hi.2⟩
  obtain ⟨H, hH, ⟨e⟩⟩ := hK.1
  let U := (comparisonLowerStar (ModuleCat.{u + 1} A) T).rightDerivedFunctor
  let adj := derivedComparisonAdjunction (ModuleCat.{u + 1} A) T
  have := isIso_derivedComparisonAdjunction_unit_app (ModuleCat.{u + 1} A) T H hH.1.1
  have hb := (Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) T).prop_of_iso
    (asIso (adj.unit.app H) ≪≫ U.mapIso e) hH
  obtain ⟨a, b, hab⟩ := hK.2
  refine ⟨hb, a, b, DerivedCategory.torAmplitudeIn_of_mapDerivedCategory_comparisonUpperStar
    A ?_⟩
  exact (DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) T a b).prop_of_iso
    (asIso (adj.counit.app K)).symm hab

end OriginProofs

/-- The Tate tensor power is bounded constructible of finite Tor amplitude.
Source: proof Step 1 (blueprint: lem-pur-coordinate-tower-normalization-induction).
Proof: the finite Tate line is etale locally free of rank one with finite stalks
by lem-pur-twist-sheaf-locally-free (3). Tensoring r such lines and shifting by 2r
puts the sole cohomology in degree -2r and gives Tor interval [-2r,-2r].
The coefficient unit is the r=0 case. Exact comparison gives etale origin;
its fully faithful bounded-below comparison identifies Rnu_* with that antecedent.
Thus the canonical ordinaryTarget is also constructible of finite Tor amplitude.
All objects vanish for an empty base. -/
theorem target_properties (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (r : ℕ) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} (setting P n).Coefficient)
        (iteratedAffineLine B r) (tatePower P n (iteratedAffineLine B r) r) ∧
      etaleFiniteTor (setting P n).Coefficient (iteratedAffineLine B r)
        (ordinaryTarget P n B r) ∧
      IsIso ((derivedComparisonAdjunction (ModuleCat.{u + 1} (setting P n).Coefficient)
        (iteratedAffineLine B r)).counit.app (tatePower P n (iteratedAffineLine B r) r)) := by
  have : Finite (setting P n).Ring :=
    Padic.finite_coefficientExtensionRing (setting P n).coefficients.l
      (setting P n).extension (setting P n).level (setting P n).level_pos
  have : Finite (setting P n).Coefficient :=
    Finite.of_equiv (setting P n).Ring Equiv.ulift.symm
  obtain ⟨K, hK, ⟨e⟩⟩ := tatePower_origin P n (iteratedAffineLine B r) (towerBase aB r) r
  have ht := (DerivedCategory.constructibleFiniteTor
    (ModuleCat.{u + 1} (setting P n).Coefficient) (iteratedAffineLine B r)).prop_of_iso e
    (DerivedCategory.constructibleFiniteTor_mapDerivedCategory (setting P n).Coefficient hK)
  exact ⟨ht, canonical_origin_properties (setting P n).Coefficient _ _ ht⟩

/-- The canonical comparison counit, made an iso by the Tate-power origin calculation.
Source: proof Step 1 (blueprint: lem-pur-coordinate-tower-normalization-induction). -/
@[irreducible]
def targetComparison (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (r : ℕ) :
    (comparison (setting P n).Coefficient (iteratedAffineLine B r)).obj
      (ordinaryTarget P n B r) ≅ tatePower P n (iteratedAffineLine B r) r :=
  letI := (target_properties P n B aB r).2.2
  asIso ((derivedComparisonAdjunction (ModuleCat.{u + 1} (setting P n).Coefficient)
    (iteratedAffineLine B r)).counit.app (tatePower P n (iteratedAffineLine B r) r))

/-- The actual ordered identification W_(r+1) with Lq_r*W_r(1)[2].
Source: proof Step 2, the I_r identification
(blueprint: lem-pur-coordinate-tower-normalization-induction). -/
@[irreducible]
def stepSource (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k)) (r : ℕ) :
    tatePower P n (iteratedAffineLine B (r + 1)) (r + 1) ≅
      (lineSource (setting P n) (iteratedAffineLine B r)).obj
        (tatePower P n (iteratedAffineLine B r) r) :=
  targetSourceIso P n B (r + 1) ≪≫
    sourceReassociation (setting P n) B aB (coefficientUnit P n B) r ≪≫
    (lineSource (setting P n) (iteratedAffineLine B r)).mapIso
      (targetSourceIso P n B r).symm

/-- The line comparison v_r, expressed at the actual ordered Tate targets.
Source: v_r in proof Step 2
(blueprint: lem-pur-coordinate-tower-normalization-induction). -/
@[irreducible]
def targetLineGamma (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (r : ℕ) :
    tatePower P n (iteratedAffineLine B (r + 1)) (r + 1) ⟶
      (rightDerivedUpperShriek (setting P n).Coefficient
        (lastProjection B r)).obj (tatePower P n (iteratedAffineLine B r) r) :=
  (stepSource P n B aB r).hom ≫ lineGamma P n B aB r
    ⟨_, target_plus P n _ (towerBase aB r) r⟩ (ordinaryTarget P n B r)
    (target_properties P n B aB r).2.1 (targetComparison P n B aB r)

/-- Contract s_r! q_r! using the inverse mate of the fixed compositor and q_r s_r=id.
Source: e_(q_r) in proof Steps 3 and 5
(blueprint: lem-pur-coordinate-tower-normalization-induction). -/
@[irreducible]
def lineCollapse (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (r : ℕ) :
    (rightDerivedUpperShriek (setting P n).Coefficient
      (lastSection B r)).obj
        ((rightDerivedUpperShriek (setting P n).Coefficient
          (lastProjection B r)).obj (tatePower P n (iteratedAffineLine B r) r)) ⟶
      tatePower P n (iteratedAffineLine B r) r :=
  letI : IsNoetherian (iteratedAffineLine B r) := tower_noetherian (setting P n) B aB r
  letI : IsNoetherian (iteratedAffineLine B (r + 1)) :=
    tower_noetherian (setting P n) B aB (r + 1)
  letI : IsNoetherian (AffineSpace PUnit.{u + 1} (iteratedAffineLine B r)) :=
    tower_noetherian (setting P n) B aB (r + 1)
  let h := AffineSpace.zeroSection_comp_over PUnit.{u + 1} (iteratedAffineLine B r)
  letI : HasCompactification (lastSection B r ≫ lastProjection B r) :=
    HasCompactification.of_eq (f := 𝟙 (iteratedAffineLine B r)) h.symm
  compositionInverse (setting P n).Coefficient (lastSection B r) (lastProjection B r)
      ⟨_, target_plus P n _ (towerBase aB r) r⟩ ≫
    (rightDerivedUpperShriekCongr (setting P n).Coefficient h).hom.app
      (tatePower P n (iteratedAffineLine B r) r) ≫
    @inv _ _ _ _ (identityUnit (setting P n).Coefficient (iteratedAffineLine B r)
      (tatePower P n (iteratedAffineLine B r) r) (target_properties P n B aB r).1.plusEtaleOrigin)
      (identityUnit_isIso _ _ _ (target_properties P n B aB r).1.plusEtaleOrigin)

/-- The inverse closed composition comparison d_r^-1, with no orientation choice.
Source: theta recursion in the statement and proof Step 5
(blueprint: lem-pur-coordinate-tower-normalization-induction). -/
@[irreducible]
def closedCompositionInverse (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (r : ℕ) :
    (rightDerivedUpperShriek (setting P n).Coefficient (zero B r)).obj
      ((rightDerivedUpperShriek (setting P n).Coefficient
        (lastSection B r)).obj (tatePower P n (iteratedAffineLine B (r + 1)) (r + 1))) ⟶
    (rightDerivedUpperShriek (setting P n).Coefficient
      (zero B (r + 1))).obj (tatePower P n (iteratedAffineLine B (r + 1)) (r + 1)) :=
  letI : IsNoetherian (iteratedAffineLine B r) := tower_noetherian (setting P n) B aB r
  letI : IsNoetherian (iteratedAffineLine B (r + 1)) :=
    tower_noetherian (setting P n) B aB (r + 1)
  letI : IsNoetherian (AffineSpace PUnit.{u + 1} (iteratedAffineLine B r)) :=
    tower_noetherian (setting P n) B aB (r + 1)
  let z : B ⟶ AffineSpace PUnit.{u + 1} (iteratedAffineLine B r) := zero B (r + 1)
  let h : zero B r ≫ lastSection B r = z := zero_successor B r
  letI : IsClosedImmersion z := zero_closed B (r + 1)
  letI hZero : HasCompactification z := HasCompactification.of_isProper z
  letI hComp : HasCompactification (zero B r ≫ lastSection B r) :=
    HasCompactification.of_eq (f := z) h.symm
  compositionInverse (setting P n).Coefficient (zero B r) (lastSection B r)
      ⟨_, target_plus P n _ (towerBase aB (r + 1)) (r + 1)⟩ ≫
    (@rightDerivedUpperShriekCongr
      (setting P n).Coefficient inferInstance inferInstance
      B (AffineSpace PUnit.{u + 1} (iteratedAffineLine B r))
      (zero B r ≫ lastSection B r) z h hComp hZero).hom.app
          (tatePower P n (iteratedAffineLine B (r + 1)) (r + 1))

/-- The finite family of supplied maps u_r, with no invertibility required.
Source: the given u_r in the statement
(blueprint: lem-pur-coordinate-tower-normalization-induction). -/
abbrev Orientations (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u}) (c : ℕ) :=
  ∀ r : Fin c, tatePower P n (iteratedAffineLine B r.val) r.val ⟶
    (rightDerivedUpperShriek (setting P n).Coefficient
      (lastSection B r.val)).obj
        (tatePower P n (iteratedAffineLine B (r.val + 1)) (r.val + 1))

/-- theta_0 is the identity under the canonical exceptional identity normalization.
Source: theta_0=1 and proof Step 4
(blueprint: lem-pur-coordinate-tower-normalization-induction). -/
@[irreducible]
def thetaZero (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] :
    coefficientUnit P n B ⟶
      (rightDerivedUpperShriek (setting P n).Coefficient
        (zero B 0)).obj (tatePower P n (iteratedAffineLine B 0) 0) :=
  letI : IsNoetherian B := tower_noetherian (setting P n) B aB 0
  letI hId : HasCompactification (𝟙 B) := HasCompactification.of_isProper (𝟙 B)
  letI hZero : HasCompactification (zero B 0 : B ⟶ B) :=
    @HasCompactification.of_eq B B (𝟙 B) (zero B 0) hId (zero_zero B).symm
  identityUnit (setting P n).Coefficient B (coefficientUnit P n B) (unit_origin P n B) ≫
    (@rightDerivedUpperShriekCongr
      (setting P n).Coefficient inferInstance inferInstance
      B B (zero B 0) (𝟙 B) (zero_zero B) hZero hId).inv.app (coefficientUnit P n B)

/-- The hom type in the recurrence, with its derived category instance cached.
Source: theta_r in the displayed recurrence
(blueprint: lem-pur-coordinate-tower-normalization-induction). -/
abbrev ThetaHom (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u}) (r : ℕ) :=
  coefficientUnit P n B ⟶
    (rightDerivedUpperShriek (setting P n).Coefficient
      (zero B r)).obj (tatePower P n (iteratedAffineLine B r) r)

/-- Map a supplied arrow and compose with the specified comparison; the categories
are fixed before specializing the coefficient ring and the coordinate tower.
Source: the theta successor formula
(blueprint: lem-pur-coordinate-tower-normalization-induction). -/
def mapComposition {C : Type v₁} [Category.{w₁} C] {D : Type v₂} [Category.{w₂} D]
    (F : C ⥤ D) {M N : C} {V W : D}
    (t : V ⟶ F.obj M) (a : M ⟶ N) (d : F.obj N ⟶ W) : V ⟶ W :=
  t ≫ F.map a ≫ d

/-- The actual successor composite with its computed target retained.
Source: theta_(r+1)=d_r^-1 Rz_r!(u_r) theta_r
(blueprint: lem-pur-coordinate-tower-normalization-induction). -/
@[irreducible]
def thetaStepRaw (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB]
    (c : ℕ) (u : Orientations P n B c) (r : ℕ) (hr : r < c)
    (previous : ThetaHom P n B r) :
    Σ N : AffineSpacePurity.C (setting P n).Coefficient B, coefficientUnit P n B ⟶ N :=
  ⟨_, mapComposition
    (rightDerivedUpperShriek (setting P n).Coefficient (zero B r))
    previous (u ⟨r, hr⟩) (closedCompositionInverse P n B aB r)⟩

/-- The retained endpoint is literally the exceptional target in the recurrence.
Source: the theta successor display
(blueprint: lem-pur-coordinate-tower-normalization-induction).
Proof: unfold thetaStepRaw. Its last arrow is closedCompositionInverse, whose
specified codomain is Rz_(r+1)! W_(r+1). The preceding factors leave that
codomain unchanged. This equality only exposes that computed endpoint. -/
theorem thetaStepRaw_target (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB]
    (c : ℕ) (u : Orientations P n B c) (r : ℕ) (hr : r < c)
    (previous : ThetaHom P n B r) :
    (thetaStepRaw P n B aB c u r hr previous).1 =
      (rightDerivedUpperShriek (setting P n).Coefficient
        (zero B (r + 1))).obj (tatePower P n (iteratedAffineLine B (r + 1)) (r + 1)) := by
  unfold thetaStepRaw
  rfl

/-- One literal successor, in the shared ambient derived-category coordinates.
Source: theta_(r+1)=d_r^-1 Rz_r!(u_r) theta_r
(blueprint: lem-pur-coordinate-tower-normalization-induction). -/
@[irreducible]
def thetaStep (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB]
    (c : ℕ) (u : Orientations P n B c) (r : ℕ) (hr : r < c)
    (previous : ThetaHom P n B r) : ThetaHom P n B (r + 1) :=
  (thetaStepRaw P n B aB c u r hr previous).2 ≫
    eqToHom (thetaStepRaw_target P n B aB c u r hr previous)

/-- The specified finite recurrence; the bound proof only selects an index of u.
Source: theta_(r+1)=d_r^-1 Rz_r!(u_r) theta_r
(blueprint: lem-pur-coordinate-tower-normalization-induction). -/
@[irreducible]
def theta (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB]
    (c : ℕ) (u : Orientations P n B c) : (r : ℕ) → (_hr : r ≤ c) → ThetaHom P n B r :=
  orderedRec (H := fun r ↦ (_hr : r ≤ c) → ThetaHom P n B r)
    (fun _ ↦ thetaZero P n B aB)
    (fun r previous hr ↦ thetaStep P n B aB c u r (Nat.lt_of_succ_le hr)
      (previous (Nat.le_of_succ_le hr)))

/-- The actual ordered gamma with its computed exceptional target retained.
Zero uses the canonical exceptional identity unit; positive stages use the
published ordered comparison, preceded by its canonical unit-pullback iso.
Source: gamma_r in the statement
(blueprint: lem-pur-coordinate-tower-normalization-induction). -/
@[irreducible]
def projectionGammaRaw (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] : (r : ℕ) →
    Σ N : AffineSpacePurity.C (setting P n).Coefficient (iteratedAffineLine B r),
      tatePower P n (iteratedAffineLine B r) r ⟶ N
  | 0 =>
    letI : IsNoetherian B := tower_noetherian (setting P n) B aB 0
    ⟨_, identityUnit (setting P n).Coefficient B (coefficientUnit P n B) (unit_origin P n B)⟩
  | r + 1 => ⟨_, (targetSourceIso P n B (r + 1)).hom ≫ gamma P n B aB (r + 1)⟩

/-- The retained target is exactly the exceptional inverse image along p_r.
Source: actual gamma_r and dimension-zero identity conventions
(blueprint: lem-pur-coordinate-tower-normalization-induction).
Proof: at zero projectionGammaRaw is identityUnit and p_0=id, giving precisely
the stated target. At a successor unfold exceptional at its outermost successor:
it is the specified rightDerivedUpperShriek of iteratedAffineLineProj. Its
argument is the same coefficient unit. Only this computed endpoint is exposed. -/
theorem projectionGammaRaw_target (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (r : ℕ) :
    (projectionGammaRaw P n B aB r).1 =
      (rightDerivedUpperShriek (setting P n).Coefficient
        (iteratedAffineLineProj B r)).obj (coefficientUnit P n B) := by
  cases r with
  | zero =>
    unfold projectionGammaRaw
    rfl
  | succ r =>
    unfold projectionGammaRaw exceptional
    rfl

/-- gamma_r at the actual Tate target, retaining the canonical unit-pullback comparison.
The endpoint equality only exposes the target of the actual raw comparison.
Source: actual gamma_r in the statement
(blueprint: lem-pur-coordinate-tower-normalization-induction). -/
@[irreducible]
def projectionGamma (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (r : ℕ) :
    tatePower P n (iteratedAffineLine B r) r ⟶
      (rightDerivedUpperShriek (setting P n).Coefficient
        (iteratedAffineLineProj B r)).obj (coefficientUnit P n B) :=
  (projectionGammaRaw P n B aB r).2 ≫ eqToHom (projectionGammaRaw_target P n B aB r)

/-- The adjunct a_r of the actual ordered projection comparison.
Source: proof Step 8 (blueprint: lem-pur-coordinate-tower-normalization-induction). -/
@[irreducible]
def augmentation (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (r : ℕ) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
      (iteratedAffineLineProj B r)).obj (tatePower P n (iteratedAffineLine B r) r) ⟶
        coefficientUnit P n B :=
  letI : IsNoetherian B := tower_noetherian (setting P n) B aB 0
  (rightDerivedUpperShriekHomEquiv (iteratedAffineLineProj B r)
    (target_properties P n B aB r).1.plusEtaleOrigin (unit_origin P n B).plus).symm
      (projectionGamma P n B aB r)

end AlgebraicGeometry.ProEtale.CoordinateTowerNormalization

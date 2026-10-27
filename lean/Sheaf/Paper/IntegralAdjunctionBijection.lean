/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.Paper.IntegralReconstructionComparisonData
import Sheaf.Paper.IntegralAdjunctionReconstruction
import Sheaf.Paper.IntegralAdjunctionSourceComparison
import Sheaf.Paper.SfDerivedCompleteLegacyComparison
public import Sheaf.Paper.SmoothPurityTowerGamma
public import Sheaf.Paper.TwistedPullbackReductionTower
public import Sheaf.Paper.CompleteCompactificationLimitSupport
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
import Mathlib.CategoryTheory.Adjunction.Restrict
public import Sheaf.Paper.CompleteCompactificationLimitRealization

/-! # Realization of the smooth tower adjunction

Source: latest blueprint, sec-smooth-purity/sk-prop-sp-integral-adjunction,
sk-prop-sp-integral-adjunction-bijection.md
(blueprint: det-sp-integral-adjunction-bijection).

The integral category is the published completed-coefficient category. Every tower
morphism below is in the ordinary derived category of strict varying-coefficient
systems. A natural-number index n denotes the positive exponent n+1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpIntegralAdjunction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The three bijections, including both directions of the comparison at the ends.
All morphisms are entire-tower morphisms. The middle bijection is the given adjunction.
Source: Bijections, displayed Hom chain
(blueprint: det-sp-integral-adjunction-bijection). -/
def homChain {X Y : Scheme.{u}} {f : X ⟶ Y} (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (q : SpTowerCalculus.Coordinates l E b)
    (c : Compactification f)
    (hF : ∀ M : SpTowerCalculus.C l E b q X,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((SpTowerCalculus.F l E b o q c).obj M.obj))
    (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
    (a : SpTowerGluing.support l E b o q c hF ⊣ G)
    (F : sfIntegralConstructibleCategory l E X ⥤ sfIntegralConstructibleCategory l E Y)
    (H : sfIntegralConstructibleCategory l E Y ⥤ sfIntegralConstructibleCategory l E X)
    (rX : sfIntegralConstructibleCategory l E X ⥤ SpTowerCalculus.C l E b q X)
    (rY : sfIntegralConstructibleCategory l E Y ⥤ SpTowerCalculus.C l E b q Y)
    (iX : rX.FullyFaithful) (iY : rY.FullyFaithful)
    (β : F ⋙ rY ≅ rX ⋙ SpTowerGluing.support l E b o q c hF)
    (χ : H ⋙ rX ≅ rY ⋙ G)
    (M : sfIntegralConstructibleCategory l E X)
    (K : sfIntegralConstructibleCategory l E Y) :
    (F.obj M ⟶ K) ≃ (M ⟶ H.obj K) :=
  iY.homEquiv.trans
    ((Iso.homCongr (β.app M) (Iso.refl _)).trans
      ((a.homEquiv _ _).trans
        ((Iso.homCongr (Iso.refl _) (χ.app K).symm).trans iX.homEquiv.symm)))

/-- The integral adjunction, with its whole-tower normalization and realized purity map.
The source comparison is asserted to exist; the isomorphism claim holds for every
source comparison, hence in particular for the canonical pullback/Tate/shift comparison.
No lift of a family of finite derived arrows is chosen.
Source: Normalization, Bijections and Purity
(blueprint: det-sp-integral-adjunction-bijection). -/
structure Realization {X Z Y : Scheme.{u}}
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : SpTowerCalculus.Coordinates l E b)
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
    [QuasiCompact (j ≫ p)] [HasCompactification (j ≫ p)]
    (d : ℕ) (w : SpChartAdmissibility.Twists l E X)
    (RX : SpReductionTower l E X (q.abelian X))
    (NX : SpNormalizedEquivalence l E X (q.abelian X) RX)
    (RY : SpReductionTower l E Y (q.abelian Y))
    (NY : SpNormalizedEquivalence l E Y (q.abelian Y) RY)
    (hF : ∀ M : SpTowerCalculus.C l E b q X,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((SpTowerCalculus.F l E b o q (SpTowerGamma.factorization j p)).obj M.obj))
    (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
    (a : SpTowerGluing.support l E b o q (SpTowerGamma.factorization j p) hF ⊣ G)
    (lv : SpTowerGluing.Levels l E b o q (SpTowerGamma.factorization j p) hF G a)
    extends Reconstruction l E b o q j p RX NX RY NY hF G a where
  purity : SpTowerGamma.Purity l E b o q j p d w hF G a lv
  adjunction : support l E (SpTowerGamma.factorization j p) support_closed ⊣
    right l E b q RX NX RY reductionY G closed
  hom_equiv : ∀ (M : sfIntegralConstructibleCategory l E X)
      (K : sfIntegralConstructibleCategory l E Y),
    adjunction.homEquiv M K = homChain l E b o q (SpTowerGamma.factorization j p)
      hF G a (support l E (SpTowerGamma.factorization j p) support_closed)
      (right l E b q RX NX RY reductionY G closed)
      (reduce l E X (q.abelian X) RX reductionX)
      (reduce l E Y (q.abelian Y) RY reductionY)
      fullyFaithfulX fullyFaithfulY leftComparison rightComparison M K
  unit_reduction : ∀ M : sfIntegralConstructibleCategory l E X,
    (reduce l E X (q.abelian X) RX reductionX).map (adjunction.unit.app M) =
      a.unit.app ((reduce l E X (q.abelian X) RX reductionX).obj M) ≫
        G.map (leftComparison.inv.app M) ≫ rightComparison.inv.app _
  counit_reduction : ∀ K : sfIntegralConstructibleCategory l E Y,
    (reduce l E Y (q.abelian Y) RY reductionY).map (adjunction.counit.app K) =
      leftComparison.hom.app _ ≫
        (SpTowerGluing.support l E b o q (SpTowerGamma.factorization j p) hF).map
          (rightComparison.hom.app K) ≫
        a.counit.app ((reduce l E Y (q.abelian Y) RY reductionY).obj K)
  finite_unit : ∀ (n : ℕ) (M : sfIntegralConstructibleCategory l E X),
    (spDerivedCoefficientEvaluation l E X (q.abelian X) n).map
        (((reduce l E X (q.abelian X) RX reductionX).map (adjunction.unit.app M) ≫
          rightComparison.hom.app _).hom) ≫
      ((lv.comparison n).hom.app
        ((reduce l E Y (q.abelian Y) RY reductionY).obj
          ((support l E (SpTowerGamma.factorization j p) support_closed).obj M))).hom ≫
      ((lv.right n).map (ObjectProperty.homMk
        ((spDerivedCoefficientEvaluation l E Y (q.abelian Y) n).map
            (leftComparison.hom.app M).hom ≫
          (lv.support_evaluation n).comparison.hom.app
            ((reduce l E X (q.abelian X) RX reductionX).obj M).obj))).hom =
      ((lv.adjunction n).unit.app ((SpTowerGluing.level l E b q X n).obj
        ((reduce l E X (q.abelian X) RX reductionX).obj M))).hom
  finite_counit : ∀ (n : ℕ) (K : sfIntegralConstructibleCategory l E Y),
    (lv.support_evaluation n).comparison.inv.app
        ((reduce l E X (q.abelian X) RX reductionX).obj
          ((right l E b q RX NX RY reductionY G closed).obj K)).obj ≫
      (spDerivedCoefficientEvaluation l E Y (q.abelian Y) n).map
        ((leftComparison.inv.app _ ≫
          (reduce l E Y (q.abelian Y) RY reductionY).map (adjunction.counit.app K)).hom) =
      (reductionCompactSupport (SpTowerShriek.R l E n) j p).map
        ((spDerivedCoefficientEvaluation l E X (q.abelian X) n).map
            (rightComparison.hom.app K).hom ≫
          ((lv.comparison n).hom.app
            ((reduce l E Y (q.abelian Y) RY reductionY).obj K)).hom) ≫
      ((lv.adjunction n).counit.app ((SpTowerGluing.level l E b q Y n).obj
        ((reduce l E Y (q.abelian Y) RY reductionY).obj K))).hom
  unit_limit : ∀ M : sfIntegralConstructibleCategory l E X,
    (adjunction.unit.app M).hom = (reconstructionX M).hom ≫
      (limit l E X (q.abelian X) RX NX).map
        ((a.unit.app ((reduce l E X (q.abelian X) RX reductionX).obj M) ≫
          G.map (leftComparison.inv.app M) ≫ rightComparison.inv.app _).hom) ≫
      (reconstructionX _).inv
  counit_limit : ∀ K : sfIntegralConstructibleCategory l E Y,
    (adjunction.counit.app K).hom = (reconstructionY _).hom ≫
      (limit l E Y (q.abelian Y) RY NY).map
        ((leftComparison.hom.app _ ≫
          (SpTowerGluing.support l E b o q (SpTowerGamma.factorization j p) hF).map
            (rightComparison.hom.app K) ≫
          a.counit.app ((reduce l E Y (q.abelian Y) RY reductionY).obj K)).hom) ≫
      (reconstructionY K).inv
  sourceComparison :
    SpTwistedPullback.source l E (j ≫ p) (d : ℤ) (2 * (d : ℤ)) ⋙
        SpTwistedPullback.reduction l E b X (q.abelian X) RX ≅
      reduce l E Y (q.abelian Y) RY reductionY ⋙
        SpTowerGamma.source l E b o q (j ≫ p) w d
  source_complete : ∀ K : sfIntegralConstructibleCategory l E Y,
    sfIntegralConstructible l E X
      ((SpTwistedPullback.source l E (j ≫ p) (d : ℤ) (2 * (d : ℤ))).obj K)
  purity_realization : ∀
      (s : SpTwistedPullback.source l E (j ≫ p) (d : ℤ) (2 * (d : ℤ)) ⋙
          SpTwistedPullback.reduction l E b X (q.abelian X) RX ≅
        reduce l E Y (q.abelian Y) RY reductionY ⋙
          SpTowerGamma.source l E b o q (j ≫ p) w d)
      (K : sfIntegralConstructibleCategory l E Y),
    IsIso (NX.adjunction.unit.app
        ((SpTwistedPullback.source l E (j ≫ p) (d : ℤ) (2 * (d : ℤ))).obj K) ≫
      (limit l E X (q.abelian X) RX NX).map
        ((SpTowerCalculus.realization l E b X (q.abelian X)).unitIso.hom.app _ ≫
          (SpTowerCalculus.realization l E b X (q.abelian X)).inverse.map
            (s.hom.app K ≫
              SpTowerGamma.gamma l E b o q (SpTowerGamma.factorization j p) w d
                purity.tensorX purity.tensorY hF G a purity.unit_mem purity.orientation
                ((reduce l E Y (q.abelian Y) RY reductionY).obj K)
                (purity.tensor_mem _) (purity.projection_iso _)) ≫
          (SpTowerCalculus.realization l E b X (q.abelian X)).unitIso.inv.app _))

/-- The reconstruction package with its geometric instances derived from the standing
finite-type setting and the specified compactification, rather than assumed separately.
Source: latest blueprint, integral adjunction
(blueprint: det-sp-integral-adjunction-bijection). -/
def realizationResult
    (D : FiniteFieldDatum.{u})
    {X Z Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
    [(j ≫ p).IsOver (Spec (.of D.k))]
    (d : ℕ)
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : SpTowerCalculus.Coordinates l E b) (w : SpChartAdmissibility.Twists l E X)
    (RX : SpReductionTower l E X (q.abelian X))
    (NX : SpNormalizedEquivalence l E X (q.abelian X) RX)
    (RY : SpReductionTower l E Y (q.abelian Y))
    (NY : SpNormalizedEquivalence l E Y (q.abelian Y) RY)
    (hF : ∀ M : SpTowerCalculus.C l E b q X,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((SpTowerCalculus.F l E b o q (SpTowerGamma.factorization j p)).obj M.obj))
    (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
    (a : SpTowerGluing.support l E b o q (SpTowerGamma.factorization j p) hF ⊣ G)
    (lv : SpTowerGluing.Levels l E b o q (SpTowerGamma.factorization j p) hF G a) : Type _ :=
  letI : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k))
  letI : QuasiSeparatedSpace Y :=
    quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of D.k))
  letI : QuasiCompact (j ≫ p) := inferInstance
  letI : HasCompactification (j ≫ p) := (SpTowerGamma.factorization j p).hasCompactification
  Realization l E b o q j p d w RX NX RY NY hF G a lv

/-- The tower adjunction realizes to the integral adjunction and its smooth purity
isomorphism, for every separated smooth pure-dimensional map in the standing setting.
Source: latest blueprint integral-adjunction-bijection, all three paragraphs
(blueprint: det-sp-integral-adjunction-bijection).

Proof:
1. lem-sp-integral-reconstruction-comparisons supplies normalized reductions,
constructibility of L_X G red_Y, fully faithful reductions, the natural compact-support
comparison b and the actual reconstruction counit c. This follows from the normalized
equivalence and the canonical complete-compactification limit comparison; finite type
over the field makes X and Y Noetherian. Both functors preserve normalized towers by
 det-sp-tower-gamma (3), so the tower adjunction restricts to those full subcategories.
2. Apply lem-sp-fully-faithful-adjunction-restriction, namely Mathlib's
Adjunction.restrictFullyFaithful, with b.symm and c.symm. Its Hom equivalence is the
three displayed bijections. Naturality gives the two triangles and its unit/counit
formulas are exactly unit_reduction and counit_reduction.
3. Naturality of the reconstruction unit gives a=u_A L_X(red(a)) u_B^{-1}.
Apply this to the preceding two morphisms: the integral unit and counit are their
actual derived-limit realizations. Apply exact finite evaluation and the unit/counit
identities of det-sp-tower-gluing (3); their reductions are the finite units/counits.
4. lem-sp-twisted-pullback-reduction-tower identifies the simultaneous reduction of
completed pullback, Tate twist and shift with their finite tower operations. Reassociate
the tensor powers into the ordered-line presentation of det-sp-tower-gamma. The source
is complete and its reconstruction unit invertible. The entire-tower gamma is invertible
by det-sp-tower-gamma (2). Its image under the inverse realization and total-limit
functors is invertible, proving purity_realization for every source comparison. -/
theorem integral_adjunction_bijection
    (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    {X Z Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
    [(j ≫ p).IsOver (Spec (.of D.k))]
    (d : ℕ) [SmoothOfRelativeDimension d (j ≫ p)]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : SpTowerCalculus.Coordinates l E b) (w : SpChartAdmissibility.Twists l E X)
    (RX : SpReductionTower l E X (q.abelian X))
    (NX : SpNormalizedEquivalence l E X (q.abelian X) RX)
    (RY : SpReductionTower l E Y (q.abelian Y))
    (NY : SpNormalizedEquivalence l E Y (q.abelian Y) RY)
    (hF : ∀ M : SpTowerCalculus.C l E b q X,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((SpTowerCalculus.F l E b o q (SpTowerGamma.factorization j p)).obj M.obj))
    (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
    (a : SpTowerGluing.support l E b o q (SpTowerGamma.factorization j p) hF ⊣ G)
    (lv : SpTowerGluing.Levels l E b o q (SpTowerGamma.factorization j p) hF G a) :
    Nonempty (realizationResult l E D j p d b o q w RX NX RY NY hF G a lv) := by
  classical
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k))
  have : QuasiSeparatedSpace Y :=
    quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of D.k))
  have : QuasiCompact (j ≫ p) := inferInstance
  have : HasCompactification (j ≫ p) := (SpTowerGamma.factorization j p).hasCompactification
  obtain ⟨r⟩ := integralAdjunctionReconstruction l E D _hl j p d b o q w RX NX RY NY
    hF G a lv
  change Reconstruction l E b o q j p RX NX RY NY hF G a at r
  have := r.noetherianX
  have := r.noetherianY
  have : Fact D.p.Prime := ⟨D.prime⟩
  let : Fintype D.k₀ := Fintype.ofFinite _
  have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card).symm.trans (D.card_base.trans D.cardinality_eq))
  have : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  obtain ⟨pur⟩ := SpTowerGamma.tower_gamma l E b o q D _hl j p d w hF G a lv
  let XO := X.asOver (Spec (.of D.k))
  let YO := Y.asOver (Spec (.of D.k))
  let fO : XO ⟶ YO := (j ≫ p).asOver (Spec (.of D.k))
  have : IsSeparated XO.hom := by change IsSeparated (X ↘ Spec (.of D.k)); infer_instance
  have : LocallyOfFiniteType XO.hom := by
    change LocallyOfFiniteType (X ↘ Spec (.of D.k)); infer_instance
  have : QuasiCompact XO.hom := by change QuasiCompact (X ↘ Spec (.of D.k)); infer_instance
  have : IsSeparated YO.hom := by change IsSeparated (Y ↘ Spec (.of D.k)); infer_instance
  have : LocallyOfFiniteType YO.hom := by
    change LocallyOfFiniteType (Y ↘ Spec (.of D.k)); infer_instance
  have : QuasiCompact YO.hom := by change QuasiCompact (Y ↘ Spec (.of D.k)); infer_instance
  have : IsSeparated fO.left := by change IsSeparated (j ≫ p); infer_instance
  have : SmoothOfRelativeDimension d fO.left := by
    change SmoothOfRelativeDimension d (j ≫ p); infer_instance
  have hred := SpTwistedPullback.twistedPullbackReductionTower l E D _hl XO YO fO d
    b (o.geometry (j ≫ p)) (q.abelian X) RX NX (q.abelian Y) RY
    (d : ℤ) (2 * (d : ℤ))
  have hs := hred.1
  obtain ⟨hX, hY, AX, AY, FX, FY, cX, cY, cg, ct, tate, shifts, pull, red,
    hpull, hred, hreal⟩ := hred.2
  obtain ⟨ordered⟩ := integralAdjunctionSourceComparison l E (j ≫ p) d hX hY b o q w
    RX RY r.reductionY
  let s := red ≪≫ ordered
  let ad := a.restrictFullyFaithful r.fullyFaithfulX r.fullyFaithfulY
    r.leftComparison.symm r.rightComparison.symm
  have hu (M : sfIntegralConstructibleCategory l E X) :
      (reduce l E X (q.abelian X) RX r.reductionX).map (ad.unit.app M) =
        a.unit.app ((reduce l E X (q.abelian X) RX r.reductionX).obj M) ≫
          G.map (r.leftComparison.inv.app M) ≫ r.rightComparison.inv.app _ :=
    a.map_restrictFullyFaithful_unit_app r.fullyFaithfulX r.fullyFaithfulY
      r.leftComparison.symm r.rightComparison.symm M
  have hc (K : sfIntegralConstructibleCategory l E Y) :
      (reduce l E Y (q.abelian Y) RY r.reductionY).map (ad.counit.app K) =
        r.leftComparison.hom.app _ ≫
          (SpTowerGluing.support l E b o q (SpTowerGamma.factorization j p) hF).map
            (r.rightComparison.hom.app K) ≫
          a.counit.app ((reduce l E Y (q.abelian Y) RY r.reductionY).obj K) :=
    a.map_restrictFullyFaithful_counit_app r.fullyFaithfulX r.fullyFaithfulY
      r.leftComparison.symm r.rightComparison.symm K
  refine ⟨{
    toReconstruction := r
    purity := pur
    adjunction := ad
    hom_equiv := by
      intro M K
      dsimp only [ad, Adjunction.restrictFullyFaithful]
      rw [Adjunction.mkOfHomEquiv_homEquiv]
      rfl
    unit_reduction := hu
    counit_reduction := hc
    finite_unit := ?_
    finite_counit := ?_
    unit_limit := ?_
    counit_limit := ?_
    sourceComparison := s
    source_complete := hs
    purity_realization := ?_ }⟩
  · intro n M
    have hunit :
        (reduce l E X (q.abelian X) RX r.reductionX).map (ad.unit.app M) ≫
            r.rightComparison.hom.app _ =
          a.unit.app ((reduce l E X (q.abelian X) RX r.reductionX).obj M) ≫
            G.map (r.leftComparison.inv.app M) := by
      erw [hu]
      simp only [Category.assoc, Iso.inv_hom_id_app]
      erw [Category.comp_id]
    erw [hunit, ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp]
    have hn := congrArg (InducedCategory.Hom.hom)
      ((lv.comparison n).hom.naturality (r.leftComparison.inv.app M))
    change (spDerivedCoefficientEvaluation l E X (q.abelian X) n).map
        (G.map (r.leftComparison.inv.app M)).hom ≫
        ((lv.comparison n).hom.app _).hom =
      ((lv.comparison n).hom.app _).hom ≫
        ((lv.right n).map ((SpTowerGluing.level l E b q Y n).map
          (r.leftComparison.inv.app M))).hom at hn
    let t :
        (SpTowerGluing.level l E b q Y n).obj
            ((SpTowerGluing.support l E b o q (SpTowerGamma.factorization j p) hF).obj
              ((reduce l E X (q.abelian X) RX r.reductionX).obj M)) ⟶
          (reductionCtfCompactSupport (SpTowerShriek.R l E n)
            (SpTowerGamma.factorization j p).i (SpTowerGamma.factorization j p).g
            (lv.finite_closed n)).obj
              ((SpTowerGluing.level l E b q X n).obj
                ((reduce l E X (q.abelian X) RX r.reductionX).obj M)) :=
      ObjectProperty.homMk ((lv.support_evaluation n).comparison.hom.app
        ((reduce l E X (q.abelian X) RX r.reductionX).obj M).obj)
    have hm :
        (lv.right n).map ((SpTowerGluing.level l E b q Y n).map
            (r.leftComparison.inv.app M)) ≫
          (lv.right n).map
            ((SpTowerGluing.level l E b q Y n).map (r.leftComparison.hom.app M) ≫ t) =
        (lv.right n).map t := by
      erw [← CategoryTheory.Functor.map_comp, ← Category.assoc,
        ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app,
        CategoryTheory.Functor.map_id, Category.id_comp]
    have hn' := congrArg (fun z => z ≫
        ((lv.right n).map
          ((SpTowerGluing.level l E b q Y n).map (r.leftComparison.hom.app M) ≫ t)).hom) hn
    simp only [Category.assoc] at hn'
    have hm' := congrArg (InducedCategory.Hom.hom) hm
    simp only [ObjectProperty.FullSubcategory.comp_hom] at hm'
    erw [Category.assoc, hn', hm']
    exact lv.unit n _
  · intro n K
    have hcounit : r.leftComparison.inv.app _ ≫
        (reduce l E Y (q.abelian Y) RY r.reductionY).map (ad.counit.app K) =
      (SpTowerGluing.support l E b o q (SpTowerGamma.factorization j p) hF).map
          (r.rightComparison.hom.app K) ≫
        a.counit.app ((reduce l E Y (q.abelian Y) RY r.reductionY).obj K) := by
      erw [hc]
      simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
    erw [hcounit, ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp]
    have hn := (lv.support_evaluation n).comparison.inv.naturality
      (r.rightComparison.hom.app K).hom
    change (reductionCompactSupport (SpTowerShriek.R l E n) j p).map
        ((spDerivedCoefficientEvaluation l E X (q.abelian X) n).map
          (r.rightComparison.hom.app K).hom) ≫ _ =
      (lv.support_evaluation n).comparison.inv.app _ ≫
        (spDerivedCoefficientEvaluation l E Y (q.abelian Y) n).map
          ((SpTowerGluing.support l E b o q (SpTowerGamma.factorization j p) hF).map
            (r.rightComparison.hom.app K)).hom at hn
    erw [← Category.assoc, ← hn, Category.assoc, lv.counit]
    rw [CategoryTheory.Functor.map_comp, Category.assoc]
    rfl
  · intro M
    have h := r.reconstructX _ _ (ad.unit.app M)
    rw [show (reduction l E X (q.abelian X) RX).map (ad.unit.app M) =
      ((reduce l E X (q.abelian X) RX r.reductionX).map (ad.unit.app M)).hom from rfl,
      hu] at h
    exact h
  · intro K
    have h := r.reconstructY _ _ (ad.counit.app K)
    rw [show (reduction l E Y (q.abelian Y) RY).map (ad.counit.app K) =
      ((reduce l E Y (q.abelian Y) RY r.reductionY).map (ad.counit.app K)).hom from rfl,
      hc] at h
    exact h
  · intro s K
    obtain ⟨p₀, hp₀, hprime⟩ := Nat.exists_infinite_primes (l + 1)
    let : Fact p₀.Prime := ⟨hprime⟩
    let D₀ : FiniteFieldDatum.{0} :=
      { p := p₀
        a := 1
        q := p₀
        prime := hprime
        exponent_pos := by decide
        cardinality_eq := by simp
        k₀ := ZMod p₀
        card_base := by simp [Nat.card_eq_fintype_card]
        k := AlgebraicClosure (ZMod p₀) }
    have hl₀ : l ≠ D₀.p := by change l ≠ p₀; omega
    have hcomplete : IntegralOnSlice.IsComplete l E X none
        ((SpTwistedPullback.source l E (j ≫ p) (d : ℤ) (2 * (d : ℤ))).obj K) :=
      ⟨D₀, hl₀, (sfDerivedComplete_iff_legacy l E X D₀ hl₀ _).mp (hs K).1⟩
    have := NX.unit_isIso _ hcomplete
    have := pur.purity_iso ((reduce l E Y (q.abelian Y) RY r.reductionY).obj K)
    infer_instance

end AlgebraicGeometry.ProEtale.SpIntegralAdjunction

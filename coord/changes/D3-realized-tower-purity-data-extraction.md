# AlgebraicGeometry.ProEtale.RealizedTowerPurity.realized

## Reason

The normalization lemma must refer to the actual realized, component, finite and
projection words. The main theorem imports that lemma. Extracting the existing
eighteen declarations into TowerPurityRealizedData prevents an import cycle.
This is not a split to address compile timing. All eighteen bodies, signatures,
attributes, namespaces and section variables are preserved verbatim; the original
module publicly re-exports them. The target theorem signature is unchanged.
The two new explicit definitions towerProjection and reduceWord record intermediate
whole-system words without choosing data from existence. No source-library file changes.

## Old

The following definition block belongs to TowerPurityRealizedTranspose:

```lean
namespace AlgebraicGeometry.ProEtale.RealizedTowerPurity

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local irreducible] integralCompletedTensor integralDerivedPullback
  HasDerivedCategory.standard

variable {X Z Y : Scheme.{u}}
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
  (Gb : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
  (ab : SpTowerGluing.support l E b o q (SpTowerGamma.factorization j p) hF ⊣ Gb)
  (lv : SpTowerGluing.Levels l E b o q (SpTowerGamma.factorization j p) hF Gb ab)
  (r : SpIntegralAdjunction.Realization l E b o q j p d w RX NX RY NY hF Gb ab lv)

/-- Realize the entire strict tower gamma after the reconstruction unit, using the
specified source comparison and both coordinate-equivalence units. This is an actual
morphism in the completed-coefficient derived category.
Source: gamma proof (2), integral realization
(blueprint: lem-pur-tower-purity-realized-transpose). -/
def realized
    (K : sfIntegralConstructibleCategory l E Y) :
    (SpTwistedPullback.source l E (j ≫ p) (d : ℤ) (2 * (d : ℤ))).obj K ⟶
      ((SpIntegralAdjunction.right l E b q RX NX RY r.reductionY Gb r.closed).obj K).obj :=
  letI := r.noetherianX
  letI := r.noetherianY
  NX.adjunction.unit.app _ ≫
    (SpIntegralAdjunction.limit l E X (q.abelian X) RX NX).map
      ((SpTowerCalculus.realization l E b X (q.abelian X)).unitIso.hom.app _ ≫
        (SpTowerCalculus.realization l E b X (q.abelian X)).inverse.map
          (r.sourceComparison.hom.app K ≫
            SpTowerGamma.gamma l E b o q (SpTowerGamma.factorization j p) w d
              r.purity.tensorX r.purity.tensorY hF Gb ab r.purity.unit_mem
              r.purity.orientation
              ((SpIntegralAdjunction.reduce l E Y (q.abelian Y) RY r.reductionY).obj K)
              (r.purity.tensor_mem _) (r.purity.projection_iso _)) ≫
        (SpTowerCalculus.realization l E b X (q.abelian X)).unitIso.inv.app _)

end AlgebraicGeometry.ProEtale.RealizedTowerPurity


namespace WeilConjectures.RealizedTowerPurity

open AlgebraicGeometry.ProEtale IntegralSystemRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local irreducible] integralCompletedTensor integralDerivedPullback
  HasDerivedCategory.standard

/-- The integral shifted Tate line. Source: gamma proof (2), T = 1(d)[2d]
(blueprint: lem-pur-tower-purity-realized-transpose). -/
def line (X : Scheme.{u}) (d : ℕ) :=
  ((DerivedCategory.singleFunctor (scalarReductionSource l E X) 0).obj
    (integralTwistLine l E X (d : ℤ)))⟦2 * (d : ℤ)⟧

/-- Move the shift onto the second tensor factor after the actual completion unit.
This fixes sigma, including the signed second-slot tensor shift.
Source: gamma proof (2), twist reassociation
(blueprint: lem-pur-tower-purity-realized-transpose). -/
def reassociation {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ)
    (m : RingedModels l E) (K : sfIntegralConstructibleCategory l E Y) :
    (SpTwistedPullback.source l E f (d : ℤ) (2 * (d : ℤ))).obj K ⟶
      (integralCompletedTensor l E X).obj
        ((integralDerivedPullback l E f).obj K.obj, line l E X d) :=
  (shiftFunctor _ (2 * (d : ℤ))).map
    (eqToHom (congrArg (fun F ↦ F.obj
      ((integralDerivedPullback l E f).obj K.obj,
        (DerivedCategory.singleFunctor _ 0).obj (integralTwistLine l E X (d : ℤ))))
        (m.tensorClosed X).symm) ≫
      ((m.tensor X).chi l E).app
        ((integralDerivedPullback l E f).obj K.obj,
          (DerivedCategory.singleFunctor _ 0).obj (integralTwistLine l E X (d : ℤ)))) ≫
    ((tensorShifts l E).integralRight X (2 * (d : ℤ))).inv.app
      ((integralDerivedPullback l E f).obj K.obj,
        (DerivedCategory.singleFunctor _ 0).obj (integralTwistLine l E X (d : ℤ)))

/-- Unit specialization using normalized completed pullback and the ordinary unitor.
Source: proof step 3, coefficient-unit normalization
(blueprint: lem-pur-tower-purity-realized-transpose). -/
def sourceUnit {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ)
    (core : CompletedUnitPullback.Core l E f)
    (mu : integralConstantCoefficientObject l E X ≅
      (calculus l E X).integralClosed.monoidal.tensorUnit) :
    (SpTwistedPullback.source l E f (d : ℤ) (2 * (d : ℤ))).obj
      ⟨integralConstantCoefficientObject l E Y, core.admissibleY.1.1⟩ ≅ line l E X d :=
  (shiftFunctor _ (2 * (d : ℤ))).mapIso
    ((calculus l E X).integralClosed.tensor.mapIso
      (Iso.prod (core.unit ≪≫ mu) (Iso.refl _)) ≪≫
      (calculus l E X).integralClosed.monoidal.leftUnitor _)

/-- Completed tensor right unitor through the actual tensor completion unit.
Source: displayed formula, understood unit constraints
(blueprint: lem-pur-tower-purity-realized-transpose). -/
def rightUnit (Y : Scheme.{u}) (m : RingedModels l E)
    (mu : integralConstantCoefficientObject l E Y ≅
      (calculus l E Y).integralClosed.monoidal.tensorUnit)
    (K : DerivedCategory (scalarReductionSource l E Y))
    (h : IsIso (((m.tensor Y).chi l E).app
      (K, integralConstantCoefficientObject l E Y))) :
    (integralCompletedTensor l E Y).obj
      (K, integralConstantCoefficientObject l E Y) ⟶ K :=
  @inv _ _ _ _ (((m.tensor Y).chi l E).app
      (K, integralConstantCoefficientObject l E Y)) h ≫
    (m.tensor Y).ordinary.tensor.map (Prod.mkHom (𝟙 K) mu.hom) ≫
    eqToHom (congrArg (fun F ↦ F.obj
      (K, (calculus l E Y).integralClosed.monoidal.tensorUnit)) (m.tensorClosed Y)) ≫
    ((calculus l E Y).integralClosed.monoidal.rightUnitor K).hom

/-- Inverse fixed-compactification projection, with coefficient-first tensor swaps.
Its completion identifications are precisely the actual augmentation maps.
Source: gamma proof (2), inverse projection with symmetries
(blueprint: lem-pur-tower-purity-realized-transpose). -/
def inverseProjection {X Y : Scheme.{u}} {f : X ⟶ Y}
    (m : CompleteProjectionDescent.DescentModels l E) (c : Compactification f)
    (K : DerivedCategory (scalarReductionSource l E Y))
    (M : DerivedCategory (scalarReductionSource l E X))
    (hv : IsIso (CompactificationBProjection.sourceUnit l E m c K M))
    (hh : IsIso (CompactificationBProjection.innerUnit l E m f K M))
    (hp : IsIso (CompactificationBProjection.alpha l E m c K M
      (@asIso _ _ _ _ (CompactificationBProjection.sourceUnit l E m c K M) hv)
      (@asIso _ _ _ _ (CompactificationBProjection.innerUnit l E m f K M) hh))) :=
  @inv _ _ _ _ (CompactificationBProjection.alpha l E m c K M
    (@asIso _ _ _ _ (CompactificationBProjection.sourceUnit l E m c K M) hv)
    (@asIso _ _ _ _ (CompactificationBProjection.innerUnit l E m f K M) hh)) hp

end WeilConjectures.RealizedTowerPurity

namespace AlgebraicGeometry.ProEtale.RealizedTowerPurity

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The actual fixed-compactification support restricted to the common finite-Tor
category. The preservation certificate is an output of the realization theorem.
Source: D^b_ctf convention and proof step 5
(blueprint: lem-pur-tower-purity-realized-transpose). -/
def support {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (h : ∀ M : finiteTorConstructibleIntegralCategory l E X,
      finiteTorConstructibleIntegral l E Y
        ((CompleteCompactificationLimit.image l E c).obj M.obj)) :
    finiteTorConstructibleIntegralCategory l E X ⥤
      finiteTorConstructibleIntegralCategory l E Y :=
  ObjectProperty.lift _
    ((finiteTorConstructibleIntegral l E X).ι ⋙ CompleteCompactificationLimit.image l E c) h

end AlgebraicGeometry.ProEtale.RealizedTowerPurity

namespace WeilConjectures.RealizedTowerPurity

open AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Restrict the actual total-limit exceptional functor to the common finite-Tor
subcategory. Source: H = Rlim f! red_Y
(blueprint: lem-pur-tower-purity-realized-transpose). -/
def restrictedRight {X Y : Scheme.{u}}
    (H : sfIntegralConstructibleCategory l E Y ⥤ sfIntegralConstructibleCategory l E X)
    (hH : ∀ K : finiteTorConstructibleIntegralCategory l E Y,
      finiteTorConstructibleIntegral l E X
        (H.obj ((PurCompactSupport.finiteTorIntegralInclusion l E Y).obj K)).obj) :=
  ObjectProperty.lift _
    (PurCompactSupport.finiteTorIntegralInclusion l E Y ⋙ H ⋙
      (sfIntegralConstructible l E X).ι) hH

/-- Restrict the given realized adjunction along the two full finite-Tor inclusions.
The comparison is the identity on both ambient composites, so its counit is fixed.
Source: proof step 5, fully faithful adjunction restriction
(blueprint: lem-pur-tower-purity-realized-transpose). -/
def restrictedAdjunction {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (hS : ∀ M : sfIntegralConstructibleCategory l E X,
      sfIntegralConstructible l E Y
        ((CompleteCompactificationLimit.image l E c).obj M.obj))
    (H : sfIntegralConstructibleCategory l E Y ⥤ sfIntegralConstructibleCategory l E X)
    (adj : SpIntegralAdjunction.support l E c hS ⊣ H)
    (hP : ∀ M : finiteTorConstructibleIntegralCategory l E X,
      finiteTorConstructibleIntegral l E Y
        ((CompleteCompactificationLimit.image l E c).obj M.obj))
    (hH : ∀ K : finiteTorConstructibleIntegralCategory l E Y,
      finiteTorConstructibleIntegral l E X
        (H.obj ((PurCompactSupport.finiteTorIntegralInclusion l E Y).obj K)).obj) :
    AlgebraicGeometry.ProEtale.RealizedTowerPurity.support l E c hP ⊣
      restrictedRight l E H hH :=
  adj.restrictFullyFaithful
    (ObjectProperty.fullyFaithfulιOfLE (fun _ h ↦ h.1))
    (ObjectProperty.fullyFaithfulιOfLE (fun _ h ↦ h.1))
    (Iso.refl _) (Iso.refl _)

end WeilConjectures.RealizedTowerPurity

namespace AlgebraicGeometry.ProEtale.RealizedTowerPurity

open WeilConjectures.RealizedTowerPurity

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

variable {X Z Y : Scheme.{u}}
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
  (Gb : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
  (ab : SpTowerGluing.support l E b o q (SpTowerGamma.factorization j p) hF ⊣ Gb)
  (lv : SpTowerGluing.Levels l E b o q (SpTowerGamma.factorization j p) hF Gb ab)
  (r : SpIntegralAdjunction.Realization l E b o q j p d w RX NX RY NY hF Gb ab lv)
  (hH : ∀ K : finiteTorConstructibleIntegralCategory l E Y,
    finiteTorConstructibleIntegral l E X
      ((SpIntegralAdjunction.right l E b q RX NX RY r.reductionY Gb r.closed).obj
        ((PurCompactSupport.finiteTorIntegralInclusion l E Y).obj K)).obj)

/-- The component on exactly the full common finite-Tor category, transferred by the
unique counit-preserving comparison for its restricted realized adjunction.
Source: proof steps 1 and 8 (blueprint: lem-pur-tower-purity-realized-transpose). -/
def component
    (hP : ∀ M : finiteTorConstructibleIntegralCategory l E X,
      finiteTorConstructibleIntegral l E Y
        ((CompleteCompactificationLimit.image l E (SpTowerGamma.factorization j p)).obj M.obj))
    (G : finiteTorConstructibleIntegralCategory l E Y ⥤
      finiteTorConstructibleIntegralCategory l E X)
    (adj : support l E (SpTowerGamma.factorization j p) hP ⊣ G)
    (K : finiteTorConstructibleIntegralCategory l E Y) :=
  realized l E b o q j p d w RX NX RY NY hF Gb ab lv r
      ((PurCompactSupport.finiteTorIntegralInclusion l E Y).obj K) ≫
    (((restrictedAdjunction l E (SpTowerGamma.factorization j p) r.support_closed _
      r.adjunction hP hH).rightAdjointUniq adj).hom.app K).hom

end AlgebraicGeometry.ProEtale.RealizedTowerPurity


namespace AlgebraicGeometry.ProEtale.RealizedTowerPurity

open WeilConjectures.RealizedTowerPurity

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

variable {X Z Y : Scheme.{u}}
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
  (Gb : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
  (ab : SpTowerGluing.support l E b o q (SpTowerGamma.factorization j p) hF ⊣ Gb)
  (lv : SpTowerGluing.Levels l E b o q (SpTowerGamma.factorization j p) hF Gb ab)
  (r : SpIntegralAdjunction.Realization l E b o q j p d w RX NX RY NY hF Gb ab lv)
  (hH : ∀ K : finiteTorConstructibleIntegralCategory l E Y,
    finiteTorConstructibleIntegral l E X
      ((SpIntegralAdjunction.right l E b q RX NX RY r.reductionY Gb r.closed).obj
        ((PurCompactSupport.finiteTorIntegralInclusion l E Y).obj K)).obj)


/-- The actual exceptional reduction: reconstruction counit after reduction of the
inverse counit-preserving right-adjoint comparison.
Source: proof step 9 (blueprint: lem-pur-tower-purity-realized-transpose). -/
def componentReduction
    (hP : ∀ M : finiteTorConstructibleIntegralCategory l E X,
      finiteTorConstructibleIntegral l E Y
        ((CompleteCompactificationLimit.image l E (SpTowerGamma.factorization j p)).obj M.obj))
    (G : finiteTorConstructibleIntegralCategory l E Y ⥤
      finiteTorConstructibleIntegralCategory l E X)
    (adj : support l E (SpTowerGamma.factorization j p) hP ⊣ G)
    (K : finiteTorConstructibleIntegralCategory l E Y) :=
  (SpTwistedPullback.reduction l E b X (q.abelian X) RX).map
    ((((restrictedAdjunction l E (SpTowerGamma.factorization j p) r.support_closed _
      r.adjunction hP hH).rightAdjointUniq adj).inv.app K).hom) ≫
    (SpTowerCalculus.realization l E b X (q.abelian X)).functor.map
      (r.rightComparison.hom.app
        ((PurCompactSupport.finiteTorIntegralInclusion l E Y).obj K)).hom

end AlgebraicGeometry.ProEtale.RealizedTowerPurity

namespace WeilConjectures.RealizedTowerPurity
open ConstructibleExceptionalCoefficients
open AlgebraicGeometry.ProEtale
open CategoryTheory.MonoidalCategory
attribute [local irreducible] integralCompletedTensor integralDerivedPullback
  HasDerivedCategory.standard
variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (S : RingSystem C.l C.Qbar D C.different (f := f)) (c : Compactification f)
/-- The finite left realization, using only the published proper/open comparison.
Source: proof step 9 (blueprint: lem-pur-tower-purity-realized-transpose). -/
@[irreducible] def finiteLeft (n : ℕ+)
    (M : finiteTorConstructibleCategory C.l E n n.pos X) :=
  letI : Finite (Padic.coefficientExtensionRing C.l E n) :=
    Padic.finite_coefficientExtensionRing C.l E n n.pos
  let eX := Scheme.sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing C.l E n)
  let eY := Scheme.sfIntrinsicDerivedEquivalence Y (Padic.coefficientExtensionRing C.l E n)
  let P := Scheme.sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing C.l E n)
  eY.inverse.mapIso
      ((S.left c (.finite {carrier := E} n)).app M ≪≫
        (constructibleFiniteImageIso C.l E n c).app M.obj ≪≫
        P.mapIso (eX.counitIso.app M.obj).symm ≪≫
        (ProEtale.sfIntrinsicCompactSupportComparison
          (Padic.coefficientExtensionRing C.l E n) c).app (eX.inverse.obj M.obj)) ≪≫
    (eY.unitIso.app _).symm

/-- Finite exceptional realization normalized by the entire site-comparison Hom
chain. This pins the maps independently of purity, at the chosen compactification.
Source: proof step 9 (blueprint: lem-pur-tower-purity-realized-transpose). -/
@[irreducible] def FiniteNormalized
    (iso : ∀ n : ℕ,
    (S.operation c (.finite {carrier := E} ⟨n + 1, Nat.succ_pos n⟩)).G ⋙
        (finiteTorConstructible C.l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) X).ι ≅
      (finiteTorConstructible C.l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) Y).ι ⋙
        ProEtale.sfFiniteExceptional (Padic.coefficientExtensionRing C.l E (n + 1)) c) : Prop :=
  ∀ (n : ℕ),
    let N : ℕ+ := ⟨n + 1, Nat.succ_pos n⟩
    letI : Finite (Padic.coefficientExtensionRing C.l E N) :=
      Padic.finite_coefficientExtensionRing C.l E N N.pos
    let A := ULift.{u + 1, u} (Padic.coefficientExtensionRing C.l E N)
    letI := c.hasCompactification
    letI := Etale.isLeftAdjoint_rightDerivedLowerShriek f A
    let O := S.operation c (.finite {carrier := E} N)
    let eX := Scheme.sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing C.l E N)
    let eY := Scheme.sfIntrinsicDerivedEquivalence Y (Padic.coefficientExtensionRing C.l E N)
    let U := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
    let P := ProEtale.sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E N) c
    let adj := (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) f).ofNatIsoLeft
      (Etale.rightDerivedLowerShriekIso A c).symm
    ∀ (M : finiteTorConstructibleCategory C.l E N N.pos X)
      (L : finiteTorConstructibleCategory C.l E N N.pos Y)
      (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
      (e : U.obj K.obj ≅ eX.inverse.obj M.obj) (v : O.F.obj M ⟶ L),
      e.hom ≫ eX.inverse.map ((O.adjunction.homEquiv M L v).hom) ≫
          eX.inverse.map ((iso n).hom.app L) ≫ eX.unitIso.inv.app _ =
        U.map (adj.homEquiv K.obj _
          ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).homEquiv _ _
            ((ProEtale.fixedCompactSupportComparisonIso A c).inv.app K ≫
              P.map e.hom ≫ (finiteLeft D C E f S c N M).inv ≫ eY.inverse.map v.hom)))


/-- The finite right comparison and its Hom normalization, with no purity data.
Source: proof step 9 (blueprint: lem-pur-tower-purity-realized-transpose). -/
structure FiniteNormalization where
  iso : ∀ n : ℕ,
    (S.operation c (.finite {carrier := E} ⟨n + 1, Nat.succ_pos n⟩)).G ⋙
        (finiteTorConstructible C.l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) X).ι ≅
      (finiteTorConstructible C.l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) Y).ι ⋙
        ProEtale.sfFiniteExceptional (Padic.coefficientExtensionRing C.l E (n + 1)) c
  hom_normalized : FiniteNormalized D C E f S c iso

set_option maxHeartbeats 150000 in
-- The two specified scalar models require conversions between intrinsic coefficient categories.
/-- The canonical exceptional coefficient mate, with normalized scalar realization
and the counit-normalized finite right realization.
Source: current blueprint purity transport, Steps 2-3 and unit-trace assembly
(blueprint: lem-pur-tower-purity-realized-transpose). -/
def finiteReduction (normal : FiniteNormalization D C E f S c)
    (K : finiteTorConstructibleIntegralCategory C.l E Y) (n : ℕ) :
    (scalarReductionDerivedExtension C.l E X n).obj
        (((S.operation c (.integral {carrier := E})).G.obj K).obj) ⟶
      (ProEtale.sfFiniteExceptional (Padic.coefficientExtensionRing C.l E (n + 1))
        c).obj
          ((scalarReductionDerivedExtension C.l E Y n).obj K.obj) :=
by
  let sx := S.scalar (s := .integral {carrier := E})
    (t := .finite {carrier := E} ⟨n + 1, Nat.succ_pos n⟩)
    (PurCompactSupport.reduction C.l E (n + 1) (Nat.succ_pos n))
    (Allowed.reduction {carrier := E} ⟨n + 1, Nat.succ_pos n⟩) true
  let sy := S.scalar (s := .integral {carrier := E})
    (t := .finite {carrier := E} ⟨n + 1, Nat.succ_pos n⟩)
    (PurCompactSupport.reduction C.l E (n + 1) (Nat.succ_pos n))
    (Allowed.reduction {carrier := E} ⟨n + 1, Nat.succ_pos n⟩) false
  letI := sx.commShift
  letI := sy.commShift
  exact
    (PurCompactSupport.finiteReductionIso C.l E X n).inv.app _ ≫
      ((S.scalar (s := .integral {carrier := E})
        (t := .finite {carrier := E} ⟨n + 1, Nat.succ_pos n⟩)
        (PurCompactSupport.reduction C.l E (n + 1) (Nat.succ_pos n))
        (Allowed.reduction {carrier := E} ⟨n + 1, Nat.succ_pos n⟩) true).realization.inv.app
          ((S.operation c (.integral {carrier := E})).G.obj K)) ≫
      ((S.comparison c
        (s := .integral {carrier := E})
        (t := .finite {carrier := E} ⟨n + 1, Nat.succ_pos n⟩)
        (PurCompactSupport.reduction C.l E (n + 1) (Nat.succ_pos n))
          (Allowed.reduction {carrier := E} ⟨n + 1, Nat.succ_pos n⟩)).b.hom.app K).hom ≫
      (normal.iso n).hom.app _ ≫
      (ProEtale.sfFiniteExceptional (Padic.coefficientExtensionRing C.l E (n + 1))
        c).map
          ((S.scalar (s := .integral {carrier := E})
        (t := .finite {carrier := E} ⟨n + 1, Nat.succ_pos n⟩)
        (PurCompactSupport.reduction C.l E (n + 1) (Nat.succ_pos n))
            (Allowed.reduction {carrier := E} ⟨n + 1, Nat.succ_pos n⟩) false).realization.hom.app K
              ≫
              (PurCompactSupport.finiteReductionIso C.l E Y n).hom.app K.obj)


/-- Lift the specified proper/open left comparison through the full finite-Tor
inclusion. Source: proof step 8, fixed-support adjunction
(blueprint: lem-pur-tower-purity-realized-transpose). -/
def specifiedLeft
    (hP : ∀ M : finiteTorConstructibleIntegralCategory C.l E X,
      finiteTorConstructibleIntegral C.l E Y
        ((CompleteCompactificationLimit.image C.l E c).obj M.obj)) :
    (S.operation c (.integral {carrier := E})).F ≅
      AlgebraicGeometry.ProEtale.RealizedTowerPurity.support C.l E c hP :=
  NatIso.ofComponents
    (fun M ↦ ObjectProperty.isoMk _ ((S.left c (.integral {carrier := E})).app M))
    (fun v ↦ by
      apply ObjectProperty.hom_ext
      exact (S.left c (.integral {carrier := E})).hom.naturality v)

/-- Transport only the left functor by its normalized proper/open comparison.
Thus its right comparison with any specified G is the counit-preserving one.
Source: proof step 8 (blueprint: lem-pur-tower-purity-realized-transpose). -/
def specifiedAdjunction
    (hP : ∀ M : finiteTorConstructibleIntegralCategory C.l E X,
      finiteTorConstructibleIntegral C.l E Y
        ((CompleteCompactificationLimit.image C.l E c).obj M.obj)) :=
  (S.operation c (.integral {carrier := E})).adjunction.ofNatIsoLeft
    (specifiedLeft D C E f S c hP)

/-- Exact twist to ordinary derived tensor, normalized on every flat resolution.
The total-single collapse and the site tensor comparison fix the source map,
without an arbitrary isomorphism between its endpoints.
Source: proof step 2, canonical source realization
(blueprint: lem-pur-tower-purity-realized-transpose). -/
def SourceNormalized (d : ℕ)
    (hL : ((CochainComplex.singleFunctor (scalarReductionSource C.l E X) 0).obj
      (integralTwistLine C.l E X (d : ℤ))).IsKFlatIndependentCoefficients)
    (s : ∀ K : finiteTorConstructibleIntegralCategory C.l E Y,
      purAdicSource D C E f d K.obj ≅
        (SpTwistedPullback.source C.l E f (d : ℤ) (2 * (d : ℤ))).obj
          ((PurCompactSupport.finiteTorIntegralInclusion C.l E Y).obj K)) : Prop :=
  ∀ (K : finiteTorConstructibleIntegralCategory C.l E Y)
    (P : CochainComplex (scalarReductionSource C.l E X) ℤ)
    (hP : P.IsKFlatIndependentCoefficients)
    (e : DerivedCategory.Q.obj P ≅ (integralDerivedPullback C.l E f).obj K.obj),
    (s K).hom = (shiftFunctor _ (2 * (d : ℤ))).map
      ((integralComplexTwist D C.l C.different E X (d : ℤ)).map e.inv ≫
        (integralSheafTwist C.l E X (d : ℤ)).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex
            (SheafOfModules.siteSheafTensorRightIso
              (completedIntegralCommRingSheafUnrestricted C.l E X)
              (integralTwistLine C.l E X (d : ℤ))) (.up ℤ)).hom.app P) ≫
        DerivedCategory.Q.map
          (CochainComplex.mapBifunctorSingle₂Iso
            (curriedTensor (scalarReductionSource C.l E X))
            (integralTwistLine C.l E X (d : ℤ)) P).inv ≫
        ((calculus C.l E X).integralTensorModel.iso (Scheme.ProEt.topology X)
          (completedIntegralCommRingSheafUnrestricted C.l E X)
          (calculus C.l E X).integralClosed P
          ((CochainComplex.singleFunctor _ 0).obj
            (integralTwistLine C.l E X (d : ℤ))) hP hL).hom ≫
        (calculus C.l E X).integralClosed.tensor.map (Prod.mkHom e.hom (𝟙 _)))

end WeilConjectures.RealizedTowerPurity

```

## New

The identical block above belongs to TowerPurityRealizedData, and the original module
adds the following public import. The theorem remains in its original module.

```lean
public import Sheaf.Paper.TowerPurityRealizedData
```

There is no mathematical definition change. The two additional explicit composites
are towerProjection (pinned b, source comparison, tensor orientation and tower
projectionCounit) and reduceWord (full-subcategory restriction followed by simultaneous
reduction and the section-preserving equivalence). Neither is a chosen witness.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.TowerPurityRealizedTranspose | D3 | Re-exports every unchanged definition and imports the normalization lemma. |
| Sheaf.Paper.TowerPurityRealizedData | D3, new in this delivery | Owns the identical definition block and two explicit tower-word composites. |
| Sheaf.Paper.TowerPurityRealizedNormalization | D3, new in this delivery | Uses the extracted definitions without a cycle. |

`tools/downstream.py Sheaf.Paper.TowerPurityRealizedTranspose` reports zero external
module consumers. The declaration search likewise finds the existing realized-map
uses only inside the item. DAG parents still cite the theorem and retain their route.
No external consumer needs adaptation. The independent reader can compare the eighteen
old declaration bodies byte for byte with the new module. No target meaning changes.

## Status

landed 20261026T001209-L-4174947 2026-10-26 (merge of deliver/D3/Sheaf.Paper.TowerPurityRealizedTranspose)

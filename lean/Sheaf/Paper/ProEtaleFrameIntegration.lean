module

public import Sheaf.Paper.ProEtaleOrderedIntegration
public import Sheaf.AlgebraicGeometry.AffineTraceTower

/-! # Canonical pro-etale ordered integration arrows
Source: main-20261015 vector-bundle integration and projective-line normalization
(blueprint: def-pur-proetale-frame-integration).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite
variable (A : Type (u + 1)) [CommRing A] [Finite A]
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (n : ℕ)


/-- The inverse-frame exchange and Tate/composition identifications, before integration.
Source: blueprint vector-bundle integration, a_i
(blueprint: def-pur-proetale-frame-integration). -/
@[irreducible]
def chartPrefix (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d]
    (V : S.Opens) (e : VectorBundleZeroSection.Trivialization S d F V) :=
  letI := (Etale.vectorIntegration_geometry S d F).1
  letI := (Etale.vectorIntegration_geometry S d F).2.1
  letI : TopologicalSpace.NoetherianSpace V.toScheme :=
    V.ι.isOpenEmbedding.isInducing.noetherianSpace
  letI : IsNoetherian V.toScheme :=
    { toIsLocallyNoetherian := inferInstance
      isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
  (Etale.rightDerivedLowerShriekBaseChangeMap A
    (Etale.vectorIntegrationChart_isPullback S d F V e)).app
      (Etale.vectorIntegrationCoefficient A N hA S d F) ≫
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (affineTraceProjection V.toScheme d)).map
        (Etale.vectorIntegrationChartCoefficient A N hA
          (Etale.projectiveLineTraceTransport N hN A hA) S hS d F V e).hom ≫
    (Etale.affineLinearCompactComparison N hN A hA V.toScheme
      (affineTracePullbackInvertible N V.ι hS) d).inv

/-- Local pro-etale integration on a frame, in comparison source coordinates.
Source: blueprint vector-bundle integration, a_i
(blueprint: def-pur-proetale-frame-integration). -/
@[irreducible]
def localIntegration (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d]
    (V : S.Opens) (e : VectorBundleZeroSection.Trivialization S d F V) :=
  letI : TopologicalSpace.NoetherianSpace V.toScheme :=
    V.ι.isOpenEmbedding.isInducing.noetherianSpace
  letI : IsNoetherian V.toScheme :=
    { toIsLocallyNoetherian := inferInstance
      isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
  (comparison (Scheme.finiteTateCoefficient l E n) V.toScheme).map
    (chartPrefix (Scheme.finiteTateCoefficient l E n) (l ^ (r + 1))
      (pow_pos (Fact.out : l.Prime).pos _) hA S
      (by simpa only [Nat.cast_pow] using hS.pow (r + 1)) d F V e) ≫
    orderedIntegration l E n V.toScheme
      (by simpa using hS.map V.ι.appTop.hom) r hA d


end AlgebraicGeometry.ProEtale.VectorIntegrationSite

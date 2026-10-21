module

public import Sheaf.AlgebraicGeometry.AmbientAffineTranslationTrace
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.PurityConventions
public import Sheaf.Paper.VectorIntegrationSiteComparison
public import Sheaf.Paper.ConstructibleExceptionalInverseImage
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.AlgebraicGeometry.CompactSupportActionBaseChange
import Sheaf.Paper.ConstantSheafSectionsLocallyConstant
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Translation invariance of normalized affine integration

Source: main-20261015, sec-smooth-purity/sk-prop-sp-orientation/
sk-prop-sp-orientation-vector-bundle.proof.md, Step 1, and sk-thm-smooth-purity,
Agreement on the model (blueprint: lem-pur-affine-translation-trace).

The affine space, shifted Tate complex, trace, exchange and translation are the
published coordinate-tower constructions. A section is given by its global coordinates.
The ordinary equality is accompanied by the actual base-change square. The pro-etale
clause states that the translation action preserves the actual vectorIntegration,
using the standard global frame and vectorSite to identify its source. Both site
versions include the tautological universal translation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- The actual translation action: compact-support exchange followed by the normalized
Tate pullback identification. Both factors are the published canonical constructions.
Source: vector-bundle orientation, Step 1
(blueprint: lem-pur-affine-translation-trace). -/
def affineTranslationAction (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (a : Fin d → Γ(S, ⊤)) :=
  ambientAffineTranslationExchange A S d a
      ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ≫
    (affineTraceLeft A S d).map
      (ambientAffineTranslationTate A N hA (ambientAffineTraceTransport N hN A hA)
        S hS d a).hom

/-- The canonical compact-support base-change arrow, with the Tate and constant
coefficient pullback comparisons inserted. No isomorphism is chosen independently.
Source: affine-space top trace, arbitrary base-change clause
(blueprint: lem-pur-affine-translation-trace). -/
def affineTranslationBaseChange (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    {S' S : Scheme.{u}} (g : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :=
  affineTraceExchange A g d
      ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ≫
    (affineTraceLeft A S' d).map
      ((affineTraceRightBaseChange A N hA (ambientAffineTraceTransport N hN A hA)
        g hS d (ordinaryFiniteUnit A S)).hom ≫
        (affineTraceRight A N hA S' d).map (ordinaryFiniteUnitPullback A g).hom)

/-- The free rank-`d` vector-bundle model used to compare affine traces with the
vector-bundle integration construction. -/
def affineTraceTrivialModule (S : Scheme.{u}) (d : ℕ) :
    SheafOfModules S.ringCatSheaf :=
  SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin d))

/-- The standard free module has rank d, including rank zero.
Source: def-amb-vector-integration, free bundle (blueprint: lem-pur-affine-translation-trace). -/
instance affineTraceTrivialModule_isFinite (S : Scheme.{u}) (d : ℕ) :
    (affineTraceTrivialModule S d).IsFiniteLocallyFreeOfRank d := by
  dsimp [affineTraceTrivialModule]
  infer_instance

/-- The canonical global frame of the free bundle, obtained by restricting its
standard basis to the top open. Source: def-amb-vector-integration, frames
(blueprint: lem-pur-affine-translation-trace). -/
def affineTraceTrivialFrame (S : Scheme.{u}) (d : ℕ) :
    VectorBundleZeroSection.Trivialization S d (affineTraceTrivialModule S d) ⊤ :=
  Scheme.Modules.restrictFreeIso (⊤ : S.Opens).ι (ULift.{u} (Fin d))

/-- The global-trivialization chart identification. This is the prefix of
`vectorIntegrationLocalTrace` at the standard frame on the top open, transported
back along that open's canonical equivalence. It uses compact-support exchange,
Tate coefficient comparison and the ordered-tower comparison, and no integration map.
Source: def-amb-vector-integration, a_i and VectorIntegrationNormalization at the top open
(blueprint: lem-pur-affine-translation-trace). -/
def affineTranslationChartBridge (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    vectorIntegrationSource A N hA S d (affineTraceTrivialModule S d) ≅
      (affineTraceRight A N hA S d ⋙ affineTraceLeft A S d).obj
        (ordinaryFiniteUnit A S) := by
  let V : S.Opens := ⊤
  let F := affineTraceTrivialModule S d
  let e := affineTraceTrivialFrame S d
  let t := ambientAffineTraceTransport N hN A hA
  letI : IsIso V.ι := S.topIso.isIso_hom
  letI : TopologicalSpace.NoetherianSpace V.toScheme :=
    V.ι.isOpenEmbedding.isInducing.noetherianSpace
  letI : IsNoetherian V.toScheme :=
    { toIsLocallyNoetherian := inferInstance
      isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
  letI := (vectorIntegration_geometry S d F).1
  letI := (vectorIntegration_geometry S d F).2.1
  letI := affineTraceNoetherian S d
  letI := affineTraceNoetherian V.toScheme d
  let sq := vectorIntegrationChart_isPullback S d F V e
  letI := isIso_rightDerivedLowerShriekBaseChangeMap A sq
  let E := (asIso (rightDerivedLowerShriekBaseChangeMap A sq)).app
      (vectorIntegrationCoefficient A N hA S d F) ≪≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (affineTraceProjection V.toScheme d)).mapIso
        (vectorIntegrationChartCoefficient A N hA t S hS d F V e) ≪≫
    (affineLinearCompactComparison N hN A hA V.toScheme
      (affineTracePullbackInvertible N V.ι hS) d).symm
  let sqA := affineTraceMap_isPullback V.ι d
  letI := isIso_rightDerivedLowerShriekBaseChangeMap A sqA
  let C := (ordinaryFinitePullback A V.ι).mapIso
      (affineLinearCompactComparison N hN A hA S hS d) ≪≫
    (asIso (rightDerivedLowerShriekBaseChangeMap A sqA)).app
      ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ≪≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (affineTraceProjection V.toScheme d)).mapIso
        (affineTraceRightBaseChange A N hA t V.ι hS d (ordinaryFiniteUnit A S) ≪≫
          (affineTraceRight A N hA V.toScheme d).mapIso
            (ordinaryFiniteUnitPullback A V.ι)) ≪≫
    (affineLinearCompactComparison N hN A hA V.toScheme
      (affineTracePullbackInvertible N V.ι hS) d).symm
  letI : (ordinaryFinitePullback A V.ι).IsEquivalence :=
    Functor.isEquivalence_of_iso
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) V.ι).symm
  exact (ordinaryFinitePullback A V.ι).preimageIso (E ≪≫ C.symm)

/-- The actual pro-etale action, conjugating the comparison image of the canonical
Ex/Tate translation action through the global chart and the specified vectorSite.
Source: vector-bundle orientation, Step 1, and vector-integration site comparison
(blueprint: lem-pur-affine-translation-trace). -/
def proEtaleAffineTranslationAction (P : WeilConjectures.PurityFiniteSetting.{u})
    (S : Scheme.{u}) [IsNoetherian S] (s : S ⟶ Spec (.of P.field.k)) (d : ℕ)
    (a : Fin d → Γ(S, ⊤)) (r : ℕ)
    (hA : ((P.coefficients.l ^ (r + 1) : ℕ) :
      Scheme.finiteTateCoefficient P.coefficients.l P.extension (P.level - 1)) = 0) :=
  let A := Scheme.finiteTateCoefficient P.coefficients.l P.extension (P.level - 1)
  let N := P.coefficients.l ^ (r + 1)
  let hN : 0 < N := pow_pos (Fact.out : P.coefficients.l.Prime).pos _
  let hS := WeilConjectures.PurityConventions.coefficientPower_isUnit P S s r
  let hSl : IsUnit ((P.coefficients.l : ℕ) : Γ(S, ⊤)) := by
    simpa using (WeilConjectures.PurityConventions.coefficientPower_isUnit P S s 0)
  let F := affineTraceTrivialModule S d
  let v := ProEtale.VectorIntegrationSite.vectorSite
    P.coefficients.l P.extension (P.level - 1) S r hA d F hSl
  let e := affineTranslationChartBridge N hN A hA S hS d
  let C := ProEtale.VectorIntegrationSite.comparison A S
  v.hom ≫ C.map e.hom ≫ C.map (affineTranslationAction N hN A hA S hS d a) ≫
    C.map e.inv ≫ v.inv

/-- Translation invariance of the actual pro-etale vector integration at the given
section, at every annihilating prime-power level. The action is the conjugate through
the canonical global frame, not through an existential orientation.
Source: vector-bundle orientation, Step 1 (blueprint: lem-pur-affine-translation-trace). -/
def ProEtaleAffineTraceCompatibility (P : WeilConjectures.PurityFiniteSetting.{u})
    (S : Scheme.{u}) (s : S ⟶ Spec (.of P.field.k))
    [IsNoetherian S] (d : ℕ) (a : Fin d → Γ(S, ⊤)) : Prop :=
  ∀ (r : ℕ)
    (hA : ((P.coefficients.l ^ (r + 1) : ℕ) :
      Scheme.finiteTateCoefficient P.coefficients.l P.extension (P.level - 1)) = 0),
    proEtaleAffineTranslationAction P S s d a r hA ≫
      ProEtale.VectorIntegrationSite.vectorIntegration
        P.coefficients.l P.extension (P.level - 1) S r hA d
        (affineTraceTrivialModule S d)
        (by simpa using (WeilConjectures.PurityConventions.coefficientPower_isUnit P S s 0)) =
      ProEtale.VectorIntegrationSite.vectorIntegration
        P.coefficients.l P.extension (P.level - 1) S r hA d
        (affineTraceTrivialModule S d)
        (by simpa using (WeilConjectures.PurityConventions.coefficientPower_isUnit P S s 0))

/-- The ordinary trace equation at the universal coordinate vector over affine d-space.
Source: vector-bundle orientation, Step 1 (blueprint: lem-pur-affine-translation-trace). -/
def AffineUniversalTranslationTraceEquation (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) : Prop :=
  letI : IsNoetherian (affineTraceTower S d) := affineTraceNoetherian S d
  affineTranslationAction N hN A hA (affineTraceTower S d)
      (affineTraceInvertible N S hS d) d (affineTraceCoordinate S d) ≫
    affineTraceCounit A N hA (ambientAffineTraceTransport N hN A hA)
      (ambientAffineTraceDatum N hN A hA) (affineTraceTower S d)
      (affineTraceInvertible N S hS d) d =
    affineTraceCounit A N hA (ambientAffineTraceTransport N hN A hA)
      (ambientAffineTraceDatum N hN A hA) (affineTraceTower S d)
      (affineTraceInvertible N S hS d) d

/-- The translation/trace equation and its arbitrary-base-change and site-comparison
clauses. Noetherianity is deduced from finite type over the specified field.
`N` is any positive invertible annihilator used to present the ordinary finite Tate
line; in particular a sufficiently large power of the coefficient prime works at
every positive coefficient level, without a ramification divisibility condition.
Source: vector-bundle orientation, Step 1, and Agreement on the model
(blueprint: lem-pur-affine-translation-trace). -/
def AffineTranslationTraceCompatibility (P : WeilConjectures.PurityFiniteSetting.{u})
    (S : Scheme.{u}) (s : S ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType s] [QuasiCompact s] [IsSeparated s]
    (N : ℕ) (hN : 0 < N) (hA : (N : P.Coefficient) = 0)
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) : Prop :=
  letI : IsNoetherian S := isNoetherian_of_locallyOfFiniteType s
  AffineUniversalTranslationTraceEquation N hN P.Coefficient hA S hS d ∧
  (letI : IsNoetherian (affineTraceTower S d) := affineTraceNoetherian S d
   ProEtaleAffineTraceCompatibility P (affineTraceTower S d)
     (affineTraceProjection S d ≫ s) d (affineTraceCoordinate S d)) ∧
  ∀ a : Fin d → Γ(S, ⊤),
    (affineTranslationAction N hN P.Coefficient hA S hS d a ≫
        affineTraceCounit P.Coefficient N hA
          (ambientAffineTraceTransport N hN P.Coefficient hA)
          (ambientAffineTraceDatum N hN P.Coefficient hA) S hS d =
      affineTraceCounit P.Coefficient N hA
        (ambientAffineTraceTransport N hN P.Coefficient hA)
        (ambientAffineTraceDatum N hN P.Coefficient hA) S hS d) ∧
    (∀ (S' : Scheme.{u}) (s' : S' ⟶ Spec (.of P.field.k))
      [LocallyOfFiniteType s'] [QuasiCompact s'] [IsSeparated s']
      (g : S' ⟶ S) (_hg : g ≫ s = s'),
      letI : IsNoetherian S' := isNoetherian_of_locallyOfFiniteType s'
      ((ordinaryFinitePullback P.Coefficient g).map
            (affineTranslationAction N hN P.Coefficient hA S hS d a) ≫
          affineTranslationBaseChange N hN P.Coefficient hA g hS d =
        affineTranslationBaseChange N hN P.Coefficient hA g hS d ≫
          affineTranslationAction N hN P.Coefficient hA S'
            (affineTracePullbackInvertible N g hS) d (fun i ↦ g.appTop (a i))) ∧
      (affineTranslationBaseChange N hN P.Coefficient hA g hS d ≫
          affineTraceCounit P.Coefficient N hA
            (ambientAffineTraceTransport N hN P.Coefficient hA)
            (ambientAffineTraceDatum N hN P.Coefficient hA) S'
            (affineTracePullbackInvertible N g hS) d =
        (ordinaryFinitePullback P.Coefficient g).map
            (affineTraceCounit P.Coefficient N hA
              (ambientAffineTraceTransport N hN P.Coefficient hA)
              (ambientAffineTraceDatum N hN P.Coefficient hA) S hS d) ≫
          (ordinaryFiniteUnitPullback P.Coefficient g).hom)) ∧
    ProEtaleAffineTraceCompatibility P S s d a

/-- Translation preserves the normalized trace at every positive finite coefficient
level, universally and compatibly with arbitrary base change and site comparison.
Source: main-20261015, vector-bundle orientation proof, Step 1; smooth-purity unit,
Agreement on the model (blueprint: lem-pur-affine-translation-trace).

Proof:
1. Work on the ordinary etale site. Finite type over k makes S Noetherian, as well
   as the affine parameter space P and its affine coordinate towers. Over P use
   the tautological vector of coordinates for the universal translation.
2. Apply lem-amb-compact-action-base-change to that automorphism and the canonical
   Tate pullback map. The normalized affine-space trace is invertible and commutes
   with base change by lem-amb-affine-space-top-trace. The unbounded comparisons
   identify these exchanges with the bounded-below ones on the shifted Tate object.
3. Conjugate the universal action by this trace. Degree-zero full faithfulness
   gives an A-linear constant-sheaf automorphism. It is multiplication by a unit
   section b; constant-sheaf sections are locally constant functions.
4. Every geometric affine fibre is nonempty and connected, including d = 0.
   The value along the zero section is one by identity normalization of exchange.
   Hence b is one on every fibre and globally. This gives the universal equality.
5. Pull back along the section a. Action and trace base change give precisely the
   exchange, coefficient and constant-unit comparisons in the displayed equations.
   Repeating over S' gives the arbitrary-base-change clause. This is also the
   published ambientAffineTranslationTrace argument; its concrete maps are reused.
6. For each annihilating prime power use the standard frame of the free rank-d
   bundle. The prefix of vectorIntegrationLocalTrace at the top open, followed by
   inverse affine base change, defines affineTranslationChartBridge without using
   an integration map. VectorIntegrationNormalization at that frame and affine trace
   base change identify its composite with the affine counit as vectorBundleIntegration.
   The specified vectorSite comparison carries that equality to vectorIntegration.
   Conjugating the comparison image of the Ex/Tate action through these two canonical
   identifications and cancelling their inverses carries the ordinary translation
   equation to action followed by vectorIntegration = vectorIntegration. Apply this
   also over the affine parameter scheme at its tautological coordinate vector.
   No flatness over Z/N is used.
-/
theorem purAffineTranslationTrace (P : WeilConjectures.PurityFiniteSetting.{u})
    (S : Scheme.{u}) (s : S ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType s] [QuasiCompact s] [IsSeparated s]
    (N : ℕ) (hN : 0 < N) (hA : (N : P.Coefficient) = 0)
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    AffineTranslationTraceCompatibility P S s N hN hA hS d := by
  sorry

end AlgebraicGeometry.Etale

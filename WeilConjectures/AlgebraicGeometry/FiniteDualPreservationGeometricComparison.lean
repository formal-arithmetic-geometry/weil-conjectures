/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.PureDimension
public import WeilConjectures.AlgebraicGeometry.DualityPairing
public import WeilConjectures.AlgebraicGeometry.ProEtaleTateTwistsOfUniverses
public import WeilConjectures.CategoryTheory.ConstantScalarRestrictionTensorSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteSchemeRingSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites
public import WeilConjectures.SixFunctors.FiniteDualitySiteComparison
public import WeilConjectures.AlgebraicGeometry.CompactifiableOverField
public import WeilConjectures.AlgebraicGeometry.EvaluationHomSiteComparison
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Basic
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLineInputs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Derived
public import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedSiteDerivedComparison
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothNormalizedExistence
public import WeilConjectures.AlgebraicGeometry.IndEtaleConstructibleMappingContinuity
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageComparisonCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided

/-! # Finite-coefficient dual preservation and geometric-field comparison

Source: `literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-pd-verdier-duality/
 det-pd-biduality-coefficients.proof.md`, Step 3 of `thm-a1-curve-perverse-heart`.
(blueprint: lem-per-finite-dual-preservation-geometric-comparison).

The statement uses the recorded coefficient quotient, ordinary finite-Tor constructible
predicate, the canonical exceptional dualizing object, the evaluation-defined site
comparison data, and the canonical derived pullback Hom comparison.  The proof is
intentionally postponed to the stage-3 proof node.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory
open AlgebraicGeometry Scheme
open scoped CategoryTheory.Functor TensorProduct

namespace AlgebraicGeometry.Etale

/-- Coherence of the actual evaluation-transpose pullback comparison. The composition
square uses the canonical derived inverse-image compositor, and therefore also applies
when one arrow is a scheme isomorphism or a finite-separable restriction to a limit.
Source: det-pd-biduality-coefficients (i), compatibility paragraph
(blueprint: lem-per-finite-dual-preservation-geometric-comparison). -/
noncomputable def finiteDualGeometricHomCoherence
    (A : Type (u + 1)) [CommRing A] : Prop :=
  ∀ {X Y Z : Scheme.{u}} (f : Z ⟶ Y) (g : Y ⟶ X)
      (K M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))),
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g (f ≫ g) rfl).hom.app
        (((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj M) ≫
      (L((f)^*[ModuleCat.{u + 1} A])).map
        (derivedHomUpperStarComparison (ModuleCat.{u + 1} A) g K M) ≫
      derivedHomUpperStarComparison (ModuleCat.{u + 1} A) f
        ((L((g)^*[ModuleCat.{u + 1} A])).obj K)
        ((L((g)^*[ModuleCat.{u + 1} A])).obj M) =
    derivedHomUpperStarComparison (ModuleCat.{u + 1} A) (f ≫ g) K M ≫
      ((derivedHom (ModuleCat.{u + 1} A) Z).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g (f ≫ g) rfl).inv.app K).op).app
          ((L(((f ≫ g))^*[ModuleCat.{u + 1} A])).obj M) ≫
      ((derivedHom (ModuleCat.{u + 1} A) Z).obj
        (op ((L((f)^*[ModuleCat.{u + 1} A])).obj
          ((L((g)^*[ModuleCat.{u + 1} A])).obj K)))).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g (f ≫ g) rfl).hom.app M)

/-- The evaluation-transpose comparison at a filtered limit is unchanged by cofinal
refinement. Every leg is the specified pullback of derived morphisms; no abstract
isomorphism or arbitrary map is substituted for the comparison.
Source: det-pd-biduality-coefficients (i), continuity paragraph; Bhatt--Scholze 6.3.16
(blueprint: lem-per-finite-dual-preservation-geometric-comparison). -/
noncomputable def finiteDualFilteredHomCoherence
    (A : Type (u + 1)) [CommRing A] : Prop :=
  ∀ {X : Scheme.{u}} (K M : DerivedCategoryModule A X)
      {I J : Type (u + 1)} [SmallCategory I] [SmallCategory J]
      [IsCofiltered I] [IsCofiltered J]
      (D : I ⥤ Over X) (c : Cone D) (r : J ⥤ I) [r.op.Final]
      (P : IndEtaleMapping.Model A K M D c),
    DerivedCategory.Q.map (colimit.pre P.diagram r.op) ≫
        IndEtaleMapping.comparison A K M D c P =
      IndEtaleMapping.comparison A K M (r ⋙ D) (c.whisker r)
        (IndEtaleMapping.Model.reindex A K M D c r P)

/-- Constant functions at the condensed point, used to pin the coefficient-ring
identification. Source: the finite-discrete coefficient paragraph of
`det-pd-biduality-coefficients` (blueprint:
lem-per-finite-dual-preservation-geometric-comparison). -/
noncomputable def finiteDualPointConstants (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    (Functor.const Profinite.{u}ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A)) ⟶
      (Profinite.continuousMapRingObjOfUniverse.{u, u} A).obj where
  app S := AddCommGrpCat.ofHom
    { toFun a := ULift.up (ContinuousMap.const S.unop a.down)
      map_zero' := rfl
      map_add' _ _ := rfl }
  naturality _ _ _ := rfl

/-- The canonical constant-function map after inverse image to the scheme.
Source: the finite-discrete coefficient paragraph of `det-pd-biduality-coefficients`
(blueprint: lem-per-finite-dual-preservation-geometric-comparison). -/
noncomputable def finiteDualSchemeConstants (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] (T : Scheme.{u}) :
    (constantSheaf (ProEt.topology T) Ab.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} A)) ⟶
      ProEtale.condensedRingObj (Profinite.continuousMapRingObjOfUniverse.{u, u} A) T :=
  (ProEtale.constantSchemeIso T).hom.app (AddCommGrpCat.of (ULift.{u + 1} A)) ≫
    (ProEtale.upperStarFromPoint T).map
      (((sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}).homEquiv
        _ (Profinite.continuousMapRingObjOfUniverse.{u, u} A)).symm
          (finiteDualPointConstants A))

/-- The section-action equivalence followed by restriction to constant scalars.
The ring isomorphism is supplied with its constant-function normalization in the
assertion below. Source: the coefficient-presentation paragraph of
`det-pd-biduality-coefficients` (blueprint:
lem-per-finite-dual-preservation-geometric-comparison). -/
noncomputable def finiteDualInternalFixed
    (A : Type u) [CommRing A]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u})
    (r : Scheme.proEtaleConstantRing T A ≅ ProEtale.ModuleObjectRingedComparison.ring Λ T) :
    ProEtale.ModuleObjectRingedComparison.Internal Λ T ⥤
      Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A)) :=
  ProEtale.ModuleObjectRingedComparison.sectionForward Λ T ⋙
    SheafOfModules.restrictScalars
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map r.hom) ⋙
    SheafOfModules.restrictScalars
      ((constantCommuteCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app
          (CommRingCat.of (ULift.{u + 1} A))) ⋙
    constantRingModuleRestriction (ProEt.topology T) (ULift.{u + 1} A)

/-- The intrinsic ctf predicate transported through the specified coefficient
encoding, with the ordinary finite-Tor constructible predicate as input.
Source: the last paragraph of `det-pd-biduality-coefficients` (blueprint:
lem-per-finite-dual-preservation-geometric-comparison). -/
noncomputable def finiteDualInternalCtf
    (A : Type u) [CommRing A]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u})
    (e : DerivedCategory (ProEtale.ModuleObjectRingedComparison.Internal Λ T) ≌
      DerivedCategory (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))))
    (P : ObjectProperty
      (DerivedCategory (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))))) :
    ObjectProperty (DerivedCategory (ProEtale.ModuleObjectRingedComparison.Internal Λ T)) :=
  P.inverseImage e.functor

/-- The section ring has the original underlying additive sheaf.
Source: section-action encoding, Stacks 00YV (blueprint:
lem-per-finite-dual-preservation-geometric-comparison). -/
noncomputable def finiteDualSectionAddIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u}) :
    (sheafCompose (ProEt.topology T) ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1}))).obj
        (ProEtale.ModuleObjectRingedComparison.ring Λ T) ≅
      ProEtale.condensedRingObj Λ T := Iso.refl _

/-- The canonical module-object coefficient transport, including its tensor/Hom
and evaluation comparison. The ring map is fixed by constant functions and the
derived functor by localization of the section-action functor.
Source: det-pd-biduality-coefficients (i) (blueprint:
lem-per-finite-dual-preservation-geometric-comparison). -/
noncomputable def finiteDualInternalTransport
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [MonObj (Profinite.continuousMapRingObjOfUniverse.{u, u} A)]
    [IsCommMonObj (Profinite.continuousMapRingObjOfUniverse.{u, u} A)]
    (X : Scheme.{u})
    (P : ObjectProperty (DerivedCategory
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} A))))) : Prop :=
  let Λ := Profinite.continuousMapRingObjOfUniverse.{u, u} A
  let H := ProEtale.CondensedRing.derivedHom Λ X
  let H' := ProEtale.derivedHom (ModuleCat.{u + 1} (ULift.{u + 1} A)) X
  let T := ProEtale.CondensedRing.derivedTensor Λ X
  let T' := ProEtale.derivedTensor (ModuleCat.{u + 1} (ULift.{u + 1} A)) X
  ∃ r : Scheme.proEtaleConstantRing X A ≅
      ProEtale.ModuleObjectRingedComparison.ring Λ X,
    r.hom ≫ r.inv = 𝟙 _ ∧
    let F := finiteDualInternalFixed A Λ X r
    ∃ (hadd : F.Additive) (hlim : PreservesFiniteLimits F)
      (hcolim : PreservesFiniteColimits F),
      letI := hadd
      letI := hlim
      letI := hcolim
      ∃ e : DerivedCategory (ProEtale.ModuleObjectRingedComparison.Internal Λ X) ≌
          DerivedCategory
            (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} A))),
        Nonempty (e.functor ≅ F.mapDerivedCategory) ∧
        ∃ (t : Functor.uncurry.obj T ⋙ e.functor ≅
            (e.functor.prod e.functor) ⋙ Functor.uncurry.obj T')
          (h : Functor.uncurry.obj H ⋙ e.functor ≅
            (e.functor.op.prod e.functor) ⋙ Functor.uncurry.obj H'),
          (∀ K N : DerivedCategory (ProEtale.ModuleObjectRingedComparison.Internal Λ X),
            e.functor.map
              ((@BraidedCategory.braiding _ _ _
                (ProEtale.ModuleObjectRingedComparison.internalBraiding Λ X)
                  ((H.obj (op K)).obj N) K).hom ≫
                (ProEtale.CondensedRing.derivedTensorHomAdjunction Λ K).counit.app N) =
              t.hom.app ((H.obj (op K)).obj N, K) ≫
                (T'.map (h.hom.app (op K, N))).app (e.functor.obj K) ≫
                ProEtale.nativeProEtaleEvaluation
                  (ModuleCat.{u + 1} (ULift.{u + 1} A)) X
                  (e.functor.obj N) (e.functor.obj K)) ∧
          ∃ eP : P.FullSubcategory ≌
            (finiteDualInternalCtf A Λ X e P).FullSubcategory,
            Nonempty (eP.functor ⋙ (finiteDualInternalCtf A Λ X e P).ι ≅
              P.ι ⋙ e.inverse)

/-- The actual finite-coefficient pro-etale Tate object and cohomological shift,
using sk-def-sp-tate-twist and the canonical constant-scalar derived restriction.
Source: sk-def-sp-tate-twist (blueprint:
lem-per-finite-dual-preservation-geometric-comparison). -/
noncomputable def finiteDualSpTateShift
    (ell : ℕ) [Fact ell.Prime] (A : Type u) [CommRing A] [Finite A]
    (X : Scheme.{u}) (r : ℕ) (hA : (ell ^ (r + 1) : ULift.{u + 1} A) = 0)
    (d : ℕ) :
    DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} A))) :=
  ((ConstantScalarRestriction.onDerived (ProEt.topology X) (ULift.{u + 1} A)).obj
    (ProEtale.spComplexTwistOfUniverses X (Scheme.proEtaleConstantRing X A)
      (ProEtale.spFiniteTwist X ell (ULift.{u + 1} A) r hA)
      ((DerivedCategory.singleFunctor _ 0).obj
        (SheafOfModules.unit (Scheme.purTwistRing X (Scheme.proEtaleConstantRing X A))))
      (d : ℤ)))⟦(2 * (d : ℤ))⟧

/-- The finite-coefficient comparison assertion, using only the recorded constructions.
All abbreviations below occur in the body of this public definition, so the theorem
signature contains no opaque let-bound objects. The purity condition is the explicit
Kummer-normalized diagonal/DNC condition and its base-change square.
Source: det-pd-biduality-coefficients (i), finite comparison and continuity
(blueprint: lem-per-finite-dual-preservation-geometric-comparison). -/
noncomputable def FiniteDualPreservationGeometricComparison
    (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [PerfectField k]
    (_hell : IsUnit (ell : k))
    (E : Type u) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E]
    (n : ℕ) (hn : 1 ≤ n)
    (T : Scheme.{u}) [T.Over (Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))]
    [QuasiCompact (T ↘ Spec (.of k))]
    [Smooth (T ↘ Spec (.of k))]
    (d : ℕ) (_hd : d = 0 ∨ d = 1)
    (_hT : Scheme.IsPureDimension T d) : Prop :=
    let A := Padic.coefficientExtensionRing ell E n
    letI : TopologicalSpace A := ⊥
    letI : DiscreteTopology A := ⟨rfl⟩
    letI : IsTopologicalRing A := by infer_instance
    letI : MonObj (Profinite.continuousMapRingObjOfUniverse.{u, u} A) :=
      Profinite.continuousMapRingObjOfUniverseMonObj.{u, u} A
    letI : IsCommMonObj (Profinite.continuousMapRingObjOfUniverse.{u, u} A) :=
      Profinite.isCommMonObj_continuousMapRingObjOfUniverse.{u, u} A
    let Λ := ULift.{u + 1, u} A
    let aT := T ↘ Spec (.of k)
    let c := NagataCompactification aT
    let barSpec := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
    let barT := pullback aT barSpec
    let p := pullback.fst aT barSpec
    let aBar := pullback.snd aT barSpec
    let cBar := NagataCompactification aBar
    letI : Finite A := Padic.finite_coefficientExtensionRing ell E n hn
    letI : Finite Λ := inferInstance
    letI : NeZero (ringChar Λ) := Etale.neZero_ringChar_of_finite Λ
    letI : Etale.HasTateTwist Λ := Etale.hasTateTwist Λ
    letI := c.hasCompactification
    letI := cBar.hasCompactification
    letI : IsNoetherian T :=
      { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian aT
        toCompactSpace := QuasiCompact.compactSpace_of_compactSpace aT }
    letI : IsNoetherian barT :=
      { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian aBar
        toCompactSpace := QuasiCompact.compactSpace_of_compactSpace aBar }
    letI := ProEtale.preservesFlat_comparisonUpperStar (X := T) (Λ := Λ)
    let P := WeilConjectures.finiteTorConstructibleEtale ell E n hn T
    (∀ K : DerivedCategory
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      P K → P ((Etale.verdierDual Λ aT).obj (op K))) ∧
      (∀ K : DerivedCategory
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
        P K →
          IsIso (Etale.derivedHomUpperStarComparison (ModuleCat.{u + 1} Λ)
            p
            K (Etale.dualizingComplex Λ aT))) ∧
      (∃ (N : ℕ) (hN : 0 < N) (hA : (N : Λ) = 0)
          (hunit : IsUnit (N : Γ(T, ⊤)))
          (G : Etale.FiniteRingSectionDeformation.Geometry d
            (pullback.fst aT aT) (pullback.diagonal aT))
          (α : Etale.dualizingComplex Λ aT ≅
            Etale.FiniteSmoothPurity.line Λ N hA T d),
          Etale.FiniteSmoothPurity.OrientationNormalized
            Λ N hN hA aT d G hunit α) ∧
      finiteDualGeometricHomCoherence Λ ∧
      finiteDualFilteredHomCoherence Λ ∧
      (∃ ω : (L((p)^*[ModuleCat.{u + 1} Λ])).obj (Etale.dualizingComplex Λ aT) ≅
          Etale.dualizingComplex Λ aBar,
        ω.hom = Etale.dualizingComplexBaseChangeMap Λ
          (IsPullback.of_hasPullback aT barSpec) ∧
        (∃ (N : ℕ) (hN : 0 < N) (hA : (N : Λ) = 0)
            (hunit : IsUnit (N : Γ(T, ⊤)))
            (hunitBar : IsUnit (N : Γ(barT, ⊤)))
            (t : Etale.OrdinaryFiniteTwistTransport Λ N hA)
            (G : Etale.FiniteRingSectionDeformation.Geometry d
              (pullback.fst aT aT) (pullback.diagonal aT))
            (Gbar : Etale.FiniteRingSectionDeformation.Geometry d
              (pullback.fst aBar aBar) (pullback.diagonal aBar))
            (α : Etale.dualizingComplex Λ aT ≅
              Etale.FiniteSmoothPurity.line Λ N hA T d)
            (αbar : Etale.dualizingComplex Λ aBar ≅
              Etale.FiniteSmoothPurity.line Λ N hA barT d),
          Etale.FiniteSmoothPurity.OrientationNormalized
            Λ N hN hA aT d G hunit α ∧
          Etale.FiniteSmoothPurity.OrientationNormalized
            Λ N hN hA aBar d Gbar hunitBar αbar ∧
          (L((p)^*[ModuleCat.{u + 1} Λ])).map α.hom ≫
              (Etale.vectorIntegrationBaseCoefficientPullback Λ N hA t p hunit d).hom =
            ω.hom ≫ αbar.hom) ∧
        ∀ K, P K →
          CategoryTheory.evaluationDualityCompatibility
            L((p)^*[ModuleCat.{u + 1} Λ])
            (Etale.derivedHom (ModuleCat.{u + 1} Λ) T)
            (Etale.derivedHom (ModuleCat.{u + 1} Λ) barT)
            (Etale.derivedTensor (ModuleCat.{u + 1} Λ) T)
            (Etale.derivedTensor (ModuleCat.{u + 1} Λ) barT)
            (Etale.derivedHomUpperStarComparison (ModuleCat.{u + 1} Λ) p)
            (fun K M ↦ (Etale.leftDerivedUpperStarTensorIso
              (ModuleCat.{u + 1} Λ) p K M).inv) ω
            (ProEtale.nativeEtaleEvaluation (ModuleCat.{u + 1} Λ) T
              (Etale.dualizingComplex Λ aT))
            (ProEtale.nativeEtaleEvaluation (ModuleCat.{u + 1} Λ) barT
              (Etale.dualizingComplex Λ aBar))
            (ProEtale.finiteDualityNativeBidual (ModuleCat.{u + 1} Λ) T
              (Etale.dualizingComplex Λ aT))
            (ProEtale.finiteDualityNativeBidual (ModuleCat.{u + 1} Λ) barT
              (Etale.dualizingComplex Λ aBar)) K) ∧
      (∃ ω :
          (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategory.obj
              (Etale.dualizingComplex Λ aT) ≅
            ProEtale.finiteDualityProEtaleObject A c,
        ω.hom = ProEtale.finiteDualityObjectMap A c ∧
          (∃ (r : ℕ) (hA : (ell ^ (r + 1) : Λ) = 0) (N : ℕ)
              (hN : (N : Λ) = 0) (hNpos : 0 < N)
              (hunit : IsUnit (N : Γ(T, ⊤)))
              (α : Etale.dualizingComplex Λ aT ≅
                Etale.FiniteSmoothPurity.line Λ N hN T d)
              (β :
                (ProEtale.comparisonUpperStar
                  (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).mapDerivedCategory.obj
                (Etale.FiniteSmoothPurity.line Λ N hN T d) ≅
                finiteDualSpTateShift ell A T r hA d)
              (γ : ProEtale.finiteDualityProEtaleObject A c ≅
                finiteDualSpTateShift ell A T r hA d),
            (∃ G : Etale.FiniteRingSectionDeformation.Geometry d
                (pullback.fst aT aT) (pullback.diagonal aT),
              Etale.FiniteSmoothPurity.OrientationNormalized Λ N hNpos hN aT d G
                hunit α) ∧
            γ.hom = ω.inv ≫
              (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategory.map α.hom ≫
                β.hom ∧
            ω.hom ≫ γ.hom =
              (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategory.map α.hom ≫
                β.hom) ∧
          (∃ hEt : Etale.AmbientDualityPairing
              (ModuleCat.{u + 1} Λ) T (Etale.dualizingComplex Λ aT),
            ∃ hPro : ProEtale.AmbientDualityPairing
                (ModuleCat.{u + 1} Λ) T
                (ProEtale.finiteDualityProEtaleObject A c),
              ∀ K, P K →
                ProEtale.FiniteDualityCompatibility
                  (ModuleCat.{u + 1} Λ) T
                  (Etale.dualizingComplex Λ aT)
                  (ProEtale.finiteDualityProEtaleObject A c)
                  ω hEt hPro K)) ∧
      (∃ e : P.FullSubcategory ≌
          (WeilConjectures.finiteTorConstructibleProEtaleModule ell E n hn T).FullSubcategory,
        Nonempty
          (e.functor ⋙ (WeilConjectures.finiteTorConstructibleProEtaleModule ell E n hn T).ι ≅
            P.ι ⋙
              (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategory)) ∧
      finiteDualInternalTransport A T
        (WeilConjectures.finiteTorConstructibleProEtaleModule ell E n hn T)

/-- Finite-coefficient Verdier dual preservation, smooth purity, and geometric comparison.

The first conjuncts are respectively: preservation of the ordinary finite-Tor constructible
subcategory by the canonical Verdier dual; the normalized smooth-purity identification of the
exceptional dualizing object with the Tate twist and shift; and invertibility of the canonical
pullback internal-Hom comparison after base change to an algebraic closure.  The final clauses
record the canonical pro-etale dualizing-object isomorphism, the evaluation and Koszul-symmetry
compatibility, the tensor-Hom adjunction and double-dual comparison, and the equivalence of the
finite-Tor constructible subcategories.  They assert no invertibility of the source
double-dual map.

Source proof: the finite-coefficient duality comparison paragraph and the smooth-purity
paragraph cited above (blueprint: lem-per-finite-dual-preservation-geometric-comparison).

Proof plan (postponed here):
1. Choose a positive power of `ell` annihilating `A`; it is invertible on every
   scheme in the argument. Finite type over a field is Noetherian, and Nagata
   compactifies each separated finite-type structural map and its base changes.
2. Smooth base change for compact support identifies the second projection's
   exceptional object with the diagonal section invariant. The finite-ring
   deformation-to-the-normal-cone comparison, with its Kummer normalization,
   identifies that invariant with the Tate twist and shift. The construction
   includes dimension zero and is compatible with Noetherian base change and
   finite Tate-line pullback.
3. The finite-Tor constructible category is thick-generated by locally closed
   extensions of lisse flat finite sheaves. Reduction is a universal-homeomorphism
   invariant, and the reduced strata are smooth of dimension zero or one because
   the ambient scheme is regular and has pure dimension at most one.
4. Compact-support composition and uniqueness of right adjoints identify the
   exceptional value on a smooth stratum. For a finite flat local model, the
   internal Hom is the finite projective dual tensored with the stratum's
   dualizing object, hence is constructible with the displayed finite Tor bound.
5. Direct-image constructibility and the Noetherian coefficient Tor theorem
   preserve the bounds. Exact internal Hom and the closed symmetric monoidal
   structure make the property thick, so Verdier duality preserves all of the
   finite-Tor constructible category.
6. For constructible `K` and bounded-below `M`, the comparison is the transpose
   of pulled-back evaluation under the canonical tensor comparison. On affine
   ind-etale basis objects, bounded-below Hom bounds reduce the assertion to
   derived mapping continuity and the finite-site/pro-etale global-section
   comparisons. The basis detects that the comparison is invertible.
7. The algebraic closure of the perfect field is the filtered union of finite
   separable extensions. These extensions are finite etale, so their scalar
   pullback is ind-etale and weakly etale. Restriction to the resulting pro-etale
   slice identifies the comparison on the geometric fibre with the comparison
   from step 6.
8. Exact etale pullback preserves constructibility and every Tor interval, so
   step 6 applies to the pulled-back complex. Full faithfulness on bounded-below
   complexes detects the displayed geometric comparison, and step 2 supplies
   the normalized identification of the pulled-back dualizing object.
9. The finite coefficient site comparison identifies the finite-Tor constructible
   etale category with the full finite-Tor constructible pro-etale subcategory.
   Constant finite rings and their pulled-back condensed ring objects identify
   the tensor, internal Hom and evaluation operations in the ordinary unbounded
   derived categories.
10. For a composite pullback, transposing the composite comparison gives the
    same pulled-back evaluation as the direct comparison. The tensor-Hom
    adjunction and the signed Koszul symmetry therefore commute with composition,
    filtered refinement and the coefficient presentation; the same calculation
    gives naturality under scheme isomorphisms.
11. Apply the transpose calculation to the double-dual arrow. The two maps from
    the pulled-back complex have equal transposes, so the comparison carries
    `p^* delta_K` to `delta_{p^* K}`. Only the comparison maps are inverted; no
    invertibility of the double-dual arrow is used.
-/
theorem finite_dual_preservation_geometric_comparison
    (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [PerfectField k]
    (hell : IsUnit (ell : k))
    (E : Type u) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E]
    (n : ℕ) (hn : 1 ≤ n)
    (T : Scheme.{u}) [T.Over (Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))]
    [QuasiCompact (T ↘ Spec (.of k))]
    [Smooth (T ↘ Spec (.of k))]
    (d : ℕ) (hd : d = 0 ∨ d = 1)
    (hT : Scheme.IsPureDimension T d) :
    FiniteDualPreservationGeometricComparison ell k hell E n hn T d hd hT := by
  sorry

end AlgebraicGeometry.Etale

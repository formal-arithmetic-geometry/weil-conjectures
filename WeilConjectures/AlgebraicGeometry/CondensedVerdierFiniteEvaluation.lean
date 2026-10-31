/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedSixOperations
public import WeilConjectures.AlgebraicGeometry.DetThmSfCtfStabilityInternalHom
public import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import WeilConjectures.AlgebraicGeometry.FiniteCondensedVerdierComparison
import WeilConjectures.Targets.FiniteFieldDualizingPullback
import all WeilConjectures.SixFunctors.FiniteCtfInternalEtaleRealization
import WeilConjectures.SixFunctors.Etale.Derived.VerdierBiduality
import WeilConjectures.SixFunctors.Etale.Derived.DoubleDual
import all WeilConjectures.AlgebraicGeometry.CondensedVerdierFiniteNormalization

/-! # Finite-coefficient evaluation for the constructible exceptional adjunction -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u c d v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme Opposite
open scoped MonoidalCategory
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- An equivalence on the indicated subcategories transports the canonical
biduality arrow when the internal-Hom comparisons are invertible. -/
private theorem finiteEvaluationTransport
    {C : Type c} {D : Type d} [Category.{v} C] [Category.{w} D]
    [MonoidalCategory C] [MonoidalClosed C] [BraidedCategory C]
    [MonoidalCategory D] [MonoidalClosed D] [BraidedCategory D]
    (F : C ⥤ D) [F.Braided] {W : C} {W' : D} (i : F.obj W ≅ W')
    (P : ObjectProperty C) (Q : ObjectProperty D)
    (e : P.FullSubcategory ≌ Q.FullSubcategory)
    (r : e.functor ⋙ Q.ι ≅ P.ι ⋙ F)
    (hD : ∀ K : C, P K → P ((ihom K).obj W))
    (hβ : ∀ K : C, P K →
      IsIso ((Functor.LaxMonoidal.ihomComparison F K).natTrans.app W))
    (hδ : ∀ K : C, P K → IsIso (MonoidalClosed.toIhomIhom W K)) :
    ∀ M : D, Q M → IsIso (MonoidalClosed.toIhomIhom W' M) := by
  intro M hM
  let K := e.inverse.obj ⟨M, hM⟩
  let a : F.obj K.obj ≅ M :=
    (r.app K).symm ≪≫ Q.ι.mapIso (e.counitIso.app ⟨M, hM⟩)
  have : IsIso (MonoidalClosed.toIhomIhom W K.obj) := hδ K.obj K.property
  have hb (L : C) (hL : P L) :
      IsIso (MonoidalClosed.dualComparison F i.hom L) := by
    have := hβ L hL
    unfold MonoidalClosed.dualComparison
    infer_instance
  have := hb K.obj K.property
  have := hb ((ihom K.obj).obj W) (hD K.obj K.property)
  have hF : IsIso (MonoidalClosed.toIhomIhom W' (F.obj K.obj)) :=
    (MonoidalClosed.isIso_map_toIhomIhom_iff F i.hom K.obj).1 (by infer_instance)
  exact (NatTrans.isIso_app_iff_of_iso (MonoidalClosed.toIhomIhomNatTrans W') a).1 hF

/-- A conservative closed comparison detects the actual evaluation transpose. -/
private theorem finiteEvaluationReflect
    {C : Type c} {D : Type d} [Category.{v} C] [Category.{w} D]
    [MonoidalCategory C] [MonoidalClosed C] [BraidedCategory C]
    [MonoidalCategory D] [MonoidalClosed D] [BraidedCategory D]
    (F : C ⥤ D) [F.LaxBraided] {W : C} {W' : D} (i : F.obj W ≅ W')
    (P : ObjectProperty C) (Q : ObjectProperty D)
    (hD : ∀ K : C, P K → P ((ihom K).obj W))
    (hF : ∀ K : C, P K → Q (F.obj K))
    (hβ : ∀ K : C, P K →
      IsIso ((Functor.LaxMonoidal.ihomComparison F K).natTrans.app W))
    (hδ : ∀ K : D, Q K → IsIso (MonoidalClosed.toIhomIhom W' K))
    (hcon : ∀ {K L : C} (f : K ⟶ L), P K → P L → IsIso (F.map f) → IsIso f) :
    ∀ K : C, P K → IsIso (MonoidalClosed.toIhomIhom W K) := by
  intro K hK
  have hb (L : C) (hL : P L) :
      IsIso (MonoidalClosed.dualComparison F i.hom L) := by
    have := hβ L hL
    unfold MonoidalClosed.dualComparison
    infer_instance
  have := hb K hK
  have := hb ((ihom K).obj W) (hD K hK)
  exact hcon _ hK (hD _ (hD K hK))
    ((MonoidalClosed.isIso_map_toIhomIhom_iff F i.hom K).2 (hδ _ (hF K hK)))

set_option maxHeartbeats 1600000 in
-- Comparing the two finite coefficient presentations requires extra elaboration work.
/-- In the normalized coefficient presentation, geometric biduality transports
through the finite comparison. The dualizing object is the value of any
right adjoint of its specified Nagata support functor on the canonical unit. -/
private theorem finiteEvaluation_geometric
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
    (E : Type u) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (n : ℕ) [Fact (1 ≤ n)]
    [HasInvertibleExponent (ULift.{u + 1} (Padic.coefficientExtensionRing ℓ E n))
      (Spec (.of k))]
    (T : Scheme.{u}) (a : T ⟶ Spec (.of k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (hp : ∀ K : ConstantModelConstructibleFiniteTor
        (finiteFieldDualizingCoefficient ℓ E n).X T,
      dctfPred (finiteFieldDualizingCoefficient ℓ E n).X
        (Spec (.of k))
        ((rightDerivedLowerShriekOfCompactification
          (finiteFieldDualizingCoefficient ℓ E n).X
          (NagataCompactification a)).obj K.obj))
    (G : ConstantModelConstructibleFiniteTor
        (finiteFieldDualizingCoefficient ℓ E n).X
        (Spec (.of k)) ⥤ ConstantModelConstructibleFiniteTor
          (finiteFieldDualizingCoefficient ℓ E n).X T)
    (adj : (dctfPred
        (finiteFieldDualizingCoefficient ℓ E n).X
        (Spec (.of k))).lift
        ((dctfPred
          (finiteFieldDualizingCoefficient ℓ E n).X T).ι ⋙
          rightDerivedLowerShriekOfCompactification
            (finiteFieldDualizingCoefficient ℓ E n).X
            (NagataCompactification a)) hp ⊣ G)
    (hunit : dctfPred (finiteFieldDualizingCoefficient ℓ E n).X
      (Spec (.of k)) (𝟙_ _)) :
    letI := DerivedCategory.braidedCategory'.{u + 1, u + 1, u + 2}
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (finiteFieldDualizingCoefficient ℓ E n).X T))
    ∀ K : moduleDerived
        (finiteFieldDualizingCoefficient ℓ E n).X T,
      dctfPred (finiteFieldDualizingCoefficient ℓ E n).X
        T K → IsIso (MonoidalClosed.toIhomIhom (G.obj ⟨𝟙_ _, hunit⟩).obj K) := by
  let A := Padic.coefficientExtensionRing ℓ E n
  let : TopologicalSpace A := ⊥
  have : DiscreteTopology A := discreteTopology_bot A
  have : IsTopologicalRing A := DiscreteTopology.topologicalRing
  let c := NagataCompactification a
  let := c.hasCompactification
  let := DerivedCategory.braidedCategory'.{u + 1, u + 1, u + 2}
    (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A)))
  let := DerivedCategory.braidedCategory'.{u + 1, u + 1, u + 2}
    (FiniteDiscreteOrdinary.Internal A T)
  obtain ⟨enc, ⟨d⟩⟩ := FiniteDiscreteOrdinary.finiteCondensedVerdierComparison
    p ℓ hpℓ k E n T a
  let F := FiniteDiscreteOrdinary.internalEtaleRealization A T (enc T)
  let : F.Monoidal := FiniteNativeTensor.realizationMonoidal A T (enc T)
  let : (FiniteDiscreteOrdinary.internalEtaleRealization A
      (Spec (.of k)) (enc (Spec (.of k)))).Monoidal :=
    FiniteNativeTensor.realizationMonoidal A (Spec (.of k)) (enc (Spec (.of k)))
  let : F.Braided := { braided := d.symmetric }
  let P := Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1} A) T ⊓
    _root_.DerivedCategory.finiteTorAmplitude _
  let Q := dctfPred (FiniteDiscreteOrdinary.coefficient A) T
  let Q₀ := dctfPred (FiniteDiscreteOrdinary.coefficient A) (Spec (.of k))
  let W := Etale.dualizingComplex (ULift.{u + 1} A) a
  have hP (K) : P K ↔ Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) T K :=
    and_congr (FiniteDiscreteOrdinary.etaleBC_iff A T K) Iff.rfl
  have hD (K) (hK : P K) : P ((ihom K).obj W) :=
    (hP _).2 (Etale.constructibleFiniteTor_verdierDual (ULift.{u + 1} A) a ((hP K).1 hK))
  have hδ (K) (hK : P K) : IsIso (MonoidalClosed.toIhomIhom W K) :=
    Etale.isIso_verdierDualDoubleDual_app (ULift.{u + 1} A) a ((hP K).1 hK)
  let eG := d.adjp.rightAdjointUniq adj
  let w : F.obj W ≅ (G.obj ⟨𝟙_ _, hunit⟩).obj := d.w ≪≫
    Q.ι.mapIso (eG.app ⟨𝟙_ _, hunit⟩)
  obtain ⟨e, ⟨r⟩⟩ := d.restriction
  exact finiteEvaluationTransport F w P Q e r hD d.beta_isIso hδ

-- Fix the site universe before inferring derived monoidal structures.
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

-- Inline the canonical data instances so their inherited tensor structures agree.
set_option linter.style.haveILetI false in
/-- The normalized geometric dualizing adjoint has invertible evaluation. -/
private theorem finiteEvaluation_normalized_geometric
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ+)
    {X : Scheme.{u}} {W : moduleDerived Λ X}
    (d : CondensedVerdierFiniteNormalizationData ℓ E n Λ X W) :
    letI := DerivedCategory.braidedCategory'.{u + 1, u + 1, u + 2}
      (Mod (Sheaf (Scheme.ProEt.topology d.geometricScheme) Ab.{u + 1})
        (condensedRingObj (condensedVerdierNormalizedCoefficient ℓ E n).X d.geometricScheme))
    ∀ K : moduleDerived (condensedVerdierNormalizedCoefficient ℓ E n).X d.geometricScheme,
      dctfPred (condensedVerdierNormalizedCoefficient ℓ E n).X d.geometricScheme K →
      IsIso (MonoidalClosed.toIhomIhom
        (d.right.obj ⟨𝟙_ _, d.unit_constructible⟩).obj K) := by
  cases d with
  | @mk baseField fieldInst algClosed charPrime charNe geometricScheme structureMap separated
      finiteType quasiCompact invertibleExponent support_preserves right adjunction
      unit_constructible
      pull monoidal symmetry preserves conservative dualizingIso beta_iso =>
    letI := fieldInst
    have := algClosed
    have := charPrime
    have := separated
    have := finiteType
    have := quasiCompact
    have := invertibleExponent
    let A := Padic.coefficientExtensionRing ℓ (ULift.{u} E.1) (n : ℕ)
    let : TopologicalSpace A := ⊥
    have : DiscreteTopology A := discreteTopology_bot A
    have : IsTopologicalRing A := DiscreteTopology.topologicalRing
    have : Fact (1 ≤ (n : ℕ)) := ⟨n.pos⟩
    letI := DerivedCategory.braidedCategory'.{u + 1, u + 1, u + 2}
      (Mod (Sheaf (Scheme.ProEt.topology geometricScheme) Ab.{u + 1})
        (condensedRingObj (condensedVerdierNormalizedCoefficient ℓ E n).X geometricScheme))
    have : FiniteDimensional ℚ_[ℓ] (ULift.{u} E.1) :=
      (ULift.moduleEquiv (R := ℚ_[ℓ]) (M := E.1)).symm.finiteDimensional
    exact
      finiteEvaluation_geometric (ringChar baseField) ℓ charNe baseField
      (ULift.{u} E.1) (n : ℕ) geometricScheme structureMap support_preserves
      right adjunction unit_constructible

-- Inline the canonical data instances so their inherited tensor structures agree.
set_option linter.style.haveILetI false in
/-- Geometric evaluation and the two closed comparisons detect evaluation before pullback. -/
private theorem finiteEvaluation_normalized
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hcd : BaseFieldFiniteCD ℓ k)
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ+)
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (T : Over (Spec (.of k))) [LocallyOfFiniteType T.hom]
    [QuasiCompact T.hom] [IsSeparated T.hom]
    (W : moduleDerived Λ T.left) (hW : dctfPred Λ T.left W)
    (d : CondensedVerdierFiniteNormalizationData ℓ E n Λ T.left W)
    (hδ :
    letI := DerivedCategory.braidedCategory'.{u + 1, u + 1, u + 2}
      (Mod (Sheaf (Scheme.ProEt.topology d.geometricScheme) Ab.{u + 1})
        (condensedRingObj (condensedVerdierNormalizedCoefficient ℓ E n).X d.geometricScheme))
    ∀ K : moduleDerived (condensedVerdierNormalizedCoefficient ℓ E n).X d.geometricScheme,
      dctfPred (condensedVerdierNormalizedCoefficient ℓ E n).X d.geometricScheme K →
      IsIso (MonoidalClosed.toIhomIhom
        (d.right.obj ⟨𝟙_ _, d.unit_constructible⟩).obj K)) :
    letI := DerivedCategory.braidedCategory'.{u + 1, u + 1, u + 2}
      (Mod (Sheaf (Scheme.ProEt.topology T.left) Ab.{u + 1}) (condensedRingObj Λ T.left))
    ∀ K : moduleDerived Λ T.left, dctfPred Λ T.left K →
      IsIso (MonoidalClosed.toIhomIhom W K) := by
  cases d with
  | @mk baseField fieldInst algClosed charPrime charNe geometricScheme structureMap separated
      finiteType quasiCompact invertibleExponent support_preserves right adjunction
      unit_constructible
      pull monoidal symmetry preserves conservative dualizingIso beta_iso =>
    letI := DerivedCategory.braidedCategory'.{u + 1, u + 1, u + 2}
      (Mod (Sheaf (Scheme.ProEt.topology T.left) Ab.{u + 1})
        (condensedRingObj Λ T.left))
    letI := DerivedCategory.braidedCategory'.{u + 1, u + 1, u + 2}
      (Mod (Sheaf (Scheme.ProEt.topology geometricScheme) Ab.{u + 1})
        (condensedRingObj (condensedVerdierNormalizedCoefficient ℓ E n).X geometricScheme))
    letI := monoidal
    let : pull.LaxBraided :=
      { toLaxMonoidal := monoidal.toLaxMonoidal, braided := symmetry }
    let : T.left.Over (Spec (.of k)) := ⟨T.hom⟩
    have : LocallyOfFiniteType (T.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType T.hom›
    have : QuasiCompact (T.left ↘ Spec (.of k)) := ‹QuasiCompact T.hom›
    have : IsSeparated (T.left ↘ Spec (.of k)) := ‹IsSeparated T.hom›
    have hD (K) (hK : dctfPred Λ T.left K) :
        dctfPred Λ T.left ((ihom K).obj W) :=
      (internalHom_stability Λ ℓ k hcd hΛ K W hK hW).1
    exact finiteEvaluationReflect pull dualizingIso (dctfPred Λ T.left)
      (dctfPred (condensedVerdierNormalizedCoefficient ℓ E n).X geometricScheme)
      hD preserves beta_iso hδ conservative

/-- The canonical evaluation transpose is invertible for finite uniformizer quotients.
The adjoint and the unit are arbitrary presentations of the prescribed adjunction.

Source: latest blueprint, det-pd-biduality-coefficients.proof.md, paragraph (i).
(blueprint: lem-sf-condensed-verdier-finite-evaluation).

Proof:
1. Identify the embedded integer ring with the spectral integer ring of ULift E by
uniqueness of the extended norm. The induced quotient equivalence identifies powers
of either uniformizer ideal. Constant sheafification and the finite discrete
constant-to-continuous comparison give the coefficient ring isomorphism.
2. Restriction along that isomorphism is an exact symmetric monoidal equivalence,
preserving finite constant models and every Tor interval. The direct-image and open
extension comparisons give the compact-support comparison. Compare compactifications
using their common proof-independent choice. Uniqueness of right adjoints identifies
the image of N under G
with the normalized finite dualizing object, compatibly with its counit.
3. If k is algebraically closed, apply finiteCondensedVerdierComparison. The
constructible etale dual and its double dual remain constructible finite-Tor.
The source etale evaluation is invertible by geometric Verdier biduality. Use the
canonical internal-Hom comparison twice (dualComparison and
isIso_map_toIhomIhom_iff) to carry this precise evaluation transpose, rather than
an arbitrary isomorphism, to the condensed category. Essential surjectivity covers
every input K.
4. If k is finite, choose its algebraic closure and use
finiteField_dualizing_pullback. Its conservative pullback preserves the indicated
subcategory, carries the normalized dualizing object to the geometric one, and
has invertible evaluation-defined internal-Hom comparisons. Applying these twice
identifies pullback of the evaluation transpose with geometric evaluation. The
latter is invertible by step 3, so conservativity proves the result over k.
5. Transport back through the coefficient equivalence and the adjoint isomorphism.
Both transports preserve the transpose of evaluation. This also covers the empty
scheme and zero input; n is positive, so every coefficient quotient is in the
finite comparison's stated range. -/
theorem condensedVerdier_finite_evaluation
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hk : Finite k ∨ IsAlgClosed k) (hcd : BaseFieldFiniteCD ℓ k)
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1))
    (n : ℕ+)
    (he : Nonempty (Mon.mk Λ ≅ Mon.mk (IntegralModelsEmbedded.discreteObj
      (PadicAlgCl.integers ℓ E.1 ⧸ (Ideal.span {π}) ^ (n : ℕ)))))
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (T : Over (Spec (.of k))) [LocallyOfFiniteType T.hom]
    [QuasiCompact T.hom] [IsSeparated T.hom]
    [LocallyOfFiniteType (Over.mk (𝟙 (Spec (.of k)))).hom]
    [QuasiCompact (Over.mk (𝟙 (Spec (.of k)))).hom]
    [IsSeparated (Over.mk (𝟙 (Spec (.of k)))).hom]
    (G : ConstantModelConstructibleFiniteTor Λ (Spec (.of k)) ⥤
      ConstantModelConstructibleFiniteTor Λ T.left)
    (adj : ctfLowerShriek Λ ℓ k hcd (Over.mkIdTerminal.from T) hΛ ⊣ G)
    (N : ConstantModelConstructibleFiniteTor Λ (Spec (.of k)))
    (hN : N.obj = 𝟙_ (moduleDerived Λ (Spec (.of k)))) :
    letI := DerivedCategory.braidedCategory'.{u + 1, u + 1, u + 2}
      (Mod (Sheaf (Scheme.ProEt.topology T.left) Ab.{u + 1}) (condensedRingObj Λ T.left))
    ∀ K : moduleDerived Λ T.left, dctfPred Λ T.left K →
      IsIso (MonoidalClosed.toIhomIhom (G.obj N).obj K) := by
  obtain ⟨e⟩ := finiteNormalization_coefficientIso Λ ℓ E π hπ n he
  obtain ⟨d⟩ := condensedVerdier_finite_normalization Λ ℓ k hk hcd E n
    e hΛ T G adj N hN
  exact finiteEvaluation_normalized Λ ℓ k hcd E n hΛ T
    (G.obj N).obj (G.obj N).property d
    (finiteEvaluation_normalized_geometric Λ ℓ E n d)

end AlgebraicGeometry.ProEtale.CondensedRing

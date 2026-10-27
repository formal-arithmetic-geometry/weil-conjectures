/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Sheaf.Paper.SmoothPurityCoefficientTowers
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Paper.SmoothPurityNormalizedTowers
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.Paper.SmoothPurityTowerGluing
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.SmoothPurityCoefficientTowersAbelian
public import WeilConjectures.Compactification.RefinementCategory
public import Sheaf.Paper.SmoothPurityTowerShriekLevels
public import Sheaf.SecSmoothPurity.ReductionDirectImage
import all Sheaf.Paper.CompactSupportUniformTorBound
import all Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import all Sheaf.Paper.CoefficientTowerShriekCalculus
import Sheaf.Paper.CoefficientTowerTransitionCompatibility
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.Finite.Basic

/-! # Actual compact-support tower reductions and uniform bounds

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-tower-geometric/
`sk-prop-sp-tower-geometric-gamma.proof.md`, (3), compact-support reduction;
`det-sp-tower-bound-uniform`, uniform output bounds
(blueprint: lem-sp-compact-support-tower-reduction).

The recorded strict-tower coordinates and compactification functor are used throughout.
Natural index n denotes the positive exponent n+1. The base interface records
ell = unit * uniformizer^e, e > 0, and identifies these quotients with A_(E,e(n+1)).
The coefficient maps below are the proper-counit transpose followed by the canonical
extension-by-zero tensor identification, not newly chosen comparison maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerCalculus

private def evaluation (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (n : ℕ) : Evaluation l E b o q c n := by
  let e : F l E b o q c ⋙ spDerivedCoefficientEvaluation l E Y (q.abelian Y) n ≅
      spDerivedCoefficientEvaluation l E X (q.abelian X) n ⋙
        reductionCompactSupport (SpTowerShriek.R l E n) c.i c.g :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
          (Iso.inverseCompIso (levelComparison l E b q Y n).symm)) ≪≫
      Functor.isoWhiskerLeft _ (SpTowerShriek.Fcomparison l E b o c n) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (levelComparison l E b q X n) _
  refine ⟨e, fun M ↦ ?_⟩
  dsimp [e, Iso.inverseCompIso]
  dsimp only [F, compactSupport, Functor.comp_obj]
  simp only [Category.assoc, Category.comp_id, Category.id_comp]

private def finite_normalization (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (k : Type u) [Field k]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) (z : FiniteCoordinates l E) :
    FiniteNormalization l E k b o q z := by
  refine ⟨fun c n ↦ evaluation l E b o q c n, ?_⟩
  intro T _ _ _ _ K n
  let A := SpTowerShriek.R l E n
  let M := (spDerivedCoefficientEvaluation l E T (q.abelian T) n).obj K.obj
  obtain ⟨L, ⟨e⟩⟩ := (finiteRing_constructibleDerived_origin T A).2.2.1 M |>.mpr
    ⟨(K.property.1 n).2.1, (K.property.1 n).1⟩
  have hL := (etale_bounded_iff T (ULift.{u + 1, u} A) L.obj).mp L.property
  let R := sfIntrinsicDerivedEquivalence T A
  let C := comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T
  let ec : R.functor.obj (C.mapDerivedCategory.obj L.obj) ≅ M :=
    (Functor.mapDerivedCategoryCompIso C (finiteCoefficientIntrinsicRealization T A)).symm.app
      L.obj ≪≫ e
  exact ⟨L.obj, hL.1.1,
    ⟨R.unitIso.app _ ≪≫ R.inverse.mapIso ec⟩⟩

/-- The actual compact-support tower has the specified coefficient-normalized reductions,
including identities and the quotient cocycle, and preserves uniform constructible Tor
bounds with upper shift 2d. No normalization condition is imposed on the input tower.

Source: blueprint latest, tower-geometric gamma proof (3), compactification reduction;
retained proof step 9 and det-sp-tower-bound-uniform
(blueprint: lem-sp-compact-support-tower-reduction).

Proof:
1. Construct Evaluation for the supplied operations using realization's counit,
   Fcomparison and the section-normalized level comparisons. Expanding this word proves
   its normalization equation. The finite-ring constructible essential-image theorem
   gives bounded-below etale origins for the input levels, so these evaluations assemble
   FiniteNormalization for the supplied operations and coordinates.
2. Base change preserves smooth relative dimension d. The proved upstream dimension
   inequality therefore bounds every geometric fibre by d, including empty fibres.
   Each positive coefficient quotient is finite and killed by ell^(n+1). This exponent
   is invertible over k because ell differs from p. Apply the finite_bound helper of
   compactSupport_uniform_tor_bound to each level, using the same input interval.
   Transport constructibility, Tor bounds and cohomological bounds through the open
   coordinate comparison and the inverse finite evaluation. The common input Tor
   interval gives precisely the unnormalized output tower predicate.
3. Apply reduction_transition_compatibility to this FiniteNormalization. It gives the
   displayed formula for the actual reduction, with the prescribed proper-counit mate
   and extension-by-zero comparison, without requiring global preservation or replacing
   the supplied operations by existentially chosen ones.
4. The proved reduction_identity_aux and reduction_composition_aux expand the intrinsic
   scalar coordinates and apply the abelian tower interface's reduction_identity and
   reduction_comp. Applied to the actual output tower, they give the two coherence laws.
   No input normalization, quotient flatness or invertibility of reduction is used.
-/
theorem compact_support_tower_reduction
    (field : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ field.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (base : SpTowerShriek.Base l E) (ops : SpTowerShriek.Operations l E base)
    (q : Coordinates l E base)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of field.k))] [Y.Over (Spec (.of field.k))]
    [IsSeparated (X ↘ Spec (.of field.k))] [IsSeparated (Y ↘ Spec (.of field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of field.k))] [QuasiCompact (X ↘ Spec (.of field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of field.k))] [QuasiCompact (Y ↘ Spec (.of field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of field.k))] [IsSeparated f]
    (d : ℕ) [SmoothOfRelativeDimension d f] (c : Compactification f)
    (K : C l E base q X) :
    ∃ v : ∀ n : ℕ, Evaluation l E base ops q c n,
      (∀ (m n : ℕ) (h : m ≤ n),
        (scalarExtensionFunctor (quotient l E h) Y).map
            ((v n).comparison.hom.app K.obj) ≫
          (reductionDirectImageComparison (quotient l E h) c.i c.g).app
            ((spDerivedCoefficientEvaluation l E X (q.abelian X) n).obj K.obj) ≫
          (reductionCompactSupport (SpTowerShriek.R l E m) c.i c.g).map
            (reduction l E X (q.abelian X) h (q.scalar X h) K.obj) =
        reduction l E Y (q.abelian Y) h (q.scalar Y h)
            ((F l E base ops q c).obj K.obj) ≫
          (v m).comparison.hom.app K.obj) ∧
      (∀ n : ℕ,
        reduction l E Y (q.abelian Y) (Nat.le_refl n) (q.scalar Y (Nat.le_refl n))
            ((F l E base ops q c).obj K.obj) =
          (scalarUnit l E base q Y n).hom.app
            ((spDerivedCoefficientEvaluation l E Y (q.abelian Y) n).obj
              ((F l E base ops q c).obj K.obj))) ∧
      (∀ (r m n : ℕ) (h : r ≤ m) (w : m ≤ n),
        (scalarExtensionFunctor (quotient l E h) Y).map
            (reduction l E Y (q.abelian Y) w (q.scalar Y w)
              ((F l E base ops q c).obj K.obj)) ≫
          reduction l E Y (q.abelian Y) h (q.scalar Y h)
            ((F l E base ops q c).obj K.obj) =
        (scalarAssoc l E base q Y h w).hom.app
            ((spDerivedCoefficientEvaluation l E Y (q.abelian Y) n).obj
              ((F l E base ops q c).obj K.obj)) ≫
          reduction l E Y (q.abelian Y) (h.trans w) (q.scalar Y (h.trans w))
            ((F l E base ops q c).obj K.obj)) ∧
      spConstructibleTorTowers l E Y (q.abelian Y) ((F l E base ops q c).obj K.obj) ∧
      (∀ (a b : ℤ), a ≤ b →
        (∀ n : ℕ, HasProEtaleTorAmplitude X (SpTowerShriek.R l E n)
          ((spDerivedCoefficientEvaluation l E X (q.abelian X) n).obj K.obj) a b) →
        ∀ n : ℕ,
          spFiniteConstructibleTor Y (SpTowerShriek.R l E n)
            ((spDerivedCoefficientEvaluation l E Y (q.abelian Y) n).obj
              ((F l E base ops q c).obj K.obj)) ∧
          HasProEtaleTorAmplitude Y (SpTowerShriek.R l E n)
            ((spDerivedCoefficientEvaluation l E Y (q.abelian Y) n).obj
              ((F l E base ops q c).obj K.obj)) a (b + 2 * (d : ℤ)) ∧
          cohomologicalInterval l E Y n
            ((spDerivedCoefficientEvaluation l E Y (q.abelian Y) n).obj
              ((F l E base ops q c).obj K.obj)) a (b + 2 * (d : ℤ))) := by
  classical
  have : Fact field.p.Prime := ⟨field.prime⟩
  let : Fintype field.k₀ := Fintype.ofFinite field.k₀
  have : CharP field.k₀ field.p := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using field.card_base.trans field.cardinality_eq)
  have : CharP field.k field.p := charP_of_injective_algebraMap' field.k₀ field.p
  have : Smooth f := SmoothOfRelativeDimension.smooth d f
  have : QuasiCompact (f ≫ (Y ↘ Spec (.of field.k))) := by
    rw [comp_over]
    infer_instance
  have : QuasiCompact f := QuasiCompact.of_comp f (Y ↘ Spec (.of field.k))
  have : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  have hd (y : Y) : topologicalKrullDim
      (↑(pullback f (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y))) ≤ (d : WithBot ℕ∞) := by
    exact topologicalKrullDim_le_of_smoothOfRelativeDimension (pullback.snd _ _) d
  obtain ⟨z⟩ := finite_coordinates_exists l E
  let fd := finite_normalization l E field.k base ops q z
  have bounds (a b : ℤ) (hab : a ≤ b)
      (hK : ∀ n : ℕ, HasProEtaleTorAmplitude X (SpTowerShriek.R l E n)
        ((spDerivedCoefficientEvaluation l E X (q.abelian X) n).obj K.obj) a b) :
      ∀ n : ℕ,
        spFiniteConstructibleTor Y (SpTowerShriek.R l E n)
          ((spDerivedCoefficientEvaluation l E Y (q.abelian Y) n).obj
            ((F l E base ops q c).obj K.obj)) ∧
        HasProEtaleTorAmplitude Y (SpTowerShriek.R l E n)
          ((spDerivedCoefficientEvaluation l E Y (q.abelian Y) n).obj
            ((F l E base ops q c).obj K.obj)) a (b + 2 * (d : ℤ)) ∧
        cohomologicalInterval l E Y n
          ((spDerivedCoefficientEvaluation l E Y (q.abelian Y) n).obj
            ((F l E base ops q c).obj K.obj)) a (b + 2 * (d : ℤ)) := by
    intro n
    let A := SpTowerShriek.R l E n
    have hnil : (l : A) ^ (n + 1) = 0 := by
      change (Ideal.Quotient.mk (spEllIdeal l E ^ (n + 1)))
        ((l : Padic.coefficientExtensionIntegers l E) ^ (n + 1)) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.pow_mem_pow (Ideal.subset_span (by simp)) (n + 1))
    have : HasInvertibleExponent (ULift.{u + 1, u} A) (Spec (.of field.k)) := by
      refine ⟨l ^ (n + 1), pow_pos (Fact.out : l.Prime).pos _, ?_, ?_⟩
      · apply ULift.ext
        simpa using hnil
      · have hl : (l : field.k) ≠ 0 :=
          CharP.cast_ne_zero_of_ne_of_prime field.k (Fact.out : l.Prime) _hl.symm
        simpa only [map_pow, map_natCast, Nat.cast_pow] using
          (Ne.isUnit (pow_ne_zero (n + 1) hl)).map
            (Scheme.ΓSpecIso (.of field.k)).inv.hom
    let M := (spDerivedCoefficientEvaluation l E X (q.abelian X) n).obj K.obj
    have h := finite_bound field.k A X Y f c d hd a b hab M (K.property.1 n) (hK n)
    let eo := (Functor.isoWhiskerRight (open_coordinates A c.i)
      (directImageConstantPush A c.g)).app M
    let e := eo ≪≫ ((fd.evaluation c n).comparison.app K.obj).symm
    have ht := tor_of_iso Y A e h.2.1
    refine ⟨⟨?_, ?_, a, b + 2 * (d : ℤ), ht⟩, ht, ?_⟩
    · obtain ⟨a', b', hab', hv⟩ := h.1.1
      refine ⟨a', b', hab', fun i hi ↦ ?_⟩
      exact (hv i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e).symm
    · intro i
      exact intrinsicConstructible_of_iso Y A
        ((DerivedCategory.homologyFunctor _ i).mapIso e) (h.1.2.1 i)
    · intro i hi
      exact (h.2.2 i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e).symm
  refine ⟨fun n ↦ fd.evaluation c n, ?_, ?_, ?_, ?_, bounds⟩
  · intro m n h
    exact reduction_transition_compatibility l E field.p field.prime.pos _hl.symm
      field.k base ops q z fd f c K h
  · intro n
    exact reduction_identity_aux l E base q Y n _
  · intro r m n h w
    exact reduction_composition_aux l E base q Y h w _
  · obtain ⟨a₀, b₀, a, b, hab₀, hab, hK⟩ := K.property.2
    have hb := bounds a b hab (fun n ↦ (hK n).2)
    exact ⟨fun n ↦ (hb n).1, a, b + 2 * (d : ℤ), a, b + 2 * (d : ℤ),
      (by omega), (by omega), fun n ↦ ⟨(hb n).2.2, (hb n).2.1⟩⟩

end AlgebraicGeometry.ProEtale.SpTowerCalculus

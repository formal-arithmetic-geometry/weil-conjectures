/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.Paper.IndHeartFullFaithfulness
public import Sheaf.Paper.ModuleObjects
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.KrullDimension
import Sheaf.Paper.CondensedQcqsPushforwardContinuity
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.LiftToFinset
import Sheaf.AlgebraicGeometry.ProperHeartBoundRational
import Sheaf.Paper.ProperHeartConstructibleCohomology
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-!
# A uniform bound for proper direct image on the ind-constructible heart

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-proper-heart-bound,
statement and proof (blueprint: sk-lem-proper-heart-bound).

## Main statements

- `properHeartBound`: the finite-extension coefficient case.
- `properHeartBound_padicAlgCl`: the condensed algebraic-closure coefficient case.

The helpers only expand the degree-zero derived direct image and the three conclusions.
IndCons is the recorded filtered-colimit closure of finite constant-model constructibles.
For an integer d, the fibre bound is expressed by testing all finite lower bounds of
`topologicalKrullDim`; this retains negative d and empty fibres, whose dimension is bottom.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The functor M ↦ H^q(Rp_*(M[0])) on internal modules over the pulled-back coefficient ring.
Source: blueprint sk-lem-proper-heart-bound, definition of R^q p_* in the standing conventions
(blueprint: sk-lem-proper-heart-bound). This is the full module-object derived direct image. -/
def properHeartHigherDirectImage
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (p : X ⟶ Y) (q : ℤ) :
    CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ⥤
      CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y) :=
  DerivedCategory.singleFunctor _ 0 ⋙ (CondensedRing.lowerStar Λ p).rightDerivedFunctor ⋙
    DerivedCategory.homologyFunctor _ q

/-- The three conclusions of the proper heart bound: vanishing in degrees q > 2d+1,
ind-constructibility in every nonnegative degree, and preservation of arbitrary small sums
of ind-constructibles by each nonnegative higher direct image. Preservation means that the
image of every colimit cofan is a colimit; its legs are the images of the original injections.
By fullness, repleteness and ambient-sum closure of IndCons, this is exactly preservation
of sums in IndCons itself, including the empty sum.
Source: blueprint sk-lem-proper-heart-bound, displayed formulas and final assertion
(blueprint: sk-lem-proper-heart-bound). -/
def ProperHeartBoundAssertions
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (p : X ⟶ Y) (d : ℤ) : Prop :=
  (∀ M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X),
    ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X) M →
    (∀ q : ℤ, 2 * d + 1 < q → IsZero ((properHeartHigherDirectImage Λ p q).obj M)) ∧
    (∀ q : ℤ, 0 ≤ q → ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible Λ Y) ((properHeartHigherDirectImage Λ p q).obj M))) ∧
  (∀ (q : ℤ), 0 ≤ q → ∀ (S : Type (u + 1))
    (M : S → CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)),
    (∀ s : S, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X) (M s)) →
    ∀ c : Cofan M, IsColimit c →
      Nonempty (IsColimit ((properHeartHigherDirectImage Λ p q).mapCocone c)))

/-- Convert the finite-lower-bound convention without losing empty fibres. -/
private theorem dimension_bound_of_finite_lower_bounds (D : WithBot ℕ∞) (d : ℤ)
    (h : ∀ n : ℕ, (n : WithBot ℕ∞) ≤ D → (n : ℤ) ≤ d) :
    D ≤ if d < 0 then ⊥ else (d.toNat : WithBot ℕ∞) := by
  induction D using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe D =>
    induction D using ENat.recTopCoe with
    | top =>
      have ht := h (d.toNat + 1) (by simp)
      omega
    | coe n =>
      have hn := h n le_rfl
      have hd : ¬ d < 0 := by omega
      rw [if_neg hd]
      exact_mod_cast (show n ≤ d.toNat by omega)

set_option synthInstance.maxHeartbeats 100000 in
-- Colimit inference in the internal module category needs a larger search budget.
set_option synthInstance.maxSize 4096 in
private theorem properHeartHigherDirectImage_preservesFilteredColimits
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (p : X ⟶ Y) [QuasiCompact p] [QuasiSeparated p] (q : ℤ) :
    PreservesFilteredColimitsOfSize.{u + 1, u + 1}
      (properHeartHigherDirectImage Λ p q) := by
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let S := CochainComplex.singleFunctor A 0
  let T := DerivedCategory.Q ⋙ (CondensedRing.lowerStar Λ p).rightDerivedFunctor ⋙
    DerivedCategory.homologyFunctor _ q
  constructor
  intro I _ _
  constructor
  intro M
  have : PreservesColimit M S := by
    change PreservesColimit M (HomologicalComplex.single A (.up ℤ) 0)
    infer_instance
  let D := M ⋙ S
  let π := Functor.whiskerLeft D ((ComplexShape.embeddingUpIntGE 0).πTruncGENatTrans A)
  have hπ (i : I) : IsIso (π.app i) := by
    change IsIso (((S.obj (M.obj i))).πTruncGE 0)
    infer_instance
  have : IsIso π := NatIso.isIso_of_isIso_app π
  have hc : IsColimit (condensedContinuityCocone D 0) :=
    (IsColimit.precomposeHomEquiv (asIso π) _).symm (colimit.isColimit _)
  have ht : IsIso (condensedContinuityComparison D 0 T) :=
    condensed_qcqs_pushforward_continuity Λ p D 0
      (fun i n hn ↦ (S.obj (M.obj i)).isZero_of_isGE 0 n hn) q
  have hcT : IsColimit (T.mapCocone (condensedContinuityCocone D 0)) :=
    IsColimit.ofPointIso (colimit.isColimit (D ⋙ T)) (i := ht)
  have : PreservesColimit D T := preservesColimit_of_preserves_colimit_cocone hc hcT
  change PreservesColimit M (S ⋙ T)
  infer_instance

set_option synthInstance.maxHeartbeats 100000 in
-- Coproduct inference for internal modules needs the same search budget as filtered colimits.
set_option synthInstance.maxSize 4096 in
private theorem properHeartHigherDirectImage_preservesSums
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (p : X ⟶ Y) [QuasiCompact p] [QuasiSeparated p]
    (q : ℤ) (S : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete S) (properHeartHigherDirectImage Λ p q) := by
  have : HasColimitsOfSize.{u + 1, u + 1}
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
    inferInstance
  have : HasColimitsOfSize.{0, u + 1}
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
    hasColimitsOfSizeShrink.{0, u + 1, u + 1, u + 1} _
  have : HasColimitsOfShape (Discrete S)
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
    HasColimitsOfShape.of_small.{u + 1, u + 1} _ _
  have := properHeartHigherDirectImage_preservesFilteredColimits Λ p q
  have : (properHeartHigherDirectImage Λ p q).Additive := by
    dsimp [properHeartHigherDirectImage]
    infer_instance
  exact preservesColimitsOfShape_discrete_of_preservesColimitsOfShape_finset S _

private theorem properHeartBound_of_continuity
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (p : X ⟶ Y) (d : ℤ)
    (hv : ∀ M, IsConstantModelConstructible Λ X M →
      ∀ q : ℤ, 2 * d + 1 < q → IsZero ((properHeartHigherDirectImage Λ p q).obj M))
    (hc : ∀ M, IsConstantModelConstructible Λ X M →
      ∀ q : ℤ, 0 ≤ q → IsConstantModelConstructible Λ Y
        ((properHeartHigherDirectImage Λ p q).obj M))
    (hf : ∀ q : ℤ, PreservesFilteredColimitsOfSize.{u + 1, u + 1}
      (properHeartHigherDirectImage Λ p q))
    (hs : ∀ (q : ℤ) (S : Type (u + 1)),
      PreservesColimitsOfShape (Discrete S) (properHeartHigherDirectImage Λ p q)) :
    ProperHeartBoundAssertions Λ p d := by
  constructor
  · intro M hM
    obtain ⟨I, hI, hIf, pres, hpres⟩ := hM
    constructor
    · intro q hq
      let := hf q
      exact (pres.map (properHeartHigherDirectImage Λ p q)).isColimit.isZero_pt
        (Functor.isZero _ fun i ↦ hv _ (hpres i) q hq)
    · intro q hq
      let := hf q
      exact ⟨I, hI, hIf, pres.map (properHeartHigherDirectImage Λ p q),
        fun i ↦ hc _ (hpres i) q hq⟩
  · intro q _ S M _ c hcol
    let := hs q S
    exact ⟨isColimitOfPreserves (properHeartHigherDirectImage Λ p q) hcol⟩

/-- For a proper morphism in the standing separated finite-type positive-characteristic
setting, higher direct image of ind-constructible E-modules vanishes above 2d+1, stays
ind-constructible in nonnegative degrees, and preserves arbitrary direct sums.
Source: blueprint main-20261015, sk-lem-proper-heart-bound, statement and proof
(blueprint: sk-lem-proper-heart-bound).

Proof: convert the finite-lower-bound convention for geometric fibre dimension,
including empty fibres and negative d, and apply the constructible rational vanishing
bound. Proper higher images of constructibles are constructible by
properHeart_constructible_cohomology. The internal-module qcqs continuity comparison
shows that the higher direct-image functor preserves filtered colimits of degree-zero
complexes. Map the filtered constructible presentation supplied by ObjectProperty.ind:
its terms vanish above the bound, and in nonnegative degrees they are constructible.
This proves vanishing and ind-constructibility of the colimit. Finally additivity and
filtered finite subsums give preservation of every small coproduct, with the actual
mapped cofan legs and including the empty family. -/
theorem properHeartBound
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p₀ : ℕ) [CharP k p₀] (hp₀ : 0 < p₀) (hpℓ : p₀ ≠ ℓ)
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] (d : ℤ)
    (hd : ∀ (y : Y) (n : ℕ),
      (n : WithBot ℕ∞) ≤ topologicalKrullDim
        (pullback p (Spec.map (CommRingCat.ofHom
          (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
            Y.fromSpecResidueField y) : Scheme.{u}) → (n : ℤ) ≤ d) :
    ProperHeartBoundAssertions (Profinite.continuousMapRingObj.{u} E) p d := by
  have hdim : ∀ y : Y, topologicalKrullDim
      (pullback p (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤
      if d < 0 then ⊥ else (d.toNat : WithBot ℕ∞) := by
    intro y
    exact dimension_bound_of_finite_lower_bounds _ d (fun n h ↦ hd y n h)
  apply properHeartBound_of_continuity _ p d
  · intro M hM q hq
    exact isZero_higherDirectImage_rational_of_isProper ℓ E k
      (by rw [ringChar.eq k p₀]; exact hp₀.ne')
      (by rw [ringChar.eq k p₀]; exact hpℓ) p d hdim M hM q hq
  · exact properHeart_constructible_cohomology ℓ (Profinite.continuousMapRingObj E)
      (Or.inl ⟨E, rfl⟩) k p₀ hp₀ hpℓ X Y p
  · exact properHeartHigherDirectImage_preservesFilteredColimits _ p
  · exact properHeartHigherDirectImage_preservesSums _ p

/-- The uniform proper heart bound for the condensed algebraic closure, whose sections
are continuous maps valued in some finite subextension, rather than all continuous maps
into the algebraic closure. Source: blueprint main-20261015, sk-lem-proper-heart-bound,
statement and proof (blueprint: sk-lem-proper-heart-bound).

Proof: use the algebraic-closure coefficient cases of the same constructible
vanishing and constructibility inputs as properHeartBound. Internal-module qcqs
continuity transports the filtered constructible presentation, yielding vanishing and
ind-constructibility. Additivity and filtered finite subsums give preservation of all
small coproduct cofans, including the empty family. -/
theorem properHeartBound_padicAlgCl
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p₀ : ℕ) [CharP k p₀] (hp₀ : 0 < p₀) (hpℓ : p₀ ≠ ℓ)
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] (d : ℤ)
    (hd : ∀ (y : Y) (n : ℕ),
      (n : WithBot ℕ∞) ≤ topologicalKrullDim
        (pullback p (Spec.map (CommRingCat.ofHom
          (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
            Y.fromSpecResidueField y) : Scheme.{u}) → (n : ℤ) ≤ d) :
    ProperHeartBoundAssertions (Profinite.padicAlgClRingObj.{u} ℓ) p d := by
  have hdim : ∀ y : Y, topologicalKrullDim
      (pullback p (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤
      if d < 0 then ⊥ else (d.toNat : WithBot ℕ∞) := by
    intro y
    exact dimension_bound_of_finite_lower_bounds _ d (fun n h ↦ hd y n h)
  apply properHeartBound_of_continuity _ p d
  · intro M hM q hq
    exact isZero_higherDirectImage_padicAlgCl_of_isProper ℓ k
      (by rw [ringChar.eq k p₀]; exact hp₀.ne')
      (by rw [ringChar.eq k p₀]; exact hpℓ) p d hdim M hM q hq
  · exact properHeart_constructible_cohomology ℓ (Profinite.padicAlgClRingObj ℓ)
      (Or.inr rfl) k p₀ hp₀ hpℓ X Y p
  · exact properHeartHigherDirectImage_preservesFilteredColimits _ p
  · exact properHeartHigherDirectImage_preservesSums _ p

end AlgebraicGeometry.ProEtale

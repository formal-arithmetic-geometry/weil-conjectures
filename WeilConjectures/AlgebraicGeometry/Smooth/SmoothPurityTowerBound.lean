/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekLevels
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.KrullDimension
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerSectionCoordinates
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportUniformTorBound

/-!
# Compactly supported direct image preserves constructible towers

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower-bound,
statement and proof (blueprint: sk-lem-sp-tower-bound).

The sequence-site presentation is transported along its section-normalized equivalence
with the recorded coefficient towers. All natural indices denote the positive exponent n+1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The ordinary derived equivalence induced by the section-normalized presentation.
Source: blueprint, coefficient towers and compactification composite
(blueprint: sk-lem-sp-tower-bound). -/
def spTowerShriekRealization (b : SpTowerShriek.Base l E) (T : Scheme.{u})
    (D : SpCoefficientTowersAbelian l E T) :
    spDerivedCoefficientTowers l E T D ≌ SpTowerShriek.D l E T :=
  letI := D.hasDerived
  letI := b.realizationAdditive T
  (b.realization T).mapDerivedCategory

/-- The actual compactification operation, in the recorded coefficient-tower category.
It is exact termwise open extension followed by total derived proper direct image,
transported by the section-normalized equivalences on source and target.
Source: blueprint, displayed definition of Rf_!,bullet
(blueprint: sk-lem-sp-tower-bound). -/
def spTowerCompactSupport (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (DX : SpCoefficientTowersAbelian l E X) (DY : SpCoefficientTowersAbelian l E Y) :
    spDerivedCoefficientTowers l E X DX ⥤ spDerivedCoefficientTowers l E Y DY :=
  (spTowerShriekRealization l E b X DX).functor ⋙ SpTowerShriek.F l E b o c ⋙
    (spTowerShriekRealization l E b Y DY).inverse

private theorem presheaf_ext {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat}
    {M N : PresheafOfModules R} (hobj : ∀ U, M.obj U = N.obj U)
    (hmap : ∀ {U V} (f : U ⟶ V), HEq (M.map f) (N.map f)) : M = N := by
  cases M with | mk MO MM MI MC =>
    cases N with | mk NO NM NI NC =>
      dsimp only at hobj hmap
      have ho : MO = NO := funext hobj
      subst ho
      have hm : @MM = @NM := by
        funext U V f
        exact eq_of_heq (hmap f)
      subst hm
      rfl

private theorem sheaf_ext {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat} {M N : SheafOfModules R} (h : M.val = N.val) : M = N := by
  cases M with | mk MV MS =>
    cases N with | mk NV NS =>
      dsimp only at h
      cases h
      rfl

private theorem sheafHom_hext {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat} {M₁ M₂ N₁ N₂ : SheafOfModules R}
    (hM : M₁ = M₂) (hN : N₁ = N₂) (f : M₁ ⟶ N₁) (g : M₂ ⟶ N₂)
    (h : ∀ U, HEq (f.val.app U) (g.val.app U)) : HEq f g := by
  cases hM
  cases hN
  apply heq_of_eq
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro U
  exact eq_of_heq (h U)

private theorem sp_evaluation_obj_eq (T : Scheme.{u}) (D₁ D₂ : SpCoefficientTowersAbelian l E T)
    (M : spCoefficientTowers l E T) (n : ℕ) :
    (spCoefficientEvaluation l E T D₁.equivalence n).obj M =
      (spCoefficientEvaluation l E T D₂.equivalence n).obj M := by
  suffices h : ((D₁.equivalence.functor.obj M).level n).val =
      ((D₂.equivalence.functor.obj M).level n).val by
    exact sheaf_ext h
  apply presheaf_ext
  · intro U
    exact eq_of_heq ((D₁.sections M n U).trans (D₂.sections M n U).symm)
  · intro U V f
    exact (D₁.restrictions M n f).trans (D₂.restrictions M n f).symm

private theorem sp_evaluation_eq (T : Scheme.{u})
    (D₁ D₂ : SpCoefficientTowersAbelian l E T) (n : ℕ) :
    spCoefficientEvaluation l E T D₁.equivalence n =
      spCoefficientEvaluation l E T D₂.equivalence n := by
  apply Functor.hext (fun M ↦ sp_evaluation_obj_eq l E T D₁ D₂ M n)
  intro M N f
  apply sheafHom_hext (sp_evaluation_obj_eq l E T D₁ D₂ M n)
    (sp_evaluation_obj_eq l E T D₁ D₂ N n)
  intro U
  exact (D₁.morphisms f n U).trans (D₂.morphisms f n U).symm

private noncomputable def sp_realization_evaluation (b : SpTowerShriek.Base l E)
    (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T) (n : ℕ) :
    (spTowerShriekRealization l E b T D).functor ⋙ SpTowerShriek.Ev l E T n ≅
      spDerivedCoefficientEvaluation l E T D n := by
  letI := D.hasDerived
  haveI := b.realizationAdditive T
  haveI := D.equivalenceAdditive
  haveI := D.evaluationLimits n
  haveI := D.evaluationColimits n
  haveI : (spCoefficientEvaluation l E T D.equivalence n).Additive :=
    Functor.additive_of_preserves_binary_products _
  let q := Classical.choice (SpTowerCalculus.coordinates_realization l E b)
  let e := q.ordinaryEvaluation T n ≪≫ eqToIso (sp_evaluation_eq l E T (q.abelian T) D n)
  exact (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso e

private noncomputable def sp_support_evaluation (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (DX : SpCoefficientTowersAbelian l E X)
    (DY : SpCoefficientTowersAbelian l E Y) (n : ℕ) :
    spTowerCompactSupport l E b o c DX DY ⋙ spDerivedCoefficientEvaluation l E Y DY n ≅
      spDerivedCoefficientEvaluation l E X DX n ⋙ SpTowerShriek.finiteF l E b c n := by
  let RX := spTowerShriekRealization l E b X DX
  let RY := spTowerShriekRealization l E b Y DY
  let F := SpTowerShriek.F l E b o c
  let evY := SpTowerShriek.Ev l E Y n
  exact Functor.isoWhiskerLeft (spTowerCompactSupport l E b o c DX DY)
      (sp_realization_evaluation l E b Y DY n).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.associator RX.functor (F ⋙ RY.inverse) RY.functor ≪≫
        Functor.isoWhiskerLeft RX.functor
          (Functor.associator F RY.inverse RY.functor ≪≫
            Functor.isoWhiskerLeft F RY.counitIso ≪≫ Functor.rightUnitor F)) evY ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft RX.functor (SpTowerShriek.Fcomparison l E b o c n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (sp_realization_evaluation l E b X DX n) _

private theorem sp_tor_of_iso (T : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : Scheme.proEtaleDerivedCategory T A} (e : K ≅ L) {a b : ℤ}
    (h : Scheme.HasProEtaleTorAmplitude T A K a b) :
    Scheme.HasProEtaleTorAmplitude T A L a b := by
  refine ⟨h.1, ?_⟩
  intro C P hC f hf hP M i hi
  obtain ⟨eC⟩ := hC
  exact h.2 C P ⟨eC ≪≫ e.symm⟩ f hf hP M i hi

private theorem sp_finite_of_iso (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    {K L : Scheme.proEtaleDerivedCategory T A} (e : K ≅ L)
    (h : spFiniteConstructibleTor T A K) : spFiniteConstructibleTor T A L := by
  obtain ⟨⟨a, b, hab, hv⟩, hc, a', b', ht⟩ := h
  refine ⟨⟨a, b, hab, fun i hi ↦
    (hv i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e).symm⟩, ?_,
    a', b', sp_tor_of_iso T A e ht⟩
  intro i
  apply (Scheme.proEtaleModuleRestriction_constructible_iff T A _).mpr
  exact isConstructible_of_iso
    ((Scheme.proEtaleModuleRestriction T A).mapIso
      ((DerivedCategory.homologyFunctor _ i).mapIso e))
    ((Scheme.proEtaleModuleRestriction_constructible_iff T A _).mp (hc i))

private noncomputable def sp_finite_compact_comparison (b : SpTowerShriek.Base l E)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) [QuasiCompact c.i]
    (n : ℕ) :
    Scheme.proEtaleRingCompactSupportImage c
        (Scheme.proEtaleConstantRing Y (SpTowerShriek.R l E n))
        (Scheme.proEtaleConstantRing c.Z (SpTowerShriek.R l E n))
        (Scheme.proEtaleConstantRing X (SpTowerShriek.R l E n))
        (Scheme.proEtaleConstantRingComparison c.g (SpTowerShriek.R l E n))
        (Scheme.proEtaleConstantRingComparison c.i (SpTowerShriek.R l E n)) ≅
      SpTowerShriek.finiteF l E b c n := by
  let A := SpTowerShriek.R l E n
  let a := Adjunction.ofIsRightAdjoint (Scheme.proEtaleConstantRingPullback A c.i)
  let z := (Scheme.sfIntrinsicOpenAdjunction A c.i).ofNatIsoRight
    (Scheme.openSquarePullbackModel A c.i).symm
  letI : (Scheme.proEtaleConstantRingPullback A c.i).leftAdjoint.Additive :=
    Scheme.proEtaleRingOpenExtension_additive c.i
      (Scheme.proEtaleConstantRing c.Z A) (Scheme.proEtaleConstantRing X A)
    (Scheme.proEtaleConstantRingComparison c.i A)
  letI : PreservesFiniteLimits (Scheme.proEtaleConstantRingPullback A c.i).leftAdjoint :=
    Scheme.proEtaleRingOpenExtension_limits c.i
      (Scheme.proEtaleConstantRing c.Z A) (Scheme.proEtaleConstantRing X A)
    (Scheme.proEtaleConstantRingComparison c.i A)
  letI : PreservesFiniteColimits (Scheme.proEtaleConstantRingPullback A c.i).leftAdjoint :=
    Scheme.proEtaleRingOpenExtension_colimits c.i
      (Scheme.proEtaleConstantRing c.Z A) (Scheme.proEtaleConstantRing X A)
    (Scheme.proEtaleConstantRingComparison c.i A)
  exact Functor.isoWhiskerRight
    (Functor.mapDerivedCategoryNatIso (a.leftAdjointUniq z)) _

private theorem sp_tower_isGE_of_levels (T : Scheme.{u})
    (D : SpCoefficientTowersAbelian l E T) (C : spDerivedCoefficientTowers l E T D)
    (a : ℤ) (hC : ∀ (n : ℕ) (i : ℤ), i < a → IsZero
      ((DerivedCategory.homologyFunctor _ i).obj
        ((spDerivedCoefficientEvaluation l E T D n).obj C))) :
    @DerivedCategory.IsGE _ _ _ D.hasDerived C a := by
  letI := D.hasDerived
  haveI := D.equivalenceAdditive
  apply (DerivedCategory.isGE_iff C a).2
  intro i hi
  let H := (DerivedCategory.homologyFunctor (spCoefficientTowers l E T) i).obj C
  have hz (n : ℕ) : IsZero ((spCoefficientEvaluation l E T D.equivalence n).obj H) := by
    haveI := D.evaluationLimits n
    haveI := D.evaluationColimits n
    haveI : (spCoefficientEvaluation l E T D.equivalence n).Additive :=
      Functor.additive_of_preserves_binary_products _
    exact (hC n i hi).of_iso
      (((spCoefficientEvaluation l E T D.equivalence n)
        |>.mapDerivedCategoryHomologyFunctorIso i).app C)
  have h : IsZero (D.equivalence.functor.obj H) :=
    (SheafOfModules.strictRingSystem_isZero_iff (spCoefficientCommRings l E T) _).2 hz
  apply (IsZero.iff_id_eq_zero H).2
  apply D.equivalence.functor.map_injective
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact (IsZero.iff_id_eq_zero _).1 h

/-- Compact support preserves the unnormalized constructible finite-Tor tower category.
The first clause gives the bounded-below domain and codomain of the displayed functor;
the second is its natural level identification; the third is preservation of Dctf.
Both smooth pure dimension d and the stated general fibre bound are included.

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower-bound,
statement and the uniform-interval proof (blueprint: sk-lem-sp-tower-bound).

Proof:
1. By sk-def-sp-normalized-towers choose uniform Tor bounds [a,b] on the input.
Test det-def-sfb-constructible-tor-amplitude with the coefficient module itself:
its cohomology vanishes outside [a,b]. Kernels and cokernels of the towers are
componentwise by sk-def-sp-coefficient-towers, so cohomology is componentwise.
Thus the tower is bounded below. The exact section-normalized presentation
preserves this conclusion and all its level cohomology.
2. Apply det-sp-tower-shriek-levels, clause (1), to the chosen compactification.
Its Fcomparison identifies every level naturally with finite-coefficient Rf_!.
Exact open extension and bounded-below right derivation preserve a lower bound;
transport by the exact presentation gives the first two clauses below.
3. Apply det-sp-tower-bound-uniform to each input level. The ramification formula
ell = unit times uniformizer^e, e > 0, identifies the actual ell-power quotient
with the finite uniformizer-power quotient of exponent e(n+1). It is killed by
ell^(n+1). The geometric hypotheses bound the fibres of f itself. In the smooth
case pure relative dimension d gives that bound. The finite theorem gives output
constructibility and Tor interval [a,b+2d], independent of n.
4. Test the output Tor interval with its degree-zero tensor unit: output cohomology
also vanishes outside [a,b+2d]. This supplies exactly the uniform cohomological and
Tor intervals in spConstructibleTorTowers. Normalization is never used. -/
theorem sp_tower_bound
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] (_hlp : l ≠ p)
    (X Y : Over (Spec (CommRingCat.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (d : ℕ) (_hd : SmoothOfRelativeDimension d f.left ∨
      ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (CommRingCat.of Ω) ⟶ Y.left),
        topologicalKrullDim (pullback f.left s : Scheme.{u}) ≤ (d : WithBot ℕ∞))
    (c : Compactification f.left)
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (DX : SpCoefficientTowersAbelian l E X.left)
    (DY : SpCoefficientTowersAbelian l E Y.left) :
    (∀ C : spDerivedCoefficientTowers l E X.left DX,
      (∃ a : ℤ, @DerivedCategory.IsGE (spCoefficientTowers l E X.left) _ _ DX.hasDerived C a) →
      ∃ a : ℤ, @DerivedCategory.IsGE (spCoefficientTowers l E Y.left) _ _ DY.hasDerived
        ((spTowerCompactSupport l E b o c DX DY).obj C) a) ∧
    (∀ n : ℕ, Nonempty
      (@DerivedCategory.Plus.ι (spCoefficientTowers l E X.left) _ _ DX.hasDerived ⋙
          spTowerCompactSupport l E b o c DX DY ⋙ spDerivedCoefficientEvaluation l E Y.left DY n ≅
        @DerivedCategory.Plus.ι (spCoefficientTowers l E X.left) _ _ DX.hasDerived ⋙
          spDerivedCoefficientEvaluation l E X.left DX n ⋙ SpTowerShriek.finiteF l E b c n)) ∧
    (∀ C : spDerivedCoefficientTowers l E X.left DX,
      spConstructibleTorTowers l E X.left DX C →
      (∃ a : ℤ, @DerivedCategory.IsGE (spCoefficientTowers l E X.left) _ _ DX.hasDerived C a) ∧
      spConstructibleTorTowers l E Y.left DY ((spTowerCompactSupport l E b o c DX DY).obj C)) := by
  letI := DX.hasDerived
  letI := DY.hasDerived
  haveI := b.realizationAdditive X.left
  haveI := b.realizationAdditive Y.left
  have hbounded (C : spDerivedCoefficientTowers l E X.left DX)
      (hC : ∃ a : ℤ, C.IsGE a) :
      ∃ a : ℤ, ((spTowerCompactSupport l E b o c DX DY).obj C).IsGE a := by
    obtain ⟨a, ha⟩ := hC
    haveI := ha
    haveI h₁ : ((spTowerShriekRealization l E b X.left DX).functor.obj C).IsGE a :=
      (b.realization X.left).functor.isGE_mapDerivedCategory_obj C a
    haveI h₂ : ((SpTowerShriek.openD l E b (o.openOp c.i)).obj
        ((spTowerShriekRealization l E b X.left DX).functor.obj C)).IsGE a :=
      (o.openOp c.i).extension.isGE_mapDerivedCategory_obj
        (((spTowerShriekRealization l E b X.left DX).functor).obj C) a
    haveI := (b.calculus c.Z).grothendieck
    haveI h₃ : ((SpTowerShriek.F l E b o c).obj
        ((spTowerShriekRealization l E b X.left DX).functor.obj C)).IsGE a :=
      (o.geometry c.g).push.isGE_rightDerivedFunctor_obj
        ((SpTowerShriek.openD l E b (o.openOp c.i)).obj
          ((spTowerShriekRealization l E b X.left DX).functor.obj C)) a
    exact ⟨a, (b.realization Y.left).inverse.isGE_mapDerivedCategory_obj
      ((SpTowerShriek.F l E b o c).obj
        ((spTowerShriekRealization l E b X.left DX).functor.obj C)) a⟩
  refine ⟨hbounded, ?_, ?_⟩
  · intro n
    exact ⟨Functor.isoWhiskerLeft _ (sp_support_evaluation l E b o c DX DY n)⟩
  · intro C hC
    obtain ⟨a, z, v, w, haz, hvw, hlev⟩ := hC.2
    have hbelow : C.IsGE a := sp_tower_isGE_of_levels l E X.left DX C a
      (fun n i hi ↦ (hlev n).1 i (.inl hi))
    refine ⟨⟨a, hbelow⟩, ?_⟩
    haveI : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
    have hdim : ∀ y : Y.left, topologicalKrullDim
        (pullback f.left (Spec.map (CommRingCat.ofHom
          (algebraMap (Y.left.residueField y) (AlgebraicClosure (Y.left.residueField y)))) ≫
          Y.left.fromSpecResidueField y) : Scheme.{u}) ≤ (d : WithBot ℕ∞) := by
      intro y
      rcases _hd with hs | hg
      · haveI := hs
        exact topologicalKrullDim_le_of_smoothOfRelativeDimension
          (pullback.snd f.left _) d
      · exact hg _ _
    haveI : IsSeparated (X.left ↘ Spec (CommRingCat.of k)) := ‹IsSeparated X.hom›
    haveI : IsSeparated (Y.left ↘ Spec (CommRingCat.of k)) := ‹IsSeparated Y.hom›
    haveI : LocallyOfFiniteType (X.left ↘ Spec (CommRingCat.of k)) :=
      ‹LocallyOfFiniteType X.hom›
    haveI : LocallyOfFiniteType (Y.left ↘ Spec (CommRingCat.of k)) :=
      ‹LocallyOfFiniteType Y.hom›
    haveI : QuasiCompact (X.left ↘ Spec (CommRingCat.of k)) := ‹QuasiCompact X.hom›
    haveI : QuasiCompact (Y.left ↘ Spec (CommRingCat.of k)) := ‹QuasiCompact Y.hom›
    have hf := compactSupport_uniform_tor_bound p l k _hlp X.left Y.left f.left c d
      hdim v w hvw
    let RC := (spTowerShriekRealization l E b X.left DX).functor.obj C
    have hinput (n : ℕ) :
        spFiniteConstructibleTor X.left (SpTowerShriek.R l E n)
          ((SpTowerShriek.Ev l E X.left n).obj RC) ∧
        Scheme.HasProEtaleTorAmplitude X.left (SpTowerShriek.R l E n)
          ((SpTowerShriek.Ev l E X.left n).obj RC) v w := by
      let e := (sp_realization_evaluation l E b X.left DX n).app C
      exact ⟨sp_finite_of_iso X.left _ e.symm (hC.1 n),
        sp_tor_of_iso X.left _ e.symm (hlev n).2⟩
    have houtput := hf.2 E b o RC hinput
    let FC := (spTowerCompactSupport l E b o c DX DY).obj C
    have hinterval (n : ℕ) :
        (∀ i : ℤ, (i < v ∨ w + 2 * (d : ℤ) < i) → IsZero
          ((DerivedCategory.homologyFunctor _ i).obj
            ((spDerivedCoefficientEvaluation l E Y.left DY n).obj FC))) ∧
        Scheme.HasProEtaleTorAmplitude Y.left (SpTowerShriek.R l E n)
          ((spDerivedCoefficientEvaluation l E Y.left DY n).obj FC)
          v (w + 2 * (d : ℤ)) := by
      let e : (SpTowerShriek.Ev l E Y.left n).obj
          ((SpTowerShriek.F l E b o c).obj RC) ≅
          (spDerivedCoefficientEvaluation l E Y.left DY n).obj FC :=
        (SpTowerShriek.Ev l E Y.left n).mapIso
          ((spTowerShriekRealization l E b Y.left DY).counitIso.app
            ((SpTowerShriek.F l E b o c).obj RC)).symm ≪≫
          (sp_realization_evaluation l E b Y.left DY n).app FC
      exact ⟨fun i hi ↦ ((houtput n).2 i hi).of_iso
          ((DerivedCategory.homologyFunctor _ i).mapIso e).symm,
        sp_tor_of_iso Y.left _ e (houtput n).1⟩
    constructor
    · intro n
      have hnil : (l : SpTowerShriek.R l E n) ^ (n + 1) = 0 := by
        change (Ideal.Quotient.mk (spEllIdeal l E ^ (n + 1)))
          ((l : Padic.coefficientExtensionIntegers l E) ^ (n + 1)) = 0
        exact Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.pow_mem_pow (Ideal.subset_span (by simp)) (n + 1))
      have hfinite := (hf.1 (SpTowerShriek.R l E n)
        ⟨n + 1, Nat.succ_pos n, hnil⟩
        ((spDerivedCoefficientEvaluation l E X.left DX n).obj C)
        (hC.1 n) (hlev n).2).1
      let e := ((sp_finite_compact_comparison l E b c n).app
        ((spDerivedCoefficientEvaluation l E X.left DX n).obj C)) ≪≫
          ((sp_support_evaluation l E b o c DX DY n).app C).symm
      exact sp_finite_of_iso Y.left _ e hfinite
    · exact ⟨v, w + 2 * (d : ℤ), v, w + 2 * (d : ℤ), by omega, by omega, hinterval⟩

end AlgebraicGeometry.ProEtale

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

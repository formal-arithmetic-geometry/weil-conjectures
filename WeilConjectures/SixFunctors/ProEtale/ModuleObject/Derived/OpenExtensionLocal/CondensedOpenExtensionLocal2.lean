/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedModule.NativeCondensedModuleLocalFrobenius
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.SixFunctors.MateIsoAlongEquivalences
public import WeilConjectures.CategoryTheory.InverseMateEquivalence
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction
import WeilConjectures.CategoryTheory.Exact.ExactLocalizationInverseMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import WeilConjectures.SixFunctors.FiniteFieldDatum.FrobeniusSquareCartesian
import WeilConjectures.CategoryTheory.PullbackFamily
import WeilConjectures.WeilObject.Sheaf.StalkFrobenius
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FinitelyPresentedStalk
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedProjective
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Adjunction.Restrict
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek
import WeilConjectures.CategoryTheory.Exact.ExactDerivedCohomologyCoherence

/-! # Condensed open extension, cohomology and local Frobenius

Source: latest blueprint, part-weights-riemann-hypothesis/sec-deligne-laumon-general/
sec-reduction-to-the-relative-affine-line/sk-prop-wgen-relative-line/
lem-zl-morphism-open-closed-reduction.proof.md, Part 2
(blueprint: lem-zl-condensed-open-extension-local).

The comparison uses the chosen compactification and the normalized trivial-open comparison.
Weil cohomology is transported by the normalized exact-derived homology comparison.
All module and derived categories are the ordinary condensed-coefficient categories.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 2000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

universe u vC vD uC uD wC wD uV vV

open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open WeilConjectures.NativeCondensedModule
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace CategoryTheory

section PointFlagsPullback

variable {C : Type uC} [Category.{vC} C] {D : C → Type uD}
  [∀ X, Category.{vD} (D X)]
  {P : ∀ {X Y : C}, (X ⟶ Y) → D Y ⥤ D X}
  {c : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), P (f ≫ g) ≅ P g ⋙ P f}

/-- The key identity behind `Iso.powSuccStr_pullbackFamilyComparison`: for `E ≫ g = g ≫ E'` and
`e ≫ g = g ≫ e'`, the two ways of identifying `P (E ≫ e) (P g F)` with
`P g (P E' (P e' F))` agree.
Source: the proved auxiliary lemma in WeilConjectures.TraceFormula.PullbackFamily. -/
@[reassoc]
private lemma pointFlags_pullbackFamilyComparison_comp_aux (hc : PullbackAssoc P c)
    {W X : C} (g : W ⟶ X)
    (E e : W ⟶ W) (E' e' : X ⟶ X) (hE : E ≫ g = g ≫ E') (he : e ≫ g = g ≫ e') (F : D X) :
    (c E e).hom.app ((P g).obj F) ≫ (P E).map ((c e g).inv.app F) ≫
        (P E).map (eqToHom (by rw [he])) ≫ (P E).map ((c g e').hom.app F) ≫
        (c E g).inv.app ((P e').obj F) ≫ eqToHom (by rw [hE]) ≫
        (c g E').hom.app ((P e').obj F) =
      (c (E ≫ e) g).inv.app F ≫
        eqToHom (by rw [Category.assoc, he, ← Category.assoc, hE, Category.assoc]) ≫
        (c g (E' ≫ e')).hom.app F ≫ (P g).map ((c E' e').hom.app F) := by
  rw [← cancel_epi ((c (E ≫ e) g).hom.app F), Iso.hom_inv_id_app_assoc,
    reassoc_of% (hc.hom_app E e g F), ← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.map_id,
    Category.id_comp, eqToHom_map, pullbackComp_hom_app_comp_eqToHom_right_assoc (c := c) E he,
    hc.hom_app_comp_map_hom_app_assoc, Iso.hom_inv_id_app_assoc,
    pullbackComp_hom_app_comp_eqToHom_left_assoc (c := c) hE,
    hc.hom_app_comp_map_hom_app]
  simp only [eqToHom_trans_assoc]

end PointFlagsPullback

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing.OpenExtensionLocal

attribute [local irreducible] upperStar
  WeilConjectures.NativeCondensedModule.pointSections openImmersionLowerShriek
  upperStarComp upperStarSquareComparison

section AbstractCohomology

variable {C : Type uC} {E : Type uD} [Category.{vC} C] [Category.{vD} E]
  [Abelian C] [Abelian E] [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} E]
  (J : C ⥤ E) (P : C ⥤ C) (Q : E ⥤ E)
  [J.Additive] [P.Additive] [Q.Additive]
  [PreservesFiniteLimits J] [PreservesFiniteColimits J]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]

private theorem exactHalfLines (K : DerivedCategory C) (n : ℤ) :
    (K.IsLE n → (J.mapDerivedCategory.obj K).IsLE n) ∧
      (K.IsGE n → (J.mapDerivedCategory.obj K).IsGE n) := by
  constructor
  · intro h
    letI : K.IsLE n := h
    exact J.isLE_mapDerivedCategory_obj K n
  · intro h
    letI : K.IsGE n := h
    exact J.isGE_mapDerivedCategory_obj K n

end AbstractCohomology

variable (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
  (U₀ X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom] [IsSeparated U₀.hom]
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  (j₀ : U₀ ⟶ X₀) [IsOpenImmersion j₀.left]

private theorem geometricNoetherian (T₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] :
    IsNoetherian
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj T₀).left := by
  let S := (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj T₀
  letI : LocallyOfFiniteType S.hom := geometricFiniteType D T₀
  letI : QuasiCompact S.hom := geometricQuasiCompact D T₀
  have : IsLocallyNoetherian S.left := LocallyOfFiniteType.isLocallyNoetherian S.hom
  have : CompactSpace S.left := QuasiCompact.compactSpace_of_compactSpace S.hom
  exact {}

/-- The closure has the characteristic specified by the finite-field datum.
Source: the finite-field setting of Part 2
(blueprint: lem-zl-condensed-open-extension-local).
Proof: the cardinality q=p^a with a positive and p prime implies characteristic p for k₀.
The algebra embedding into its algebraic closure preserves characteristic. -/
private theorem closure_characteristic : ringChar D.k = D.p := by
  letI := Fintype.ofFinite D.k₀
  have hcard : Fintype.card D.k₀ = D.q := by
    rw [Fintype.card_eq_nat_card]
    exact D.card_base
  have hzero : (D.q : D.k₀) = 0 := by
    rw [← hcard]
    exact FiniteField.cast_card_eq_zero D.k₀
  have hpowa : (D.p : D.k₀) ^ D.a = 0 := by
    rw [← Nat.cast_pow, ← D.cardinality_eq, hzero]
  have hp0 : (D.p : D.k₀) = 0 := eq_zero_of_pow_eq_zero hpowa
  have hk₀ : ringChar D.k₀ = D.p :=
    CharP.ringChar_of_prime_eq_zero D.prime hp0
  exact (Algebra.ringChar_eq D.k₀ D.k).symm.trans hk₀

/-- The prime-characteristic instance required by the published compactification functor.
Source: the finite-field setting of Part 2
(blueprint: lem-zl-condensed-open-extension-local). -/
private instance closureCharacteristicPrime : Fact (ringChar D.k).Prime :=
  ⟨(closure_characteristic D).symm ▸ D.prime⟩

/-- The coefficient characteristic separation in the published compactification interface.
Source: the ell different from p setting of Part 2
(blueprint: lem-zl-condensed-open-extension-local). -/
private instance closureCharacteristicDifferent [Fact (ℓ ≠ D.p)] : Fact (ringChar D.k ≠ ℓ) :=
  ⟨fun h ↦ (Fact.out : ℓ ≠ D.p) (h.symm.trans (closure_characteristic D))⟩

private theorem constructible_extension {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [TopologicalSpace.NoetherianSpace X]
    (M : WeilConjectures.NativeCondensedModule.Modules ℓ U)
    (hM : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) U) M) :
    IsConstructibleModuleObject (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)
      ((openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) j).obj M) :=
  isConstructibleModuleObject_openImmersionLowerShriek_obj
    (Profinite.padicAlgClRingObj ℓ) j M hM

private theorem open_constructible :
    (∀ F : WeilConjectures.NativeCondensedModule.Modules ℓ (D.geometricFiber U₀).left,
      IsConstructibleModuleObject (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
          (D.geometricFiber U₀).left) F →
      IsConstructibleModuleObject (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
          (D.geometricFiber X₀).left)
        ((openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ)
          (((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left)).obj F)) := by
  letI : IsNoetherian
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj X₀).left :=
    geometricNoetherian D X₀
  exact constructible_extension ℓ
    (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left)

private theorem open_bounded_constructible [Fact (ℓ ≠ D.p)] :
    (∀ K : DerivedCategory
        (WeilConjectures.NativeCondensedModule.Modules ℓ (D.geometricFiber U₀).left),
      boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
          (D.geometricFiber U₀).left) K →
      boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
          (D.geometricFiber X₀).left)
        ((openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ)
          (((Over.pullback
        (Spec.map (CommRingCat.ofHom
              (algebraMap D.k₀ D.k)))).map j₀).left)).mapDerivedCategory.obj K)) := by
  intro K hK
  exact boundedConstructible_openImmersionLowerShriek_obj
    (Profinite.padicAlgClRingObj ℓ) ℓ
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀) ⟨K, hK⟩

private theorem open_half_lines :
    (∀ (K : DerivedCategory
        (WeilConjectures.NativeCondensedModule.Modules ℓ (D.geometricFiber U₀).left)) (n : ℤ),
      boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
          (D.geometricFiber U₀).left) K →
      (K.IsLE n → ((openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ)
        (((Over.pullback
        (Spec.map (CommRingCat.ofHom
              (algebraMap D.k₀ D.k)))).map j₀).left)).mapDerivedCategory.obj K).IsLE n) ∧
      (K.IsGE n → ((openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ)
        (((Over.pullback
        (Spec.map (CommRingCat.ofHom
              (algebraMap D.k₀ D.k)))).map j₀).left)).mapDerivedCategory.obj K).IsGE n)) := by
  intro K n _
  exact exactHalfLines _ K n

namespace NativePowerTransport
universe v w w'
open WeilConjectures WeilConjectures.NativeCondensedModule
open WeilConjectures.NativeCondensedModule

section Generic
variable {D : Scheme.{u} → Type v} [∀ X, Category.{w} (D X)]
  (P : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → D Y ⥤ D X)
  (c : ∀ {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z), P (a ≫ b) ≅ P b ⋙ P a)

private def iter {X : Scheme.{u}} (a : X ⟶ X) (M : D X)
    (θ : (P a).obj M ≅ M) : ∀ n : ℕ, (P (localPositivePower a n)).obj M ≅ M :=
  NativeCondensedModule.isoChain (fun n ↦ (P (localPositivePower a n)).obj M) M
    (NativeCondensedModule.evaluateInitial (P a) (P a) (Iso.refl _) M θ)
    (fun n ↦ NativeCondensedModule.evaluateStep (P (localPositivePower a n)) (P a)
      (P (localPositivePower a (n + 1))) (c (localPositivePower a n) a) M θ)

private theorem iter_initial_eq {X : Scheme.{u}} (a : X ⟶ X) (M : D X)
    (θ : (P a).obj M ≅ M) (e : P a ≅ P a) (he : e = Iso.refl _) (n : ℕ) :
    NativeCondensedModule.isoChain (fun n ↦ (P (localPositivePower a n)).obj M) M
      (NativeCondensedModule.evaluateInitial (P a) (P a) e M θ)
      (fun n ↦ NativeCondensedModule.evaluateStep (P (localPositivePower a n)) (P a)
        (P (localPositivePower a (n + 1))) (c (localPositivePower a n) a) M θ) n =
      iter P c a M θ n := by
  subst e
  rfl

private theorem iter_pullback (hc : PullbackAssoc P c) {X Y : Scheme.{u}}
    (f : X ⟶ Y) (a : X ⟶ X) (b : Y ⟶ Y) (h : a ≫ f = f ≫ b)
    (M : D Y) (θ : (P b).obj M ≅ M) (n : ℕ) :
    (iter P c a ((P f).obj M)
      ((pullbackFamilyComparison (c := c) f a b h).app M ≪≫ (P f).mapIso θ) n).hom =
    (pullbackFamilyComparison (c := c) f (localPositivePower a n) (localPositivePower b n)
      (power_square f a b h n)).hom.app M ≫ (P f).map (iter P c b M θ n).hom := by
  induction n with
  | zero =>
    simp only [iter_zero, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
      localPositivePower]
  | succ n ih =>
    rw [iter_succ, iter_succ]
    simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
    rw [ih]
    simp only [pullbackFamilyComparison_hom_app, Functor.map_comp, Category.assoc]
    have nat₁ := (c (localPositivePower a n) f).inv.naturality θ.hom
    have nat₂ := (c f (localPositivePower b n)).hom.naturality θ.hom
    simp only [Functor.comp_map] at nat₁ nat₂
    rw [reassoc_of% nat₁,
      map_comp_eqToHom_of_eq_assoc (P := P) (power_square f a b h n),
      reassoc_of% nat₂,
      pointFlags_pullbackFamilyComparison_comp_aux_assoc hc f _ _ _ _ (power_square f a b h n) h M]
    rfl

private theorem return_comp (hc : PullbackAssoc P c) {S X : Scheme.{u}}
    (τ : ∀ s : S ⟶ S, P s ≅ 𝟭 (D S))
    (hτ : ∀ s t (N : D S), (c s t).hom.app N ≫ (P s).map ((τ t).hom.app N) ≫
      (τ s).hom.app N = (τ (s ≫ t)).hom.app N)
    (σ ρ : S ⟶ S) (a b : X ⟶ X) (M : D X)
    (ψa : (P a).obj M ⟶ M) (ψb : (P b).obj M ⟶ M) (z : S ⟶ X)
    (ha : z ≫ a = σ ≫ z) (hb : z ≫ b = ρ ≫ z)
    (hab : z ≫ (a ≫ b) = (σ ≫ ρ) ≫ z) :
    returnMap P c τ (σ ≫ ρ) (a ≫ b) M
        ((c a b).hom.app M ≫ (P a).map ψb ≫ ψa) z hab =
      returnMap P c τ ρ b M ψb z hb ≫ returnMap P c τ σ a M ψa z ha := by
  have hβ (N : D X) :
      (c σ ρ).hom.app ((P z).obj N) ≫
        (P σ).map ((pullbackFamilyComparison (c := c) z ρ b hb.symm).hom.app N) ≫
        (pullbackFamilyComparison (c := c) z σ a ha.symm).hom.app ((P b).obj N) =
      (pullbackFamilyComparison (c := c) z (σ ≫ ρ) (a ≫ b) hab.symm).hom.app N ≫
        (P z).map ((c a b).hom.app N) := by
    simpa only [pullbackFamilyComparison_hom_app, Functor.map_comp, Category.assoc] using
      pointFlags_pullbackFamilyComparison_comp_aux hc z σ ρ a b ha.symm hb.symm N
  simpa only [returnMap, pullbackFamilyStalkComparison_hom_app,
    pullbackFamilyComparison_hom_app, Functor.map_comp, Category.assoc] using
    transport_comp (P z) (P a) (P b) (P (a ≫ b)) (P σ) (P ρ) (P (σ ≫ ρ))
      (c a b) (c σ ρ)
      (pullbackFamilyComparison (c := c) z σ a ha.symm)
      (pullbackFamilyComparison (c := c) z ρ b hb.symm)
      (pullbackFamilyComparison (c := c) z (σ ≫ ρ) (a ≫ b) hab.symm)
      (τ σ) (τ ρ) (τ (σ ≫ ρ)) hβ (hτ σ ρ) M ψa ψb

end Generic


attribute [local irreducible]
  CondensedRing.upperStarFromPointMod CondensedRing.upperStarIsoIdOfIsSepClosed

private theorem condensed_iter_eq (l : ℕ) [Fact l.Prime] {X : Scheme.{u}}
    (a : X ⟶ X) (M : NativeCondensedModule.Modules l X)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M) (n : ℕ) :
    NativeCondensedModule.iterate l a M θ n =
      iter (CondensedRing.upperStar (Profinite.padicAlgClRingObj l))
        (fun f g ↦ CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) f g) a M θ n := by
  unfold NativeCondensedModule.iterate NativeCondensedModule.iterateStep
  exact iter_initial_eq
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l))
    (fun f g ↦ CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) f g)
    a M θ _ (CondensedRing.upperStarCongr_self _ _) n

private theorem condensed_transport_eq (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {X : Scheme.{u}} (a : X ⟶ X) (M : NativeCondensedModule.Modules l X)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M)
    (z : Spec (.of D.k) ⟶ X) (n : ℕ)
    (h : z ≫ localPositivePower a n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z) :
    NativeCondensedModule.transport l D a M θ z z n h =
      (NativeCondensedModule.pointSections l D.k).mapIso
        (X := (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).obj M)
        (Y := (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).obj M)
        ((pullbackFamilyStalkComparison
          (c := fun f g ↦ CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) f g)
          (CondensedRing.upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj l)
            (localPositivePower (frobeniusPointIso D).hom n))
          z (localPositivePower a n) h).app M ≪≫
          (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).mapIso
            (iter (CondensedRing.upperStar (Profinite.padicAlgClRingObj l))
              (fun f g ↦ CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) f g)
              a M θ n)) := by
  unfold NativeCondensedModule.transport
  rw [condensed_iter_eq]
  congr 2

/-- The specified fibre compositor identifies a pulled-back Weil return with a power
of a shorter return. No constructibility or finite-dimensionality is needed.

Source: latest blueprint, part-weights-riemann-hypothesis/sec-deligne-laumon-a1/
sec-purity-of-the-lisse-part-of-the-fourier-transform/sk-p-dl-a1-some-weight/
lem-fd-realified-kernel-real.proof.md, Step 2, residue-degree pullback sentence
(blueprint: lem-fd-condensed-pullback-power-transport).

Proof: First prove the composition formula for semilinear point transports using
naturality, associativity of pullback compositors, and the composition law for the
canonical trivializations of pullback on a separably closed point. The last law can
be checked on modules pulled back from the condensed point, since this pullback is
an equivalence; there it is the existing comparison-composition identity. Induct on
the Weil iteration to commute it with pullback and to group an iteration into two
blocks. The transport-composition formula then identifies a return of length e*d
with the e-th power of the length-d return. The canonical inverse compositor
intertwines same-length returns by pullback-family naturality. Finally apply
pointSections, which preserves composition and powers. The exponent-one case is
the identity calculation; zero modules require no separate case. -/
private theorem condensedPullbackPowerTransport (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) (a : X ⟶ X) (b : Y ⟶ Y)
    (hf : a ≫ f = f ≫ b) (M : NativeCondensedModule.Modules l Y)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) b).obj M ≅ M)
    (z : Spec (.of D.k) ⟶ X) (x : Spec (.of D.k) ⟶ Y)
    (hx : z ≫ f = x) (n d e : ℕ) (hd : 0 < d) (he : 1 ≤ e) (hi : n = e * d - 1)
    (ha : z ≫ localPositivePower a n = localPositivePower (frobeniusPointIso D).hom n ≫ z)
    (hb : x ≫ localPositivePower b (d - 1) =
      localPositivePower (frobeniusPointIso D).hom (d - 1) ≫ x) :
    NativeCondensedModule.operator l D a
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f).obj M)
        ((pullbackFamilyComparison (c := fun f g ↦ CondensedRing.upperStarComp
            (Profinite.padicAlgClRingObj l) f g) f a b hf).app M ≪≫
          (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f).mapIso θ) z n ha ≫
      (NativeCondensedModule.pointSections l D.k).map
        ((CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) z f).inv.app M ≫
          eqToHom (congrArg (fun x ↦
            (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) x).obj M) hx)) =
      (NativeCondensedModule.pointSections l D.k).map
        ((CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) z f).inv.app M ≫
          eqToHom (congrArg (fun x ↦
            (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) x).obj M) hx)) ≫
        ModuleCat.ofHom ((NativeCondensedModule.operator l D b M θ x (d - 1) hb).hom ^ e) := by
  subst x
  have hA := condensed_transport_eq l D a
    ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f).obj M)
    ((pullbackFamilyComparison (c := fun f g ↦ CondensedRing.upperStarComp
        (Profinite.padicAlgClRingObj l) f g) f a b hf).app M ≪≫
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f).mapIso θ) z n ha
  have hB := condensed_transport_eq l D b M θ (z ≫ f) (d - 1) hb
  exact evaluated_intertwining_congr _ _ _ _ _ e hA hB
    (evaluated_pullback_power
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l))
      (fun f g ↦ CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) f g)
      (condensed_assoc _) (CondensedRing.upperStarIsoIdOfIsSepClosed
        (Profinite.padicAlgClRingObj l)) (tau_comp _) (NativeCondensedModule.pointSections l D.k)
      (frobeniusPointIso D).hom f a b hf M θ z (z ≫ f) rfl n d e hd he hi ha hb)


end NativePowerTransport

private def evaluatedOpenUnit {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : WeilConjectures.NativeCondensedModule.Modules ℓ U) (z : Spec (.of D.k) ⟶ U) :
    WeilConjectures.NativeCondensedModule.fibre ℓ D F z ⟶
      WeilConjectures.NativeCondensedModule.fibre ℓ D
        ((upperStar (Profinite.padicAlgClRingObj ℓ) j).obj
          ((openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) j).obj F)) z :=
  (WeilConjectures.NativeCondensedModule.pointSections ℓ D.k).map ((upperStar
    (Profinite.padicAlgClRingObj ℓ) z).map
    ((openImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) j).unit.app F))

private def evaluatedOpenCompositor {U X : Scheme.{u}} (j : U ⟶ X)
    (M : WeilConjectures.NativeCondensedModule.Modules ℓ X) (z : Spec (.of D.k) ⟶ U) :
    WeilConjectures.NativeCondensedModule.fibre ℓ D
      ((upperStar (Profinite.padicAlgClRingObj ℓ) j).obj M) z ⟶
      WeilConjectures.NativeCondensedModule.fibre ℓ D M (z ≫ j) :=
  (WeilConjectures.NativeCondensedModule.pointSections ℓ D.k).map
    ((upperStarComp (Profinite.padicAlgClRingObj ℓ) z j).inv.app M)

private instance nativeSectionsAdditive (k : Type u) [Field k] :
    (WeilConjectures.NativeCondensedModule.pointSections ℓ k).Additive := by
  unfold WeilConjectures.NativeCondensedModule.pointSections
  infer_instance

private instance nativeSectionsFiniteColimits (k : Type u) [Field k] [IsSepClosed k] :
    PreservesFiniteColimits (WeilConjectures.NativeCondensedModule.pointSections ℓ k) := by
  have : Projective (𝟙_ (WeilConjectures.NativeCondensedModule.Modules ℓ (Spec (.of k)))) :=
    projective_regular_of_isSepClosed (k := k) _
  have : (ModuleCat.restrictScalars.{u + 1} (pointScalarsOp ℓ k)).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1}
      (pointScalarsOp ℓ k)).isLeftAdjoint
  unfold WeilConjectures.NativeCondensedModule.pointSections
  infer_instance

private theorem finite_pointSections (k : Type u) [Field k] [IsSepClosed k]
    (M : WeilConjectures.NativeCondensedModule.Modules ℓ (Spec (.of k)))
    (hM : Mod.IsFinitelyPresented _ M) :
    FiniteDimensional (ULift.{u + 1} (PadicAlgCl ℓ))
      ((WeilConjectures.NativeCondensedModule.pointSections ℓ k).obj M) := by
  obtain ⟨n, m, g, ⟨e⟩⟩ := hM
  let G := WeilConjectures.NativeCondensedModule.pointSections ℓ k
  let f : Fin n → WeilConjectures.NativeCondensedModule.Modules ℓ (Spec (.of k)) :=
    fun _ ↦ 𝟙_ (WeilConjectures.NativeCondensedModule.Modules ℓ (Spec (.of k)))
  have hunit : FiniteDimensional (ULift.{u + 1} (PadicAlgCl ℓ))
      (G.obj (𝟙_ (WeilConjectures.NativeCondensedModule.Modules ℓ (Spec (.of k))))) :=
    Module.Finite.equiv (WeilConjectures.NativeCondensedModule.pointSectionsUnitIso ℓ
      k).toLinearEquiv
  letI : ∀ i : Fin n, Module.Finite (ULift.{u + 1} (PadicAlgCl ℓ)) ((G.obj ∘ f) i) :=
    fun _ ↦ hunit
  letI : FiniteDimensional (ULift.{u + 1} (PadicAlgCl ℓ))
      (ModuleCat.of (ULift.{u + 1} (PadicAlgCl ℓ)) (∀ j, (G.obj ∘ f) j)) :=
    Module.Finite.pi
  letI : FiniteDimensional (ULift.{u + 1} (PadicAlgCl ℓ)) (G.obj (⨁ f)) :=
    Module.Finite.equiv (G.mapBiproduct f ≪≫ ModuleCat.biproductIsoPi _).toLinearEquiv.symm
  exact Module.Finite.of_surjective (G.map (cokernel.π g ≫ e.inv)).hom
    ((ModuleCat.epi_iff_surjective _).1 inferInstance)

-- Field-structure transport, as in WeilConjectures.WeilObject.Sheaf.StalkFiniteFree.
private theorem sepClosed_recoveredField {k : Type u} [hk : Field k] [hs : IsSepClosed k] :
    letI := (Field.toIsField k).toField; IsSepClosed k :=
  @IsSepClosed.mk k (Field.toIsField k).toField fun p hp ↦
    @IsSepClosed.splits_of_separable k hk hs p hp

private theorem finite_geometric_fibre (k : Type u) [Field k] [IsSepClosed k]
    {X : Scheme.{u}} (M : WeilConjectures.NativeCondensedModule.Modules ℓ X)
    (hM : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) M) (z : Spec (.of k) ⟶ X) :
    FiniteDimensional (ULift.{u + 1} (PadicAlgCl ℓ))
      ((WeilConjectures.NativeCondensedModule.pointSections ℓ k).obj ((upperStar
        (Profinite.padicAlgClRingObj ℓ) z).obj M)) := by
  exact finite_pointSections ℓ k _
    (isFinitelyPresented_upperStar_of_isConstructibleModuleObject
      (Profinite.padicAlgClRingObj ℓ) (Field.toIsField k) sepClosed_recoveredField hM z)

private theorem disjoint_fibre_zero (k : Type u) [Field k] [IsSepClosed k]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (z : Spec (.of k) ⟶ X)
    (h : Disjoint (Set.range j.base) (Set.range z.base))
    (M : WeilConjectures.NativeCondensedModule.Modules ℓ U) :
    IsZero ((WeilConjectures.NativeCondensedModule.pointSections ℓ k).obj ((upperStar
      (Profinite.padicAlgClRingObj ℓ) z).obj
      ((openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) j).obj M))) := by
  exact (WeilConjectures.NativeCondensedModule.pointSections ℓ k).map_isZero
    (isZero_upperStar_obj_openImmersionLowerShriek_of_disjoint
      (Profinite.padicAlgClRingObj ℓ) j z h M)

private theorem finite_fibre {X : Scheme.{u}}
    (M : WeilConjectures.NativeCondensedModule.Modules ℓ X)
    (hM : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) M)
    (z : Spec (.of D.k) ⟶ X) :
    FiniteDimensional (ULift.{u + 1} (PadicAlgCl ℓ))
      (WeilConjectures.NativeCondensedModule.fibre ℓ D M z) := by
  exact finite_geometric_fibre ℓ D.k M hM z

private theorem zero_fibre {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (z : Spec (.of D.k) ⟶ X)
    (h : Disjoint (Set.range j.base) (Set.range z.base))
    (M : WeilConjectures.NativeCondensedModule.Modules ℓ U) :
    IsZero (WeilConjectures.NativeCondensedModule.fibre ℓ D
      ((openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) j).obj M) z) := by
  exact disjoint_fibre_zero ℓ D.k j z h M

private theorem isoChain_naturality {C : Type uC} [Category.{vC} C]
    (A B : ℕ → C) (M N : C) (f : ∀ n, A n ⟶ B n) (g : M ⟶ N)
    (a : A 0 ≅ M) (b : B 0 ≅ N)
    (s : ∀ n, A (n + 1) ≅ A n) (t : ∀ n, B (n + 1) ≅ B n)
    (hzero : f 0 ≫ b.hom = a.hom ≫ g)
    (hstep : ∀ n, f (n + 1) ≫ (t n).hom = (s n).hom ≫ f n) :
    ∀ n, f n ≫ (WeilConjectures.NativeCondensedModule.isoChain B N b t n).hom =
      (WeilConjectures.NativeCondensedModule.isoChain A M a s n).hom ≫ g := by
  intro n
  induction n with
  | zero => exact hzero
  | succ n hn =>
    change f (n + 1) ≫ ((t n).hom ≫
        (WeilConjectures.NativeCondensedModule.isoChain B N b t n).hom) =
      ((s n).hom ≫ (WeilConjectures.NativeCondensedModule.isoChain A M a s n).hom) ≫ g
    rw [← Category.assoc, hstep, Category.assoc, hn, Category.assoc]

private theorem iterate_naturality {T : Scheme.{u}} (a : T ⟶ T)
    (F G : WeilConjectures.condensedWeilModules (Profinite.padicAlgClRingObj ℓ) a)
    (f : F ⟶ G) (n : ℕ) :
    (upperStar (Profinite.padicAlgClRingObj ℓ)
      (WeilConjectures.NativeCondensedModule.localPositivePower a n)).map f.hom.f ≫
        (WeilConjectures.NativeCondensedModule.iterate ℓ a G.carrier G.str n).hom =
      (WeilConjectures.NativeCondensedModule.iterate ℓ a F.carrier F.str n).hom ≫ f.hom.f := by
  have hf : (upperStar (Profinite.padicAlgClRingObj ℓ) a).map f.hom.f ≫ G.str.hom =
      F.str.hom ≫ f.hom.f := f.hom.h
  unfold WeilConjectures.NativeCondensedModule.iterate
  refine isoChain_naturality
    (fun m ↦ (upperStar (Profinite.padicAlgClRingObj ℓ)
      (WeilConjectures.NativeCondensedModule.localPositivePower a m)).obj F.carrier)
    (fun m ↦ (upperStar (Profinite.padicAlgClRingObj ℓ)
      (WeilConjectures.NativeCondensedModule.localPositivePower a m)).obj G.carrier)
    F.carrier G.carrier
    (fun m ↦ (upperStar (Profinite.padicAlgClRingObj ℓ)
      (WeilConjectures.NativeCondensedModule.localPositivePower a m)).map f.hom.f)
    f.hom.f
    (WeilConjectures.NativeCondensedModule.evaluateInitial _ _
      (upperStarCongr (Profinite.padicAlgClRingObj ℓ)
        (show WeilConjectures.NativeCondensedModule.localPositivePower a 0 = a from rfl))
          F.carrier F.str)
    (WeilConjectures.NativeCondensedModule.evaluateInitial _ _
      (upperStarCongr (Profinite.padicAlgClRingObj ℓ)
        (show WeilConjectures.NativeCondensedModule.localPositivePower a 0 = a from rfl))
          G.carrier G.str)
    (WeilConjectures.NativeCondensedModule.iterateStep ℓ a F.carrier F.str)
    (WeilConjectures.NativeCondensedModule.iterateStep ℓ a G.carrier G.str) ?_ ?_ n
  · dsimp only [WeilConjectures.NativeCondensedModule.evaluateInitial, Iso.trans_hom, Iso.app_hom]
    rw [← Category.assoc, NatTrans.naturality, Category.assoc]
    rw [hf]
    rw [Category.assoc]
  · intro m
    unfold WeilConjectures.NativeCondensedModule.iterateStep
    dsimp only [WeilConjectures.NativeCondensedModule.evaluateStep, Iso.trans_hom,
      Iso.app_hom, Functor.mapIso_hom]
    rw [← Category.assoc, NatTrans.naturality, Category.assoc]
    simp only [Functor.comp_map, Category.assoc, ← Functor.map_comp]
    rw [hf]

private theorem evaluatedOperator_naturality
    {C : Type uC} {E : Type uD} {W : Type uV}
    [Category.{vC} C] [Category.{vD} E] [Category.{vV} W]
    (P : C ⥤ C) (Z : C ⥤ E) (V : E ⥤ W) (c : Z ⋙ 𝟭 E ≅ P ⋙ Z)
    {M N : C} (f : M ⟶ N) (a : P.obj M ⟶ M) (b : P.obj N ⟶ N)
    (h : P.map f ≫ b = a ≫ f) :
    V.map (c.hom.app M ≫ Z.map a) ≫ V.map (Z.map f) =
      V.map (Z.map f) ≫ V.map (c.hom.app N ≫ Z.map b) := by
  rw [← V.map_comp, ← V.map_comp]
  congr 1
  rw [Category.assoc, ← Z.map_comp, ← h, Z.map_comp, ← Category.assoc]
  simpa only [Functor.comp_map, Functor.id_map, Category.assoc] using
    congrArg (fun t ↦ t ≫ Z.map b) (c.hom.naturality f).symm

private theorem evaluatedIso_naturality
    {C : Type uC} {E : Type uD} {W : Type uV}
    [Category.{vC} C] [Category.{vD} E] [Category.{vV} W]
    (P : C ⥤ C) (Z : C ⥤ E) (V : E ⥤ W) (c : Z ⋙ 𝟭 E ≅ P ⋙ Z)
    {M N : C} (f : M ⟶ N) (a : P.obj M ≅ M) (b : P.obj N ≅ N)
    (h : P.map f ≫ b.hom = a.hom ≫ f) :
    (V.mapIso (c.app M ≪≫ Z.mapIso a)).hom ≫ V.map (Z.map f) =
      V.map (Z.map f) ≫ (V.mapIso (c.app N ≪≫ Z.mapIso b)).hom := by
  simpa only [Functor.mapIso_hom, Iso.trans_hom, Iso.app_hom] using
    evaluatedOperator_naturality P Z V c f a.hom b.hom h

private theorem iso_intertwining_congr {C : Type uC} [Category.{vC} C]
    {X Y : C} (A A' : X ≅ X) (B B' : Y ≅ Y) (f : X ⟶ Y)
    (hA : A = A') (hB : B = B') (h : A'.hom ≫ f = f ≫ B'.hom) :
    A.hom ≫ f = f ≫ B.hom := by
  subst A' B'
  exact h

private theorem transport_eq {T : Scheme.{u}} (a : T ⟶ T)
    (M : WeilConjectures.NativeCondensedModule.Modules ℓ T)
    (θ : (upperStar (Profinite.padicAlgClRingObj ℓ) a).obj M ≅ M)
    (z : Spec (.of D.k) ⟶ T) (n : ℕ)
    (h : z ≫ WeilConjectures.NativeCondensedModule.localPositivePower a n =
      WeilConjectures.NativeCondensedModule.localPositivePower
        (WeilConjectures.NativeCondensedModule.frobeniusPointIso D).hom n ≫ z) :
    WeilConjectures.NativeCondensedModule.transport ℓ D a M θ z z n h =
      (WeilConjectures.NativeCondensedModule.pointSections ℓ D.k).mapIso
        (X := (upperStar (Profinite.padicAlgClRingObj ℓ) z).obj M)
        (Y := (upperStar (Profinite.padicAlgClRingObj ℓ) z).obj M)
        ((pointComparison (Profinite.padicAlgClRingObj ℓ)
          (upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj ℓ)
            (WeilConjectures.NativeCondensedModule.localPositivePower
              (WeilConjectures.NativeCondensedModule.frobeniusPointIso D).hom n))
          (WeilConjectures.NativeCondensedModule.localPositivePower a n) h).app M ≪≫
          (upperStar (Profinite.padicAlgClRingObj ℓ) z).mapIso
            (WeilConjectures.NativeCondensedModule.iterate ℓ a M θ n)) := rfl

private theorem operator_naturality {T : Scheme.{u}} (a : T ⟶ T)
    (F G : WeilConjectures.condensedWeilModules (Profinite.padicAlgClRingObj ℓ) a)
    (f : F ⟶ G) (z : Spec (.of D.k) ⟶ T) (n : ℕ)
    (h : z ≫ WeilConjectures.NativeCondensedModule.localPositivePower a n =
      WeilConjectures.NativeCondensedModule.localPositivePower
        (WeilConjectures.NativeCondensedModule.frobeniusPointIso D).hom n ≫ z) :
    WeilConjectures.NativeCondensedModule.operator ℓ D a F.carrier F.str z n h ≫
        (WeilConjectures.NativeCondensedModule.pointSections ℓ D.k).map ((upperStar
          (Profinite.padicAlgClRingObj ℓ) z).map f.hom.f) =
      (WeilConjectures.NativeCondensedModule.pointSections ℓ D.k).map ((upperStar
        (Profinite.padicAlgClRingObj ℓ) z).map f.hom.f) ≫
        WeilConjectures.NativeCondensedModule.operator ℓ D a G.carrier G.str z n h := by
  let Z := upperStar (Profinite.padicAlgClRingObj ℓ) z
  let V := WeilConjectures.NativeCondensedModule.pointSections ℓ D.k
  let c := pointComparison (Profinite.padicAlgClRingObj ℓ)
    (upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj ℓ)
      (WeilConjectures.NativeCondensedModule.localPositivePower
        (WeilConjectures.NativeCondensedModule.frobeniusPointIso D).hom n))
    (WeilConjectures.NativeCondensedModule.localPositivePower a n) h
  exact iso_intertwining_congr
    (WeilConjectures.NativeCondensedModule.transport ℓ D a F.carrier F.str z z n h)
    (V.mapIso (c.app F.carrier ≪≫ Z.mapIso
      (WeilConjectures.NativeCondensedModule.iterate ℓ a F.carrier F.str n)))
    (WeilConjectures.NativeCondensedModule.transport ℓ D a G.carrier G.str z z n h)
    (V.mapIso (c.app G.carrier ≪≫ Z.mapIso
      (WeilConjectures.NativeCondensedModule.iterate ℓ a G.carrier G.str n)))
    (V.map (Z.map f.hom.f))
    (transport_eq D ℓ a F.carrier F.str z n h)
    (transport_eq D ℓ a G.carrier G.str z n h)
    (evaluatedIso_naturality
      (upperStar (Profinite.padicAlgClRingObj ℓ)
        (WeilConjectures.NativeCondensedModule.localPositivePower a n))
      Z V c f.hom.f
      (WeilConjectures.NativeCondensedModule.iterate ℓ a F.carrier F.str n)
      (WeilConjectures.NativeCondensedModule.iterate ℓ a G.carrier G.str n)
      (iterate_naturality ℓ a F G f n))

private def Intertwines {C : Type uC} [Category.{vC} C] {X Y : C}
    (p : X ⟶ X) (q : Y ⟶ Y) (f : X ⟶ Y) : Prop := p ≫ f = f ≫ q

private theorem power_square {U X : Scheme.{u}} (j : U ⟶ X)
    (a : U ⟶ U) (b : X ⟶ X) (h : a ≫ j = j ≫ b) (n : ℕ) :
    WeilConjectures.NativeCondensedModule.localPositivePower a n ≫ j =
      j ≫ WeilConjectures.NativeCondensedModule.localPositivePower b n := by
  induction n with
  | zero => exact h
  | succ n ih =>
    simp only [WeilConjectures.NativeCondensedModule.localPositivePower, Category.assoc, h, ←
      reassoc_of% ih]

private theorem return_on_open {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (a : U ⟶ U) (b : X ⟶ X) (sq : a ≫ j = j ≫ b)
    (z : Spec (.of D.k) ⟶ U) (n : ℕ)
    (hy : (z ≫ j) ≫ WeilConjectures.NativeCondensedModule.localPositivePower b n =
      WeilConjectures.NativeCondensedModule.localPositivePower
        (WeilConjectures.NativeCondensedModule.frobeniusPointIso D).hom n ≫
        (z ≫ j)) :
    z ≫ WeilConjectures.NativeCondensedModule.localPositivePower a n =
      WeilConjectures.NativeCondensedModule.localPositivePower
        (WeilConjectures.NativeCondensedModule.frobeniusPointIso D).hom n ≫ z := by
  apply (cancel_mono j).1
  simpa only [Category.assoc, power_square j a b sq n] using hy

private noncomputable def fibreUnitIso
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : WeilConjectures.NativeCondensedModule.Modules ℓ U) (z : Spec (.of D.k) ⟶ U) :
    WeilConjectures.NativeCondensedModule.fibre ℓ D F z ≅
      WeilConjectures.NativeCondensedModule.fibre ℓ D
        ((openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) j).obj F) (z ≫ j) := by
  let a := openImmersionLowerShriekUpperStarAdjunction (Profinite.padicAlgClRingObj ℓ) j
  letI : IsIso a.unit := a.unit_isIso_of_L_fully_faithful
  exact (upperStar (Profinite.padicAlgClRingObj ℓ) z ⋙
    WeilConjectures.NativeCondensedModule.pointSections ℓ D.k).mapIso
      (asIso (a.unit.app F)) ≪≫
    (WeilConjectures.NativeCondensedModule.pointSections ℓ D.k).mapIso
      ((upperStarComp (Profinite.padicAlgClRingObj ℓ) z j).symm.app
        ((openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) j).obj F))

set_option linter.unusedSimpArgs false in
private theorem pullbackComparison_eq {U X : Scheme.{u}} (j : U ⟶ X)
    (a : U ⟶ U) (b : X ⟶ X) (h : a ≫ j = j ≫ b) :
    CategoryTheory.pullbackFamilyComparison
      (c := fun f g ↦ upperStarComp (Profinite.padicAlgClRingObj ℓ) f g) j a b h =
      (upperStarSquareComparison (Profinite.padicAlgClRingObj ℓ) (CommSq.mk h)).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  simp only [CategoryTheory.pullbackFamilyComparison_hom_app, upperStarSquareComparison,
    Iso.symm_hom, Iso.trans_inv, NatTrans.comp_app, eqToIso.inv,
    Iso.symm_inv, eqToHom_app, Category.assoc]

private theorem intertwining_change {C : Type uC} [Category.{vC} C]
    {X Y : C} (A A' : X ⟶ X) (B B' : Y ⟶ Y) (f f' : X ⟶ Y)
    (hA : A = A') (hB : B = B') (hf : f = f')
    (h : A ≫ f = f ≫ B) : A' ≫ f' = f' ≫ B' := by
  subst A' B' f'
  exact h

private theorem map_comp_id {C : Type uC} {E : Type uD}
    [Category.{vC} C] [Category.{vD} E] (V : C ⥤ E)
    {X Y : C} (c : X ⟶ Y) : V.map (c ≫ 𝟙 Y) = V.map c :=
  congrArg (fun f ↦ V.map f) (Category.comp_id c)

private theorem ofHom_pow_one {K : Type uC} [Field K]
    {M : ModuleCat.{vC} K} (B : M ⟶ M) : ModuleCat.ofHom (B.hom ^ 1) = B := by
  simp only [pow_one, ModuleCat.ofHom_hom]

private theorem pullback_structure_eq {U X : Scheme.{u}} (j : U ⟶ X)
    (a : U ⟶ U) (b : X ⟶ X) (h : a ≫ j = j ≫ b)
    (M : WeilConjectures.condensedWeilModules (Profinite.padicAlgClRingObj ℓ) b) :
    (CategoryTheory.pullbackFamilyComparison
      (c := fun f g ↦ upperStarComp (Profinite.padicAlgClRingObj ℓ) f g)
      j a b h).app M.carrier ≪≫
        (upperStar (Profinite.padicAlgClRingObj ℓ) j).mapIso M.str =
      ((IsoAlgebra.mapOfNatIso
        (upperStarSquareComparison (Profinite.padicAlgClRingObj ℓ)
          (CommSq.mk h)).symm).obj M).str := by
  rw [pullbackComparison_eq]
  exact (IsoAlgebra.mapOfNatIso_obj_str
    (upperStarSquareComparison (Profinite.padicAlgClRingObj ℓ) (CommSq.mk h)).symm M).symm

private theorem pullback_operator_intertwining {U X : Scheme.{u}} (j : U ⟶ X)
    (a : U ⟶ U) (b : X ⟶ X) (hs : a ≫ j = j ≫ b)
    (M : WeilConjectures.condensedWeilModules (Profinite.padicAlgClRingObj ℓ) b)
    (z : Spec (.of D.k) ⟶ U) (n : ℕ)
    (hz : z ≫ WeilConjectures.NativeCondensedModule.localPositivePower a n =
      WeilConjectures.NativeCondensedModule.localPositivePower
        (WeilConjectures.NativeCondensedModule.frobeniusPointIso D).hom n ≫ z)
    (hy : (z ≫ j) ≫ WeilConjectures.NativeCondensedModule.localPositivePower b n =
      WeilConjectures.NativeCondensedModule.localPositivePower
        (WeilConjectures.NativeCondensedModule.frobeniusPointIso D).hom n ≫
        (z ≫ j)) :
    let N := (IsoAlgebra.mapOfNatIso
      (upperStarSquareComparison (Profinite.padicAlgClRingObj ℓ) (CommSq.mk hs)).symm).obj M
    Intertwines
      (WeilConjectures.NativeCondensedModule.operator ℓ D a
        ((upperStar (Profinite.padicAlgClRingObj ℓ) j).obj M.carrier) N.str z n hz)
      (WeilConjectures.NativeCondensedModule.operator ℓ D b M.carrier M.str (z ≫ j) n hy)
      (evaluatedOpenCompositor D ℓ j M.carrier z) := by
  let N := (IsoAlgebra.mapOfNatIso
    (upperStarSquareComparison (Profinite.padicAlgClRingObj ℓ) (CommSq.mk hs)).symm).obj M
  have hp := NativePowerTransport.condensedPullbackPowerTransport ℓ D j a b hs
    M.carrier M.str z (z ≫ j) rfl n (n + 1) 1 (by omega) (by omega) (by omega)
    hz (by simpa only [Nat.add_sub_cancel] using hy)
  have hA := congrArg (fun θ ↦ WeilConjectures.NativeCondensedModule.operator ℓ D a
      ((upperStar (Profinite.padicAlgClRingObj ℓ) j).obj M.carrier) θ z n hz)
    (pullback_structure_eq ℓ j a b hs M)
  exact intertwining_change _ _ _ _ _ _ hA
    (ofHom_pow_one (WeilConjectures.NativeCondensedModule.operator ℓ D b M.carrier M.str
      (z ≫ j) n hy))
    (map_comp_id (WeilConjectures.NativeCondensedModule.pointSections ℓ D.k)
      ((upperStarComp (Profinite.padicAlgClRingObj ℓ) z j).inv.app M.carrier)) hp

private theorem pullback_at_mapped {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (a : U ⟶ U) (b : X ⟶ X) (hs : a ≫ j = j ≫ b)
    (β : openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) j ⋙
        upperStar (Profinite.padicAlgClRingObj ℓ) b ≅
      upperStar (Profinite.padicAlgClRingObj ℓ) a ⋙
        openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) j)
    (F : WeilConjectures.condensedWeilModules (Profinite.padicAlgClRingObj ℓ) a)
    (z : Spec (.of D.k) ⟶ U) (n : ℕ)
    (hz : z ≫ WeilConjectures.NativeCondensedModule.localPositivePower a n =
      WeilConjectures.NativeCondensedModule.localPositivePower
        (WeilConjectures.NativeCondensedModule.frobeniusPointIso D).hom n ≫ z)
    (hy : (z ≫ j) ≫ WeilConjectures.NativeCondensedModule.localPositivePower b n =
      WeilConjectures.NativeCondensedModule.localPositivePower
        (WeilConjectures.NativeCondensedModule.frobeniusPointIso D).hom n ≫
        (z ≫ j)) :
    let N := (IsoAlgebra.mapOfNatIso
      (upperStarSquareComparison (Profinite.padicAlgClRingObj ℓ) (CommSq.mk hs)).symm).obj
        ((IsoAlgebra.mapOfNatIso β).obj F)
    Intertwines
      (WeilConjectures.NativeCondensedModule.operator ℓ D a
        ((upperStar (Profinite.padicAlgClRingObj ℓ) j).obj
          ((openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) j).obj F.carrier))
        N.str z n hz)
      (WeilConjectures.NativeCondensedModule.operator ℓ D b
        ((openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) j).obj F.carrier)
        ((IsoAlgebra.mapOfNatIso β).obj F).str (z ≫ j) n hy)
      (evaluatedOpenCompositor D ℓ j
        ((openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) j).obj F.carrier) z) := by
  exact pullback_operator_intertwining D ℓ j a b hs
    ((IsoAlgebra.mapOfNatIso β).obj F) z n hz hy

private theorem disjoint_of_residue_square {U₀ X₀ U X : Scheme.{u}}
    {k : Type u} [Field k] (j₀ : U₀ ⟶ X₀) (j : U ⟶ X)
    (qU : U ⟶ U₀) (qX : X ⟶ X₀) (z : Spec (.of k) ⟶ X) (x : X₀)
    (t : Spec (.of k) ⟶ Spec (X₀.residueField x))
    (hj : j ≫ qX = qU ≫ j₀) (hz : z ≫ qX = t ≫ X₀.fromSpecResidueField x)
    (hx : x ∉ Set.range j₀) : Disjoint (Set.range j.base) (Set.range z.base) := by
  rw [Set.disjoint_left]
  intro p hp hz'
  obtain ⟨u, rfl⟩ := hp
  obtain ⟨s, hs⟩ := hz'
  apply hx
  refine ⟨qU u, ?_⟩
  have heval : qX (z s) = x := by
    have h := congrArg (fun f : Spec (.of k) ⟶ X₀ ↦ f s) hz
    simpa only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] using h
  have heval' : j₀ (qU u) = qX (j u) := by
    have h := congrArg (fun f : U ⟶ X₀ ↦ f u) hj.symm
    simpa only [Scheme.Hom.comp_apply] using h
  exact heval'.trans ((congrArg qX hs.symm).trans heval)

private theorem closedPoint_disjoint
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (ι : X₀.left.residueField x.val →+* D.k)
    (hι : ι.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
    (hx : x.val ∉ Set.range j₀.left) :
    Disjoint (Set.range (((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left).base)
      (Set.range (WeilConjectures.NativeCondensedModule.localClosedPoint D X₀ x ι hι).base) := by
  let j := (((Over.pullback
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left)
  let qU := pullback.fst U₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
  let qX := pullback.fst X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
  have hj : j ≫ qX = qU ≫ j₀.left := pullback.lift_fst _ _ _
  have hp : WeilConjectures.NativeCondensedModule.localClosedPoint D X₀ x ι hι ≫ qX =
      Spec.map (CommRingCat.ofHom ι) ≫ X₀.left.fromSpecResidueField x.val :=
    pullback.lift_fst _ _ _
  exact disjoint_of_residue_square j₀.left j qU qX
    (WeilConjectures.NativeCondensedModule.localClosedPoint D X₀ x ι hι) x.val
    (Spec.map (CommRingCat.ofHom ι)) hj hp hx

/-- Every compatible closed geometric point on the open has its geometric lift there.
Together with PointwiseOpenComparison this supplies the on-open fibre identification,
rather than merely a conditional assertion about a potentially absent lift.
Source: Part 2, same stalks on the open
(blueprint: lem-zl-condensed-open-extension-local).
Proof: factor the residue point through the open using its membership in the open range.
Base change this factorization along Spec k. Pullback uniqueness gives both projection
identities, including compatibility with the fixed geometric residue embedding. -/
theorem closedPoint_open_lift
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (ι : X₀.left.residueField x.val →+* D.k)
    (hι : ι.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
    (hx : x.val ∈ Set.range j₀.left) :
    ∃ z : Spec (.of D.k) ⟶ (D.geometricFiber U₀).left,
      z ≫ (D.geometricFiber U₀).hom = 𝟙 _ ∧
      z ≫ ((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left =
          WeilConjectures.NativeCondensedModule.localClosedPoint D X₀ x ι hι := by
  let a : Spec (.of D.k) ⟶ X₀.left :=
    Spec.map (CommRingCat.ofHom ι) ≫ X₀.left.fromSpecResidueField x.val
  have ha : Set.range a ⊆ Set.range j₀.left := by
    rintro _ ⟨t, rfl⟩
    change X₀.left.fromSpecResidueField x.val ((Spec.map (CommRingCat.ofHom ι)) t) ∈ _
    rw [Scheme.fromSpecResidueField_apply]
    exact hx
  let b := IsOpenImmersion.lift j₀.left a ha
  have hb : b ≫ j₀.left = a := IsOpenImmersion.lift_fac _ _ _
  have hc : b ≫ U₀.hom = (𝟙 _) ≫
      Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)) := by
    rw [← j₀.w, ← Category.assoc, hb]
    exact WeilConjectures.NativeCondensedModule.localClosedPoint_compatible D X₀ x ι hι
  refine ⟨pullback.lift b (𝟙 _) hc, pullback.lift_snd _ _ _, ?_⟩
  apply pullback.hom_ext
  · simpa only [Category.assoc, Over.pullback_map_left, pullback.lift_fst,
      pullback.lift_fst_assoc, WeilConjectures.NativeCondensedModule.localClosedPoint]
      using hb
  · simp only [Category.assoc, Over.pullback_map_left, pullback.lift_snd,
      WeilConjectures.NativeCondensedModule.localClosedPoint]


/-- On sheaves in degree zero the termwise functor is the exact module open extension,
with the existing single-functor comparison, before imposing the Weil structure.
Source: Part 2, restriction to exact extension of sheaves
(blueprint: lem-zl-condensed-open-extension-local).
Proof: exact module extension acts on each term of a cochain complex. A single complex
is therefore sent to the single complex of the extended module. The localization
factorizations identify this comparison with mapDerivedCategorySingleFunctor. The
inverse-mate construction then gives the induced structure on the same module. -/
theorem degreeZero_comparison :
    Nonempty
      ((DerivedCategory.singleFunctor _ 0) ⋙
          (openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ)
            (((Over.pullback
              (Spec.map (CommRingCat.ofHom
                (algebraMap D.k₀ D.k)))).map j₀).left)).mapDerivedCategory ≅
        openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ)
          (((Over.pullback
            (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left) ⋙
              DerivedCategory.singleFunctor _ 0) := by
  exact ⟨(openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ)
    (((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left)
      ).mapDerivedCategorySingleFunctor 0⟩

end AlgebraicGeometry.ProEtale.CondensedRing.OpenExtensionLocal

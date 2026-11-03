/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.RelativeCurve.RelativeCurvePunctual
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import Mathlib.Algebra.CharP.CharAndCard
import all WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartClosure
import WeilConjectures.AlgebraicGeometry.Pullback.PullbackFiniteConstantLocalModel

/-! # Constructibility of native higher compact support

Source: latest blueprint, compact-support constructibility in
lem-zl-relative-curve-mixedness (blueprint: lem-zl-native-higher-shriek-constructible).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.RelativeCurve

/-- Lisse actual coefficient modules are constructible on a noetherian scheme.
Source: latest blueprint, sk-lem-coefficient-heart, trivial-stratification case.
(blueprint: lem-zl-native-higher-shriek-constructible)

Proof: take the trivial one-stratum stratification. Lisse local finite freeness
implies local finite presentation, which is the ordinary constructibility condition
on this stratum. Apply the coefficient-heart comparison.
-/
theorem native_lisse_constructible (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    [IsNoetherian X] (M : NativeCondensedModule.Modules l X)
    (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M) :
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l) X M := by
  classical
  rw [IsConstantModelConstructible, if_pos ⟨inferInstance, inferInstance⟩]
  exact ⟨Scheme.Stratification.trivial X, fun _ ↦
    pullback_finiteConstantLocalModel (Profinite.padicAlgClRingObj l) (𝟙 X) M
      (heart_free_model (Profinite.padicAlgClRingObj l) M hM)⟩

/-- Every higher compact-support module of a constructible native Weil module is constructible.
Source: latest blueprint, lem-zl-relative-curve-mixedness, constructibility clause.
(blueprint: lem-zl-native-higher-shriek-constructible)

Proof: place the input carrier in degree zero. The bounded-constructible compact-support
functor for the specified geometric compactification preserves bounded constructibility;
its inclusion comparison identifies its image with the ambient compact-support composite.
Every cohomology module is therefore constructible. The coefficient-heart comparison
identifies ordinary constructibility with finite constant stratified constructibility.
-/
theorem higherShriek_constructible
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    {U₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom] [IsSeparated U₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (h₀ : U₀ ⟶ Y₀) (c₀ : Compactification h₀.left)
    (M : NativeL2.WeilModule D l U₀)
    (hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber U₀).left M.carrier) (i : ℕ) :
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber Y₀).left (higherShriek D l h₀ c₀ M i).carrier := by
  classical
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  have : Fact D.p.Prime := ⟨D.prime⟩
  have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card.symm.trans D.card_base).trans D.cardinality_eq)
  have : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  have : Fact (ringChar D.k).Prime := ⟨by rw [ringChar.eq D.k D.p]; exact D.prime⟩
  have : Fact (ringChar D.k ≠ l) := ⟨by rw [ringChar.eq D.k D.p]; exact hl.symm⟩
  let X := D.geometricFiber U₀
  let Y := D.geometricFiber Y₀
  let f : X ⟶ Y :=
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map h₀
  have : LocallyOfFiniteType X.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd U₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have : LocallyOfFiniteType Y.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have : QuasiCompact X.hom :=
    inferInstanceAs (QuasiCompact (pullback.snd U₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have : QuasiCompact Y.hom :=
    inferInstanceAs (QuasiCompact (pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have : IsSeparated X.hom :=
    inferInstanceAs (IsSeparated (pullback.snd U₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have : IsSeparated Y.hom :=
    inferInstanceAs (IsSeparated (pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  let Λ := Profinite.padicAlgClRingObj.{u} l
  have hsingle := CondensedRing.boundedConstructible_singleFunctor_obj Λ X.left 0 M.carrier
    ((adicConstructibilityPredicateComparison l X.left Λ .algebraicClosure).1 _ |>.mpr hM)
  let c : Compactification f.left := geometricCompactification D h₀ c₀
  let K : BoundedConstructible (condensedRingObj Λ X.left) := ⟨_, hsingle⟩
  let R := CondensedRing.boundedConstructibleLowerShriekOfCompactification l c
  have he := (CondensedRing.boundedConstructibleLowerShriekOfCompactificationCompatibility
    l c).app K
  have hc := (R.obj K).property
  have hpush := (boundedConstructible (condensedRingObj Λ Y.left)).prop_of_iso he hc
  apply (adicConstructibilityPredicateComparison l Y.left Λ .algebraicClosure).1 _ |>.mp
  unfold higherShriek
  exact hpush.2 (i : ℤ)

end WeilConjectures.RelativeCurve

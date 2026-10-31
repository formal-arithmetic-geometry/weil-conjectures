/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteProperLocalizing
public import WeilConjectures.AlgebraicGeometry.CohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
import all WeilConjectures.AlgebraicGeometry.CohomologicalDimension
import WeilConjectures.AlgebraicGeometry.ProperFiniteTorAmplitude
import WeilConjectures.SixFunctors.FiniteCtfInternalEtaleRealization
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-!
# Proper direct image for finite coefficients

Source: literature/blueprint/slopmaster2-20261029-2300/blueprint/sec-six-functors-basics/
sk-prop-ctf-finite-proper/_section.md, node sk-prop-ctf-finite-proper, order 2348;
Stacks Project, Tags 0GL0, 0F10, 0F12, 0F0D (blueprint: sk-prop-ctf-finite-proper).

## Main statements

- `AlgebraicGeometry.ProEtale.properFiniteCoefficient`: for a finite ring `A` killed by a
  power of `ℓ` and a proper `k`-morphism `p`, `Rp_*` preserves `Dctf`, the localizing closure
  and all small coproducts there, and turns the Tor interval `[a,b]` into `[a,b+d]` when `d`
  bounds the `ℓ`-cohomological dimension of every geometric fibre.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.overlappingInstances false
set_option linter.unusedVariables false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry Scheme
open scoped CategoryTheory.Functor CategoryTheory.Obj
open scoped AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale

set_option maxHeartbeats 800000 in
-- Coefficient encodings and derived tensor instances require additional elaboration budget.
/-- Proper direct image preserves finite-coefficient constructible finite-Tor complexes,
its localizing closure, and arbitrary coproducts; a fibrewise cohomological-dimension bound
controls the upper endpoint of a Tor interval.

Source: literature/blueprint/slopmaster2-20261029-2300/blueprint/sec-six-functors-basics/
sk-prop-ctf-finite-proper/_section.md, node statement; Stacks Project, Tags 0GL0, 0F10,
0F12, 0F0D (blueprint: sk-prop-ctf-finite-proper).

The setting is that of sk-def-sfb-dc-setting: `k` of prime characteristic different from `ℓ`,
`X`, `Y` separated of finite type over `k`, `p` a proper `k`-morphism. No finiteness or
algebraic closedness of `k` is assumed, as in det-ctf-finite-proper-tor and
det-ctf-finite-proper-localizing.

Proof:
1. Apply `finiteProperLocalizing` (det-ctf-finite-proper-localizing) for the localizing,
   exactness, coproduct and bounded-constructibility assertions.
2. If `a > b`, testing the input Tor interval against the tensor unit makes `C` zero.
   Its direct image and every tensor test are zero, hence have every Tor interval.
3. For `a ≤ b`, choose the normalized finite-discrete encoding
   (lem-sf-finite-discrete-normalized-encoding). The interval equivalence in
   `finiteCtfInternalEtaleRealization` (lem-sfb-finite-ctf-internal-etale-realization)
   realizes `C` by an étale bounded constructible complex `K` with interval `[a,b]`.
4. By `cohomologicalDimension_eq_etaleCohomologicalDimension` (sk-def-cd), `hcd` bounds
   the étale supremum. Sectionwise prime-power torsion implies the local torsion
   convention using the maximal sieve. Nonvanishing in degree `i > d` would put
   `i.toNat` in the supremum and contradict its bound.
5. Apply the étale proper Tor theorem (det-ctf-finite-proper-tor) to `K`, after lifting
   the finite coefficient ring to its scalar universe. It gives interval `[a,b+d]`.
   The target realization equivalence preserves this interval; its natural direct-image
   comparison applies because `K` is bounded below. Compose with direct image of the
   input realization isomorphism, then use isomorphism invariance of Tor amplitude. -/
theorem properFiniteCoefficient
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))]
    [IsProper p]
    (A : Type u) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, 1 ≤ n ∧ (ℓ ^ n : ℕ) • (1 : A) = 0)
    (d : ℕ)
    (hcd : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (ybar : Spec (.of Ω) ⟶ Y),
      AlgebraicGeometry.ProEtale.cohomologicalDimension ℓ (Fact.out : Nat.Prime ℓ)
        (pullback p ybar) ≤ (d : WithTop ℕ)) :
    finiteCoefficientLocalizingProperties (finiteDiscreteCondensedCoefficient A)
        (R(AlgebraicGeometry.ProEtale.CondensedRing.lowerStar
          (finiteDiscreteCondensedCoefficient A) p)) ∧
      ∀ (C : DerivedCategory
        (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj (finiteDiscreteCondensedCoefficient A) X)))
        (a b : ℤ),
        (constantModelBoundedConstructible (finiteDiscreteCondensedCoefficient A) X C ∧
          DerivedCategory.torAmplitudeIn _ a b C) →
        constantModelBoundedConstructible (finiteDiscreteCondensedCoefficient A) Y
            ((R(AlgebraicGeometry.ProEtale.CondensedRing.lowerStar
          (finiteDiscreteCondensedCoefficient A) p)).obj C) ∧
          DerivedCategory.torAmplitudeIn _ a (b + (d : ℤ))
            ((R(AlgebraicGeometry.ProEtale.CondensedRing.lowerStar
          (finiteDiscreteCondensedCoefficient A) p)).obj C) := by
  classical
  have hf := finiteProperLocalizing ℓ (ringChar k) (Fact.out : ℓ.Prime)
    (Fact.out : (ringChar k).Prime).pos (Fact.out : ringChar k ≠ ℓ) k A hA p
  refine ⟨hf, ?_⟩
  intro C a b hC
  refine ⟨(hf.1 C ⟨hC.1, a, b, hC.2⟩).1, ?_⟩
  let F := (CondensedRing.lowerStar (finiteDiscreteCondensedCoefficient A) p).rightDerivedFunctor
  by_cases hab : a ≤ b
  · let : TopologicalSpace A := ⊥
    let : DiscreteTopology A := ⟨rfl⟩
    let : IsTopologicalRing A := by infer_instance
    change DerivedCategory.torAmplitudeIn _ a (b + (d : ℤ)) (F.obj C)
    let E (T : Scheme.{u}) := (FiniteDiscreteOrdinary.encoding_exists A T).some
    let SX : Over (Spec (.of k)) := Over.mk (X ↘ Spec (.of k))
    let SY : Over (Spec (.of k)) := Over.mk (Y ↘ Spec (.of k))
    let : LocallyOfFiniteType SX.hom := ‹LocallyOfFiniteType (X ↘ Spec (.of k))›
    let : QuasiCompact SX.hom := ‹QuasiCompact (X ↘ Spec (.of k))›
    let : IsSeparated SX.hom := ‹IsSeparated (X ↘ Spec (.of k))›
    let : LocallyOfFiniteType SY.hom := ‹LocallyOfFiniteType (Y ↘ Spec (.of k))›
    let : QuasiCompact SY.hom := ‹QuasiCompact (Y ↘ Spec (.of k))›
    let : IsSeparated SY.hom := ‹IsSeparated (Y ↘ Spec (.of k))›
    let f : SX ⟶ SY := Over.homMk p (comp_over p (Spec (.of k)))
    let : QuasiCompact f.left := inferInstanceAs (QuasiCompact p)
    let : QuasiSeparated f.left := inferInstanceAs (QuasiSeparated p)
    have hreal := FiniteDiscreteOrdinary.finiteCtfInternalEtaleRealization
      ℓ (ringChar k) k (Fact.out : (ringChar k).Prime).pos
      (Fact.out : ringChar k ≠ ℓ) A E
    obtain ⟨eX, ⟨jX⟩⟩ := hreal.1 SX a b hab
    let K := eX.inverse.obj ⟨C, hC⟩
    let j : (FiniteDiscreteOrdinary.internalEtaleRealization A X (E X)).obj K.obj ≅ C :=
      (jX.app K).symm ≪≫ (ObjectProperty.ι _).mapIso (eX.counitIso.app ⟨C, hC⟩)
    have hd : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (y : Spec (.of Ω) ⟶ Y)
        (G : Sheaf (pullback p y).smallEtaleTopology AddCommGrpCat.{u + 1}),
        (∀ (U : (pullback p y).Etale) (s : G.obj.obj (Opposite.op U)),
          ∃ n : ℕ, (ℓ ^ n) • s = 0) →
        ∀ i : ℤ, (d : ℤ) < i →
          IsZero ((Etale.cohomology AddCommGrpCat.{u + 1} (pullback p y) i).obj
            ((DerivedCategory.singleFunctor _ 0).obj G)) := by
      intro Ω _ _ y G hG i hi
      have htors : IsEllPowerTorsion ℓ (Fact.out : ℓ.Prime) G := by
        apply (ellPowerTorsion_iff_local_general _ ℓ (Fact.out : ℓ.Prime) G).mpr
        intro U s
        refine ⟨⊤, (pullback p y).smallEtaleTopology.top_mem _, ?_⟩
        intro V g _
        exact hG V ((G.obj.map g.op).hom s)
      have hbound := hcd Ω y
      rw [cohomologicalDimension_eq_etaleCohomologicalDimension] at hbound
      have heq : (i.toNat : ℤ) = i := Int.toNat_of_nonneg (by omega)
      by_contra hnz
      have hnz' : ¬ IsZero ((Etale.cohomology AddCommGrpCat.{u + 1}
          (pullback p y) (i.toNat : ℤ)).obj
          ((DerivedCategory.singleFunctor _ 0).obj G)) := by simpa only [heq] using hnz
      have hle : (i.toNat : WithTop ℕ) ≤ (d : WithTop ℕ) :=
        (show (i.toNat : WithTop ℕ) ≤
            etaleCohomologicalDimension ℓ (Fact.out : ℓ.Prime) (pullback p y) from
          le_sSup ⟨i.toNat, rfl, G, htors, hnz'⟩).trans hbound
      have hle' : i.toNat ≤ d := by exact_mod_cast hle
      omega
    have hA' : ∃ n : ℕ, 1 ≤ n ∧ (ℓ ^ n : ℕ) • (1 : ULift.{u + 1} A) = 0 := by
      obtain ⟨n, hn, hnA⟩ := hA
      refine ⟨n, hn, ?_⟩
      apply ULift.ext
      exact hnA
    have hK := Etale.isBoundedConstructible_hasTorAmplitudeIn_rightDerivedLowerStar_of_proper
      ℓ (ringChar k) (Fact.out : ℓ.Prime) (Fact.out : (ringChar k).Prime).pos
      (Fact.out : ringChar k ≠ ℓ) k p (ULift.{u + 1} A) hA' d hd a b hab
      K.obj K.property.1 K.property.2
    have hab' : a ≤ b + (d : ℤ) := by omega
    obtain ⟨eY, ⟨jY⟩⟩ := hreal.1 SY a (b + (d : ℤ)) hab'
    let L := eY.functor.obj ⟨_, hK⟩
    have hout := (DerivedCategory.torAmplitudeIn _ a (b + (d : ℤ))).prop_of_iso
      (jY.app ⟨_, hK⟩) L.property.2
    have hplus : DerivedCategory.TStructure.t.plus K.obj := by
      obtain ⟨c, e, _, hv⟩ := K.property.1.2
      exact ⟨c, (DerivedCategory.isGE_iff K.obj c).2 fun i hi ↦ hv i (Or.inl hi)⟩
    obtain ⟨ex⟩ := hreal.2 SX SY f
    let KP : DerivedCategory.Plus _ := ⟨K.obj, hplus⟩
    exact (DerivedCategory.torAmplitudeIn _ a (b + (d : ℤ))).prop_of_iso
      (ex.app KP ≪≫ F.mapIso j) hout
  · have hconc := DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn hC.2
    have := hconc.1
    have := hconc.2
    have hz : IsZero C := DerivedCategory.TStructure.t.isZero C b a (by omega)
    have hz' : IsZero (F.obj C) := F.map_isZero hz
    intro M
    have hzt := (CategoryTheory.MonoidalCategory.tensorRight
      ((DerivedCategory.singleFunctor _ 0).obj M)).map_isZero hz'
    exact ⟨DerivedCategory.TStructure.t.isGE_of_isZero hzt a,
      DerivedCategory.TStructure.t.isLE_of_isZero hzt (b + (d : ℤ))⟩

end AlgebraicGeometry.ProEtale

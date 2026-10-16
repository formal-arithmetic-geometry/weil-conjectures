/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ContinuousIntegralCoefficients
import Sheaf.Paper.ContinuousEtaleLocalLattices
import Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent
import Sheaf.AlgebraicGeometry.EtaleStratifiedFinite
import Sheaf.Paper.ContinuousLocallyFreePullback

/-! # Lattices on finitely many strata of a continuous local system

Source: Bhatt--Scholze, first paragraph of the proof of Lemma 6.8.13.
(blueprint: lem-weil-pbc-continuous-lisse-stratified-lattices)
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

private lemma locallyFree_lfp {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (hP : LocallyFree R P) : ProEtale.IsLocallyFinitelyPresented R P := by
  obtain ⟨C, hC⟩ := hP
  refine ⟨C, fun s ↦ ?_⟩
  obtain ⟨n, ⟨e⟩⟩ := hC s
  exact ⟨n, 0, 0, ⟨e ≪≫ Limits.cokernelZeroIsoTarget.symm⟩⟩

private lemma locallyFree_constructible {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (hP : LocallyFree R P) : ProEtale.IsConstructibleModuleObject R P := by
  let S : Scheme.Stratification X :=
    { n := 1
      stratum := fun _ ↦ Set.univ
      isLocallyClosed_stratum := fun _ ↦ isOpen_univ.isLocallyClosed
      isConstructible_stratum := fun _ ↦ Topology.IsConstructible.univ
      iUnion_stratum_eq_univ := Set.iUnion_const _
      pairwise_disjoint_stratum := fun i j hij ↦ (hij (Subsingleton.elim i j)).elim
      domain := fun _ ↦ X
      immersion := fun _ ↦ 𝟙 X
      range_immersion := fun _ ↦ Set.range_id' }
  exact ⟨S, fun s ↦ locallyFree_lfp (locallyFree_map (S.immersion s) hP)⟩

private structure PullbackSystem
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] where
  integral : ∀ {X Y : Scheme.{u}}, (Y ⟶ X) →
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X) ⥤
    Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) Y)
  rational : ∀ {X Y : Scheme.{u}}, (Y ⟶ X) →
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X) ⥤
    Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) Y)
  rationalIso : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X),
    rational f ≅ CondensedRing.upperStar (Profinite.continuousMapRingObj E) f
  scalar : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X),
    integral f ⋙ Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) Y) ≅
      Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X) ⋙ rational f
  comp : ∀ {X Y Z : Scheme.{u}} (f : Z ⟶ Y) (g : Y ⟶ X),
    rational (f ≫ g) ≅ rational g ⋙ rational f
  integralFree : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X)},
    LocallyFree _ M → LocallyFree _ ((integral f).obj M)
  rationalFree : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
    {P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X)},
    LocallyFree _ P → LocallyFree _ ((rational f).obj P)

private noncomputable def canonicalPullbackSystem
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] :
    PullbackSystem.{u} ℓ E where
  integral := CondensedRing.upperStar (integralCoeff ℓ E)
  rational := CondensedRing.upperStar (Profinite.continuousMapRingObj E)
  rationalIso _ := Iso.refl _
  scalar := pullIso (integralScalarMap ℓ E)
  comp f g := upperStarComp (Profinite.continuousMapRingObj E) f g
  integralFree := locallyFree_upperStar (integralCoeff ℓ E)
  rationalFree := locallyFree_upperStar (Profinite.continuousMapRingObj E)

/-- A locally finite free rational sheaf admits lisse integral lattices after a finite
stratification. Source: Bhatt--Scholze, Lemma 6.8.13, first paragraph.
(blueprint: lem-weil-pbc-continuous-lisse-stratified-lattices)

Proof in words. Proposition 6.8.4(6) supplies integral lattices on an etale cover.
Refine its members by affine opens and take a finite subcover, possible because the
base is topologically noetherian and etale maps are open. The finite disjoint union
of these affines is quasi-compact and quasi-separated; its map to the base is etale
and surjective. The local lattices assemble on that disjoint union. Stratify the
base so this cover becomes finite etale. Pull back the lattice to each resulting
cover, using the coefficient and inverse-image composition isomorphisms.
Finite etale lattice descent gives a lisse integral model on each stratum, without
requiring a descent datum on the supplied lattice. A locally finite free integral
module is locally finitely presented and hence constructible, using the singleton
stratification. On empty strata or in rank zero use the zero module. This theorem
supplies the stratum models only: reconstructing the original sheaf by extensions
is the separate integral gluing theorem. -/
theorem continuousLisse_stratified_lattices
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (hP : ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ s : C.I₀,
      Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (C.f s)).obj
        (condensedRingObj (Profinite.continuousMapRingObj E) X))
        (((ProEtale.upperStar Ab.{u + 1} (C.f s)).mapMod _).obj P)) :
    ∃ S : Scheme.Stratification X, ∀ s : Fin S.n,
      ∃ M : Mod (Sheaf (Scheme.ProEt.topology (S.domain s)) Ab.{u + 1})
          (condensedRingObj (integralCoeff ℓ E) (S.domain s)),
        ProEtale.IsConstructibleModuleObject
          (condensedRingObj (integralCoeff ℓ E) (S.domain s)) M ∧
        Nonempty ((Mod.extendScalars
          (coefficientMap (integralScalarMap ℓ E) (S.domain s))).obj M ≅
            (CondensedRing.upperStar (Profinite.continuousMapRingObj E)
              (S.immersion s)).obj P) := by
  obtain ⟨D⟩ : Nonempty (PullbackSystem.{u} ℓ E) := ⟨canonicalPullbackSystem ℓ E⟩
  obtain ⟨U, p, hp, hs, hc, hqs, M, hM, ⟨e⟩⟩ :=
    continuousLisse_etale_lattice ℓ E X P hP
  let : Etale p := hp
  let : Surjective p := hs
  let : CompactSpace U := hc
  let : QuasiSeparatedSpace U := hqs
  obtain ⟨T, _, hT⟩ := Scheme.exists_etale_stratified_finite p
  let S : Scheme.Stratification X :=
    { toStratification := T.toStratification
      domain := T.domain
      immersion := T.immersion
      isImmersion := T.isImmersion
      range_immersion := T.range_immersion }
  refine ⟨S, fun s ↦ ?_⟩
  let j := S.immersion s
  let : IsImmersion j := S.isImmersion s
  obtain ⟨V, r, q, w, hf, he, hs⟩ :
      ∃ (V : Scheme.{u}) (r : V ⟶ U) (q : V ⟶ S.domain s),
        r ≫ p = q ≫ j ∧ IsFinite q ∧ Etale q ∧ Surjective q :=
    ⟨Limits.pullback p j, Limits.pullback.fst p j, Limits.pullback.snd p j,
      Limits.pullback.condition, (hT s).1, (hT s).2, inferInstance⟩
  let : IsFinite q := hf
  let : Etale q := he
  let : Surjective q := hs
  let : TopologicalSpace.NoetherianSpace (S.domain s) :=
    j.isEmbedding.isInducing.noetherianSpace
  obtain ⟨P', hP', ⟨iP⟩⟩ : ∃ P' : Mod _
      (condensedRingObj (Profinite.continuousMapRingObj E) (S.domain s)),
      LocallyFree _ P' ∧ Nonempty
        (P' ≅ (D.rational j).obj P) :=
    ⟨_, D.rationalFree j hP, ⟨Iso.refl _⟩⟩
  obtain ⟨M', hM', ⟨iM⟩⟩ : ∃ M' : Mod _
      (condensedRingObj (integralCoeff ℓ E) V),
      LocallyFree _ M' ∧ Nonempty
        (M' ≅ (D.integral r).obj M) :=
    ⟨_, D.integralFree r hM, ⟨Iso.refl _⟩⟩
  have e' : (Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) _)).obj M' ≅
      (D.rational q).obj P' :=
    (Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) _)).mapIso iM ≪≫
      (D.scalar r).app M ≪≫
      (D.rational r).mapIso (e ≪≫ (D.rationalIso p).symm.app P) ≪≫
      (D.comp r p).symm.app P ≪≫
      eqToIso (congrArg
        (fun f ↦ (D.rational f).obj P)
        w) ≪≫
      (D.comp q j).app P ≪≫
      (D.rational q).mapIso iP.symm
  obtain ⟨N, hN, eN⟩ := continuousLisse_finiteEtale_lattice ℓ E (S.domain s) P' hP'
    q M' hM' ⟨e' ≪≫ (D.rationalIso q).app P'⟩
  exact ⟨N, locallyFree_constructible hN, ⟨eN.some ≪≫ iP ≪≫ (D.rationalIso j).app P⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartTopologicalClosure
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLocallyFreePullbackSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import all WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralGluing
import all WeilConjectures.AlgebraicGeometry.Condensed.CondensedLocallyClosedScalarExtension
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.ConstructibleSheaf.OpenClosedStratification
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence

/-! # Lisse closed-then-open extensions on a topologically Noetherian scheme

Let `t : T ⟶ V` be a closed immersion, `v : V ⟶ X` an open immersion into a topologically
Noetherian scheme, and `L` a module on `T` which on the strata of a finite locally closed
stratification of `T` is the scalar extension of a locally free module along `c : A ⟶ B`.
Then `v_! t_* L` in degree zero lies in every triangulated, isomorphism-closed property
containing the scalar extensions of the locally closed extensions of locally free
`A`-modules.

Source: Bhatt--Scholze, Lemma 6.8.13 and Proposition 6.8.14(2)
(blueprint: lem-sfb-topological-lisse-integral-closure).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- A finite locally closed stratification of `T`, for a closed immersion `t : T ⟶ V` followed
by an open immersion `v : V ⟶ X` into a topologically Noetherian scheme, extends to a
stratification of `X` each of whose strata is either disjoint from the range of `t ≫ v` or
contained in the image of a stratum of `T`.

Source: Stacks Project, Tag 09XZ
(blueprint: lem-sfb-topological-lisse-integral-closure). -/
theorem exists_stratification_disjoint_or_subset_range
    {X T V : Scheme.{u}} [TopologicalSpace.NoetherianSpace X]
    (t : T ⟶ V) (v : V ⟶ X) [IsClosedImmersion t] [IsOpenImmersion v]
    (R : T.FiniteLocallyClosedStratification) :
    ∃ S : Scheme.Stratification X, ∀ a : Fin S.n,
      Disjoint (S.stratum a) (Set.range (t ≫ v)) ∨
        ∃ i : Fin R.n, S.stratum a ⊆ Set.range (R.immersion i ≫ t ≫ v) := by
  have : TopologicalSpace.NoetherianSpace V := v.isEmbedding.isInducing.noetherianSpace
  have : TopologicalSpace.NoetherianSpace T := (t ≫ v).isEmbedding.isInducing.noetherianSpace
  let U := Scheme.openComplementOfIsClosedImmersion t
  have : TopologicalSpace.NoetherianSpace U.toScheme :=
    U.ι.isEmbedding.isInducing.noetherianSpace
  have hU : Set.range t = (Set.range U.ι)ᶜ := by
    simp [U, Scheme.openComplementOfIsClosedImmersion]
  have hv : Set.range v.closedComplement = (Set.range v)ᶜ := v.range_closedComplement
  let ST := Scheme.Stratification.ofNoetherianSpace R.n R.stratum R.isLocallyClosed_stratum
    R.iUnion_stratum_eq_univ R.pairwise_disjoint_stratum R.domain R.immersion R.isImmersion
    R.range_immersion
  let SV := Scheme.Stratification.openClosed U.ι t hU (Scheme.Stratification.trivial _) ST
  refine ⟨Scheme.Stratification.openClosed v v.closedComplement hv SV
    (Scheme.Stratification.trivial _), fun a ↦ ?_⟩
  dsimp only [Scheme.Stratification.openClosed]
  generalize finSumFinEquiv.symm a = s
  rcases s with l | l
  · dsimp only [Sum.elim_inl, SV, Scheme.Stratification.openClosed]
    generalize finSumFinEquiv.symm l = s'
    rcases s' with m | m
    · left
      rw [Set.disjoint_left]
      rintro _ ⟨_, ⟨y, -, rfl⟩, rfl⟩ ⟨z, hz⟩
      have hy : U.ι y ∈ Set.range U.ι := ⟨y, rfl⟩
      rw [← compl_compl (Set.range U.ι), ← hU] at hy
      exact hy ⟨z, v.isEmbedding.injective hz⟩
    · right
      refine ⟨m, ?_⟩
      rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      obtain ⟨w, rfl⟩ : y ∈ Set.range (R.immersion m) := by
        rw [R.range_immersion]
        exact hy
      exact ⟨w, rfl⟩
  · left
    rw [Set.disjoint_left]
    rintro _ ⟨y, -, rfl⟩ ⟨z, hz⟩
    have hy : v.closedComplement y ∈ Set.range v.closedComplement := ⟨y, rfl⟩
    rw [hv] at hy
    exact hy ⟨t z, hz⟩

/-- One step of the open-prefix filtration of `v_! t_* L`: for opens `W₀ ≤ W` whose difference
is disjoint from the range of `t ≫ v` or lies in the image of a stratum carrying a locally
free model of `L`, the corresponding graded piece lies in `P`.

Source: Bhatt--Scholze, Lemma 6.8.13
(blueprint: lem-sfb-topological-lisse-integral-closure). -/
theorem closedOpenExtension_graded_mem
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B] (c : A ⟶ B) [IsMonHom c]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (P : ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj B X))))
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    (hP : ∀ (Y : Scheme.{u}) (d : Y ⟶ X) (hd : IsImmersion d)
      (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj A Y)),
      LocallyFree (condensedRingObj A Y) M →
      P ((DerivedCategory.singleFunctor _ 0).obj
        ((Mod.extendScalars (coefficientMap c X)).obj
          ((coefficientHeartLocallyClosedExtension A d hd).obj M))))
    {T V : Scheme.{u}} (t : T ⟶ V) (v : V ⟶ X) [IsClosedImmersion t] [IsOpenImmersion v]
    (L : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj B T))
    (R : T.FiniteLocallyClosedStratification)
    (hR : ∀ i : Fin R.n, ∃ M : Mod (Sheaf (Scheme.ProEt.topology (R.domain i)) Ab.{u + 1})
        (condensedRingObj A (R.domain i)),
      LocallyFree (condensedRingObj A (R.domain i)) M ∧
      Nonempty ((Mod.extendScalars (coefficientMap c (R.domain i))).obj M ≅
        (upperStar B (R.immersion i)).obj L))
    (W₀ W : X.Opens) (h : W₀ ≤ W)
    (hcase : Disjoint ((W : Set X) \ W₀) (Set.range (t ≫ v)) ∨
      ∃ i : Fin R.n, (W : Set X) \ W₀ ⊆ Set.range (R.immersion i ≫ t ≫ v)) :
    P ((DerivedCategory.singleFunctor _ 0).obj
      ((W.ι)_!open⟦B⟧.obj (cokernel
        ((openImmersionLowerShriekUpperStarAdjunction B (X.homOfLE h)).counit.app
          ((W.ι)^*⟦B⟧.obj ((v)_!open⟦B⟧.obj ((t)_*⟦B⟧.obj L))))))) := by
  have : TopologicalSpace.NoetherianSpace W₀.toScheme :=
    W₀.ι.isEmbedding.isInducing.noetherianSpace
  have : TopologicalSpace.NoetherianSpace W.toScheme :=
    W.ι.isEmbedding.isInducing.noetherianSpace
  obtain ⟨Z, k, hk, hred, hcompl, hr⟩ := closed_difference_data X W₀ W h
  let := hk
  let := hred
  let F := (v)_!open⟦B⟧.obj ((t)_*⟦B⟧.obj L)
  let G := cokernel ((openImmersionLowerShriekUpperStarAdjunction B (X.homOfLE h)).counit.app
    ((W.ι)^*⟦B⟧.obj F))
  have hunit := supported_unit B k (X.homOfLE h) hcompl G
    (open_cokernel_zero B (X.homOfLE h) _)
  let e₀ : (W.ι)_!open⟦B⟧.obj G ≅
      (W.ι)_!open⟦B⟧.obj ((k)_*⟦B⟧.obj ((k ≫ W.ι)^*⟦B⟧.obj F)) :=
    (W.ι)_!open⟦B⟧.mapIso (asIso ((upperStarLowerStarAdjunction B k).unit.app G) ≪≫
      (k)_*⟦B⟧.mapIso ((closed_cokernel_iso B k (X.homOfLE h) hcompl _).symm ≪≫
        ((upperStarComp B k W.ι).app F).symm))
  refine P.prop_of_iso ((DerivedCategory.singleFunctor _ 0).mapIso e₀).symm ?_
  rcases hcase with hd | ⟨i, hi⟩
  · have hz := isZero_upperStar_openImmersionLowerShriek_lowerStar_of_disjoint B t v
      (k ≫ W.ι) (hd.mono_left hr) L
    exact P.prop_of_isZero ((DerivedCategory.singleFunctor _ 0).map_isZero
      ((W.ι)_!open⟦B⟧.map_isZero ((k)_*⟦B⟧.map_isZero hz)))
  · have := R.isImmersion i
    obtain ⟨g, hg⟩ := immersion_factor_of_reduced (R.immersion i ≫ t ≫ v) (k ≫ W.ι)
      (hr.trans hi)
    obtain ⟨M, hM, ⟨eM⟩⟩ := hR i
    obtain ⟨eL⟩ :=
      nonempty_upperStar_openImmersionLowerShriek_lowerStar_iso B t v (t ≫ v) rfl L
    let N := (g)^*⟦A⟧.obj M
    have hN : LocallyFree (condensedRingObj A Z) N := locallyFree_upperStar A g hM
    let e₁ : (k ≫ W.ι)^*⟦B⟧.obj F ≅ (Mod.extendScalars (coefficientMap c Z)).obj N :=
      (upperStarCongr B hg.symm).app F ≪≫
        (upperStarComp B g (R.immersion i ≫ t ≫ v)).app F ≪≫
        (g)^*⟦B⟧.mapIso ((upperStarComp B (R.immersion i) (t ≫ v)).app F ≪≫
          (R.immersion i)^*⟦B⟧.mapIso eL ≪≫ eM.symm) ≪≫ ((pullIso c g).app M).symm
    have := closed_scalar_iso c (X.homOfLE h) k hcompl N
    let e₂ : (W.ι)_!open⟦B⟧.obj
          ((k)_*⟦B⟧.obj ((Mod.extendScalars (coefficientMap c Z)).obj N)) ≅
        (Mod.extendScalars (coefficientMap c X)).obj
          ((W.ι)_!open⟦A⟧.obj ((k)_*⟦A⟧.obj N)) :=
      (W.ι)_!open⟦B⟧.mapIso (asIso ((pushHom c k).app N)).symm ≪≫
        ((openImmersionShriekIso c W.ι).app ((k)_*⟦A⟧.obj N)).symm
    obtain ⟨e₃⟩ :=
      nonempty_openImmersionLowerShriek_lowerStar_iso_coefficientHeartLocallyClosedExtension A
        (k ≫ W.ι) k W.ι rfl N
    exact P.prop_of_iso ((DerivedCategory.singleFunctor _ 0).mapIso
      ((W.ι)_!open⟦B⟧.mapIso ((k)_*⟦B⟧.mapIso e₁) ≪≫ e₂ ≪≫
        (Mod.extendScalars (coefficientMap c X)).mapIso e₃)).symm
      (hP Z (k ≫ W.ι) inferInstance N hN)

/-- A module `L` over `B_T` has *stratified lattice models* along `c : A ⟶ B` if on the strata
of some finite locally closed stratification of `T` it is the scalar extension of a locally
free `A`-module.

Source: Bhatt--Scholze, Lemma 6.8.13, first paragraph
(blueprint: lem-sfb-topological-lisse-integral-closure). -/
def StratifiedLatticeModels
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B] (c : A ⟶ B) [IsMonHom c]
    {T : Scheme.{u}}
    (L : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj B T)) : Prop :=
  ∃ R : T.FiniteLocallyClosedStratification, ∀ i : Fin R.n,
    ∃ M : Mod (Sheaf (Scheme.ProEt.topology (R.domain i)) Ab.{u + 1})
        (condensedRingObj A (R.domain i)),
      LocallyFree (condensedRingObj A (R.domain i)) M ∧
      Nonempty ((Mod.extendScalars (coefficientMap c (R.domain i))).obj M ≅
        (upperStar B (R.immersion i)).obj L)

/-- A module `L` on `T` with stratified lattice models along `c : A ⟶ B` has its
closed-then-open extension by zero `v_! t_* L` (in degree zero) in every triangulated,
isomorphism-closed property containing the scalar extensions of locally closed extensions of
locally free `A`-modules, provided `X` is topologically Noetherian.

Source: Bhatt--Scholze, Lemma 6.8.13 and Proposition 6.8.14(2)
(blueprint: lem-sfb-topological-lisse-integral-closure).

Proof. Extend the stratification of `T` to a stratification of `X` whose strata are disjoint
from `t ≫ v` or lie in a stratum of `T`. Noetherian induction gives a finite chain of opens
whose successive differences lie in single strata, and the open-prefix filtration of
`v_! t_* L` along it has graded pieces `W_! k_* k^*(v_! t_* L)` for the reduced closed
complement `k`. These vanish on the first kind of strata; on the second they are scalar
extensions of locally closed extensions of pulled-back locally free models. -/
theorem closedOpenExtension_mem_of_stratifiedLatticeModels
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B] (c : A ⟶ B) [IsMonHom c]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (P : ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj B X))))
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    (hP : ∀ (Y : Scheme.{u}) (d : Y ⟶ X) (hd : IsImmersion d)
      (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj A Y)),
      LocallyFree (condensedRingObj A Y) M →
      P ((DerivedCategory.singleFunctor _ 0).obj
        ((Mod.extendScalars (coefficientMap c X)).obj
          ((coefficientHeartLocallyClosedExtension A d hd).obj M))))
    {T V : Scheme.{u}} (t : T ⟶ V) (v : V ⟶ X) [IsClosedImmersion t] [IsOpenImmersion v]
    (L : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj B T))
    (hL : StratifiedLatticeModels A B c L) :
    P ((DerivedCategory.singleFunctor _ 0).obj ((v)_!open⟦B⟧.obj ((t)_*⟦B⟧.obj L))) := by
  obtain ⟨R, hR⟩ := hL
  obtain ⟨S, hS⟩ := exists_stratification_disjoint_or_subset_range t v R
  refine stratification_mem B X _ S P fun W₀ W h a hs ↦ ?_
  refine closedOpenExtension_graded_mem A B c X P hP t v L R hR W₀ W h ?_
  rcases hS a with hd | ⟨i, hi⟩
  · exact Or.inl (hd.mono_left hs)
  · exact Or.inr ⟨i, hs.trans hi⟩

end AlgebraicGeometry.ProEtale.CondensedRing

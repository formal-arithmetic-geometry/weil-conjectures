/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import WeilConjectures.SixFunctors.ProEtale.Derived.ClopenIdempotent
public import WeilConjectures.SixFunctors.ProEtale.ExceptionalAdjoint

/-!
# The ambient exceptional right adjoint fails for an elliptic curve

Blueprint `sk-rem-sf-fullcd-scope`: the ambient exceptional right adjoint datum
`AlgebraicGeometry.ProEtale.HasAmbientExceptionalRightAdjoint` of `sk-def-sf-admissible` (1) is
*false in general*, already for the structure morphism `a_E : E ⟶ Spec k` of an elliptic curve
over an algebraically closed field `k`.

Let `r` be a prime invertible in `k`, `T = Spec k(E)^sep` the pro-étale geometric generic point of
`E` and `G = Gal(k(E)^sep / k(E))`. The multiplication covers `[r^m] : E ⟶ E` give a surjection
`χ : G ↠ T_r E ≅ ℤ_r² ↠ ℤ_r`, and inside the pro-`r` part of a procyclic subgroup one finds an
abstract subgroup `H ≅ ⊕_ℕ ℤ` on which `χ` is injective. Evaluation at `T` is an exact
cocontinuous functor `U_H` to `Λ[H]`-modules whose right adjoint `V_H` is exact, and
`F = V_H(Λ)` has `Hⁿ(E_proét, F) ≅ Hⁿ(H, Λ) ≠ 0` for all `n ≥ 1`. Consequently:

* (i) `FullCD(a_E, Λ; c)` fails for every `c`
  (`AlgebraicGeometry.ProEtale.not_hasUniformCohomologicalDimensionLE_of_isAbelianVariety`), so
  clause (1) of `sk-def-sf-admissible` fails
  (`AlgebraicGeometry.ProEtale.not_hasAmbientExceptionalRightAdjoint_of_isAbelianVariety`);
* (ii) `Ra_{E!} = Ra_{E*}` does not preserve countable coproducts and has no right adjoint on
  `D(E_proét, Λ)`
  (`AlgebraicGeometry.ProEtale.not_isLeftAdjoint_rightDerivedLowerShriek_of_isAbelianVariety`);
* (iii) nor on `D⁺(E_proét, Λ)`
  (`AlgebraicGeometry.ProEtale.not_isLeftAdjoint_rightDerivedLowerShriekPlus_of_isAbelianVariety`).

The sheaf `F` is not of étale origin. On the étale-origin class the exceptional adjoint is the
unconditional constructible `Rf^!` of `sk-def-sf-operations` (vi), which is the only exceptional
functor used downstream (`AlgebraicGeometry.ProEtale.rightDerivedUpperShriek`).

Blueprint `open-sf-ambient-adjoint-input` records the same failure: the exceptional right adjoint
of `Rf_!` on unbounded (or bounded below) pro-étale complexes does not exist in general.

## Implementation notes

The construction works for abelian varieties of any positive dimension `g`, since then
`T_r A ≅ ℤ_r^{2g}` surjects onto `ℤ_r`; elliptic curves are the case `IsAbelianVariety.dim E = 1`.
The statements are made in that generality.

The chosen compactification of the proper morphism `a_E` need not be the trivial one; it is
`E ⟶ Z ⟶ Spec k` with `E` clopen in `Z`. Two general facts transport the failure to it:
`AlgebraicGeometry.ProEtale.HasUniformCohomologicalDimensionLE.comp_of_isOpenImmersion`
(restricting `FullCD` to a clopen piece) and
`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekIsoOfIsProper` (`Rf_! ≅ Rf_*` for proper `f`).

## Main statements

- `AlgebraicGeometry.ProEtale.exists_forall_not_isZero_homology_rightDerivedLowerStar`: the sheaf
  with nonvanishing pro-étale cohomology in every positive degree.
- `AlgebraicGeometry.ProEtale.not_hasAmbientExceptionalRightAdjoint_of_isAbelianVariety`.
- `AlgebraicGeometry.ProEtale.not_isLeftAdjoint_rightDerivedLowerShriek_of_isAbelianVariety`.
- `AlgebraicGeometry.ProEtale.not_isLeftAdjoint_rightDerivedLowerShriekPlus_of_isAbelianVariety`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

namespace ProEtale

section General

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {X Y Z : Scheme.{u}}

/-- For a proper morphism `f` admitting a compactification, the pro-étale `Rf_!` is the right
derived pushforward `Rf_*`. Write `Rf_! = D(i_!) ⋙ Rg_*` for the chosen compactification
`X ⟶[i] Z ⟶[g] Y`. As `f` is proper, `i` has closed range, so `i_! ≅ i_*`
(`AlgebraicGeometry.ProEtale.isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range`) and
`i_!` preserves K-injective complexes; hence `Rf_! ≅ R(i_! ⋙ g_*)`, and `i_! ⋙ g_* ≅ f_*`
(`AlgebraicGeometry.ProEtale.isIso_lowerShriekToLowerStar`). -/
noncomputable def rightDerivedLowerShriekIsoOfIsProper (f : X ⟶ Y) [IsProper f]
    [HasCompactification f] :
    rightDerivedLowerShriek A f ≅ ((f)_*[A]).rightDerivedFunctor := by
  let c := HasCompactification.compactification f
  have : IsIso (openImmersionLowerShriekToLowerStar A c.i) :=
    isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range A c.i
      (c.isClopen_range_openImmersion inferInstance).isClosed
  have : ((c.i)_*[A]).PreservesKInjectiveComplexes :=
    (upperStarLowerStarAdjunction A c.i).preservesKInjectiveComplexes
  have : ((c.i)_!open[A]).PreservesKInjectiveComplexes :=
    Functor.preservesKInjectiveComplexes_of_iso
      (asIso (openImmersionLowerShriekToLowerStar A c.i)).symm
  exact Functor.isoWhiskerRight
      ((c.i)_!open[A]).rightDerivedFunctorIsoMapDerivedCategory.symm _ ≪≫
    (Functor.rightDerivedFunctorCompIso _ _).symm ≪≫
    Functor.rightDerivedFunctorNatIso (asIso (lowerShriekToLowerStar A f))

/-- The cohomology of the derived pushforward along `i ≫ g`, for an open immersion `i` with
closed range, of a sheaf `F` is the cohomology of the derived pushforward along `g` of the
extension by zero `i_! F`: `Ri_* ≅ D(i_!)` is exact, and `R(i ≫ g)_* ≅ Ri_* ⋙ Rg_*`. -/
noncomputable def homologyRightDerivedLowerStarCompIso (i : X ⟶ Z) [IsOpenImmersion i]
    (hi : IsClosed (Set.range i.base)) (g : Z ⟶ Y) (F : Sheaf (Scheme.ProEt.topology X) A)
    (r : ℤ) :
    (DerivedCategory.homologyFunctor _ r).obj
        ((R((i ≫ g)_*[A])).obj ((DerivedCategory.singleFunctor _ 0).obj F)) ≅
      (DerivedCategory.homologyFunctor _ r).obj
        ((R((g)_*[A])).obj ((DerivedCategory.singleFunctor _ 0).obj ((i)_!open[A].obj F))) :=
  have : ((i)_*[A]).PreservesKInjectiveComplexes :=
    (upperStarLowerStarAdjunction A i).preservesKInjectiveComplexes
  (DerivedCategory.homologyFunctor _ r).mapIso
    ((Functor.rightDerivedFunctorCompIso' _ _ (lowerStarComp A i g)).symm.app _ ≪≫
      (R((g)_*[A])).mapIso ((rightDerivedLowerStarIsoOfIsClosedRange A i hi).app _ ≪≫
        (((i)_!open[A]).mapDerivedCategorySingleFunctor 0).app F))

/-- `FullCD` restricts to clopen pieces: if `g : Z ⟶ Y` has uniform cohomological dimension at
most `c` at `A` and `i : X ⟶ Z` is a proper open immersion (so `X` is clopen in `Z`), then so
has `i ≫ g`. A base change `X' ⟶ V` of `i ≫ g` factors through the base change `Z' ⟶ V` of `g`
by a proper open immersion `i'`, and a sheaf `F` on `X'` has the same derived pushforward as its
extension by zero `i'_! F` on `Z'`
(`AlgebraicGeometry.ProEtale.homologyRightDerivedLowerStarCompIso`). -/
theorem HasUniformCohomologicalDimensionLE.comp_of_isOpenImmersion {i : X ⟶ Z}
    [IsOpenImmersion i] [IsProper i] {g : Z ⟶ Y} {c : ℕ}
    (h : HasUniformCohomologicalDimensionLE A g c) :
    HasUniformCohomologicalDimensionLE A (i ≫ g) c := by
  intro V X' g' p' sq F r hr
  let i' : X' ⟶ pullback g V.hom := pullback.lift (g' ≫ i) p' (by rw [Category.assoc, sq.w])
  have hp' : p' = i' ≫ pullback.snd g V.hom := (pullback.lift_snd _ _ _).symm
  have sq₁ : IsPullback g' i' i (pullback.fst g V.hom) :=
    IsPullback.of_bot (hp' ▸ sq) (pullback.lift_fst _ _ _).symm
      (IsPullback.of_hasPullback g V.hom)
  have : IsOpenImmersion i' := MorphismProperty.of_isPullback sq₁ inferInstance
  have : IsProper i' := MorphismProperty.of_isPullback sq₁ inferInstance
  rw [hp']
  exact (h V (pullback.fst g V.hom) (pullback.snd g V.hom) (IsPullback.of_hasPullback g V.hom)
    _ r hr).of_iso (homologyRightDerivedLowerStarCompIso A i'
      (Scheme.Hom.isClopen_range i').isClosed _ F r)

/-- `FullCD` for the proper part of any compactification of a proper morphism `f` implies
`FullCD` for `f` itself: the open immersion of the compactification is proper, so
`AlgebraicGeometry.ProEtale.HasUniformCohomologicalDimensionLE.comp_of_isOpenImmersion`
applies. -/
theorem HasUniformCohomologicalDimensionLE.of_compactification {f : X ⟶ Y} [IsProper f]
    (cf : Compactification f) {c : ℕ} (h : HasUniformCohomologicalDimensionLE A cf.g c) :
    HasUniformCohomologicalDimensionLE A f c := by
  have := cf.isProper_openImmersion inferInstance
  rw [cf.comm]
  exact h.comp_of_isOpenImmersion A

end General

section AbelianVariety

variable (Λ : Type (u + 1)) [Field Λ] {k : Type u} [Field k] [IsAlgClosed k]
  (E : Over (Spec (.of k))) [GrpObj E] [IsAbelianVariety E]

/-- Blueprint `sk-rem-sf-fullcd-scope`, the counterexample sheaf: for an elliptic curve (more
generally an abelian variety of positive dimension) `E` over an algebraically closed field `k`
and a field `Λ`, there is a pro-étale sheaf `F` of `Λ`-modules on `E` whose pro-étale cohomology
`Hⁿ(E_proét, F) = Hⁿ(Ra_{E*} F)` is nonzero in every degree `n ≥ 1`.

The sheaf is `F = V_H(Λ)`, for `V_H` the right adjoint of evaluation at the pro-étale geometric
generic point `T = Spec k(E)^sep`, viewed as a functor to modules over the group ring of an
abstract subgroup `H ≅ ⊕_ℕ ℤ` of `Gal(k(E)^sep / k(E))` acting freely on `Hom_E(T, W)` for every
affine weakly contractible `W`; then `Hⁿ(E_proét, F) ≅ Hⁿ(H, Λ) ≠ 0`. -/
theorem exists_forall_not_isZero_homology_rightDerivedLowerStar
    (hE : 0 < IsAbelianVariety.dim E) :
    ∃ F : Sheaf (Scheme.ProEt.topology E.left) (ModuleCat.{u + 1} Λ), ∀ n : ℤ, 0 < n →
      ¬ IsZero ((DerivedCategory.homologyFunctor _ n).obj
        ((R((E.hom)_*[ModuleCat.{u + 1} Λ])).obj
          ((DerivedCategory.singleFunctor _ 0).obj F))) :=
  sorry

/-- Blueprint `sk-rem-sf-fullcd-scope` (i): for the structure morphism `a_E` of an elliptic
curve (more generally an abelian variety of positive dimension) over an algebraically closed
field, `FullCD(a_E, Λ; c)` fails for every `c`. The base change along the terminal object of
`(Spec k)_proét` already violates it, by
`AlgebraicGeometry.ProEtale.exists_forall_not_isZero_homology_rightDerivedLowerStar`. -/
theorem not_hasUniformCohomologicalDimensionLE_of_isAbelianVariety
    (hE : 0 < IsAbelianVariety.dim E) (c : ℕ) :
    ¬ HasUniformCohomologicalDimensionLE (ModuleCat.{u + 1} Λ) E.hom c := by
  intro h
  obtain ⟨F, hF⟩ := exists_forall_not_isZero_homology_rightDerivedLowerStar Λ E hE
  exact hF (c + 1) (by omega) (h (Scheme.ProEt.mk (𝟙 _)) (𝟙 _) E.hom
    (IsPullback.id_horiz E.hom) F (c + 1) (by omega))

/-- Blueprint `sk-rem-sf-fullcd-scope` (i): clause (1) of `sk-def-sf-admissible`, the ambient
exceptional right adjoint datum, fails for the smooth proper structure morphism of an elliptic
curve (more generally an abelian variety of positive dimension) over an algebraically closed
field, whatever compactification is chosen. -/
theorem not_hasAmbientExceptionalRightAdjoint_of_isAbelianVariety
    (hE : 0 < IsAbelianVariety.dim E) :
    ¬ HasAmbientExceptionalRightAdjoint (ModuleCat.{u + 1} Λ) E.hom := fun h ↦
  have ⟨c, hc⟩ := h.exists_hasUniformCohomologicalDimensionLE
  not_hasUniformCohomologicalDimensionLE_of_isAbelianVariety Λ E hE c
    (hc.of_compactification _ _)

/-- Blueprint `sk-rem-sf-fullcd-scope` (ii), `open-sf-ambient-adjoint-input`: for the structure
morphism `a_E` of an elliptic curve (more generally an abelian variety of positive dimension)
over an algebraically closed field, `Ra_{E*}` does not preserve countable coproducts on
`D(E_proét, Λ)`.

With `F` the sheaf of
`AlgebraicGeometry.ProEtale.exists_forall_not_isZero_homology_rightDerivedLowerStar` and
`Kₙ = F[n]`, countable products and coproducts of pro-étale sheaves are exact, so
`⊕ Kₙ ≅ ∏ Kₙ`, while in degree `0` the coproduct comparison for `Ra_{E*}` is the non-surjective
map `⊕_{n ≥ 1} Hⁿ(E, F) ⟶ ∏_{n ≥ 1} Hⁿ(E, F)`. -/
theorem not_preservesColimitsOfShape_rightDerivedLowerStar_of_isAbelianVariety
    (hE : 0 < IsAbelianVariety.dim E) :
    ¬ PreservesColimitsOfShape (Discrete ℕ) (R((E.hom)_*[ModuleCat.{u + 1} Λ])) :=
  sorry

/-- Blueprint `sk-rem-sf-fullcd-scope` (ii), `open-sf-ambient-adjoint-input`: for the structure
morphism `a_E` of an elliptic curve (more generally an abelian variety of positive dimension)
over an algebraically closed field, `Ra_{E!}` has no right adjoint on `D(E_proét, Λ)`. Indeed
`Ra_{E!} ≅ Ra_{E*}` (`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekIsoOfIsProper`) does not
preserve countable coproducts
(`not_preservesColimitsOfShape_rightDerivedLowerStar_of_isAbelianVariety`),
whereas left adjoints preserve all colimits. -/
theorem not_isLeftAdjoint_rightDerivedLowerShriek_of_isAbelianVariety
    (hE : 0 < IsAbelianVariety.dim E) :
    ¬ (R(E.hom)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint := fun _ ↦
  not_preservesColimitsOfShape_rightDerivedLowerStar_of_isAbelianVariety Λ E hE
    (preservesColimitsOfShape_of_natIso
      (rightDerivedLowerShriekIsoOfIsProper (ModuleCat.{u + 1} Λ) E.hom))

/-- Blueprint `sk-rem-sf-fullcd-scope` (iii), `open-sf-ambient-adjoint-input`: for the structure
morphism `a_E` of an elliptic curve (more generally an abelian variety of positive dimension)
over an algebraically closed field, `Ra_{E!}` has no right adjoint on the bounded below derived
category `D⁺(E_proét, Λ)` either.

Let `F` be the sheaf of
`AlgebraicGeometry.ProEtale.exists_forall_not_isZero_homology_rightDerivedLowerStar` and `I` an
injective coseparator of the pro-étale sheaves on `Spec k`. As `Ra_{E!} ≅ Ra_{E*}`
(`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekIsoOfIsProper`), `H⁰(Ra_{E!}(F[n])) =
Hⁿ(E_proét, F) ≠ 0`, so `Hom(Ra_{E!}(F[n]), I) ≠ 0` for every `n ≥ 1`
(`DerivedCategory.exists_ne_zero_hom_singleFunctor_obj`). A right adjoint `G` on `D⁺` would
give `Hom(F[n], G(I)) ≠ 0` for all `n ≥ 1`, whereas `G(I)` is bounded below, so these groups
vanish for `n` large by `t`-structure orthogonality. -/
theorem not_isLeftAdjoint_rightDerivedLowerShriekPlus_of_isAbelianVariety
    (hE : 0 < IsAbelianVariety.dim E) :
    ¬ (R(E.hom)_![ModuleCat.{u + 1} Λ]+).IsLeftAdjoint := by
  intro hL
  let adj := Adjunction.ofIsLeftAdjoint (R(E.hom)_![ModuleCat.{u + 1} Λ]+)
  obtain ⟨F, hF⟩ := exists_forall_not_isZero_homology_rightDerivedLowerStar Λ E hE
  obtain ⟨I, _, hI⟩ := Abelian.has_injective_coseparator
    (separator (Sheaf (Scheme.ProEt.topology (Spec (.of k))) (ModuleCat.{u + 1} Λ)))
    (isSeparator_separator _)
  let IP : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology (Spec (.of k)))
      (ModuleCat.{u + 1} Λ)) := ⟨(DerivedCategory.singleFunctor _ 0).obj I, ⟨0, inferInstance⟩⟩
  obtain ⟨a, ha⟩ := ((R(E.hom)_![ModuleCat.{u + 1} Λ]+).rightAdjoint.obj IP).property
  let n : ℕ := (-a).toNat + 1
  have hn : -(n : ℤ) < a := by have := Int.self_le_toNat (-a); simp only [n]; push_cast; omega
  let K := ((DerivedCategory.singleFunctor
    (Sheaf (Scheme.ProEt.topology E.left) (ModuleCat.{u + 1} Λ)) 0).obj F)⟦(n : ℤ)⟧
  have : DerivedCategory.TStructure.t.IsLE K (-n) :=
    DerivedCategory.TStructure.t.isLE_shift _ 0 n (-n)
  have : DerivedCategory.TStructure.t.IsGE K (-n) :=
    DerivedCategory.TStructure.t.isGE_shift _ 0 n (-n)
  let KP : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology E.left) (ModuleCat.{u + 1} Λ)) :=
    ⟨K, ⟨-n, inferInstance⟩⟩
  -- every morphism `Ra_{E!}(F[n]) ⟶ I` vanishes
  have hzero (φ : (R(E.hom)_![ModuleCat.{u + 1} Λ]+).obj KP ⟶ IP) : φ = 0 := by
    have h : adj.homEquiv _ _ φ = 0 := (ObjectProperty.fullyFaithfulι _).map_injective
      (DerivedCategory.TStructure.t.zero_of_isLE_of_isGE _ (-n) a hn ‹_› ha)
    rw [← (adj.homEquiv _ _).symm_apply_apply φ, h, Adjunction.homEquiv_counit,
      Functor.map_zero, Limits.zero_comp]
  -- but `H⁰(Ra_{E!}(F[n])) ≅ Hⁿ(Ra_{E*} F) ≠ 0`
  let e : (DerivedCategory.Plus.ι.obj ((R(E.hom)_![ModuleCat.{u + 1} Λ]+).obj KP)) ≅
      ((R((E.hom)_*[ModuleCat.{u + 1} Λ])).obj
        ((DerivedCategory.singleFunctor _ 0).obj F))⟦(n : ℤ)⟧ :=
    (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} Λ) E.hom).app KP ≪≫
      (rightDerivedLowerShriekIsoOfIsProper (ModuleCat.{u + 1} Λ) E.hom).app K ≪≫
      ((R((E.hom)_*[ModuleCat.{u + 1} Λ])).commShiftIso (n : ℤ)).app _
  have hK : ¬ IsZero ((DerivedCategory.homologyFunctor _ 0).obj
      (DerivedCategory.Plus.ι.obj ((R(E.hom)_![ModuleCat.{u + 1} Λ]+).obj KP))) := fun h ↦
    hF n (by omega) (h.of_iso ((DerivedCategory.homologyFunctor _ 0).mapIso e ≪≫
      ((DerivedCategory.homologyFunctor _ 0).shiftIso (n : ℤ) 0 n (by simp)).app _).symm)
  obtain ⟨φ, hφ⟩ := DerivedCategory.exists_ne_zero_hom_singleFunctor_obj _ hI hK
  have := congrArg DerivedCategory.Plus.ι.map
    (hzero ((ObjectProperty.fullyFaithfulι _).preimage φ))
  exact hφ (by simpa using this)

end AbelianVariety

end ProEtale

end AlgebraicGeometry

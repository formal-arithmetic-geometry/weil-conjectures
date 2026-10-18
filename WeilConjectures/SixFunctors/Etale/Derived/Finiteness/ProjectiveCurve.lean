/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.GeometricFibreRank
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.BoundedConstructible
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Curve.GenericModel
import WeilConjectures.AlgebraicGeometry.InvertibleExponentBase
import WeilConjectures.ConstructibleSheaf.FiniteMorphism
import WeilConjectures.ConstructibleSheaf.IntegralGenericCriterion
import WeilConjectures.ConstructibleSheaf.Noetherian
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstantCoefficients
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImageSigma
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteComparison
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Constant coefficients on projective families of curves

Let `f : X ⟶ S` be a projective morphism of finite-type schemes over a field whose geometric
fibres have dimension at most one. The higher direct images `Rᵠf_* M` of a constant sheaf with
finite value `M` of order invertible on `S` are constructible. This is the curve case of the
constructibility of proper direct images (`thm-fin-projective-line-constructible`).

The case of a smooth projective family of curves comes first: there the stalks of `Rᵠf_* 𝔽_ℓ`
are the cohomology groups of the geometric fibres, whose cardinalities `ℓ^c`, `ℓ^{2g}`, `ℓ^c`
are constructible functions of the base point by coherent base change
(`lem-fin-projective-curve-betti-cardinalities`, `thm-fin-projective-smooth-curve-finiteness`).
The general case is reduced to it by a generic curve model
(`lem-fin-generic-curve-model`), Noetherian induction and a filtration of `M`
(`thm-fin-projective-curve-constant`, `cor-fin-projective-curve-finite-group`).

## Main statements

- `AlgebraicGeometry.Etale.natCard_sheafH_constantZMod_geometricFibre`
- `AlgebraicGeometry.Etale.isConstructibleSheaf_homology_rightDerivedLowerStar_of_smooth`
- `AlgebraicGeometry.Etale.exists_isConstructibleSheaf_upperStar_rightDerivedLowerStar_zmod`
- `AlgebraicGeometry.Etale.isConstructibleSheaf_homology_rightDerivedLowerStar_zmod`
- `AlgebraicGeometry.Etale.isConstructibleSheaf_homology_rightDerivedLowerStar_constantSheaf`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {X S : Scheme.{u}}

/-- Blueprint `lem-fin-projective-curve-betti-cardinalities`: Betti cardinalities in a smooth
projective curve family.

Let `S` be Noetherian, `f : X ⟶ S` smooth of relative dimension one and projective
(`f = π ∘ i` for a closed immersion `i : X ⟶ ℙ(n; S)`), and `ℓ` a prime invertible on `S`. For a
point `s` of `S` let `X_{s̄} = X ×_S Spec κ(s)‾` be the geometric fibre, `c_s` the number of its
connected components and `g_s = dim H¹(X_{s̄}, 𝒪)` its arithmetic genus, which is the sum of the
genera of its connected components (each an integral smooth proper curve). Then
`|H⁰(X_{s̄}, 𝔽_ℓ)| = |H²(X_{s̄}, 𝔽_ℓ)| = ℓ^{c_s}`, `|H¹(X_{s̄}, 𝔽_ℓ)| = ℓ^{2 g_s}` and
`|Hʳ(X_{s̄}, 𝔽_ℓ)| = 1` for `r > 2`, and `c` and `g` are constructible functions on `S`: they
take finitely many values, each on a constructible subset. -/
theorem natCard_sheafH_constantZMod_geometricFibre [IsNoetherian S] (f : X ⟶ S)
    [SmoothOfRelativeDimension 1 f] {n : Type u} [Finite n] (i : X ⟶ ℙ(n; S))
    [IsClosedImmersion i] (hi : i ≫ ℙ(n; S) ↘ S = f) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : IsUnit (ℓ : Γ(S, ⊤))) :
    let Xs : S → Scheme.{u} := fun s ↦ Limits.pullback f (S.geometricPointAt s)
    let c : S → ℕ := fun s ↦ Nat.card (_root_.ConnectedComponents (Xs s))
    let g : S → ℕ := fun s ↦
      letI : (Xs s).Over (Spec (.of (AlgebraicClosure (S.residueField s)))) :=
        ⟨pullback.snd f (S.geometricPointAt s)⟩
      arithmeticGenus (AlgebraicClosure (S.residueField s)) (Xs s)
    (∀ s : S,
      Nat.card (Sheaf.H ((Xs s).constantZMod ℓ) 0) = ℓ ^ c s ∧
      Nat.card (Sheaf.H ((Xs s).constantZMod ℓ) 1) = ℓ ^ (2 * g s) ∧
      Nat.card (Sheaf.H ((Xs s).constantZMod ℓ) 2) = ℓ ^ c s ∧
      ∀ r, 2 < r → Nat.card (Sheaf.H ((Xs s).constantZMod ℓ) r) = 1) ∧
    ((Set.range c).Finite ∧ ∀ m : ℕ, Topology.IsConstructible (c ⁻¹' {m})) ∧
    ((Set.range g).Finite ∧ ∀ m : ℕ, Topology.IsConstructible (g ⁻¹' {m})) := by
  sorry

/-- Blueprint `thm-fin-projective-smooth-curve-finiteness`: Constant-coefficient finiteness for
projective smooth curves.

Let `S` be Noetherian, `f : X ⟶ S` projective and smooth of relative dimension one, and `ℓ` a
prime invertible on `S`. Every higher direct image `Rʳf_* 𝔽_ℓ` is constructible. -/
theorem isConstructibleSheaf_homology_rightDerivedLowerStar_of_smooth [IsNoetherian S]
    (f : X ⟶ S) [SmoothOfRelativeDimension 1 f] {n : Type u} [Finite n] (i : X ⟶ ℙ(n; S))
    [IsClosedImmersion i] (hi : i ≫ ℙ(n; S) ↘ S = f) (ℓ : ℕ) [Fact ℓ.Prime]
    [HasInvertibleExponent (ULift.{u + 1} (ZMod ℓ)) S] (r : ℤ) :
    IsConstructibleSheaf ((_root_.DerivedCategory.homologyFunctor _ r).obj
      ((R((f)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
            (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ))))))) := by
  sorry

variable {k : Type u} [Field k]

/-- `IsConstructibleSheaf.of_iso` with the constructibility hypothesis as an explicit argument. -/
private lemma isConstructibleSheaf_of_iso {Y : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    {F F' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (e : F ≅ F')
    (h : IsConstructibleSheaf F) : IsConstructibleSheaf F' :=
  IsConstructibleSheaf.of_iso e

/-- The generic case of `thm-fin-projective-curve-constant`, the dense-open assertion of its
blueprint proof: over an integral base `S`, every higher direct image `Rᵠf_* 𝔽_ℓ` is constructible
on some nonempty open `U ⊆ S`.

The generic curve model (`lem-fin-generic-curve-model`) gives `U`, a finite surjection
`p : S' ⟶ U`, the reduction `t : T ⟶ X_{S'}` and a finite modification `ν : ∐ₐ Yₐ ⟶ T` by smooth
projective curve families and finite étale families. The direct images of `𝔽_ℓ` along
`∐ₐ Yₐ ⟶ S'` are constructible (`thm-fin-projective-smooth-curve-finiteness`,
`lem-fin-finite-morphism`), hence so are those along `T ⟶ S'`
(`lem-finrepair-constant-finite-comparison`) and along `X_{S'} ⟶ S'`, the pullback along the
surjective closed immersion `t` being an equivalence
(`thm-weil-pbc-universal-homeomorphism-invariance`). By proper base change these are the
pullbacks `p^* Rᵠf_* 𝔽_ℓ`, so `Rᵠf_* 𝔽_ℓ |_U` embeds into the constructible sheaf
`p_* p^* Rᵠf_* 𝔽_ℓ` and is constructible (`lem-weil-pbc-constructible-subobjects-noetherian`). -/
theorem exists_isConstructibleSheaf_upperStar_rightDerivedLowerStar_zmod [IsIntegral S]
    (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS] [QuasiCompact aS] (f : X ⟶ S)
    {n : Type u} [Finite n] (i : X ⟶ ℙ(n; S)) [IsClosedImmersion i] (hi : i ≫ ℙ(n; S) ↘ S = f)
    (hf : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
      topologicalKrullDim (pullback f s : Scheme.{u}) ≤ 1)
    (ℓ : ℕ) [Fact ℓ.Prime] [HasInvertibleExponent (ULift.{u + 1} (ZMod ℓ)) S] :
    ∃ U : S.Opens, U ≠ ⊥ ∧ ∀ q : ℤ, IsConstructibleSheaf
      ((U.ι)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))].obj
        ((_root_.DerivedCategory.homologyFunctor _ q).obj
          ((R((f)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj
              ((constantSheaf X.smallEtaleTopology
                (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
                  (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ)))))))) := by
  obtain ⟨U, hU, S', _, p, _, _, T, t, _, _, _, ι, _, Y, ν, _, _, D, d, _, hD, hν, hY⟩ :=
    exists_isFinite_sigmaDesc_genericCurveModel aS f i hi hf
  refine ⟨U, hU, fun q ↦ ?_⟩
  let A := ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))
  let M : A := ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ))
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian aS
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace aS
  have : IsNoetherian S := {}
  have : IsProper f := hi ▸ inferInstance
  have : CompactSpace U := isCompact_iff_compactSpace.mp
    (TopologicalSpace.NoetherianSpace.isCompact _)
  have : IsNoetherian U := {}
  have : CompactSpace S' := QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiCompact (p ≫ U.ι ≫ aS) := inferInstance
  have : IsLocallyNoetherian S' := LocallyOfFiniteType.isLocallyNoetherian (p ≫ U.ι ≫ aS)
  have : IsNoetherian S' := {}
  have : HasInvertibleExponent (ULift.{u + 1} (ZMod ℓ)) S' := .of_hom (p ≫ U.ι)
  have : IsProper (f ∣_ U) := inferInstance
  have : IsProper (pullback.snd (f ∣_ U) p) := inferInstance
  have : Module.Finite (ULift.{u + 1} (ZMod ℓ)) M := Module.Finite.of_finite
  -- the direct images along `∐ₐ Yₐ ⟶ S'`
  have h₁ (q : ℤ) : IsConstructibleSheaf ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((R((ν ≫ t ≫ pullback.snd (f ∣_ U) p)_*[A])).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((ν)^*[A].obj ((constantSheaf T.smallEtaleTopology A).obj M))))) := by
    refine isConstructibleSheaf_of_iso ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
      ((R((ν ≫ t ≫ pullback.snd (f ∣_ U) p)_*[A])).mapIso
        ((_root_.DerivedCategory.singleFunctor _ 0).mapIso
          ((upperStarConstantSheafIso A ν).app M).symm))) ?_
    refine isConstructibleSheaf_homology_rightDerivedLowerStar_sigma _ _ q fun a ↦ ?_
    refine isConstructibleSheaf_of_iso ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
      ((R((Sigma.ι Y a ≫ ν ≫ t ≫ pullback.snd (f ∣_ U) p)_*[A])).mapIso
        ((_root_.DerivedCategory.singleFunctor _ 0).mapIso
          ((upperStarConstantSheafIso A (Sigma.ι Y a)).app M).symm))) ?_
    rcases hY a with ⟨⟨m, _, j, hj, hjv⟩, hsm⟩ | ⟨hfin, -⟩
    · exact isConstructibleSheaf_homology_rightDerivedLowerStar_of_smooth _ j hjv ℓ q
    · have : IsConstructibleSheaf ((constantSheaf (Y a).smallEtaleTopology A).obj M) :=
        (isFiniteLocallyConstantSheaf_constantSheaf M).isConstructibleSheaf
      exact (boundedConstructible_rightDerivedLowerStar_of_isFinite _
        (Sigma.ι Y a ≫ ν ≫ t ≫ pullback.snd (f ∣_ U) p)
        (DerivedCategory.boundedConstructible_singleFunctor_obj _ 0)).2 q
  -- the direct images along `T ⟶ S'`, by the finite modification `ν`
  let V : T.Opens := ⟨(Set.range d.base)ᶜ, d.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have : IsIso (pullback.snd ν V.ι) := by
    rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict]
    infer_instance
  have h₂ := (constructible_and_isIso_rightDerivedLowerStarUnitComparison (p ≫ U.ι ≫ aS)
    (t ≫ pullback.snd (f ∣_ U) p) ν d V.ι (by simp [V]) inferInstance M h₁).1
  -- the direct images along `X_{S'} ⟶ S'`: `t^*` is an equivalence
  have h₃ (q : ℤ) : IsConstructibleSheaf ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((R((pullback.snd (f ∣_ U) p)_*[A])).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf (pullback (f ∣_ U) p).smallEtaleTopology A).obj M)))) := by
    have := isEquivalence_upperStar_of_thickening A t t.surjective
    let G := (constantSheaf (pullback (f ∣_ U) p).smallEtaleTopology A).obj M
    have : IsIso ((upperStarLowerStarAdjunction A t).unit.app G) := inferInstance
    refine isConstructibleSheaf_of_iso ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
      ((R((pullback.snd (f ∣_ U) p)_*[A])).mapIso ((_root_.DerivedCategory.singleFunctor _ 0).mapIso
        (asIso ((upperStarLowerStarAdjunction A t).unit.app G))) ≪≫
        rightDerivedLowerStarSingleLowerStarIso t _ _ ≪≫
        (R((t ≫ pullback.snd (f ∣_ U) p)_*[A])).mapIso
          ((_root_.DerivedCategory.singleFunctor _ 0).mapIso
            ((upperStarConstantSheafIso A t).app M))).symm) (h₂ q)
  -- proper base change along `S' ⟶ S`
  have sq : IsPullback (pullback.fst (f ∣_ U) p ≫ (f ⁻¹ᵁ U).ι) (pullback.snd (f ∣_ U) p) f
      (p ≫ U.ι) :=
    (IsPullback.of_hasPullback (f ∣_ U) p).paste_horiz (isPullback_morphismRestrict f U).flip
  let E := (_root_.DerivedCategory.homologyFunctor _ q).obj
    ((R((f)_*[A])).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj
      ((constantSheaf X.smallEtaleTopology A).obj M)))
  have h₄ : IsConstructibleSheaf ((p)^*[A].obj ((U.ι)^*[A].obj E)) :=
    isConstructibleSheaf_of_iso (((upperStarComp A p U.ι).app E).symm ≪≫
      upperStarHomologyRightDerivedLowerStarIsoOfIsProper sq _ q ≪≫
      (_root_.DerivedCategory.homologyFunctor _ q).mapIso
        ((R((pullback.snd (f ∣_ U) p)_*[A])).mapIso
          ((_root_.DerivedCategory.singleFunctor _ 0).mapIso
            ((upperStarConstantSheafIso A _).app M)))).symm (h₃ q)
  -- `E |_U` embeds into the constructible sheaf `p_* p^* (E |_U)`
  have : IsConstructibleSheaf (((p)^*[A] ⋙ (p)_*[A]).obj ((U.ι)^*[A].obj E)) :=
    Scheme.IsConstructibleSheaf.lowerStar_of_isFinite p ((p)^*[A].obj ((U.ι)^*[A].obj E))
  have := Etale.mono_unit_app_of_surjective (ULift.{u + 1} (ZMod ℓ)) p p.surjective
    ((U.ι)^*[A].obj E)
  exact Scheme.IsConstructibleSheaf.of_mono
    ((upperStarLowerStarAdjunction A p).unit.app ((U.ι)^*[A].obj E))

/-- Blueprint `thm-fin-projective-curve-constant`: Constant coefficients on projective families
of dimension at most one.

Let `f : X ⟶ S` be projective (`f = π ∘ i` for a closed immersion `i : X ⟶ ℙ(n; S)`), with `S`
of finite type over a field `k`, such that every geometric fibre `X ×_S Spec Ω` has dimension at
most one, and let `ℓ` be a prime invertible on `S`. Every higher direct image `Rᵠf_* 𝔽_ℓ` is
constructible.

By Noetherian induction (`AlgebraicGeometry.Scheme.isConstructibleSheaf_of_forall_isIntegral`)
it suffices that the pullback of `Rᵠf_* 𝔽_ℓ` to every integral `W` immersed in `S` is
constructible on a nonempty open of `W`. By proper base change this pullback is the direct image
along the projective family `X ×_S W ⟶ W`, and the generic case
`AlgebraicGeometry.Etale.exists_isConstructibleSheaf_upperStar_rightDerivedLowerStar_zmod`
applies. -/
theorem isConstructibleSheaf_homology_rightDerivedLowerStar_zmod (aS : S ⟶ Spec (.of k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] (f : X ⟶ S) {n : Type u} [Finite n]
    (i : X ⟶ ℙ(n; S)) [IsClosedImmersion i] (hi : i ≫ ℙ(n; S) ↘ S = f)
    (hf : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
      topologicalKrullDim (pullback f s : Scheme.{u}) ≤ 1)
    (ℓ : ℕ) [Fact ℓ.Prime] [HasInvertibleExponent (ULift.{u + 1} (ZMod ℓ)) S] (q : ℤ) :
    IsConstructibleSheaf ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
            (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ))))))) := by
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian aS
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace aS
  have : IsNoetherian S := {}
  have : IsProper f := hi ▸ inferInstance
  refine Scheme.isConstructibleSheaf_of_forall_isIntegral _ fun W _ _ g _ ↦ ?_
  -- the base change `f_W : X ×_S W ⟶ W`, again projective with fibres of dimension `≤ 1`
  have hsq : IsPullback (pullback.fst f g) (pullback.snd f g) (i ≫ ℙ(n; S) ↘ S) g := by
    rw [hi]
    exact IsPullback.of_hasPullback f g
  have w : pullback.snd f g ≫ g = (pullback.fst f g ≫ i) ≫ ℙ(n; S) ↘ S := by
    rw [Category.assoc, hi, pullback.condition]
  have : IsClosedImmersion (ProjectiveSpace.liftBaseChange _ _ w) :=
    MorphismProperty.of_isPullback
      (ProjectiveSpace.isPullback_liftBaseChange (pullback.snd f g) hsq w)
      inferInstance
  have : QuasiCompact (g ≫ aS) := inferInstance
  have : HasInvertibleExponent (ULift.{u + 1} (ZMod ℓ)) W := .of_hom g
  obtain ⟨V, hV, hc⟩ := exists_isConstructibleSheaf_upperStar_rightDerivedLowerStar_zmod
    (g ≫ aS) (pullback.snd f g) (ProjectiveSpace.liftBaseChange _ _ w)
    (ProjectiveSpace.liftBaseChange_over _ _ w) (fun Ω _ _ s ↦ by
      rw [← IsHomeomorph.topologicalKrullDim_eq _
        (pullbackLeftPullbackSndIso f g s).inv.homeomorph.isHomeomorph]
      exact hf Ω (s ≫ g)) ℓ
  refine ⟨V, (TopologicalSpace.Opens.ne_bot_iff_nonempty V).mp hV, ?_⟩
  -- proper base change along `g`
  exact isConstructibleSheaf_of_iso ((V.ι)^*[_].mapIso
    (upperStarHomologyRightDerivedLowerStarIsoOfIsProper (IsPullback.of_hasPullback f g) _ q ≪≫
      (_root_.DerivedCategory.homologyFunctor _ q).mapIso
        ((R((pullback.snd f g)_*[_])).mapIso ((_root_.DerivedCategory.singleFunctor _ 0).mapIso
          ((upperStarConstantSheafIso _ _).app _)))).symm ≪≫
    ((upperStarComp _ V.ι g).app _).symm) (hc q)

/-- Blueprint `cor-fin-projective-curve-finite-group`: Finite constant groups on projective
curve families.

Let `f : X ⟶ S` be projective, with `S` of finite type over a field `k`, such that every
geometric fibre has dimension at most one. Let `Λ` be a finite ring whose exponent is invertible
on `S` and `M` a finite `Λ`-module. Every higher direct image `Rᵠf_* M` of the constant sheaf
`M` is constructible.

The blueprint states this for a finite abelian group `M` of order invertible on `S`, i.e. for
`Λ = ℤ/N` with `N = |M|`; the statement for finite modules over a finite ring is what the
constructibility of `Rπ_*` on `ℙ¹_S` (`thm-fin-projective-line-constructible`) consumes. -/
theorem isConstructibleSheaf_homology_rightDerivedLowerStar_constantSheaf
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (aS : S ⟶ Spec (.of k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] (f : X ⟶ S) {n : Type u} [Finite n]
    (i : X ⟶ ℙ(n; S)) [IsClosedImmersion i] (hi : i ≫ ℙ(n; S) ↘ S = f)
    (hf : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
      topologicalKrullDim (pullback f s : Scheme.{u}) ≤ 1)
    [HasInvertibleExponent Λ S] (M : ModuleCat.{u + 1} Λ) [Finite M] (q : ℤ) :
    IsConstructibleSheaf ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))) := by
  refine constructibleHomology_rightDerivedLowerStar_constantSheaf_of_zmod f
    (fun ℓ _ hℓ q' ↦ ?_) M q
  -- `ℓ` divides the characteristic of `Λ`, which is invertible on `S`
  have : HasInvertibleExponent (ULift.{u + 1} (ZMod ℓ)) S := by
    obtain ⟨c, hc⟩ := hℓ
    have hu := isUnit_ringChar_of_hasInvertibleExponent (Λ := Λ) S
    rw [hc, Nat.cast_mul] at hu
    exact ⟨ℓ, (Fact.out : ℓ.Prime).pos, by ext; simp, isUnit_of_mul_isUnit_left hu⟩
  exact isConstructibleSheaf_homology_rightDerivedLowerStar_zmod aS f i hi hf ℓ q'

end Etale

end AlgebraicGeometry

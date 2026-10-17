/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.GeometricFibreRank
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ProjectiveCurve.Betti
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ProjectiveCurve.ConstantDevissage
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ProjectiveCurve.FibreCohomology

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
- `AlgebraicGeometry.Etale.isConstructibleSheaf_homology_rightDerivedLowerStar_zmod`
- `AlgebraicGeometry.Etale.isConstructibleSheaf_homology_rightDerivedLowerStar_constantSheaf`

## Implementation notes

The ingredients are proved in the files of the directory `ProjectiveCurve`: the Betti numbers
of a single smooth proper curve (`Betti`), the comparison of the stalks of proper direct images
with the cohomology of the geometric fibres (`FibreCohomology`), the reduction to smooth families
over integral bases and the Noetherian induction (`GenericReduction`, `NoetherianInduction`,
`Sigma`), and the dévissage of finite coefficients (`ConstantDevissage`). Only cardinalities of
stalks and of cohomology groups are compared, which avoids the construction of edge maps.
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
  dsimp only
  have : IsProper f := by
    rw [← hi]
    infer_instance
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have hflat : Modules.IsFlatOver (SheafOfModules.unit X.ringCatSheaf) f :=
    Modules.isFlatOver_of_isInvertible f _
  have : (SheafOfModules.unit X.ringCatSheaf).IsFinitePresentation :=
    SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} _
  -- the dimensions of the cohomology of the structure sheaf of the fibres
  have hφ (r : ℕ) (s : S) :
      letI : (Limits.pullback f (S.geometricPointAt s)).Over
          (Spec (.of (AlgebraicClosure (S.residueField s)))) := ⟨pullback.snd _ _⟩
      ((Modules.pullback (pullback.fst f (S.geometricPointAt s))).obj
        (SheafOfModules.unit X.ringCatSheaf)).finrankH (AlgebraicClosure (S.residueField s)) r =
      Modules.finrankH (AlgebraicClosure (S.residueField s))
        (SheafOfModules.unit (Limits.pullback f (S.geometricPointAt s)).ringCatSheaf) r := by
    let : (Limits.pullback f (S.geometricPointAt s)).Over
        (Spec (.of (AlgebraicClosure (S.residueField s)))) := ⟨pullback.snd _ _⟩
    exact Modules.finrankH_congr _ (Modules.pullbackObjUnitIso _) r
  -- the geometric fibres are smooth proper curves over algebraically closed fields
  have hfib (s : S) :
      letI : (Limits.pullback f (S.geometricPointAt s)).Over
          (Spec (.of (AlgebraicClosure (S.residueField s)))) := ⟨pullback.snd _ _⟩
      Nat.card (Sheaf.H ((Limits.pullback f (S.geometricPointAt s)).constantZMod ℓ) 0) =
          ℓ ^ Nat.card (_root_.ConnectedComponents
            (Limits.pullback f (S.geometricPointAt s) : Scheme.{u})) ∧
        Nat.card (Sheaf.H ((Limits.pullback f (S.geometricPointAt s)).constantZMod ℓ) 1) =
          ℓ ^ (2 * arithmeticGenus (AlgebraicClosure (S.residueField s))
            (Limits.pullback f (S.geometricPointAt s))) ∧
        Nat.card (Sheaf.H ((Limits.pullback f (S.geometricPointAt s)).constantZMod ℓ) 2) =
          ℓ ^ Nat.card (_root_.ConnectedComponents
            (Limits.pullback f (S.geometricPointAt s) : Scheme.{u})) ∧
        (∀ r, 2 < r →
          Nat.card (Sheaf.H ((Limits.pullback f (S.geometricPointAt s)).constantZMod ℓ) r) = 1) ∧
        Nat.card (_root_.ConnectedComponents
            (Limits.pullback f (S.geometricPointAt s) : Scheme.{u})) =
          Modules.finrankH (AlgebraicClosure (S.residueField s))
            (SheafOfModules.unit (Limits.pullback f (S.geometricPointAt s)).ringCatSheaf) 0 := by
    let : (Limits.pullback f (S.geometricPointAt s)).Over
        (Spec (.of (AlgebraicClosure (S.residueField s)))) := ⟨pullback.snd _ _⟩
    have : SmoothOfRelativeDimension 1 (Limits.pullback f (S.geometricPointAt s) ↘
        Spec (.of (AlgebraicClosure (S.residueField s)))) :=
      inferInstanceAs (SmoothOfRelativeDimension 1 (pullback.snd f _))
    have : IsProper (Limits.pullback f (S.geometricPointAt s) ↘
        Spec (.of (AlgebraicClosure (S.residueField s)))) :=
      inferInstanceAs (IsProper (pullback.snd f _))
    have hℓs := hℓ.map ((S.geometricPointAt s).appTop ≫ (Scheme.ΓSpecIso _).hom).hom
    rw [map_natCast] at hℓs
    obtain ⟨h₀, h₁, h₂, h₃⟩ := natCard_sheafH_constantZMod_of_smoothOfRelativeDimension
      (Limits.pullback f (S.geometricPointAt s)) ℓ hℓs.ne_zero
    exact ⟨h₀, h₁, h₂, h₃, (finrankH_unit_zero_eq_natCard_connectedComponents _).symm⟩
  refine ⟨fun s ↦ ⟨(hfib s).1, (hfib s).2.1, (hfib s).2.2.1, (hfib s).2.2.2.1⟩, ?_, ?_⟩
  · have key : (fun s : S ↦
        Nat.card (_root_.ConnectedComponents
          (Limits.pullback f (S.geometricPointAt s) : Scheme.{u}))) =
        fun s ↦
          letI : (Limits.pullback f (S.geometricPointAt s)).Over
              (Spec (.of (AlgebraicClosure (S.residueField s)))) := ⟨pullback.snd _ _⟩
          ((Modules.pullback (pullback.fst f (S.geometricPointAt s))).obj
            (SheafOfModules.unit X.ringCatSheaf)).finrankH
              (AlgebraicClosure (S.residueField s)) 0 :=
      funext fun s ↦ (hfib s).2.2.2.2.trans (hφ 0 s).symm
    rw [key]
    exact Modules.finite_range_and_isConstructible_finrankH_geometricFibre f i hi
      (SheafOfModules.unit X.ringCatSheaf) hflat 0
  · have key : (fun s : S ↦
        letI : (Limits.pullback f (S.geometricPointAt s)).Over
            (Spec (.of (AlgebraicClosure (S.residueField s)))) := ⟨pullback.snd _ _⟩
        arithmeticGenus (AlgebraicClosure (S.residueField s))
          (Limits.pullback f (S.geometricPointAt s))) =
        fun s ↦
          letI : (Limits.pullback f (S.geometricPointAt s)).Over
              (Spec (.of (AlgebraicClosure (S.residueField s)))) := ⟨pullback.snd _ _⟩
          ((Modules.pullback (pullback.fst f (S.geometricPointAt s))).obj
            (SheafOfModules.unit X.ringCatSheaf)).finrankH
              (AlgebraicClosure (S.residueField s)) 1 :=
      funext fun s ↦ (hφ 1 s).symm
    rw [key]
    exact Modules.finite_range_and_isConstructible_finrankH_geometricFibre f i hi
      (SheafOfModules.unit X.ringCatSheaf) hflat 1

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
  have : IsProper f := by
    rw [← hi]
    infer_instance
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  -- `ℓ` is invertible on `S`
  have hℓ : IsUnit (ℓ : Γ(S, ⊤)) := by
    obtain ⟨m, -, hm, hu⟩ :=
      HasInvertibleExponent.exists_isUnit_natCast (Λ := ULift.{u + 1} (ZMod ℓ)) (X := S)
    have : (m : ZMod ℓ) = 0 := by simpa using congrArg ULift.down hm
    exact isUnit_of_dvd_unit (Nat.cast_dvd_cast ((ZMod.natCast_eq_zero_iff m ℓ).1 this)) hu
  obtain ⟨hcard, ⟨hcfin, hcc⟩, ⟨hgfin, hgc⟩⟩ :=
    natCard_sheafH_constantZMod_geometricFibre f i hi ℓ hℓ
  beta_reduce at hcard hcfin hcc hgfin hgc
  rcases lt_or_ge r 0 with hr | hr
  · exact IsConstructibleSheaf.of_isZero (_root_.DerivedCategory.isZero_of_isGE _ 0 r hr
      (hX := CategoryTheory.Functor.isGE_rightDerivedFunctor_obj _ _ 0))
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hr
  let E := (_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).obj
    ((R((f)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
          (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ))))))
  let v : S → ℕ := fun x ↦
    Nat.card (Sheaf.H ((Limits.pullback f (S.geometricPointAt x)).constantZMod ℓ) q)
  have hpt (x : S) : Nat.card (((pointSmallEtale (S.algClosurePoint x)).sheafFiber
      (A := ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj E) = v x :=
    natCard_sheafFiber_homology_rightDerivedLowerStar_zmod f (S.algClosurePoint x) ℓ q
  have hpos (x : S) : 0 < v x := by
    obtain ⟨h₀, h₁, h₂, h₃⟩ := hcard x
    rcases q with _ | _ | _ | q
    · simp only [v, h₀]
      exact pow_pos (Fact.out : ℓ.Prime).pos _
    · simp only [v, h₁]
      exact pow_pos (Fact.out : ℓ.Prime).pos _
    · simp only [v, h₂]
      exact pow_pos (Fact.out : ℓ.Prime).pos _
    · simp only [v, h₃ _ (by lia : 2 < q + 3)]
      exact Nat.one_pos
  have : IsFiniteSheaf E := ⟨fun Ω _ _ s ↦ by
    obtain ⟨x, hx⟩ := exists_natCard_sheafFiber_eq_natCard_sheafFiber_algClosurePoint s E
    have : Finite (((pointSmallEtale s).sheafFiber
      (A := ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj E) :=
      Nat.finite_of_card_ne_zero (by rw [hx, hpt]; exact (hpos x).ne')
    rw [ModuleCat.isFinitelyGenerated_iff]
    exact Module.Finite.of_finite⟩
  -- the cardinalities of the stalks are constructible functions
  have hpre (φ : S → ℕ) (hfin : (Set.range φ).Finite)
      (hφ : ∀ m, Topology.IsConstructible (φ ⁻¹' {m})) (T : Set ℕ) :
      Topology.IsConstructible (φ ⁻¹' T) := by
    have : φ ⁻¹' T = ⋃ m ∈ T ∩ Set.range φ, φ ⁻¹' {m} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_range,
        Set.mem_singleton_iff, exists_prop]
      exact ⟨fun h ↦ ⟨φ x, ⟨h, x, rfl⟩, rfl⟩, by rintro ⟨_, ⟨h, -⟩, rfl⟩; exact h⟩
    rw [this]
    exact Topology.IsConstructible.biUnion (hfin.subset Set.inter_subset_right) fun m _ ↦ hφ m
  rw [Scheme.isConstructibleSheaf_iff_isConstructible_card]
  intro m _
  have hset : {x : S | Nat.card (((pointSmallEtale (S.algClosurePoint x)).sheafFiber
      (A := ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj E) = m} =
      {x | v x = m} := by
    ext x
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hpt]
  rw [hset]
  rcases q with _ | _ | _ | q
  · convert hpre _ hcfin hcc {k | ℓ ^ k = m} using 1
    ext x
    exact Iff.of_eq (congrArg (· = m) (hcard x).1)
  · convert hpre _ hgfin hgc {k | ℓ ^ (2 * k) = m} using 1
    ext x
    exact Iff.of_eq (congrArg (· = m) (hcard x).2.1)
  · convert hpre _ hcfin hcc {k | ℓ ^ k = m} using 1
    ext x
    exact Iff.of_eq (congrArg (· = m) (hcard x).2.2.1)
  · have h₃ (x : S) : v x = 1 := (hcard x).2.2.2 _ (by lia)
    by_cases hm : 1 = m
    · convert Topology.IsConstructible.univ (X := S) using 1
      exact Set.eq_univ_of_forall fun x ↦ ((h₃ x).trans hm :)
    · convert Topology.IsConstructible.empty (X := S) using 1
      exact Set.eq_empty_of_forall_notMem fun x hx ↦ hm ((h₃ x).symm.trans hx)

variable {k : Type u} [Field k]

/-- Blueprint `thm-fin-projective-curve-constant`: Constant coefficients on projective families
of dimension at most one.

Let `f : X ⟶ S` be projective (`f = π ∘ i` for a closed immersion `i : X ⟶ ℙ(n; S)`), with `S`
of finite type over a field `k`, such that every geometric fibre `X ×_S Spec Ω` has dimension at
most one, and let `ℓ` be a prime invertible on `S`. Every higher direct image `Rᵠf_* 𝔽_ℓ` is
constructible. -/
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
  exact isConstructibleSheaf_homology_rightDerivedLowerStar_zmod_of_smooth ℓ
    (by
      intro _ _ _ f _ _ _ i _ hi _ r
      exact isConstructibleSheaf_homology_rightDerivedLowerStar_of_smooth f i hi ℓ r)
    aS f i hi hf q

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
    (fun ℓ _ hℓ q ↦ ?_) M q
  have : HasInvertibleExponent (ULift.{u + 1} (ZMod ℓ)) S :=
    ⟨ℓ, (Fact.out : ℓ.Prime).pos, ULift.ext _ _ (ZMod.natCast_self ℓ), hℓ⟩
  exact isConstructibleSheaf_homology_rightDerivedLowerStar_zmod aS f i hi hf ℓ q

end Etale

end AlgebraicGeometry

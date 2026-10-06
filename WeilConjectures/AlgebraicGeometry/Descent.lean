/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Descent.IsStack
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Fpqc descent for quasi-coherent modules and for finite locally free closed subschemes

Let `{T i ⟶ T}` be an fpqc covering, i.e. a family of arrows generating a covering sieve
for `AlgebraicGeometry.Scheme.fpqcTopology`. This file states the two descent theorems
needed for the construction of the Picard scheme.

**(D1) Descending modules.** Descent data for quasi-coherent modules relative to the
covering are effectively represented by quasi-coherent modules on `T`: the comparison
functor from `T.Modules` to descent data is fully faithful on quasi-coherent objects, and
every descent datum with quasi-coherent components comes from a quasi-coherent module.
The equivalence preserves finite presentability and local freeness, and in particular
invertible modules glue to an invertible module.

**(D2) Effective closed immersions.** Given `X ⟶ T` and closed subschemes of the base
changes `X ×_T T i` which are finite locally free of degree `d` over `T i` and agree after
further base change, there is a unique closed subscheme of `X` restricting to them, and it
is finite locally free of degree `d` over `T`.

## Implementation notes

Closed subschemes are spelled as ideal sheaves (`AlgebraicGeometry.Scheme.IdealSheafData`),
which is what makes the cocycle condition of the blueprint degenerate to a plain equality:
`IdealSheafData` is a *set*, so descent data for it carry no extra structure and (D2) is a
genuine sheaf condition. Degrees are measured by `AlgebraicGeometry.Scheme.Hom.finrank`.

(D1) is stated as five separate assertions rather than through
`CategoryTheory.Functor.IsStack`: `Mathlib.CategoryTheory.Sites.Descent.IsStack` asks for
effectivity of *all* descent data, whereas what holds here is effectivity of the
quasi-coherent ones, which is not an instance of that class.

Flatness of a sheaf of modules has no name in Mathlib yet, so its preservation under the
equivalence of (D1) is not part of the statements below.

Local freeness is only claimed to descend for modules of finite presentation: a module which is
locally free of infinite rank after a faithfully flat base change need not be locally free. A
module of finite presentation which becomes locally free after such a base change is flat and
of finite presentation, hence finite locally free.

## Main statements

- `AlgebraicGeometry.bijective_toDescentData_map`,
  `AlgebraicGeometry.exists_isQuasicoherent_toDescentData_iso`,
  `AlgebraicGeometry.isFinitePresentation_of_toDescentData_iso`,
  `AlgebraicGeometry.isLocallyFree_of_toDescentData_iso`,
  `AlgebraicGeometry.isFiniteLocallyFreeOfRank_of_toDescentData_iso` and
  `AlgebraicGeometry.isInvertible_of_toDescentData_iso`: (D1), fpqc descent for
  quasi-coherent modules.
- `AlgebraicGeometry.Scheme.IdealSheafData.exists_comap_eq_of_mem_fpqcTopology` and
  `AlgebraicGeometry.Scheme.IdealSheafData.eq_of_comap_eq_of_mem_fpqcTopology`: closed
  subschemes satisfy fpqc descent.
- `AlgebraicGeometry.isSheaf_fpqc_finiteLocallyFreeSubscheme`: (D2), the sheaf condition
  for closed subschemes which are finite locally free of a fixed degree.

## Proofs

Invertibility descends because an invertible module is the same as a finite locally free
module of rank one. (D2) follows the blueprint: the closed subschemes glue to a closed
subscheme `Z ⊆ X`, unique because pulling back ideal sheaves along an fpqc covering is
injective, and `Z ⟶ T` is finite, flat and of finite presentation because these properties
descend along fpqc coverings
(`AlgebraicGeometry.Scheme.of_isPullback_of_ofArrows_mem_fpqcTopology`); the degree is read
off on the covering.
-/

@[expose] public section

universe w u

open CategoryTheory Opposite CategoryTheory.Bicategory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The pseudofunctor sending a scheme `X` to its category `X.Modules` of sheaves of
modules and a morphism to the pullback functor. This is the pseudofunctor underlying
`AlgebraicGeometry.Scheme.Modules.pseudofunctor`, which also records the pushforward
functors and the adjunctions; here we only keep the contravariant part, which is the
shape required by `CategoryTheory.Pseudofunctor.DescentData`. -/
noncomputable abbrev modulesPseudofunctor :
    Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat :=
  Scheme.Modules.pseudofunctor.comp Adj.forget₁

variable {T : Scheme.{u}} {ι : Type w} {T' : ι → Scheme.{u}} (g : ∀ i, T' i ⟶ T)

/-- **Fpqc descent for modules: full faithfulness.** For an fpqc covering `{g i : T i ⟶ T}`,
the comparison functor from sheaves of modules on `T` to descent data relative to the covering
is fully faithful on quasi-coherent objects.

(blueprint: `lem-pc-fpqc-descent`; `sk-thm-picard-descent`, part (D1)) -/
theorem bijective_toDescentData_map (hg : Sieve.ofArrows T' g ∈ Scheme.fpqcTopology T)
    (M N : modulesPseudofunctor.obj (.mk (op T)))
    (hM : (M : T.Modules).IsQuasicoherent) (hN : (N : T.Modules).IsQuasicoherent) :
    Function.Bijective ((modulesPseudofunctor.toDescentData g).map : (M ⟶ N) → _) :=
  sorry

/-- **Fpqc descent for modules: effectivity.** For an fpqc covering `{g i : T i ⟶ T}`, every
descent datum whose components are quasi-coherent comes from a quasi-coherent module on `T`.

(blueprint: `lem-pc-fpqc-descent`; `sk-thm-picard-descent`, part (D1)) -/
theorem exists_isQuasicoherent_toDescentData_iso
    (hg : Sieve.ofArrows T' g ∈ Scheme.fpqcTopology T)
    (D : modulesPseudofunctor.DescentData g)
    (hD : ∀ i, (D.obj i : (T' i).Modules).IsQuasicoherent) :
    ∃ M : modulesPseudofunctor.obj (.mk (op T)), (M : T.Modules).IsQuasicoherent ∧
      Nonempty ((modulesPseudofunctor.toDescentData g).obj M ≅ D) :=
  sorry

/-- **Finite presentation descends along an fpqc covering.**

(blueprint: `lem-pc-fpqc-descent`; `sk-thm-picard-descent`, part (D1)) -/
theorem isFinitePresentation_of_toDescentData_iso (hg : Sieve.ofArrows T' g ∈ Scheme.fpqcTopology T)
    (D : modulesPseudofunctor.DescentData g)
    (M : modulesPseudofunctor.obj (.mk (op T)))
    (hM : Nonempty ((modulesPseudofunctor.toDescentData g).obj M ≅ D))
    (hD : ∀ i, (D.obj i : (T' i).Modules).IsFinitePresentation) :
    (M : T.Modules).IsFinitePresentation :=
  sorry

/-- **Finite local freeness descends along an fpqc covering.** A descent datum whose
components are of finite presentation and locally free, i.e. finite locally free with a rank
allowed to vary locally, comes from a module on `T` which is locally free; it is of finite
presentation by `isFinitePresentation_of_toDescentData_iso`.

(blueprint: `lem-pc-fpqc-descent`; `sk-thm-picard-descent`, part (D1)) -/
theorem isLocallyFree_of_toDescentData_iso (hg : Sieve.ofArrows T' g ∈ Scheme.fpqcTopology T)
    (D : modulesPseudofunctor.DescentData g)
    (M : modulesPseudofunctor.obj (.mk (op T)))
    (hM : Nonempty ((modulesPseudofunctor.toDescentData g).obj M ≅ D))
    (hD : ∀ i, (D.obj i : (T' i).Modules).IsFinitePresentation ∧
      (D.obj i : (T' i).Modules).IsLocallyFree) :
    (M : T.Modules).IsLocallyFree :=
  sorry

/-- **Finite local freeness of a fixed rank descends along an fpqc covering.** A descent datum
whose components are finite locally free of rank `r` comes from a module on `T` which is
finite locally free of rank `r`. This refines `isLocallyFree_of_toDescentData_iso`: the rank
of a finite locally free module is locally constant, and can be read off after a faithfully
flat base change.

(blueprint: `lem-pc-fpqc-descent`; `sk-thm-picard-descent`, part (D1)) -/
theorem isFiniteLocallyFreeOfRank_of_toDescentData_iso
    (hg : Sieve.ofArrows T' g ∈ Scheme.fpqcTopology T)
    (D : modulesPseudofunctor.DescentData g)
    (M : modulesPseudofunctor.obj (.mk (op T)))
    (hM : Nonempty ((modulesPseudofunctor.toDescentData g).obj M ≅ D)) (r : ℕ)
    (hD : ∀ i, (D.obj i : (T' i).Modules).IsFiniteLocallyFreeOfRank r) :
    (M : T.Modules).IsFiniteLocallyFreeOfRank r :=
  sorry

/-- **Invertibility descends along an fpqc covering**: a compatible family of invertible
modules `ℒ i` on the `T i` glues to an invertible module `ℒ` on `T` with `ℒ|_{T i} ≅ ℒ i`.

(blueprint: `lem-pc-fpqc-descent`; `sk-thm-picard-descent`, part (D1)) -/
theorem isInvertible_of_toDescentData_iso (hg : Sieve.ofArrows T' g ∈ Scheme.fpqcTopology T)
    (D : modulesPseudofunctor.DescentData g)
    (M : modulesPseudofunctor.obj (.mk (op T)))
    (hM : Nonempty ((modulesPseudofunctor.toDescentData g).obj M ≅ D))
    (hD : ∀ i, (D.obj i : (T' i).Modules).IsInvertible) :
    (M : T.Modules).IsInvertible :=
  (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one (M : T.Modules)).mpr <|
    isFiniteLocallyFreeOfRank_of_toDescentData_iso g hg D M hM 1 fun i ↦
      (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one
        (D.obj i : (T' i).Modules)).mp (hD i)

namespace Scheme.IdealSheafData

/-- **Fpqc descent for closed subschemes: existence.** Let `{p i : X' i ⟶ X}` be an fpqc
covering and let `I i` be ideal sheaves on the `X' i` whose pullbacks agree on every scheme
mapping compatibly to two members of the covering. Then the `I i` are the pullbacks of a single
ideal sheaf on `X`.

This is the step "descending the quotients" of the proof of
`lem-pc-descent-finite-flat-closed-subschemes`: the quotients `𝒪 / I i` form a descent datum
of quasi-coherent modules, which is effective by `lem-pc-fpqc-descent`.

(blueprint: `lem-pc-descent-finite-flat-closed-subschemes`) -/
theorem exists_comap_eq_of_mem_fpqcTopology {X : Scheme.{u}} {X' : ι → Scheme.{u}}
    (p : ∀ i, X' i ⟶ X) (hp : Sieve.ofArrows X' p ∈ Scheme.fpqcTopology X)
    (I : ∀ i, (X' i).IdealSheafData)
    (hcompat : ∀ ⦃Y : Scheme.{u}⦄ ⦃i j : ι⦄ (a : Y ⟶ X' i) (b : Y ⟶ X' j),
      a ≫ p i = b ≫ p j → (I i).comap a = (I j).comap b) :
    ∃ J : X.IdealSheafData, ∀ i, J.comap (p i) = I i :=
  sorry

set_option backward.isDefEq.respectTransparency.types false in
/-- An ideal sheaf whose pullback along every member of an fpqc covering sieve vanishes, vanishes:
the inclusion of the closed subscheme it cuts out becomes an isomorphism after base change along
the covering, hence is an isomorphism. -/
theorem eq_bot_of_comap_eq_bot_of_mem_fpqcTopology {X : Scheme.{u}} {S : Sieve X}
    (hS : S ∈ Scheme.fpqcTopology X) (K : X.IdealSheafData)
    (hK : ∀ ⦃Y : Scheme.{u}⦄ (h : Y ⟶ X), S h → K.comap h = ⊥) : K = ⊥ := by
  rw [← isIso_subschemeι_iff_eq_bot]
  refine Scheme.of_isPullback_of_mem_fpqcTopology (P := MorphismProperty.isomorphisms Scheme)
    hS K.subschemeι fun Y W h a b hh hab ↦ ?_
  have : IsIso (K.comap h).subschemeι := by
    rw [isIso_subschemeι_iff_eq_bot]
    exact hK h hh
  have : IsIso (pullback.fst h K.subschemeι) := by
    rw [← comapIso_inv_subschemeι]
    infer_instance
  change IsIso b
  rw [← hab.flip.isoPullback_hom_fst]
  infer_instance

/-- **Fpqc descent for closed subschemes: uniqueness.** Two ideal sheaves on `X` whose pullbacks
along every member of an fpqc covering family agree are equal.

(blueprint: `lem-pc-descent-finite-flat-closed-subschemes`) -/
theorem eq_of_comap_eq_of_mem_fpqcTopology {X : Scheme.{u}} {X' : ι → Scheme.{u}}
    (p : ∀ i, X' i ⟶ X) (hp : Sieve.ofArrows X' p ∈ Scheme.fpqcTopology X)
    {J J' : X.IdealSheafData} (h : ∀ i, J.comap (p i) = J'.comap (p i)) : J = J' := by
  suffices H : ∀ J J' : X.IdealSheafData, (∀ i, J.comap (p i) = J'.comap (p i)) → J' ≤ J from
    le_antisymm (H J' J fun i ↦ (h i).symm) (H J J' h)
  intro J J' h
  rw [← J.ker_subschemeι]
  refine le_ker_of_comap_eq_bot _ (eq_bot_of_comap_eq_bot_of_mem_fpqcTopology
    (Scheme.fpqcTopology.pullback_stable J.subschemeι hp) _ fun Y k hk ↦ ?_)
  obtain ⟨i, a, ha⟩ := (Sieve.mem_ofArrows_iff ..).mp hk
  rw [← comap_comp, ha, comap_comp, ← h i, ← comap_comp, ← ha, comap_comp,
    comap_subschemeι, comap_bot]

end Scheme.IdealSheafData

/-- **Fpqc descent for finite locally free closed subschemes.** Let `f : X ⟶ T` be a morphism
of schemes, let `{g i : T i ⟶ T}` be an fpqc covering and let `p i : X i ⟶ X`,
`q i : X i ⟶ T i` exhibit `X i` as the base change `X ×_T T i`:

```
   X' i ──── p i ────▶ X
     │                 │
   q i                 f
     │                 │
     ▼                 ▼
   T' i ──── g i ────▶ T
```

Given closed subschemes `Z i ⊆ X i`, described by ideal sheaves `I i`, which are finite
locally free of degree `d` over `T i` and whose pullbacks agree over `X i ×_X X j`, there
is a unique closed subscheme `Z ⊆ X` with `Z ×_T T i = Z i`, and `Z` is finite locally
free of degree `d` over `T`.

(blueprint: `lem-pc-descent-finite-flat-closed-subschemes`; `sk-thm-picard-descent`,
part (D2)) -/
theorem isSheaf_fpqc_finiteLocallyFreeSubscheme (hg : Sieve.ofArrows T' g ∈ Scheme.fpqcTopology T)
    {X : Scheme.{u}} (f : X ⟶ T) (d : ℕ)
    {X' : ι → Scheme.{u}} (p : ∀ i, X' i ⟶ X) (q : ∀ i, X' i ⟶ T' i)
    (hp : ∀ i, IsPullback (p i) (q i) f (g i)) (I : ∀ i, (X' i).IdealSheafData)
    (hfin : ∀ i, IsFinite ((I i).subschemeι ≫ q i))
    (hflat : ∀ i, Flat ((I i).subschemeι ≫ q i))
    (hfp : ∀ i, LocallyOfFinitePresentation ((I i).subschemeι ≫ q i))
    (hdeg : ∀ i (t : T' i), ((I i).subschemeι ≫ q i).finrank t = d)
    (hcompat : ∀ ⦃Y : Scheme.{u}⦄ ⦃i j : ι⦄ (a : Y ⟶ X' i) (b : Y ⟶ X' j),
      a ≫ p i = b ≫ p j → (I i).comap a = (I j).comap b) :
    ∃ J : X.IdealSheafData, (∀ i, J.comap (p i) = I i) ∧
      IsFinite (J.subschemeι ≫ f) ∧ Flat (J.subschemeι ≫ f) ∧
      LocallyOfFinitePresentation (J.subschemeι ≫ f) ∧
      (∀ t : T, (J.subschemeι ≫ f).finrank t = d) ∧
      ∀ J' : X.IdealSheafData, (∀ i, J'.comap (p i) = I i) → J' = J := by
  -- the base change `{p i : X' i ⟶ X}` of the covering is an fpqc covering of `X`
  have hpX : Sieve.ofArrows X' p ∈ Scheme.fpqcTopology X := by
    refine Scheme.fpqcTopology.superset_covering ?_ (Scheme.fpqcTopology.pullback_stable f hg)
    intro Y h hh
    obtain ⟨i, k, hk⟩ := (Sieve.mem_ofArrows_iff ..).mp hh
    exact (Sieve.mem_ofArrows_iff ..).mpr ⟨i, (hp i).lift h k hk, ((hp i).lift_fst _ _ _).symm⟩
  obtain ⟨J, hJ⟩ := Scheme.IdealSheafData.exists_comap_eq_of_mem_fpqcTopology p hpX I hcompat
  obtain rfl : I = fun i ↦ J.comap (p i) := funext fun i ↦ (hJ i).symm
  -- `Z ×_T T i` is the closed subscheme cut out by `J.comap (p i)`
  have hsq : ∀ i, IsPullback ((J.comapIso (p i)).hom ≫ pullback.snd _ _)
      ((J.comap (p i)).subschemeι ≫ q i) (J.subschemeι ≫ f) (g i) := fun i ↦
    ((IsPullback.of_hasPullback (p i) J.subschemeι).flip.paste_vert (hp i)).of_iso'
      (J.comapIso (p i)) (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp)
      (by simp)
  have : MorphismProperty.DescendsAlong @IsFinite (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
    IsFinite.descendsAlong_surjective_inf_flat_inf_quasicompact
  have hfin' : IsFinite (J.subschemeι ≫ f) :=
    Scheme.of_isPullback_of_ofArrows_mem_fpqcTopology hg _ _ _ hsq hfin
  have hflat' : Flat (J.subschemeι ≫ f) :=
    Scheme.of_isPullback_of_ofArrows_mem_fpqcTopology hg _ _ _ hsq hflat
  have hfp' : LocallyOfFinitePresentation (J.subschemeι ≫ f) :=
    Scheme.of_isPullback_of_ofArrows_mem_fpqcTopology hg _ _ _ hsq hfp
  refine ⟨J, fun _ ↦ rfl, hfin', hflat', hfp', fun t ↦ ?_, fun J' hJ' ↦
    Scheme.IdealSheafData.eq_of_comap_eq_of_mem_fpqcTopology p hpX hJ'⟩
  obtain ⟨Y, h, hh, y, rfl⟩ := Scheme.exists_mem_of_mem_fpqcTopology hg t
  obtain ⟨i, k, rfl⟩ := (Sieve.mem_ofArrows_iff ..).mp hh
  rw [Scheme.Hom.comp_apply, ← Scheme.Hom.finrank_of_isPullback _ _ _ _ (hsq i) (k y)]
  exact hdeg i (k y)

end AlgebraicGeometry

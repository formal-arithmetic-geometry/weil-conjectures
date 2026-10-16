/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra
public import WeilConjectures.SixFunctors.BaseChange.DerivedForget
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.CohomologyMapDevissage
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.EdgeMapBaseChange
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Invariance of the cohomology of a proper curve under extension of the base field

Let `k ⊆ k'` be separably closed fields, `C` a proper curve over `k` (a proper `k`-scheme of
dimension at most one), and `F` a torsion étale sheaf on `C`. Then the pullback map
`Hᵠ(C, F) ⟶ Hᵠ(C_{k'}, F|)` is bijective in every degree. This is the input of the proof of
proper base change for the projective line: there the stalk of the exchange morphism at a
geometric point is such a pullback map, between the projective lines over the residue fields
of two strict henselisations.

The case of algebraically closed fields is the real content; it is reached from the curve
calculations by dévissage and is stated here without proof. The separably closed case is
deduced from it, the extensions `k̄/k` and `k̄'/k'` being purely inseparable, so that the
corresponding base changes are universal homeomorphisms, which do not change étale cohomology.

The base change `C_{k'}` is given by an arbitrary cartesian square

```
C' --ι'--> C
|          |
f'         f
v          v
Spec k' -ι-> Spec k
```

and the coefficient sheaf is a torsion sheaf of `Λ`-modules
(`AlgebraicGeometry.Scheme.IsTorsionModuleSheaf`, torsion of the geometric stalks); its cohomology
is that of the underlying sheaf of abelian groups.

## Main statements

- `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_isAlgClosed`: the algebraically closed
  case.
- `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_isSepClosed_of_isAlgClosed`: the
  passage from algebraically closed to separably closed fields.
- `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_isSepClosed`: the separably closed
  case.
- `AlgebraicGeometry.Etale.bijective_cohomologyMap_comp_iff`: pulling back in two steps is
  bijective on étale cohomology exactly when pulling back along the composite is.

## References

- Stacks Project, Lemma 59.80.4 (invariance of the cohomology of a proper curve),
  <https://stacks.math.columbia.edu/tag/0A5E>
- Stacks Project, Theorem 59.83.1, <https://stacks.math.columbia.edu/tag/03SC>
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

open Abelian Limits

/-- Pulling étale cohomology back along `b` and then along `a` is bijective exactly when pulling
it back along the composite `c = a ≫ b` is: the two maps differ by the isomorphisms
`(a ≫ b)^* ≅ b^* ⋙ a^*` of pullback functors and of constant sheaves `ℤ`. -/
theorem bijective_cohomologyMap_comp_iff {W Z Y : Scheme.{u}} (a : W ⟶ Z) (b : Z ⟶ Y)
    (c : W ⟶ Y) (hc : a ≫ b = c) (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (n : ℕ) :
    Function.Bijective (cohomologyMap a _ n ∘ cohomologyMap b F n) ↔
      Function.Bijective (cohomologyMap c F n) := by
  subst hc
  let τ := Etale.upperStarComp AddCommGrpCat.{u + 1} a b
  let ℤY := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift ℤ))
  let eA := (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} a).symm.app
    (AddCommGrpCat.of (ULift ℤ))
  let eB := (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} b).symm.app
    (AddCommGrpCat.of (ULift ℤ))
  let eC := (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} (a ≫ b)).symm.app
    (AddCommGrpCat.of (ULift ℤ))
  let v := eA ≪≫ ((a)^*[AddCommGrpCat.{u + 1}]).mapIso eB ≪≫ τ.symm.app ℤY ≪≫ eC.symm
  have key : cohomologyMap a _ n ∘ cohomologyMap b F n =
      (Ext.precompAddEquiv v _ n) ∘ Sheaf.H.map (τ.hom.app F) n ∘ cohomologyMap (a ≫ b) F n := by
    funext x
    have := comp_preservesFiniteLimits ((b)^*[AddCommGrpCat.{u + 1}])
      ((a)^*[AddCommGrpCat.{u + 1}])
    have := comp_preservesFiniteColimits ((b)^*[AddCommGrpCat.{u + 1}])
      ((a)^*[AddCommGrpCat.{u + 1}])
    rw [Function.comp_apply, cohomologyMap_cohomologyMap, Ext.mapExactFunctor_eq_of_iso τ x]
    simp only [Function.comp_apply, cohomologyMap_apply, Sheaf.H.map_apply]
    change _ = (Ext.mk₀ v.hom).comp _ (zero_add n)
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀_assoc, Ext.mk₀_comp_mk₀_assoc]
    congr 2
    simp [v, eA, eB, eC, ℤY]
  rw [key]
  exact Function.Bijective.of_comp_iff' ((AddEquiv.bijective _).comp
    (bijective_sheafHMap_hom (τ.app F) n)) _

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.IsCurve

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **Invariance of the cohomology of a proper curve under extension of algebraically closed
fields.** Let `k ⊆ k'` be algebraically closed fields, `C` a proper curve over `k` and `F` a
torsion étale sheaf of `Λ`-modules on `C`. For every cartesian square

```
C' --ι'--> C
|          |
f'         f
v          v
Spec k' -ι-> Spec k
```

the pullback map `Hᵠ(C, F) ⟶ Hᵠ(C', ι'^* F)` on the cohomology of the underlying abelian
sheaves is bijective for every `q`. This is the assertion `C₇(C, F)` of the eight curve
calculations; it is proved by reducing to reduced curves and constructible `𝐅_r`-coefficients,
splitting off the zero-dimensional components, localising to a dense open, passing to the
normalisation and to the smooth constant case of the curve calculations.
(blueprint: `prop-weil-pbc-algebraically-closed-extension`) -/
@[stacks 0A5E]
theorem bijective_cohomologyMap_of_isAlgClosed {k k' : Type u} [Field k] [IsAlgClosed k]
    [Field k'] [IsAlgClosed k'] {C C' : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f]
    [IsProper f] {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C}
    (h : IsPullback ι' f' f ι) (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsTorsionModuleSheaf F] (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap ι'
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q) :=
  sorry

open Limits Etale in
/-- **Passage between separably closed fields.** Let `k ⊆ k'` be separably closed fields, `C`
a proper curve over `k` and `F` a torsion étale sheaf of `Λ`-modules on `C`. If the cohomology
of proper curves is invariant under extensions of algebraically closed fields (the hypothesis
`H`, which is `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_isAlgClosed`), then for
every cartesian square

```
C' --ι'--> C
|          |
f'         f
v          v
Spec k' -ι-> Spec k
```

the pullback map `Hᵠ(C, F) ⟶ Hᵠ(C', ι'^* F)` is bijective for every `q`.

Choose compatible algebraic closures `k̄ ⊆ k̄'`. As `k` and `k'` are separably closed, `k̄/k`
and `k̄'/k'` are purely inseparable, so the base changes `C_{k̄} ⟶ C` and `C_{k̄'} ⟶ C'` are
universal homeomorphisms and are bijective on étale cohomology
(`AlgebraicGeometry.Etale.cohomologyMap_bijective`). The square of pullback maps between the
four cohomology groups commutes, and its bottom row `Hᵠ(C_{k̄}) ⟶ Hᵠ(C_{k̄'})` is bijective by
`H`.
(blueprint: `lemma-weil-pbc-curve-separably-closed-passage`) -/
theorem bijective_cohomologyMap_of_isSepClosed_of_isAlgClosed
    (H : ∀ {k k' : Type u} [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k']
      {C C' : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f] [IsProper f]
      {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C}
      (_ : IsPullback ι' f' f ι) (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      [Scheme.IsTorsionModuleSheaf F] (q : ℕ),
      Function.Bijective (Etale.cohomologyMap ι'
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q))
    {k k' : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k'] {C C' : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsCurve f] [IsProper f] {ι : Spec (.of k') ⟶ Spec (.of k)}
    {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C} (h : IsPullback ι' f' f ι)
    (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Scheme.IsTorsionModuleSheaf F] (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap ι'
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q) := by
  obtain ⟨φ, rfl⟩ : ∃ φ : CommRingCat.of k ⟶ CommRingCat.of k', Spec.map φ = ι :=
    ⟨Spec.preimage ι, Spec.map_preimage ι⟩
  -- compatible algebraic closures `k̄ ⟶ k̄'`
  let : Algebra k (AlgebraicClosure k') :=
    ((algebraMap k' (AlgebraicClosure k')).comp φ.hom).toAlgebra
  let ψ : AlgebraicClosure k →ₐ[k] AlgebraicClosure k' := IsAlgClosed.lift
  let s := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  let s' := Spec.map (CommRingCat.ofHom (algebraMap k' (AlgebraicClosure k')))
  let κ : Spec (.of (AlgebraicClosure k')) ⟶ Spec (.of (AlgebraicClosure k)) :=
    Spec.map (CommRingCat.ofHom ψ.toRingHom)
  have hκ : κ ≫ s = s' ≫ Spec.map φ := by
    simp only [κ, s, s', ← Spec.map_comp]
    congr 1
    ext x
    exact ψ.commutes x
  -- the base changes `C_{k̄} ⟶ C` and `C'_{k̄'} ⟶ C'`, and the comparison `C'_{k̄'} ⟶ C_{k̄}`
  let p := pullback.fst f s
  let p' := pullback.fst f' s'
  let j : pullback f' s' ⟶ pullback f s := pullback.lift (p' ≫ ι') (pullback.snd f' s' ≫ κ)
    (by rw [Category.assoc, h.w, pullback.condition_assoc, Category.assoc, hκ])
  have hj : j ≫ p = p' ≫ ι' := pullback.lift_fst _ _ _
  have hsq : IsPullback j (pullback.snd f' s') (pullback.snd f s) κ := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f s)
    rw [hj, hκ]
    exact (IsPullback.of_hasPullback f' s').paste_horiz h
  have : IsCurve (pullback.snd f s) :=
    { krullDim_le_one := by
        rw [IsHomeomorph.topologicalKrullDim_eq _ (pullback.fst f s).isHomeomorph]
        exact IsCurve.krullDim_le_one (f := f) }
  -- the bottom row is bijective by the algebraically closed case
  have hb := H (pullback.snd f s) hsq ((p)^*[ModuleCat.{u + 1} Λ].obj F) q
  let G := (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F
  replace hb : Function.Bijective (Etale.cohomologyMap j ((p)^*[AddCommGrpCat.{u + 1}].obj G) q) :=
    Etale.bijective_cohomologyMap_of_iso j
      ((asIso (Etale.upperStarForget₂ Λ p).natTrans).app F).symm q hb
  have h₁ := (Etale.bijective_cohomologyMap_comp_iff j p _ hj G q).1
    (hb.comp (Etale.cohomologyMap_bijective p G q))
  rw [← Etale.bijective_cohomologyMap_comp_iff p' ι' _ rfl G q] at h₁
  exact (Function.Bijective.of_comp_iff' (Etale.cohomologyMap_bijective p' _ q) _).1 h₁

/-- **Invariance of the cohomology of a proper curve under extension of separably closed
fields.** Let `k ⊆ k'` be separably closed fields, `C` a proper curve over `k` (a proper
`k`-scheme of dimension at most one) and `F` a torsion étale sheaf of `Λ`-modules on `C`. For
every cartesian square

```
C' --ι'--> C
|          |
f'         f
v          v
Spec k' -ι-> Spec k
```

the pullback map `Hᵠ(C, F) ⟶ Hᵠ(C', ι'^* F)` on the cohomology of the underlying abelian
sheaves is bijective for every `q`: the algebraically closed case
`AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_isAlgClosed`, transported to separably
closed fields by
`AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_isSepClosed_of_isAlgClosed`.
(blueprint: `prop-weil-pbc-proper-curve-sepclosed-invariance`) -/
@[stacks 0A5E]
theorem bijective_cohomologyMap_of_isSepClosed {k k' : Type u} [Field k] [IsSepClosed k]
    [Field k'] [IsSepClosed k'] {C C' : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f]
    [IsProper f] {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C}
    (h : IsPullback ι' f' f ι) (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsTorsionModuleSheaf F] (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap ι'
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q) :=
  bijective_cohomologyMap_of_isSepClosed_of_isAlgClosed Λ
    (fun f _ _ _ _ _ h F _ q ↦ bijective_cohomologyMap_of_isAlgClosed Λ f h F q) f h F q

end AlgebraicGeometry.IsCurve

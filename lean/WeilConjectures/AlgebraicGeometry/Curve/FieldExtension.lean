/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf
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
(`AlgebraicGeometry.Scheme.IsTorsionSheaf`, torsion of the geometric stalks); its cohomology
is that of the underlying sheaf of abelian groups.

## Main statements

- `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_isAlgClosed`: the algebraically closed
  case.
- `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_isSepClosed_of_isAlgClosed`: the
  passage from algebraically closed to separably closed fields.
- `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_isSepClosed`: the separably closed
  case.

## References

- Stacks Project, Lemma 59.80.4 (invariance of the cohomology of a proper curve),
  <https://stacks.math.columbia.edu/tag/0A5E>
- Stacks Project, Theorem 59.83.1, <https://stacks.math.columbia.edu/tag/03SC>
-/

@[expose] public section

universe u

open CategoryTheory

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
    [Scheme.IsTorsionSheaf F] (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap ι'
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q) :=
  sorry

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
      [Scheme.IsTorsionSheaf F] (q : ℕ),
      Function.Bijective (Etale.cohomologyMap ι'
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q))
    {k k' : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k'] {C C' : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsCurve f] [IsProper f] {ι : Spec (.of k') ⟶ Spec (.of k)}
    {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C} (h : IsPullback ι' f' f ι)
    (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Scheme.IsTorsionSheaf F] (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap ι'
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q) :=
  sorry

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
    [Scheme.IsTorsionSheaf F] (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap ι'
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q) :=
  bijective_cohomologyMap_of_isSepClosed_of_isAlgClosed Λ
    (fun f _ _ _ _ _ h F _ q ↦ bijective_cohomologyMap_of_isAlgClosed Λ f h F q) f h F q

end AlgebraicGeometry.IsCurve

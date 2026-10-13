/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# The eight curve-cohomology assertions

Let `k` be an algebraically closed field, `X` a separated `k`-scheme of finite type of
dimension at most one (`AlgebraicGeometry.IsCurve`), and `F` a torsion étale sheaf on `X`.
The proof of proper base change for the projective line rests on eight assertions
`C₁(X, F), …, C₈(X, F)` about the étale cohomology `Hᵠ(X, F)`:

1. `Hᵠ(X, F) = 0` for `q > 2`;
2. `Hᵠ(X, F) = 0` for `q > 1` when `X` is affine;
3. `Hᵠ(X, F) = 0` for `q > 1` when `char k = p > 0` and `F` is `p`-primary;
4. `Hᵠ(X, F)` is finite when `F` is constructible with torsion prime to `char k`;
5. `Hᵠ(X, F)` is finite when `X` is proper and `F` is constructible;
6. `Hᵠ(X, F) ⟶ Hᵠ(X_{k'}, F|)` is bijective for every algebraically closed extension `k'/k`
   when the torsion of `F` is prime to `char k`;
7. the same map is bijective when `X` is proper, with no restriction on the torsion;
8. `H²(X, F) ⟶ H²(W, F|_W)` is surjective for every open `W ⊆ X`.

They are bundled in `AlgebraicGeometry.IsCurve.Assertions`. The coefficient sheaf is a
sheaf of `Λ`-modules and `Hᵠ(X, F)` is the cohomology of its underlying abelian sheaf; the
torsion conditions are conditions on the geometric stalks
(`AlgebraicGeometry.Scheme.IsTorsionModuleSheaf`,
`AlgebraicGeometry.Scheme.IsTorsionModuleSheafOfInvertibleOrder`). The field extension in `C₆` and
`C₇` is given by an arbitrary cartesian square

```
X' --ι'--> X
|          |
f'         f
v          v
Spec k' -ι-> Spec k
```

## Main definitions

- `AlgebraicGeometry.Scheme.IsPrimaryTorsionSheaf`: a sheaf whose geometric stalks are
  `p`-primary torsion groups.
- `AlgebraicGeometry.IsCurve.Assertions`: the conjunction `C(X, F)` of the eight assertions.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- A sheaf `F` of `Λ`-modules on the small étale site of `X` is *`p`-primary torsion* if
every element of every geometric stalk of `F` is killed by a power of `p`. -/
def Scheme.IsPrimaryTorsionSheaf {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (p : ℕ) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (x : ↥((pointSmallEtale s).sheafFiber.obj F)), ∃ n : ℕ, p ^ n • x = 0

/-- **The eight curve-cohomology assertions** `C(X, F) = C₁(X, F) ∧ ⋯ ∧ C₈(X, F)` for a
`k`-scheme `f : X ⟶ Spec k` and a sheaf `F` of `Λ`-modules on `X_ét`, where `Hᵠ(X, F)` is the
cohomology of the underlying abelian sheaf of `F`. They are meant for `k` algebraically
closed, `X` a curve over `k` (`AlgebraicGeometry.IsCurve`) and `F` torsion; each field
carries the hypotheses of the corresponding assertion.
(blueprint: `def-weil-pbc-eight-curve-assertions`) -/
structure IsCurve.Assertions {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) : Prop where
  /-- `C₁`: `Hᵠ(X, F) = 0` for `q > 2`. -/
  subsingleton_of_two_lt (q : ℕ) (hq : 2 < q) :
    Subsingleton (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q)
  /-- `C₂`: `Hᵠ(X, F) = 0` for `q > 1` when `X` is affine. -/
  subsingleton_of_one_lt_of_isAffine [IsAffine X] (q : ℕ) (hq : 1 < q) :
    Subsingleton (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q)
  /-- `C₃`: `Hᵠ(X, F) = 0` for `q > 1` when `char k = p > 0` and `F` is `p`-primary. -/
  subsingleton_of_one_lt_of_isPrimaryTorsionSheaf (p : ℕ) [Fact p.Prime] [CharP k p]
    (hF : Scheme.IsPrimaryTorsionSheaf Λ F p) (q : ℕ) (hq : 1 < q) :
    Subsingleton (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q)
  /-- `C₄`: `Hᵠ(X, F)` is finite when `F` is constructible with torsion prime to `char k`. -/
  finite_of_isTorsionSheafOfInvertibleOrder [Scheme.IsConstructibleSheaf F]
    [Scheme.IsTorsionModuleSheafOfInvertibleOrder (Spec (.of k)) F] (q : ℕ) :
    Finite (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q)
  /-- `C₅`: `Hᵠ(X, F)` is finite when `X` is proper and `F` is constructible. -/
  finite_of_isProper [IsProper f] [Scheme.IsConstructibleSheaf F] (q : ℕ) :
    Finite (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q)
  /-- `C₆`: the pullback `Hᵠ(X, F) ⟶ Hᵠ(X_{k'}, F|)` is bijective for every algebraically
  closed extension `k'/k` when the torsion of `F` is prime to `char k`. -/
  bijective_cohomologyMap_of_isTorsionSheafOfInvertibleOrder
    [Scheme.IsTorsionModuleSheafOfInvertibleOrder (Spec (.of k)) F]
    (k' : Type u) [Field k'] [IsAlgClosed k'] {X' : Scheme.{u}} {ι : Spec (.of k') ⟶ Spec (.of k)}
    {f' : X' ⟶ Spec (.of k')} {ι' : X' ⟶ X} (h : IsPullback ι' f' f ι) (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap ι'
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q)
  /-- `C₇`: the pullback `Hᵠ(X, F) ⟶ Hᵠ(X_{k'}, F|)` is bijective for every algebraically
  closed extension `k'/k` when `X` is proper. -/
  bijective_cohomologyMap_of_isProper [IsProper f]
    (k' : Type u) [Field k'] [IsAlgClosed k'] {X' : Scheme.{u}} {ι : Spec (.of k') ⟶ Spec (.of k)}
    {f' : X' ⟶ Spec (.of k')} {ι' : X' ⟶ X} (h : IsPullback ι' f' f ι) (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap ι'
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q)
  /-- `C₈`: the restriction `H²(X, F) ⟶ H²(W, F|_W)` is surjective for every open
  immersion `a : W ⟶ X`. -/
  surjective_cohomologyMap_of_isOpenImmersion {W : Scheme.{u}} (a : W ⟶ X) [IsOpenImmersion a] :
    Function.Surjective (Etale.cohomologyMap a
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) 2)

end AlgebraicGeometry

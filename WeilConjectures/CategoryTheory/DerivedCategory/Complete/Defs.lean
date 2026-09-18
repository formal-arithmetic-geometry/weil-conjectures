/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.RingTheory.AdicCompletion.Basic

/-!

# Derived complete objects of the derived category of étale sheaves of modules

Let `X` be a scheme, let `R` be a commutative ring and let `I` be an ideal of `R`, the
intended case being that `R` is `I`-adically complete — for instance the ring of integers
`𝒪_E` of a finite extension of `ℚ_ℓ`, with `I` its maximal ideal. This file defines what it
means for an object `K` of the derived category

```
  D(X_ét, R) := DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat R))
```

of étale sheaves of `R`-modules on `X` to be *derived complete*: that `K` is the limit of
its reductions `K ⊗ᴸ R/Iⁿ`.

The tower of reductions and the maps into it are built as a chain of cones, each the image
of the previous one under a functor:

* `Ideal.quotPowCone I`, the quotient maps `R ⟶ R ⧸ Iⁿ`, a cone over the tower
  `Ideal.quotPowFunctor I` in `ModuleCat R` whose point is the monoidal unit
  `𝟙_ (ModuleCat R) = R`. If `R` is `I`-adically complete this cone is a limit cone
  (`Ideal.isLimitQuotPowCone`), which is the classical completeness of `R` in the language
  of limits;
* `AlgebraicGeometry.Etale.quotPowCone I X`, its image under the constant sheaf functor
  `constantSheaf X.smallEtaleTopology (ModuleCat R)`, whose point is the monoidal unit of
  the category of étale sheaves, the constant sheaf on `R = 𝟙_ (ModuleCat R)` being that
  unit;
* `AlgebraicGeometry.Etale.derivedCompletionCone I X K`, the image of the previous cone
  under `DerivedCategory.singleFunctor _ 0` and then `K ⊗ᴸ -`, with its point moved to `K`
  itself along

  ```
    K  ≅  K ⊗ᴸ 𝟙_ D(X_ét, R)  ⟶  K ⊗ᴸ (R in degree 0),
  ```

  the second map coming from the unit `ε` of the lax monoidal structure of the localization
  functor `Q`. Its legs are therefore the reduction maps `K ⟶ K ⊗ᴸ R/Iⁿ`, and its point is
  `K`.

The object `K` is *derived complete* when this last cone is a limit cone, i.e. when the
canonical map

```
  K ⟶ R lim_n (K ⊗ᴸ R/Iⁿ)
```

is an isomorphism. Asking that the cone be a limit cone, rather than that a map into a
chosen limit be invertible, means the definition does not have to assume that the limit
exists; `AlgebraicGeometry.Etale.derivedComplete_iff_isIso_lift` gives the isomorphism
statement whenever it does. Derived completeness of `K` does not presuppose completeness of
`R`, and the definition does not assume `IsAdicComplete I R`.

## Main definitions

- `Ideal.quotPowFunctor` and `Ideal.quotPowCone` : the tower `n ↦ R ⧸ Iⁿ` in `ModuleCat R`
  and the cone over it given by the quotient maps out of the monoidal unit.
- `AlgebraicGeometry.Etale.quotPowFunctor` and `AlgebraicGeometry.Etale.quotPowCone` : the
  same tower and cone in the category of étale sheaves of `R`-modules, through the constant
  sheaf functor.
- `AlgebraicGeometry.Etale.derivedQuotPowFunctor` : the tower `n ↦ R/Iⁿ` in `D(X_ét, R)`.
- `AlgebraicGeometry.Etale.derivedCompletionCone` : the cone `K ⟶ K ⊗ᴸ R/Iⁿ`, with point
  `K`.
- `AlgebraicGeometry.Etale.derivedComplete` : the object property of being derived complete.

## Main results

- `Ideal.isLimitQuotPowCone` : if `R` is `I`-adically complete then `R` is the limit of the
  tower `n ↦ R ⧸ Iⁿ`.
- `AlgebraicGeometry.Etale.derivedComplete_iff_isIso_lift` : when `R lim_n (K ⊗ᴸ R/Iⁿ)`
  exists, derived completeness of `K` says exactly that the canonical map
  `K ⟶ R lim_n (K ⊗ᴸ R/Iⁿ)` is an isomorphism.

## Implementation notes

The development is stated for the small étale site, which is the site for which this
repository supplies the whole monoidal package as global instances: the monoidal structure
on étale sheaves (`AlgebraicGeometry.Etale.sheafMonoidalCategory`), its braiding and
closedness (`AlgebraicGeometry.Etale.sheafMonoidalClosed`) and functorial flat resolutions
(`AlgebraicGeometry.Etale.hasFunctorialFlatResolution_sheaf`), from which
`DerivedCategory.hasDerivedMonoidalCategory` produces the derived tensor product on
`D(X_ét, R)` and the lax monoidal structure of `Q`. Nothing here activates a local instance
or assumes extra structure on the sheaf category: the only hypothesis beyond `X` and `R` is
`Abelian.HasFunctorialFlatResolution (ModuleCat R)`, on the *coefficient* category, which
is what the étale instance above takes as input.

Mathlib's `IsAdicComplete` API is phrased in terms of the quotients `M ⧸ (Iⁿ • ⊤)` of a
module `M`, whereas the tower here is phrased in terms of the ideal quotients `R ⧸ Iⁿ`,
which is the form in which it is tensored downstream. The two are compared by
`Ideal.quotSmulTopEquiv`, which is where `Iⁿ • (⊤ : Submodule R R) = Iⁿ` is used; every
compatibility with it holds by `rfl`, both sides being quotients of `R` by propositionally
equal submodules.

-/

@[expose] public section

universe w v₁ u₁ u

open CategoryTheory Limits MonoidalCategory Opposite AlgebraicGeometry

namespace Ideal

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The tower `n ↦ R ⧸ Iⁿ` of quotients by the powers of an ideal `I`, as a functor
`ℕᵒᵖ ⥤ ModuleCat R`. The transition map attached to `m ≤ n` is the projection
`R ⧸ Iⁿ ⟶ R ⧸ Iᵐ`. -/
noncomputable def quotPowFunctor : ℕᵒᵖ ⥤ ModuleCat.{u} R where
  obj n := ModuleCat.of R (R ⧸ I ^ n.unop)
  map f := ModuleCat.ofHom (Submodule.factor (Ideal.pow_le_pow_right (leOfHom f.unop)))
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- The tower `n ↦ R ⧸ Iⁿ` together with the quotient maps out of `R`, as a cone whose
point is the monoidal unit `𝟙_ (ModuleCat R) = R`. -/
noncomputable def quotPowCone : Cone (quotPowFunctor I) where
  pt := 𝟙_ (ModuleCat.{u} R)
  π :=
    { app n := ModuleCat.ofHom (Submodule.mkQ (I ^ n.unop))
      naturality _ _ _ := by ext; rfl }

/-- The quotient `R ⧸ (Iⁿ • ⊤)` used by mathlib's `IsAdicComplete` API is the quotient
`R ⧸ Iⁿ` used by `Ideal.quotPowFunctor`: the submodule `Iⁿ • (⊤ : Submodule R R)` is the
ideal `Iⁿ`. -/
noncomputable def quotSmulTopEquiv (n : ℕ) :
    (R ⧸ (I ^ n • ⊤ : Submodule R R)) ≃ₗ[R] (R ⧸ I ^ n) :=
  Submodule.quotEquivOfEq _ _ (by simp)

variable {I}

/-- The family of maps into the mathlib model `R ⧸ (Iⁿ • ⊤)` of the tower attached to a
cone over `Ideal.quotPowFunctor`; this is the input of `IsAdicComplete.lift`. -/
noncomputable def quotPowConeFamily (s : Cone (quotPowFunctor I)) (n : ℕ) :
    s.pt →ₗ[R] R ⧸ (I ^ n • ⊤ : Submodule R R) :=
  (quotSmulTopEquiv I n).symm.toLinearMap ∘ₗ (s.π.app (op n)).hom

lemma quotPowConeFamily_compat (s : Cone (quotPowFunctor I)) {m n : ℕ} (hle : m ≤ n) :
    Submodule.factorPow I R hle ∘ₗ quotPowConeFamily s n = quotPowConeFamily s m := by
  have hs : Submodule.factor (Ideal.pow_le_pow_right hle) ∘ₗ (s.π.app (op n)).hom
      = (s.π.app (op m)).hom :=
    congrArg ModuleCat.Hom.hom (s.w (op (homOfLE hle) : (op n : ℕᵒᵖ) ⟶ op m))
  have h : Submodule.factorPow I R hle ∘ₗ (quotSmulTopEquiv I n).symm.toLinearMap =
      (quotSmulTopEquiv I m).symm.toLinearMap ∘ₗ
        Submodule.factor (Ideal.pow_le_pow_right hle) := by
    ext; rfl
  rw [quotPowConeFamily, quotPowConeFamily, ← LinearMap.comp_assoc, h, LinearMap.comp_assoc,
    hs]

variable (I) [IsAdicComplete I R]

/-- If `R` is `I`-adically complete, then `R` is the limit of the tower `n ↦ R ⧸ Iⁿ` along
the quotient maps. This is `IsAdicComplete` in the language of limits of `R`-modules: the
lift is `IsAdicComplete.lift` and its uniqueness is `IsAdicComplete.eq_lift`. -/
noncomputable def isLimitQuotPowCone : IsLimit (quotPowCone I) where
  lift s := ModuleCat.ofHom
    (IsAdicComplete.lift I (quotPowConeFamily s) (quotPowConeFamily_compat s))
  fac s n := by
    ext x
    exact (quotSmulTopEquiv I n.unop).symm.injective
      (IsAdicComplete.mk_lift I (quotPowConeFamily_compat s) n.unop x)
  uniq s m hm := by
    ext x
    refine congrFun (congrArg _ (IsAdicComplete.eq_lift I (quotPowConeFamily_compat s)
      (F := m.hom) fun n ↦ ?_)) x
    have h : (quotSmulTopEquiv I n).symm.toLinearMap ∘ₗ Submodule.mkQ (I ^ n) =
        Submodule.mkQ (I ^ n • ⊤ : Submodule R R) := by ext; rfl
    rw [quotPowConeFamily, ← congrArg ModuleCat.Hom.hom (hm (op n)), ← h]
    rfl

end Ideal

section Aux

/- An auxiliary construction, stated for a variable category rather than for the concrete
category of étale sheaves. This is not gratuitous generality: once `A` is the concrete
category of étale sheaves, the monoidal unit of `CochainComplex A ℤ` is a term the kernel
cannot unfold within the default budget, so the concrete development below never mentions
it and only applies this definition. -/

section SingleFunctor

variable (A : Type u₁) [Category.{v₁} A] [Abelian A] [HasColimitsOfSize.{0, 0} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
  [HasDerivedCategory.{w} A]
  [DerivedCategory.Qh.HasDerivedMonoidalCategory
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]

/-- The comparison from the monoidal unit of the derived category of `A` to the monoidal
unit of `A` placed in degree `0`. It is the unit of the lax monoidal structure of the
localization functor `Q`: the monoidal unit of `CochainComplex A ℤ` is by definition the
unit of `A` in degree `0`, and `Q` of a complex concentrated in degree `0` is by definition
`DerivedCategory.singleFunctor A 0` of its value. -/
noncomputable def DerivedCategory.εSingleFunctorZero :
    𝟙_ (DerivedCategory A) ⟶ (DerivedCategory.singleFunctor A 0).obj (𝟙_ A) :=
  Functor.LaxMonoidal.ε DerivedCategory.Q

end SingleFunctor

end Aux

namespace AlgebraicGeometry.Etale

open Scheme

variable {R : Type (u + 1)} [CommRing R] (I : Ideal R) (X : Scheme.{u})

/-- The tower `n ↦ R/Iⁿ` of constant étale sheaves of `R`-modules on `X`, the image of the
tower `Ideal.quotPowFunctor` under the constant sheaf functor. -/
noncomputable def quotPowFunctor :
    ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R) :=
  Ideal.quotPowFunctor I ⋙ constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)

/-- The tower `n ↦ R/Iⁿ` of constant étale sheaves together with the quotient maps out of
the monoidal unit, the image of `Ideal.quotPowCone` under the constant sheaf functor. Its
point is `𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat R))`, since the constant sheaf on
`R = 𝟙_ (ModuleCat R)` is the monoidal unit of the category of étale sheaves. -/
noncomputable def quotPowCone : Cone (quotPowFunctor I X) :=
  (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).mapCone (Ideal.quotPowCone I)

@[simp]
lemma quotPowCone_pt :
    (quotPowCone I X).pt = 𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) := rfl

variable [Abelian.HasFunctorialFlatResolution (ModuleCat.{u + 1} R)]

/-- The tower `n ↦ R/Iⁿ` of constant étale sheaves, viewed in the derived category
`D(X_ét, R)` through `DerivedCategory.singleFunctor _ 0`. -/
noncomputable def derivedQuotPowFunctor :
    ℕᵒᵖ ⥤ DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) :=
  quotPowFunctor I X ⋙ DerivedCategory.singleFunctor _ 0
/-
/-- The reduction maps `K ⟶ K ⊗ᴸ R/Iⁿ`, as a cone over `derivedQuotPowFunctor` **whose
point is `K` itself**: the cone `Etale.quotPowCone` pushed into the derived category by
`DerivedCategory.singleFunctor _ 0` and tensored on the left with `K`, with `K` itself as
its point: the leg at `n` is

```
  K  ≅  K ⊗ᴸ 𝟙_ D(X_ét, R)  ⟶  K ⊗ᴸ (R in degree 0)  ⟶  K ⊗ᴸ R/Iⁿ,
```

the middle map being `DerivedCategory.εSingleFunctorZero`. -/
noncomputable def derivedCompletionCone
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    Cone (derivedQuotPowFunctor I X ⋙ tensorLeft K) where
  pt := K
  π :=
    { app n := (ρ_ K).inv ≫ K ◁ (DerivedCategory.εSingleFunctorZero _ ≫
        (DerivedCategory.singleFunctor _ 0).map ((quotPowCone I X).π.app n))
      naturality _ _ _ := by
        simp [derivedQuotPowFunctor, ← MonoidalCategory.whiskerLeft_comp,
          ← Functor.map_comp] }

@[simp]
lemma derivedCompletionCone_pt
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (derivedCompletionCone I X K).pt = K := rfl

/-- An object `K` of the derived category of étale sheaves of `R`-modules on `X` is
*derived complete* with respect to the ideal `I` if the cone `K ⟶ K ⊗ᴸ R/Iⁿ` of
`Etale.derivedCompletionCone`, whose point is `K`, is a limit cone: `K` is the limit of its
reductions modulo the powers of `I`. Equivalently, when that limit exists,

```
  K ⟶ R lim_n (K ⊗ᴸ R/Iⁿ)
```

is an isomorphism (`Etale.derivedComplete_iff_isIso_lift`). The intended setting is that
`R` is `I`-adically complete, which by `Ideal.isLimitQuotPowCone` says that `R` is itself
the limit of the tower `n ↦ R/Iⁿ`; the definition does not need that hypothesis. -/
noncomputable def derivedComplete :
    ObjectProperty (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :=
  fun K ↦ Nonempty (IsLimit (derivedCompletionCone I X K))

variable {I X}

lemma derivedComplete_iff
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    derivedComplete I X K ↔ Nonempty (IsLimit (derivedCompletionCone I X K)) := Iff.rfl

/-- If the limit `R lim_n (K ⊗ᴸ R/Iⁿ)` exists, then `K` is derived complete precisely when
the canonical map `K ⟶ R lim_n (K ⊗ᴸ R/Iⁿ)` is an isomorphism. -/
lemma derivedComplete_iff_isIso_lift
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)))
    [HasLimit (derivedQuotPowFunctor I X ⋙ tensorLeft K)] :
    derivedComplete I X K ↔
      IsIso (limit.lift (derivedQuotPowFunctor I X ⋙ tensorLeft K)
        (derivedCompletionCone I X K)) :=
  (limit.isLimit (derivedQuotPowFunctor I X ⋙ tensorLeft K)).nonempty_isLimit_iff_isIso_lift
-/
end AlgebraicGeometry.Etale

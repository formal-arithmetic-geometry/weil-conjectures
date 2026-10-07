/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfSize
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!

# Torsion étale sheaves and torsion cohomology

Let `Λ` be a commutative ring and `X` a scheme. This file defines the two
torsion conditions entering the statement of the proper base change theorem:

- `AlgebraicGeometry.Scheme.IsTorsionSheaf`: a sheaf `F` of `Λ`-modules on the small
  étale site of `X` is *torsion* if the stalk of `F` at every geometric point of `X` is
  a torsion abelian group. A geometric point `Spec Ω ⟶ X`, with `Ω` a separably closed
  field, induces a point of the small étale site (`Scheme.pointSmallEtale`), and the
  stalk of `F` is its fiber `CategoryTheory.GrothendieckTopology.Point.sheafFiber` at
  this point. Since the geometric points form a conservative family, this stalkwise
  condition agrees with the classical definition [Stacks 03SA] that `F` is the filtered
  union of its `n`-torsion subsheaves.
- `AlgebraicGeometry.Etale.DerivedCategory.Plus.torsionHomology`: the property of an
  object of the bounded below derived category of étale sheaves of `Λ`-modules that all
  its cohomology sheaves are torsion.
- `AlgebraicGeometry.Scheme.IsTorsionSheafOfPrimes` and
  `AlgebraicGeometry.Etale.DerivedCategoryPlusTorsionOfPrimes`: `P`-torsion sheaves, for a set
  `P` of primes, and the category `D⁺_P-tor(X, Λ)` of bounded below complexes with `P`-torsion
  cohomology sheaves.
- `AlgebraicGeometry.Scheme.IsTorsionSheafOfInvertibleOrder`: the refinement of
  `IsTorsionSheaf` in which the orders are required to be invertible on a second scheme
  `S`. This is the coefficient condition of the smooth base change theorem, and it
  implies `IsTorsionSheaf`. Such a sheaf is the filtered colimit of subsheaves killed by
  integers invertible on `S`
  (`AlgebraicGeometry.Scheme.IsTorsionSheafOfInvertibleOrder.exists_isColimit`).

Torsion refers throughout to the underlying abelian group, not to the `Λ`-module
structure: for `Λ = ℤ` the definition specializes to torsion abelian sheaves, the
setting of the classical proper base change theorem [Stacks 0DDE], and for a coefficient
ring `Λ` which is torsion as an additive group — in particular for the finite rings
`Λ = ℤ/ℓⁿℤ` of the `ℓ`-adic formalism — every sheaf of `Λ`-modules is torsion
(`AlgebraicGeometry.Scheme.IsTorsionSheaf.of_isTorsion`).

The design follows `AlgebraicGeometry.Scheme.IsFiniteSheaf` of
`WeilConjectures.ConstructibleSheaf.Defs` (stalkwise condition at geometric points) and
`AlgebraicGeometry.Etale.DerivedCategory.constructibleHomology` of
`WeilConjectures.DerivedCategory.Constructible` (homologywise `ObjectProperty` on a
derived category).

Following the convention of the `SixFunctors` folder, the coefficient category has
`Hom`-types in the universe `u + 1`, one above the universe `u` of the base schemes: it
is `ModuleCat.{u + 1} Λ` for a commutative ring `Λ : Type (u + 1)`, mathlib insisting
that the ring and the modules live in the same universe. The `Type u`-valued geometric
points of the small étale site nevertheless have fibers in `ModuleCat.{u + 1} Λ`, the
`u`-indexed filtered colimits computing them being obtained by shrinking from the
`u + 1`-indexed ones, see
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfSize`.

-/

@[expose] public section

universe w u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

section TorsionSheaf

/-- A sheaf `F` of `Λ`-modules on the small étale site of `X` is *torsion* if the stalk
of `F` at every geometric point of `X` is a torsion abelian group, i.e. every element of
every geometric stalk is killed by a positive integer. Torsion refers to the underlying
abelian group of the stalk, not to its `Λ`-module structure; for `Λ = ℤ` this is the
classical notion of a torsion abelian sheaf [Stacks 03SA]. -/
class Scheme.IsTorsionSheaf {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) : Prop where
  isTorsion_sheafFiber (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    IsAddTorsion (↥((pointSmallEtale s).sheafFiber.obj F))

/-- If the coefficient ring `Λ` is torsion as an additive group — in particular if `Λ`
is finite, e.g. `Λ = ℤ/ℓⁿℤ` — then every sheaf of `Λ`-modules on the small étale site is
torsion: every stalk is a `Λ`-module, and is killed elementwise by the additive order of
`1 : Λ`. -/
lemma Scheme.IsTorsionSheaf.of_isTorsion {Λ : Type (u + 1)} [CommRing Λ]
    (hΛ : IsAddTorsion Λ) {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsTorsionSheaf F where
  isTorsion_sheafFiber _ _ _ _ := IsAddTorsion.module_of_torsion Λ _ hΛ

/-- Every sheaf of modules over a finite coefficient ring is torsion. -/
instance {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) : IsTorsionSheaf F :=
  .of_isTorsion isAddTorsion_of_finite F

/-- A quotient of a torsion sheaf is torsion. -/
lemma Scheme.IsTorsionSheaf.of_epi {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (π : F ⟶ G) [Epi π]
    [IsTorsionSheaf F] : IsTorsionSheaf G where
  isTorsion_sheafFiber Ω _ _ s x := by
    have : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
      hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
    have :=
      ((pointSmallEtale s).skyscraperSheafAdjunction (A := ModuleCat.{u + 1} Λ)).isLeftAdjoint
    obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective
      ((pointSmallEtale s).sheafFiber.map π)).mp inferInstance x
    obtain ⟨n, hn, hy⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1
      (IsTorsionSheaf.isTorsion_sheafFiber (F := F) Ω s y)
    exact isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, by rw [← map_nsmul, hy, map_zero]⟩

open Etale in
/-- The pullback of a torsion sheaf of `Λ`-modules is torsion: the stalk of `f^* F` at a
geometric point `s` is the stalk of `F` at `s ≫ f`. -/
instance isTorsionSheaf_upperStar {Λ : Type (u + 1)} [CommRing Λ] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsTorsionSheaf F] :
    IsTorsionSheaf ((f)^*[ModuleCat.{u + 1} Λ].obj F) where
  isTorsion_sheafFiber Ω _ _ s :=
    IsAddTorsion.of_surjective
      (f := ((Etale.upperStarCompSheafFiberIso _ f s).app F).toLinearEquiv.symm.toAddMonoidHom)
      (LinearEquiv.surjective _) (IsTorsionSheaf.isTorsion_sheafFiber Ω (s ≫ f))

/-- A sheaf `F` of `Λ`-modules on the small étale site of `T` is *torsion of orders
invertible on `S`*, for a second scheme `S`, if every element of every geometric stalk of
`F` is killed by a positive integer which is invertible on `S`, i.e. which is a unit of
`Γ(S, ⊤)` (blueprint `sk-def-smooth`, "allowed torsion"). No common annihilator is required,
and invertibility is read globally on `S`, not only near the support of `F`.

This strengthening of `AlgebraicGeometry.Scheme.IsTorsionSheaf` is the coefficient
condition of the smooth base change theorem, where `T` lies over `S` along the morphism
`g : T ⟶ S` of the Cartesian square and the smooth morphism is the one with target `S`.
For `Λ = ℤ/nℤ` with `n` invertible on `S` every sheaf of `Λ`-modules satisfies it, and a
general such sheaf is the filtered union of its `n`-torsion subsheaves over the integers
`n` invertible on `S`. -/
class Scheme.IsTorsionSheafOfInvertibleOrder {Λ : Type (u + 1)} [CommRing Λ] (S : Scheme.{u})
    {T : Scheme.{u}} (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) : Prop where
  exists_isUnit_nsmul_eq_zero (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ T)
    (x : ↥((pointSmallEtale s).sheafFiber.obj F)) :
    ∃ n : ℕ, 0 < n ∧ IsUnit (n : Γ(S, ⊤)) ∧ n • x = 0

/-- A sheaf which is torsion of orders invertible on some scheme `S` is in particular a
torsion sheaf, so that the coefficients allowed by smooth base change are among those
allowed by proper base change. This is not an instance: the scheme `S` cannot be
recovered from the conclusion. -/
lemma Scheme.IsTorsionSheaf.of_isTorsionSheafOfInvertibleOrder
    {Λ : Type (u + 1)} [CommRing Λ] (S : Scheme.{u}) {T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsTorsionSheafOfInvertibleOrder S F] : IsTorsionSheaf F where
  isTorsion_sheafFiber Ω _ _ s x := by
    obtain ⟨n, hn, -, hx⟩ :=
      Scheme.IsTorsionSheafOfInvertibleOrder.exists_isUnit_nsmul_eq_zero (S := S) Ω s x
    exact isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, hx⟩

/-- A sheaf `F` of `Λ`-modules on the small étale site of `X` is *`P`-torsion*, for a set `P`
of primes, if every element of every geometric stalk of `F` is killed by a positive integer all
of whose prime divisors lie in `P`. This is the condition on the cohomology sheaves in the
categories with allowable torsion of blueprint `sbc-def-derived-categories-with-allowable-torsion`
and `sk-def-sf-categories`. -/
class Scheme.IsTorsionSheafOfPrimes (P : Set ℕ) {Λ : Type (u + 1)} [CommRing Λ]
    {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) : Prop where
  exists_nsmul_eq_zero (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (x : ↥((pointSmallEtale s).sheafFiber.obj F)) :
    ∃ n : ℕ, 0 < n ∧ (∀ p ∈ n.primeFactors, p ∈ P) ∧ n • x = 0

/-- A `P`-torsion sheaf is in particular a torsion sheaf. This is not an instance: the set `P`
cannot be recovered from the conclusion. -/
lemma Scheme.IsTorsionSheaf.of_isTorsionSheafOfPrimes (P : Set ℕ) {Λ : Type (u + 1)}
    [CommRing Λ] {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsTorsionSheafOfPrimes P F] : IsTorsionSheaf F where
  isTorsion_sheafFiber Ω _ _ s x := by
    obtain ⟨n, hn, -, hx⟩ := Scheme.IsTorsionSheafOfPrimes.exists_nsmul_eq_zero (P := P) Ω s x
    exact isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, hx⟩

/-- A torsion sheaf `F` of `Λ`-modules is the point of a colimit cocone over a filtered diagram
of sheaves, each of which is killed by some positive integer.

This is blueprint `lemma-weil-pbc-torsion-filtered-union`: `F` is the colimit of its
`n`-torsion subsheaves `F[n] = ker (n : F ⟶ F)` over the positive integers ordered by
divisibility, because every local section of `F` is, locally, killed by a positive integer;
this lemma only records the existence of some such diagram, which is the form in which it is
used. -/
theorem Scheme.IsTorsionSheaf.exists_isColimit (Λ : Type (u + 1)) [CommRing Λ] {T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Scheme.IsTorsionSheaf F] :
    ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J)
      (D : J ⥤ Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (c : Cocone D)
      (_ : IsColimit c), c.pt = F ∧ ∀ j, ∃ n : ℕ, 0 < n ∧ n • 𝟙 (D.obj j) = 0 :=
  sorry

/-- A sheaf `F` of `Λ`-modules which is torsion of orders invertible on `S` is the point of a
colimit cocone over a filtered diagram of sheaves, each of which is killed by some positive
integer `n` invertible on `S`.

This follows from blueprint `lemma-weil-pbc-torsion-filtered-union`, which says that `F` is the
colimit of its `n`-torsion subsheaves `F[n] = ker (n : F ⟶ F)` over the positive integers
ordered by divisibility; this lemma only records the existence of some such diagram, which is
the form in which it is used. -/
theorem Scheme.IsTorsionSheafOfInvertibleOrder.exists_isColimit
    (Λ : Type (u + 1)) [CommRing Λ] (S : Scheme.{u}) {T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsTorsionSheafOfInvertibleOrder S F] :
    ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J)
      (D : J ⥤ Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (c : Cocone D)
      (_ : IsColimit c), c.pt = F ∧
        ∀ j, ∃ n : ℕ, 0 < n ∧ IsUnit (n : Γ(S, ⊤)) ∧ n • 𝟙 (D.obj j) = 0 :=
  sorry

end TorsionSheaf

section TorsionHomology

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- `ℤ`-indexed colimits of `Λ`-modules are exact: `ℤ` is a filtered category, and
`ModuleCat.{u + 1} Λ` is Grothendieck abelian, hence satisfies `AB5` for shapes of size
`u + 1`; `AB5OfSize_of_univLE` brings that down to the shapes of size `0` in which `ℤ`
lives. It is not an instance in mathlib because in that generality instance search would
climb the universes. -/
instance : HasExactColimitsOfShape ℤ (ModuleCat.{u + 1} Λ) := by
  have : AB5OfSize.{0, 0} (ModuleCat.{u + 1} Λ) :=
    AB5OfSize_of_univLE.{0, 0, u + 1, u + 1} (ModuleCat.{u + 1} Λ)
  infer_instance

variable (X : Scheme.{u})
  [HasDerivedCategory.{w} (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))]

/-- An object of the bounded below derived category of étale sheaves of `Λ`-modules has
*torsion cohomology* if all its cohomology sheaves are torsion
(`AlgebraicGeometry.Scheme.IsTorsionSheaf`). This is the hypothesis on the coefficient
complex in the general proper base change theorem. -/
noncomputable def Etale.DerivedCategory.Plus.torsionHomology :
    ObjectProperty (DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  fun K ↦ ∀ n : ℤ, IsTorsionSheaf
    ((DerivedCategory.Plus.homologyFunctor
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) n).obj K)

/-- If the coefficient ring `Λ` is torsion as an additive group — in particular if `Λ`
is finite — then every object of the bounded below derived category of étale sheaves of
`Λ`-modules has torsion cohomology. -/
lemma Etale.DerivedCategory.Plus.torsionHomology_of_isTorsion (hΛ : IsAddTorsion Λ)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Etale.DerivedCategory.Plus.torsionHomology Λ X K :=
  fun _ ↦ .of_isTorsion hΛ _

/-- A torsion sheaf placed in degree `0` has torsion cohomology: its cohomology sheaf in
degree `0` is the sheaf itself, and all its other cohomology sheaves vanish. -/
lemma Etale.DerivedCategory.Plus.torsionHomology_singleFunctor_obj
    (I : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsTorsionSheaf I] :
    Etale.DerivedCategory.Plus.torsionHomology Λ X
      ((DerivedCategory.Plus.singleFunctor _ 0).obj I) := by
  intro n
  by_cases hn : n = 0
  · subst hn
    exact IsTorsionSheaf.of_epi (F := I)
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).inv.app I)
  · have hZ : IsZero ((DerivedCategory.Plus.homologyFunctor _ n).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj I)) :=
      IsZero.of_iso (HomologicalComplex.isZero_single_obj_homology _ _ _ _ hn)
        ((DerivedCategory.homologyFunctorFactors _ n).app _)
    have := hZ.epi (0 : I ⟶ _)
    exact IsTorsionSheaf.of_epi (0 : I ⟶ _)

/-- An object of the bounded below derived category of étale sheaves of `Λ`-modules has
*`P`-torsion cohomology*, for a set `P` of primes, if all its cohomology sheaves are `P`-torsion
(`AlgebraicGeometry.Scheme.IsTorsionSheafOfPrimes`). -/
noncomputable def Etale.DerivedCategory.Plus.torsionHomologyOfPrimes (P : Set ℕ) :
    ObjectProperty (DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  fun K ↦ ∀ n : ℤ, IsTorsionSheafOfPrimes P
    ((DerivedCategory.Plus.homologyFunctor
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) n).obj K)

/-- `P`-torsion cohomology is in particular torsion cohomology. -/
lemma Etale.DerivedCategory.Plus.torsionHomologyOfPrimes_le_torsionHomology (P : Set ℕ) :
    Etale.DerivedCategory.Plus.torsionHomologyOfPrimes Λ X P ≤
      Etale.DerivedCategory.Plus.torsionHomology Λ X :=
  fun _ hK n ↦ have := hK n; .of_isTorsionSheafOfPrimes P _

/-- Blueprint `sk-def-sf-categories`: Ambient categories and small subcategories.

The ambient category `D⁺_P-tor(X, Λ)` of bounded below complexes of étale sheaves of
`Λ`-modules whose cohomology sheaves have `P`-torsion geometric stalks, for a set `P` of primes,
as a full subcategory of `D⁺(X_ét, Λ)` (blueprint
`sbc-def-derived-categories-with-allowable-torsion`). -/
noncomputable def Etale.DerivedCategoryPlusTorsionOfPrimes (P : Set ℕ) : Type _ :=
  (Etale.DerivedCategory.Plus.torsionHomologyOfPrimes Λ X P).FullSubcategory

noncomputable instance (P : Set ℕ) : Category (Etale.DerivedCategoryPlusTorsionOfPrimes Λ X P) :=
  inferInstanceAs <|
    Category (Etale.DerivedCategory.Plus.torsionHomologyOfPrimes Λ X P).FullSubcategory

/-- The inclusion of `D⁺_P-tor(X, Λ)` into `D⁺(X_ét, Λ)`. -/
noncomputable def Etale.DerivedCategoryPlusTorsionOfPrimes.ι (P : Set ℕ) :
    Etale.DerivedCategoryPlusTorsionOfPrimes Λ X P ⥤
      DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (Etale.DerivedCategory.Plus.torsionHomologyOfPrimes Λ X P).ι

end TorsionHomology

end AlgebraicGeometry

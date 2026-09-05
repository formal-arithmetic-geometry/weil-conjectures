/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Abelian

/-!
# The derived category of `𝒪`-modules on the pro-étale site, and derived completeness

Let `Y` be a scheme and `𝒪` a commutative ring — in the application, the valuation ring
`𝒪_E` of a finite extension `E/ℚ_ℓ`. This file introduces

* `AlgebraicGeometry.Scheme.ProEt.ModuleSheaf Y 𝒪`, the category of sheaves of
  `𝒪`-modules on the small pro-étale site of `Y`, and
* `AlgebraicGeometry.Scheme.ProEt.ModuleDerived Y 𝒪`, its derived category
  `D(Y_proét, 𝒪)`,

and defines *derived `ℓ`-completeness* for objects of the latter.

## Derived completeness

Naive `ℓ`-adic completeness — asking that `K ≅ lim_n K/ℓⁿ` — is badly behaved in a derived
category, because `lim` is not exact. The derived replacement asks that the canonical map

`K ⟶ R lim_n (K ⊗^L_𝒪 𝒪/ℓⁿ)`

be an isomorphism. Rather than construct `R lim`, we use the standard equivalent
characterisation (Stacks 091N, Bhatt–Scholze 3.4): `K` is derived `ℓ`-complete if and only
if

`R Hom(𝒪[1/ℓ], K) = 0`,

that is, if and only if every map into `K` from a shift of the constant sheaf on the
`𝒪`-module `𝒪[1/ℓ]` vanishes. This is a `Prop` about `K`, needs neither `R lim` nor a
derived tensor product, and makes the good formal properties immediate: the derived
`ℓ`-complete objects are the right-orthogonal complement of a single object, hence a
strictly full triangulated subcategory closed under all limits that exist. Those
properties are proved here rather than assumed.

## Main definitions

* `AlgebraicGeometry.Scheme.ProEt.invSheaf`: the constant sheaf on `𝒪[1/ℓ]`.
* `AlgebraicGeometry.Scheme.ProEt.IsDerivedComplete`: derived `ℓ`-completeness.
* `AlgebraicGeometry.Scheme.ProEt.derivedComplete`: the same, as an `ObjectProperty`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry.Scheme.ProEt

variable (Y : Scheme.{u}) (O : Type u) [CommRing O]

/-- Sheaves of `𝒪`-modules on the small pro-étale site of `Y`. The coefficients are taken
in `Type (u + 1)`, one universe above the base schemes, because the pro-étale site is only
essentially small there. -/
abbrev ModuleSheaf : Type _ := Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} O)

/-- The derived category `D(Y_proét, 𝒪)` of sheaves of `𝒪`-modules on the pro-étale site
of `Y`. -/
abbrev ModuleDerived : Type _ := DerivedCategory (ModuleSheaf Y O)

variable (l : O)

/-- The constant sheaf on the `𝒪`-module `𝒪[1/ℓ]`. Since the constant-sheaf functor is a
left adjoint it commutes with the filtered colimit defining `𝒪[1/ℓ]`, so this is the sheaf
`colim (𝒪 --ℓ--> 𝒪 --ℓ--> ⋯)` obtained by inverting `ℓ` on the structure sheaf. -/
noncomputable def invSheaf : ModuleSheaf Y O :=
  (constantSheaf (ProEt.topology Y) (ModuleCat.{u + 1} O)).obj
    (ModuleCat.of O (ULift.{u + 1} (Localization.Away l)))

/-- `𝒪[1/ℓ]` as an object of the derived category, placed in degree `0`. -/
noncomputable def invObj : ModuleDerived Y O :=
  (DerivedCategory.singleFunctor (ModuleSheaf Y O) 0).obj (invSheaf Y O l)

/-- An object `K` of `D(Y_proét, 𝒪)` is **derived `ℓ`-complete** if `RHom(𝒪[1/ℓ], K) = 0`,
i.e. if every morphism into `K` from a shift of `𝒪[1/ℓ]` vanishes.

This is equivalent to the more familiar condition that `K ⟶ R lim_n (K ⊗^L 𝒪/ℓⁿ)` be an
isomorphism, and is the condition that makes an object of the derived category be
determined by its tower of reductions. It must not be confused with the underived
condition `K ≅ lim_n K/ℓⁿ`. -/
def IsDerivedComplete (K : ModuleDerived Y O) : Prop :=
  ∀ (n : ℤ) (f : (invObj Y O l)⟦n⟧ ⟶ K), f = 0

/-- Derived `ℓ`-completeness as a property of objects of `D(Y_proét, 𝒪)`. -/
def derivedComplete : ObjectProperty (ModuleDerived Y O) := IsDerivedComplete Y O l

variable {Y O l}

lemma isDerivedComplete_iff (K : ModuleDerived Y O) :
    IsDerivedComplete Y O l K ↔ ∀ (n : ℤ) (f : (invObj Y O l)⟦n⟧ ⟶ K), f = 0 := Iff.rfl

/-- Derived `ℓ`-completeness is invariant under isomorphism. -/
lemma IsDerivedComplete.of_iso {K L : ModuleDerived Y O} (hK : IsDerivedComplete Y O l K)
    (e : K ≅ L) : IsDerivedComplete Y O l L := by
  intro n f
  have : f ≫ e.inv = 0 := hK n _
  rw [← Category.comp_id f, ← e.inv_hom_id, ← Category.assoc, this, zero_comp]

instance : (derivedComplete Y O l).IsClosedUnderIsomorphisms where
  of_iso e hK := IsDerivedComplete.of_iso hK e

/-- Derived `ℓ`-complete objects are stable under shifts. -/
lemma IsDerivedComplete.shift {K : ModuleDerived Y O} (hK : IsDerivedComplete Y O l K)
    (m : ℤ) : IsDerivedComplete Y O l (K⟦m⟧) := by
  intro n f
  have h : (shiftFunctorAdd' (ModuleDerived Y O) n (-m) (n + -m) rfl).hom.app
      (invObj Y O l) ≫ (shiftFunctor (ModuleDerived Y O) (-m)).map f ≫
      (shiftFunctorCompIsoId (ModuleDerived Y O) m (-m) (by ring)).hom.app K = 0 :=
    hK (n + -m) _
  have h2 : (shiftFunctor (ModuleDerived Y O) (-m)).map f = 0 := by
    rw [← cancel_epi ((shiftFunctorAdd' (ModuleDerived Y O) n (-m) (n + -m) rfl).hom.app
        (invObj Y O l)), ← cancel_mono ((shiftFunctorCompIsoId (ModuleDerived Y O) m (-m)
        (by ring)).hom.app K)]
    simpa using h
  refine (shiftFunctor (ModuleDerived Y O) (-m)).map_injective ?_
  simpa using h2

/-- The zero object is derived `ℓ`-complete. -/
lemma isDerivedComplete_zero {K : ModuleDerived Y O} (hK : IsZero K) :
    IsDerivedComplete Y O l K := fun _ _ ↦ hK.eq_of_tgt _ _

/-- Derived `ℓ`-completeness is a two-out-of-three property in distinguished triangles: it
is the right-orthogonal complement of `𝒪[1/ℓ]`, so it is stable under cones. -/
lemma IsDerivedComplete.of_distTriang {T : Triangle (ModuleDerived Y O)}
    (hT : T ∈ distinguishedTriangles) (h₁ : IsDerivedComplete Y O l T.obj₁)
    (h₂ : IsDerivedComplete Y O l T.obj₂) : IsDerivedComplete Y O l T.obj₃ := by
  intro n f
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₃ T hT f (h₁.shift 1 n (f ≫ T.mor₃))
  rw [hg, h₂ n g, zero_comp]

section Reduction

variable (Y O l)

/-- A choice of cone of a morphism of `D(Y_proét, 𝒪)`. Cones are unique up to
(non-canonical) isomorphism, so any property of objects closed under isomorphism — such as
`IsDerivedComplete` — is independent of the choice. -/
noncomputable def coneOf {K L : ModuleDerived Y O} (f : K ⟶ L) : ModuleDerived Y O :=
  (Pretriangulated.distinguished_cocone_triangle f).choose

lemma exists_coneOf_distTriang {K L : ModuleDerived Y O} (f : K ⟶ L) :
    ∃ (g : L ⟶ coneOf Y O f) (h : coneOf Y O f ⟶ K⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distinguishedTriangles := by
  obtain ⟨g, h, hgh⟩ := (Pretriangulated.distinguished_cocone_triangle f).choose_spec
  exact ⟨g, h, hgh⟩

/-- The reduction `K ⊗^L_𝒪 𝒪/ℓⁿ` of an object of `D(Y_proét, 𝒪)`.

Since `𝒪/ℓⁿ` is the two-term complex `𝒪 --ℓⁿ--> 𝒪`, the derived tensor product with it is
the cone of multiplication by `ℓⁿ`; taking this as the definition avoids having to
construct a derived tensor product on sheaves of modules. -/
noncomputable def reduction (n : ℕ) (K : ModuleDerived Y O) : ModuleDerived Y O :=
  coneOf Y O ((l ^ n) • 𝟙 K)

/-- The defining distinguished triangle `K --ℓⁿ--> K ⟶ K/ℓⁿ ⟶ K[1]` of the reduction. -/
lemma exists_reduction_distTriang (n : ℕ) (K : ModuleDerived Y O) :
    ∃ (g : K ⟶ reduction Y O l n K) (h : reduction Y O l n K ⟶ K⟦(1 : ℤ)⟧),
      Triangle.mk ((l ^ n) • 𝟙 K) g h ∈ distinguishedTriangles :=
  exists_coneOf_distTriang Y O _

end Reduction

section BoundedConstructible

variable (Y O l)

/-- The reduction tower of `K` is *uniformly bounded constructible* with amplitude
`[a, b]` if every reduction `K ⊗^L 𝒪/ℓⁿ` is constructible and lies in the interval
`[a, b]` for the canonical t-structure, the interval being independent of `n`.

The uniformity is essential: asking each reduction to be bounded, with a bound allowed to
depend on `n`, is strictly weaker and is not the adic notion of boundedness. -/
def UniformlyBoundedConstructible (a b : ℤ) (K : ModuleDerived Y O) : Prop :=
  ∀ n : ℕ,
    DerivedCategory.TStructure.t.le b (reduction Y O l n K) ∧
    DerivedCategory.TStructure.t.ge a (reduction Y O l n K) ∧
    ProEtale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} O) Y
      (reduction Y O l n K)

/-- The objects of `Dᵇ_c(Y, 𝒪)`: the derived `ℓ`-complete objects of `D(Y_proét, 𝒪)`
whose reductions modulo `ℓⁿ` are constructible with a cohomological amplitude independent
of `n`. -/
def adicBoundedConstructible : ObjectProperty (ModuleDerived Y O) :=
  fun K ↦ IsDerivedComplete Y O l K ∧
    ∃ a b : ℤ, UniformlyBoundedConstructible Y O l a b K

/-- The **integral coefficient category** `Dᵇ_c(Y, 𝒪)`, realized as the full subcategory of
`D(Y_proét, 𝒪)` cut out by `adicBoundedConstructible`. -/
def AdicDerivedCategory : Type _ := (adicBoundedConstructible Y O l).FullSubcategory

noncomputable instance : Category (AdicDerivedCategory Y O l) :=
  inferInstanceAs <| Category (adicBoundedConstructible Y O l).FullSubcategory

noncomputable instance : Preadditive (AdicDerivedCategory Y O l) :=
  inferInstanceAs <| Preadditive (adicBoundedConstructible Y O l).FullSubcategory

noncomputable instance : Linear O (AdicDerivedCategory Y O l) :=
  inferInstanceAs <| Linear O (adicBoundedConstructible Y O l).FullSubcategory

/-- The inclusion of `Dᵇ_c(Y, 𝒪)` into `D(Y_proét, 𝒪)`. -/
noncomputable def AdicDerivedCategory.ι :
    AdicDerivedCategory Y O l ⥤ ModuleDerived Y O :=
  (adicBoundedConstructible Y O l).ι

end BoundedConstructible

end AlgebraicGeometry.Scheme.ProEt

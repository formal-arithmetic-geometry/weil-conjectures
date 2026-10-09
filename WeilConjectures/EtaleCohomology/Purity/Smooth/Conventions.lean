/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

/-!
# Conventions for smooth purity

This file fixes the twist-side vocabulary the smooth-purity chapter runs on: the Tate twist
`(m)` built from the sheaf `μ_n` of roots of unity, the twist-and-shift `K ↦ K(m)[2m]`, the
dualizing complex `ω_f = Rf^! Λ_Y`, and the *section invariant* `𝒞(g, s) = Ls^* ω_g` of a
morphism with a section. The constant complex `Λ_X`, finite Tor amplitude, `D^b_{ctf}` and
⊗-invertibility are framework-level notions and live in
`WeilConjectures.SixFunctors.Etale.Derived.Coefficients`. The dualizing complex
`ω_f = Rf^! Λ_Y` is the framework's `AlgebraicGeometry.Etale.dualizingComplex` for
`A = ModuleCat Λ`, the constant complex `Λ_Y` being the monoidal unit.

The coefficient stage is the finite one: a commutative ring `Λ` and the abelian category
`ModuleCat Λ`, so that `D(X_ét, Λ)` is
`DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat Λ))`. Every statement of the chapter
assumes moreover that `Λ` is finite and that its exponent is invertible on the schemes in
sight (`AlgebraicGeometry.HasInvertibleExponent`); without that hypothesis smooth purity is
false, already for `Λ = ℤ/p` over a base of characteristic `p`. The remaining stages `𝒪_E`,
`E` and `ℚ̄_ℓ` are the derived-complete and rationalized categories of
`WeilConjectures.CategoryTheory.DerivedCategory.Complete`, taken on the *pro-étale* site (the
blueprint makes no assertion for non-torsion coefficients on the étale site); purity is to be
transported to them in `WeilConjectures.EtaleCohomology.Purity.Smooth.Transport`.

## Implementation notes

The Tate twist is constructed from the sheaf of roots of unity
`μ_n = AlgebraicGeometry.Scheme.rootsOfUnitySheaf X n` of
`WeilConjectures.AlgebraicGeometry.Sites.Kummer`, with `n = ringChar Λ`: the Tate sheaf is
`Λ_X(1) = Λ ⊗_ℤ μ_n` (`AlgebraicGeometry.Etale.tateSheaf`, objectwise extension of scalars
followed by sheafification), `Λ_X(k)` for `k ≥ 0` is its `k`-th derived tensor power and
`Λ_X(-k) = RHom(Λ_X(k), Λ_X)`. The twist is thus an operation `K ↦ K(m) = K ⊗^L Λ_X(m)`, not a
parameter. Its structural properties — `Λ_X(m) ⊗ Λ_X(m') ≅ Λ_X(m + m')`, `Lf^* Λ_Y(m) ≅ Λ_X(m)`,
⊗-invertibility, membership in `D^b_{ctf}`, and the coherences between the identifications listed
in "Additivity and pullback of twists" of the framework chapter — hold only when the exponent of
`Λ` is invertible, and are stated under `AlgebraicGeometry.HasInvertibleExponent`. The
identifications `AlgebraicGeometry.Etale.tateObjectAddIso` and
`AlgebraicGeometry.Etale.leftDerivedUpperStarTateObjectIso` are data whose construction is not
yet formalised. The Kummer classes of units are the boundary maps of the Kummer sequence, in
`WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass`.

## Main definitions

- `AlgebraicGeometry.Etale.addCommGrpExtendScalars`, `AlgebraicGeometry.Etale.sheafExtendScalars`:
  extension of scalars `A ↦ Λ ⊗_ℤ A`, for abelian groups and for étale sheaves.
- `AlgebraicGeometry.Etale.tateSheaf`: the Tate sheaf `Λ ⊗_ℤ μ_n`.
- `AlgebraicGeometry.Etale.tateObject`: the twisting object `Λ_X(m)`.
- `AlgebraicGeometry.Etale.tateObjectAddIso`: `Λ_X(m) ⊗^L Λ_X(m') ≅ Λ_X(m + m')`.
- `AlgebraicGeometry.Etale.leftDerivedUpperStarTateObjectIso`: `Lf^* Λ_Y(m) ≅ Λ_X(m)`.
- `AlgebraicGeometry.Etale.tateTwist`: the twist `K ↦ K(m)`.
- `AlgebraicGeometry.Etale.twistShift`: `K ↦ K(m)[2m]`.
- `AlgebraicGeometry.Etale.shiftTateObjectAddIso`:
  `Λ_X(m)[2m] ⊗ Λ_X(m')[2m'] ≅ Λ_X(m + m')[2(m + m')]`.
- `AlgebraicGeometry.Etale.leftDerivedUpperStarConstantComplexIso`: `Lf^* Λ_Y ≅ Λ_X`.
- `AlgebraicGeometry.Etale.sectionInvariant`: `𝒞(g, s) = Ls^* ω_g`.

## Main statements

- `AlgebraicGeometry.Etale.isInvertible_tateObject`
- `AlgebraicGeometry.Etale.constructibleFiniteTor_tateObject`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- If the exponent of `Λ` is invertible on `X`, then so is its characteristic `ringChar Λ`,
which divides every integer killing `Λ`. -/
theorem _root_.AlgebraicGeometry.HasInvertibleExponent.isUnit_ringChar (X : Scheme.{u})
    [HasInvertibleExponent Λ X] : IsUnit ((ringChar Λ : ℕ) : Γ(X, ⊤)) := by
  obtain ⟨n, -, hΛ, hu⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ) (X := X)
  obtain ⟨k, rfl⟩ := ringChar.dvd hΛ
  rw [Nat.cast_mul] at hu
  exact isUnit_of_mul_isUnit_left hu

/-- Extension of scalars from abelian groups to `Λ`-modules, `A ↦ Λ ⊗_ℤ A`. -/
noncomputable def addCommGrpExtendScalars : AddCommGrpCat.{u + 1} ⥤ ModuleCat.{u + 1} Λ where
  obj A := ModuleCat.of Λ (TensorProduct ℤ Λ A)
  map f := ModuleCat.ofHom (LinearMap.baseChange Λ f.hom.toIntLinearMap)
  map_id A := by
    apply ModuleCat.hom_ext
    apply TensorProduct.AlgebraTensorModule.curry_injective
    ext x
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply TensorProduct.AlgebraTensorModule.curry_injective
    ext x
    rfl

instance : (addCommGrpExtendScalars Λ).Additive where
  map_add {_ _ f g} := by
    change ModuleCat.ofHom (LinearMap.baseChange Λ (f + g).hom.toIntLinearMap) =
      ModuleCat.ofHom _ + ModuleCat.ofHom _
    refine (congrArg ModuleCat.ofHom ?_).trans (ModuleCat.ofHom_add _ _)
    rw [← LinearMap.baseChange_add]
    rfl

variable (X : Scheme.{u})

/-- Extension of scalars `F ↦ Λ ⊗_ℤ F` from étale sheaves of abelian groups to étale sheaves of
`Λ`-modules: the objectwise extension of scalars, sheafified. -/
noncomputable abbrev sheafExtendScalars :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  Sheaf.composeAndSheafify X.smallEtaleTopology (addCommGrpExtendScalars Λ)

/-- Blueprint `sk-def-purity-conv`: Purity conventions and the rank-one datum

The *Tate sheaf* `Λ_X(1) = Λ ⊗_ℤ μ_n` on `X_ét`, where `n = ringChar Λ` and
`μ_n = AlgebraicGeometry.Scheme.rootsOfUnitySheaf X n` is the sheaf of `n`-th roots of unity.
When `n` is invertible on `X` it is locally free of rank one over `Λ`; as `n Λ = 0` it is also
`Λ ⊗_{ℤ/n} μ_n`, and for `n = ℓ^N` it is the sheaf `μ_{ℓ^N} ⊗_{ℤ/ℓ^N} Λ` of the blueprint. -/
-- TODO(unify): def:coefficient-twists
noncomputable def tateSheaf : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  (sheafExtendScalars Λ X).obj (X.rootsOfUnitySheaf (ringChar Λ))

/-- The non-negative tensor powers `Λ_X(k) = Λ_X(1)^{⊗ k}` of the Tate sheaf placed in degree
zero: `Λ_X(0) = Λ_X`, `Λ_X(1)` is the Tate sheaf and `Λ_X(k + 2) = Λ_X(k + 1) ⊗^L Λ_X(1)`. -/
noncomputable def tatePow :
    ℕ → DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  | 0 => constantComplex Λ X
  | 1 => (DerivedCategory.singleFunctor _ 0).obj (tateSheaf Λ X)
  | k + 2 => ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (tatePow (k + 1))).obj
      ((DerivedCategory.singleFunctor _ 0).obj (tateSheaf Λ X))

/-- Blueprint `sk-def-purity-conv`: Purity conventions and the rank-one datum

The *Tate twisting object* `Λ_X(m) ∈ D(X_ét, Λ)`: for `m = k ≥ 0` the `k`-th derived tensor
power of the Tate sheaf `Λ_X(1) = Λ ⊗_ℤ μ_n` (`AlgebraicGeometry.Etale.tatePow`), and for
`m = -k < 0` the dual `RHom(Λ_X(k), Λ_X)`. This is the twist of the framework chapter
(`def:coefficient-twists`); its good properties (invertibility, `Λ_X(m) ⊗ Λ_X(m') ≅
Λ_X(m + m')`, compatibility with pullback) need the exponent of `Λ` to be invertible. -/
-- TODO(unify): def:coefficient-twists
noncomputable def tateObject :
    ℤ → DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  | (k : ℕ) => tatePow Λ X k
  | Int.negSucc k =>
      ((derivedHom (ModuleCat.{u + 1} Λ) X).obj (Opposite.op (tatePow Λ X (k + 1)))).obj
        (constantComplex Λ X)

/-- `Λ_X(0)` is the constant complex, by definition. -/
noncomputable def tateObjectZeroIso : tateObject Λ X 0 ≅ constantComplex Λ X :=
  Iso.refl _

/-- `Λ_X(1)` is the Tate sheaf `Λ ⊗_ℤ μ_n` placed in degree zero, by definition. -/
noncomputable def tateObjectOneIso :
    tateObject Λ X 1 ≅ (DerivedCategory.singleFunctor _ 0).obj (tateSheaf Λ X) :=
  Iso.refl _

/-- Every Tate twisting object is ⊗-invertible, `Λ_X(m) ⊗^L Λ_X(-m) ≅ Λ_X`, when the exponent of
`Λ` is invertible on `X`: then `Λ_X(1)` is étale-locally isomorphic to `Λ_X`. -/
theorem isInvertible_tateObject [HasInvertibleExponent Λ X] (m : ℤ) :
    DerivedCategory.isInvertible Λ X (tateObject Λ X m) :=
  sorry

/-- For a finite coefficient ring whose exponent is invertible on `X`, every Tate twisting
object lies in `D^b_{ctf}(X, Λ)`: `Λ_X(m)` is a locally constant sheaf, locally free of rank one
over `Λ`, in degree zero (`def-coefficient-twists-detailed`). It is what lets the co-projection
of `sk-lem-coprojection` be applied to `L = Λ_X(m)[2m]`. -/
theorem constructibleFiniteTor_tateObject [Finite Λ] [HasInvertibleExponent Λ X] (m : ℤ) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X (tateObject Λ X m) :=
  sorry

/-- `Λ_X(m) ⊗^L Λ_X(m') ≅ Λ_X(m + m')`, which is what makes `Λ(c)[2c]` the `c`-th tensor
power of `Λ(1)[2]` in the Künneth iteration of `sk-prop-an`. For `m, m' ≥ 0` it is
associativity of the tensor product; for mixed signs it uses the invertibility of `Λ_X(1)`,
hence the hypothesis on the exponent of `Λ`. -/
noncomputable def tateObjectAddIso [HasInvertibleExponent Λ X] (m m' : ℤ) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (tateObject Λ X m)).obj (tateObject Λ X m') ≅
      tateObject Λ X (m + m') :=
  sorry

/-- The left unit law: `Λ_X(0) ⊗ Λ_X(m) ≅ Λ_X(m)` is the left unitor, through
`Λ_X(0) ≅ Λ_X`.

```
Λ_X(0) ⊗ Λ_X(m) ──tateObjectAddIso──▶ Λ_X(0 + m) = Λ_X(m)
       │                                     ‖
zero ⊗ 1                                     ‖
       ▼                                     ‖
 Λ_X ⊗ Λ_X(m) ───────────λ──────────────▶ Λ_X(m)
``` -/
theorem tateObjectAddIso_zero_left [HasInvertibleExponent Λ X] (m : ℤ) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).map (tateObjectZeroIso Λ X).hom).app
        (tateObject Λ X m) ≫ (λ_ (tateObject Λ X m)).hom =
      (tateObjectAddIso Λ X 0 m).hom ≫ eqToHom (by rw [zero_add]) :=
  sorry

/-- The right unit law: `Λ_X(m) ⊗ Λ_X(0) ≅ Λ_X(m)` is the right unitor, through
`Λ_X(0) ≅ Λ_X`.

```
Λ_X(m) ⊗ Λ_X(0) ──tateObjectAddIso──▶ Λ_X(m + 0) = Λ_X(m)
       │                                     ‖
1 ⊗ zero                                     ‖
       ▼                                     ‖
 Λ_X(m) ⊗ Λ_X ───────────ρ──────────────▶ Λ_X(m)
``` -/
theorem tateObjectAddIso_zero_right [HasInvertibleExponent Λ X] (m : ℤ) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (tateObject Λ X m)).map
        (tateObjectZeroIso Λ X).hom ≫ (ρ_ (tateObject Λ X m)).hom =
      (tateObjectAddIso Λ X m 0).hom ≫ eqToHom (by rw [add_zero]) :=
  sorry

/-- The associativity law for the products of twisting objects.

```
(Λ(a) ⊗ Λ(b)) ⊗ Λ(c) ───────α───────▶ Λ(a) ⊗ (Λ(b) ⊗ Λ(c))
        │                                      │
        ▼                                      ▼
 Λ(a + b) ⊗ Λ(c)                         Λ(a) ⊗ Λ(b + c)
        │                                      │
        ▼                                      ▼
 Λ((a + b) + c) ════════════════════════ Λ(a + (b + c))
``` -/
theorem tateObjectAddIso_assoc [HasInvertibleExponent Λ X] (a b c : ℤ) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).map (tateObjectAddIso Λ X a b).hom).app
        (tateObject Λ X c) ≫ (tateObjectAddIso Λ X (a + b) c).hom =
      (α_ (tateObject Λ X a) (tateObject Λ X b) (tateObject Λ X c)).hom ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (tateObject Λ X a)).map
          (tateObjectAddIso Λ X b c).hom ≫ (tateObjectAddIso Λ X a (b + c)).hom ≫
            eqToHom (by rw [add_assoc]) :=
  sorry

/-- The Tate twist `(m) : D(X_ét, Λ) ⥤ D(X_ét, Λ)`, tensoring with the twisting object
`Λ_X(m)`. -/
noncomputable def tateTwist (m : ℤ) :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (derivedTensor (ModuleCat.{u + 1} Λ) X).flip.obj (tateObject Λ X m)

/-- The twist-and-shift functor `K ↦ K(m)[2m]` in which every purity statement is phrased. -/
noncomputable def twistShift (m : ℤ) :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  tateTwist Λ X m ⋙ shiftFunctor _ (2 * m)

/-- For a finite coefficient ring whose exponent is invertible on `X`,
`Λ_X(m)[2m] = (Λ_X ⊗^L Λ_X(m))[2m]` lies in `D^b_{ctf}(X, Λ)`. This is the invertible object to
which `thm:regular` Step 2 applies the co-projection `sk-lem-coprojection`; it follows from
`AlgebraicGeometry.Etale.DerivedCategory.constructibleFiniteTor_constantComplex`,
`AlgebraicGeometry.Etale.constructibleFiniteTor_tateObject` and the stability of
`D^b_{ctf}` under `⊗^L` and shifts. -/
theorem constructibleFiniteTor_twistShift_constantComplex [Finite Λ] [HasInvertibleExponent Λ X]
    (m : ℤ) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
      ((twistShift Λ X m).obj (constantComplex Λ X)) :=
  sorry

/-- The identification `Λ_X(m)[2m] ⊗^L Λ_X(m')[2m'] ≅ Λ_X(m + m')[2(m + m')]`: the shifts are
moved out of the tensor product (`AlgebraicGeometry.Etale.derivedTensorShiftIso`) and the
twisting objects multiplied with `AlgebraicGeometry.Etale.tateObjectAddIso`. All shifts are
even, so no sign is involved. -/
noncomputable def shiftTateObjectAddIso [HasInvertibleExponent Λ X] (m m' : ℤ) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj ((tateObject Λ X m)⟦2 * m⟧)).obj
        ((tateObject Λ X m')⟦2 * m'⟧) ≅
      (tateObject Λ X (m + m'))⟦2 * (m + m')⟧ :=
  derivedTensorShiftIso _ _ _ (2 * m) (2 * m') ≪≫
    (shiftFunctor _ (2 * m + 2 * m')).mapIso (tateObjectAddIso Λ X m m') ≪≫
      eqToIso (by rw [mul_add])

variable {Λ X} {Y : Scheme.{u}}

variable (Λ) in
/-- The identification `Lf^* Λ_Y ≅ Λ_X` of the constant complexes: the derived pullback
preserves the monoidal unit (`AlgebraicGeometry.Etale.leftDerivedUpperStarUnitIso`). -/
noncomputable def leftDerivedUpperStarConstantComplexIso (f : X ⟶ Y) :
    (L((f)^*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ Y) ≅ constantComplex Λ X :=
  leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) f

/-- The identification `Lf^* Λ_Y(m) ≅ Λ_X(m)`, when the exponent of `Λ` is invertible on `Y`.
For `m = 1` it is the pullback of the Tate sheaf: `f^* μ_{n,Y} ≅ μ_{n,X}` because `μ_n` is
represented by a finite étale group scheme when `n` is invertible; the general case follows by
compatibility of `Lf^*` with `⊗^L` and with duals of invertible objects. -/
noncomputable def leftDerivedUpperStarTateObjectIso [HasInvertibleExponent Λ Y] (f : X ⟶ Y)
    (m : ℤ) : (L((f)^*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ Y m) ≅ tateObject Λ X m :=
  sorry

/-- The pullback identifications are compatible with composition: for `f : X ⟶ Y` and
`g : Y ⟶ S`, `L(f ≫ g)^* Λ_S(m) ≅ Λ_X(m)` is the composite

```
L(f ≫ g)^* Λ_S(m) ≅ Lf^* Lg^* Λ_S(m) ≅ Lf^* Λ_Y(m) ≅ Λ_X(m)
```

through `AlgebraicGeometry.Etale.leftDerivedUpperStarComp`. -/
theorem leftDerivedUpperStarTateObjectIso_comp {S : Scheme.{u}} [HasInvertibleExponent Λ S]
    (f : X ⟶ Y) (g : Y ⟶ S) (m : ℤ) :
    haveI : HasInvertibleExponent Λ Y := .of_hom g
    leftDerivedUpperStarTateObjectIso (f ≫ g) m =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f g).app (tateObject Λ S m) ≪≫
        (L((f)^*[ModuleCat.{u + 1} Λ])).mapIso (leftDerivedUpperStarTateObjectIso g m) ≪≫
          leftDerivedUpperStarTateObjectIso f m :=
  sorry

/-- The pullback identifications are compatible with the products of twisting objects, along
the monoidal structure `Lf^* (K ⊗ M) ≅ Lf^* K ⊗ Lf^* M` of the derived pullback
(`AlgebraicGeometry.Etale.leftDerivedUpperStarTensorIso`).

```
Lf^*(Λ_Y(m) ⊗ Λ_Y(m')) ────≅────▶ Lf^* Λ_Y(m) ⊗ Lf^* Λ_Y(m') ───≅───▶ Λ_X(m) ⊗ Λ_X(m')
          │                                                               │
          ▼                                                               ▼
   Lf^* Λ_Y(m + m') ──────────────────────≅──────────────────────▶ Λ_X(m + m')
``` -/
theorem leftDerivedUpperStar_map_tateObjectAddIso [HasInvertibleExponent Λ Y] (f : X ⟶ Y)
    (m m' : ℤ) :
    haveI : HasInvertibleExponent Λ X := .of_hom f
    (L((f)^*[ModuleCat.{u + 1} Λ])).map (tateObjectAddIso Λ Y m m').hom ≫
        (leftDerivedUpperStarTateObjectIso f (m + m')).hom =
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) f _ _).hom ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) X).map
          (leftDerivedUpperStarTateObjectIso f m).hom).app _ ≫
          ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (tateObject Λ X m)).map
            (leftDerivedUpperStarTateObjectIso f m').hom ≫ (tateObjectAddIso Λ X m m').hom :=
  sorry

variable (Λ) in
/-- The identification `Le^* (Λ_X(m)[2m]) ≅ Λ_U(m)[2m]`, through the shift compatibility of
`Le^*` and the identification `Le^* Λ_X(m) ≅ Λ_U(m)`. -/
noncomputable def leftDerivedUpperStarTateShiftIso [HasInvertibleExponent Λ Y] (f : X ⟶ Y)
    (m : ℤ) :
    (L((f)^*[ModuleCat.{u + 1} Λ])).obj ((tateObject Λ Y m)⟦2 * m⟧) ≅
      (tateObject Λ X m)⟦2 * m⟧ :=
  ((L((f)^*[ModuleCat.{u + 1} Λ])).commShiftIso (2 * m)).app _ ≪≫
    (shiftFunctor _ (2 * m)).mapIso (leftDerivedUpperStarTateObjectIso f m)

variable (Λ) in
/-- The identification `Lc^* Lg^* Λ_Y ≅ Λ_X` for the chosen compactification `(c, g)` of
`f : X ⟶ Y`, through `AlgebraicGeometry.Etale.leftDerivedUpperStarConstantComplexIso`. -/
noncomputable def compactificationConstantComplexIso (f : X ⟶ Y) [HasCompactification f] :
    (L(((HasCompactification.compactification f).i)^*[ModuleCat.{u + 1} Λ])).obj
        ((L(((HasCompactification.compactification f).g)^*[ModuleCat.{u + 1} Λ])).obj
          (constantComplex Λ Y)) ≅ constantComplex Λ X :=
  (L(((HasCompactification.compactification f).i)^*[ModuleCat.{u + 1} Λ])).mapIso
      (leftDerivedUpperStarConstantComplexIso Λ _) ≪≫
    leftDerivedUpperStarConstantComplexIso Λ _

variable (Λ X)

/-- Blueprint `sk-def-purity-conv`: Purity conventions and the rank-one datum

The *section invariant* `𝒞(g, s) = Ls^* ω_g = Ls^* Rg^! Λ_B` of a morphism `g : V ⟶ B`
together with a section `s : B ⟶ V`. For `g` smooth of pure relative dimension `d` with `s` a
closed section, smooth purity identifies it with `Λ_B(d)[2d]`; the deformation to the normal
cone of the section reduces the general case to the standard pair `(𝔸^d_B → B, 0)`. -/
noncomputable def sectionInvariant {V B : Scheme.{u}} (g : V ⟶ B) [HasCompactification g]
    (s : B ⟶ V) : DerivedCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (L((s)^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex (ModuleCat.{u + 1} Λ) g)

end Etale

end AlgebraicGeometry

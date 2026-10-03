/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import WeilConjectures.SixFunctors.OpenClosed.Exact

/-!
# The supported localization triangle

For complementary immersions `i : Z ⟶ X` and `j : U ⟶ X` the two adjunction maps of the
exceptional formalism assemble into the *supported localization triangle*

`Ri_! Ri^! L ⟶ L ⟶ Rj_* Lj^* L ⟶ [1]`,

the derived counterpart of the open–closed short exact sequence
`AlgebraicGeometry.Etale.shortExact_openClosedShortComplex`. Its first term is
cohomology-with-supports along `Z`; applied to the closed–open pair `(s, j)` on the affine
line it is what computes the fundamental class of the zero section.

The triangle rests on the *closed-immersion unit*: for a closed immersion `i` the exceptional
adjunction unit `Q ⟶ Ri^! Ri_! Q` is an isomorphism, and `Ri_!` is `Ri_*` because `i` is
proper.

## Main statements

- `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekAdjunction_unit_app`
- `AlgebraicGeometry.Etale.subsingleton_hom_rightDerivedLowerStar_rightDerivedLowerStar_shift`
- `AlgebraicGeometry.Etale.existsUnique_distTriang_supportedLocalization`
- `AlgebraicGeometry.Etale.supportedLocalization_naturality`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A] {U Z X : Scheme.{u}}

/-- Blueprint `sk-prop-sf-closed-unit`: Closed-immersion unit

For a closed immersion `i : Z ⟶ X` and `Q ∈ D^b_{ctf}(Z, Λ)` the unit

`Q ⟶ Ri^! Ri_! Q`

of the exceptional adjunction `AlgebraicGeometry.Etale.rightDerivedUpperShriekAdjunction` is
an isomorphism; since a closed immersion is proper, `Ri_!` is `Ri_*`, so this says that `Ri_*`
is fully faithful on the exceptional side. It is the derived counterpart of the full
faithfulness of `i_*` recorded in `AlgebraicGeometry.Etale.fullyFaithfulLowerStar`. -/
theorem isIso_rightDerivedUpperShriekAdjunction_unit_app (i : Z ⟶ X) [IsClosedImmersion i]
    [HasCompactification i] (Q : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A)) :
    IsIso ((rightDerivedUpperShriekAdjunction A i).unit.app Q) :=
  sorry

section Localization

/- The closed symmetric preadditive monoidal structure on the coefficient category: it is
what `AlgebraicGeometry.Etale.derivedUpperStarLowerStarAdjunction`, the source of the second
map of the triangle, is stated under. -/
variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- Blueprint `sk-prop-sf-localization`: Supported localization

**No maps from the closed side to the open side.** Let `i : Z ⟶ X` be a closed immersion with
complementary open `j : U ⟶ X`. Then `Hom(Ri_* A, (Rj_* B)[n]) = 0` for all `A`, `B` and `n`:
by `Lj^* ⊣ Rj_*` it is `Hom(Lj^* Ri_* A, B[n])`, and `Lj^* Ri_* = 0` [BBD, 1.1.9]. -/
theorem subsingleton_hom_rightDerivedLowerStar_rightDerivedLowerStar_shift (i : Z ⟶ X)
    (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (B : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A))
    (C : _root_.DerivedCategory (Sheaf U.smallEtaleTopology A)) (n : ℤ) :
    Subsingleton ((R((i)_*[A])).obj B ⟶ ((R((j)_*[A])).obj C)⟦n⟧) :=
  sorry

/-- Blueprint `sk-prop-sf-localization`: Supported localization

**The supported localization triangle.** Let `i : Z ⟶ X` be a closed immersion with
complementary open `j : U ⟶ X`. For `L ∈ D(X_ét, A)` the *adjunction maps*

```
  Ri_! Ri^! L --ε_L--> L --η_L--> Rj_* Lj^* L --w--> (Ri_! Ri^! L)[1]
```

— `ε` the counit of `Ri_! ⊣ Ri^!` and `η` the unit of `Lj^* ⊣ Rj_*` — extend to a
distinguished triangle, and the connecting map `w` is *unique*: two choices differ by a map
`Rj_* Lj^* L ⟶ (Ri_! Ri^! L)[1]` factoring through `L`, hence by
`subsingleton_hom_rightDerivedLowerStar_rightDerivedLowerStar_shift` they agree [BBD, 1.1.10].
Under the closed-immersion unit `Ri_! Ri^! L` is cohomology with supports along `Z`.

The triangle is the derived form of the open–closed sequence, obtained from the open–closed
triangle by the closed-immersion unit and the determination of a natural transformation on a
generating class. -/
theorem existsUnique_distTriang_supportedLocalization (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [HasCompactification i] [IsOpenImmersion j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ∃! w, Triangle.mk ((rightDerivedUpperShriekAdjunction A i).counit.app L)
      ((derivedUpperStarLowerStarAdjunction A j).unit.app L) w ∈ distTriang _ :=
  sorry

/-- Blueprint `sk-prop-sf-localization`: Supported localization

**Naturality of the supported localization triangle.** For `φ : L ⟶ L'` and the supported
localization triangles of `L` and `L'` (with their unique connecting maps, see
`existsUnique_distTriang_supportedLocalization`), the triple
`(Ri_! Ri^! φ, φ, Rj_* Lj^* φ)` is a morphism of triangles, and it is the only morphism of
triangles whose middle component is `φ`: by
`subsingleton_hom_rightDerivedLowerStar_rightDerivedLowerStar_shift` a morphism of these
triangles is determined by its middle component [BBD, 1.1.9]. -/
theorem supportedLocalization_naturality (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [HasCompactification i] [IsOpenImmersion j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    {L L' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (φ : L ⟶ L')
    (w : (R((j)_*[A])).obj ((L((j)^*[A])).obj L) ⟶
      ((R(i)_![A]).obj ((R(i)^![A]).obj L))⟦(1 : ℤ)⟧)
    (w' : (R((j)_*[A])).obj ((L((j)^*[A])).obj L') ⟶
      ((R(i)_![A]).obj ((R(i)^![A]).obj L'))⟦(1 : ℤ)⟧)
    (hw : Triangle.mk ((rightDerivedUpperShriekAdjunction A i).counit.app L)
      ((derivedUpperStarLowerStarAdjunction A j).unit.app L) w ∈ distTriang _)
    (hw' : Triangle.mk ((rightDerivedUpperShriekAdjunction A i).counit.app L')
      ((derivedUpperStarLowerStarAdjunction A j).unit.app L') w' ∈ distTriang _) :
    (∃ τ : Triangle.mk ((rightDerivedUpperShriekAdjunction A i).counit.app L)
        ((derivedUpperStarLowerStarAdjunction A j).unit.app L) w ⟶
      Triangle.mk ((rightDerivedUpperShriekAdjunction A i).counit.app L')
        ((derivedUpperStarLowerStarAdjunction A j).unit.app L') w',
      τ.hom₁ = (R(i)_![A]).map ((R(i)^![A]).map φ) ∧ τ.hom₂ = φ ∧
        τ.hom₃ = (R((j)_*[A])).map ((L((j)^*[A])).map φ)) ∧
    ∀ τ τ' : Triangle.mk ((rightDerivedUpperShriekAdjunction A i).counit.app L)
        ((derivedUpperStarLowerStarAdjunction A j).unit.app L) w ⟶
      Triangle.mk ((rightDerivedUpperShriekAdjunction A i).counit.app L')
        ((derivedUpperStarLowerStarAdjunction A j).unit.app L') w',
      τ.hom₂ = φ → τ'.hom₂ = φ → τ = τ' :=
  sorry

end Localization

end Etale

end AlgebraicGeometry

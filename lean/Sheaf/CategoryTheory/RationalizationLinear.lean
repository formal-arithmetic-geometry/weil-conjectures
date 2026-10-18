/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Localization.Triangulated
public import Mathlib.RingTheory.Localization.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.Rationalization

import Mathlib.CategoryTheory.Center.Linear
import Mathlib.CategoryTheory.Localization.Linear
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Linear structure of rationalization

Source: `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/`
`sk-def-sfb-rationalization/def-sfb-rationalization-linear.md`
(blueprint: def-sfb-rationalization-linear).
-/

@[expose] public section

universe w w' v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Rationalization

/-- The rationalization has invertible `M`-scalars and a unique compatible
`A`-linear structure for every localization `A` of `R` at `M`.

Source: blueprint `sec-proetale-coefficients/sk-def-sfb-rationalization/`
`def-sfb-rationalization-linear.md` and its proof; Stacks Project, Tag 00CP,
`algebra.tex`, `proposition-universal-property-localization`.
(blueprint: def-sfb-rationalization-linear).

Proof plan:
1. Put `D = Rationalization M C` and use the triangulated localization functor `Q` of
   def-sfb-rationalization-quotient. Triangulated categories and their exact functors are
   additive (def-weil-triangulated-category). By lem-sfb-additive-localization-linear, `D`
   has its induced `R`-linear structure, `Q` is `R`-linear and inverts `W M C`, and every
   object of `D` is isomorphic to some `Q.obj X`.
2. By lem-sfb-smul-id-in-w, `m • 𝟙 X` belongs to `W M C` for `m ∈ M`. Its image under
   `Q` is `m • 𝟙 (Q.obj X)` and is invertible. Conjugate this map and its inverse along
   an isomorphism `Q.obj X ≅ Y` to get invertibility of `m • 𝟙 Y` for arbitrary `Y`.
3. By lem-sfb-category-center-linear the original action is the ring map
   `ρ : R →+* CatCenter D`, with component `ρ(r)_Y = r • 𝟙 Y`. For `m ∈ M`, the
   componentwise inverses of `ρ(m)` are natural: multiply its naturality equation by
   the inverses on both sides. They give an inverse in the center, so `ρ(m)` is a unit.
4. Apply lem-weil-pbc-ring-localization-universal-property (Stacks 00CP) to obtain the
   unique extension `φ : A →+* CatCenter D`. For any localization model `A`, its
   universal maps to and from the fraction model are inverse by uniqueness. Thus this
   step applies to every `A` in the statement without assuming `R → A` injective.
5. Use lem-sfb-category-center-linear to let `a` act on `f : X ⟶ Y` by composition
   with `φ(a)_X`. Its module laws and bilinearity give a `Linear A D` structure. Since
   `φ(algebraMap R A r) = ρ(r)`, the new action on `f` is exactly `r • f`.
6. Any other compatible `A`-linear structure defines `ψ(a)_X = a • 𝟙 X`, a ring map
   to the center by lem-sfb-category-center-linear. Compatibility makes `ψ` extend `ρ`,
   so uniqueness in lem-weil-pbc-ring-localization-universal-property gives `ψ = φ`.
   Bilinearity recovers the action on every `f` from the action on its source identity.
   The actions therefore coincide; extensionality and proof irrelevance identify the
   module structures and then the two `Linear` structures. -/
theorem isIso_smul_id_and_existsUnique_linear {R : Type w} [CommRing R] (M : Submonoid R)
    {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
    [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor C n).Linear R] [Pretriangulated C] [IsTriangulated C]
    {A : Type w'} [CommRing A] [Algebra R A] [IsLocalization M A] :
    (∀ (m : R), m ∈ M → ∀ (Y : Rationalization M C), IsIso (m • 𝟙 Y)) ∧
    ∃! l : Linear A (Rationalization M C),
      ∀ (r : R) {X Y : Rationalization M C} (f : X ⟶ Y),
        @SMul.smul A (X ⟶ Y)
            (SemigroupAction.toSMul (self :=
              MulAction.toSemigroupAction (self :=
                DistribMulAction.toMulAction (self :=
                  Module.toDistribMulAction (self :=
                    Linear.homModule (self := l) X Y)))))
          (algebraMap R A r) f = r • f := by
  sorry

end CategoryTheory.Rationalization

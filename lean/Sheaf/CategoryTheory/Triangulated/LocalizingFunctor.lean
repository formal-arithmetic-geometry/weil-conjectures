/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q90
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Mathlib.CategoryTheory.Limits.Preserves.Basic


/-!
# Exact functors on localizing closures

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-proper-image-localizing,
statement and proof of sk-prop-proper-image-localizing-principle
(blueprint: det-proper-image-localizing-principle).

## Main statements

- `CategoryTheory.Functor.maps_localizingClosure`: the general localizing principle.
- `AlgebraicGeometry.ProEtale.maps_localizingClosureProEtale`: its pro-etale specialization.
-/

@[expose] public section

set_option autoImplicit false

universe w v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits

open scoped CategoryTheory.Obj

namespace CategoryTheory.Functor

/-- An exact coproduct-preserving functor carrying the generators into the target closure
carries their localizing closure there and restricts to an exact coproduct-preserving functor.
Source: blueprint main-20261015, sk-prop-proper-image-localizing-principle, both paragraphs
(blueprint: det-proper-image-localizing-principle).

Proof: (1) The defining intersection contains the generators and zero and is replete,
shift-stable and triangulated: check each condition in every localizing candidate.
The same intersection argument gives closure under sums in universe `w` and minimality.
(2) Intersect the source closure with the inverse image of the target closure under `F`.
It contains the generators by the hypothesis. Exactness sends zero to zero, commutes
with shifts and sends distinguished triangles to distinguished triangles; these facts
prove the triangulated closure condition. Functoriality preserves isomorphisms, and
preservation of coproducts proves sum closure. Minimality therefore gives the claimed
object inclusion. (3) Fullness restricts the object and morphism maps, and the ambient
shift comparison restricts too. Distinguished triangles in the full subcategories are
exactly the ambient ones with vertices in them, so the restriction is exact.
(4) Ambient coprojections satisfy the same universal property in the full subcategories.
They therefore compute their coproducts, including the empty coproduct. Preservation
of ambient coproduct cocones proves preservation by the restriction.
(5) Specialize to the unbounded pro-etale module-object derived category and its
bounded constructible finite-Tor object property from `sk-def-localizing-closure`.
The coproduct-existence input is `det-def-localizing-closure-existence` (1).
No derived-completeness condition or additional geometric conclusion is used. -/
theorem maps_localizingClosure
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [CategoryTheory.IsTriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [CategoryTheory.IsTriangulated D]
    [HasCoproducts.{w} C] [HasCoproducts.{w} D]
    (G : ObjectProperty C) (G' : ObjectProperty D) (F : C ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated]
    [∀ I : Type w, PreservesColimitsOfShape (Discrete I) F]
    (hG : ∀ K : C, G K → localizingClosureOfSize.{w} G' (F.obj K)) :
    ∃ (_ : (localizingClosureOfSize.{w} G).IsTriangulated)
      (_ : (localizingClosureOfSize.{w} G').IsTriangulated)
      (hF : ∀ K : C, localizingClosureOfSize.{w} G K → localizingClosureOfSize.{w} G' (F.obj K)),
      ((localizingClosureOfSize.{w} G').lift ((localizingClosureOfSize.{w} G).ι ⋙ F)
        (fun K : (localizingClosureOfSize.{w} G).FullSubcategory ↦
          hF K.obj K.property)).IsTriangulated ∧
      ∀ I : Type w, PreservesColimitsOfShape (Discrete I)
        ((localizingClosureOfSize.{w} G').lift ((localizingClosureOfSize.{w} G).ι ⋙ F)
          (fun K : (localizingClosureOfSize.{w} G).FullSubcategory ↦
            hF K.obj K.property)) := by
  sorry

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- The same localizing principle for the unbounded pro-etale module-object derived category
and the bounded constructible finite-Tor generators of `sk-def-localizing-closure`.
Source: blueprint main-20261015, sk-prop-proper-image-localizing-principle, final sentence
(blueprint: det-proper-image-localizing-principle).

Proof: `det-def-localizing-closure-existence` (1) supplies the ambient small coproducts.
Apply `CategoryTheory.Functor.maps_localizingClosure` with the index universe `u₁ + 1`
and the generator property
`constantModelBoundedConstructible Λ X ⊓ DerivedCategory.finiteTorAmplitude _`.
The recorded `localizingClosureProEtale Λ X` closes this property under all existing
coproducts in the object universe `u₁ + 2`. It equals the closure under `u₁ + 1`-indexed
coproducts, because the Hom types live in `u₁ + 1`: in an existing larger coproduct the
nonzero summands give distinct nonzero coordinate idempotents of its endomorphisms,
so they form a `u₁ + 1`-small family with the same coproduct; conversely a
`u₁ + 1`-indexed sum is a larger-indexed sum by universe lift (proof step 4 of
`det-def-localizing-closure-existence`). So the localizing candidates of the two
conventions coincide. The inclusion, exactness and preservation conclusions are
therefore precisely those of the general principle. The coefficient conventions are
those of `sk-def-localizing-closure`: the supported adic coefficient families are
regarded as condensed commutative rings. -/
theorem maps_localizingClosureProEtale
    (Λ : Sheaf (coherentTopology Profinite.{u₁}) Ab.{u₁ + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u₁})
    {D : Type u₂} [Category.{v₂} D]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [CategoryTheory.IsTriangulated D]
    [HasCoproducts.{u₁ + 1} D]
    (G' : ObjectProperty D)
    (F : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X)
      Ab.{u₁ + 1}) (condensedRingObj Λ X)) ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated]
    [∀ I : Type (u₁ + 1), PreservesColimitsOfShape (Discrete I) F]
    (hG : ∀ K : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X)
      Ab.{u₁ + 1}) (condensedRingObj Λ X)), constantModelBoundedConstructible Λ X K ∧
      DerivedCategory.finiteTorAmplitude _ K → localizingClosureOfSize.{u₁ + 1} G' (F.obj K)) :
    ∃ (_ : (localizingClosureProEtale Λ X).IsTriangulated)
      (_ : (localizingClosureOfSize.{u₁ + 1} G').IsTriangulated)
      (hF : ∀ K : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X)
        Ab.{u₁ + 1}) (condensedRingObj Λ X)), localizingClosureProEtale Λ X K →
        localizingClosureOfSize.{u₁ + 1} G' (F.obj K)),
      ((localizingClosureOfSize.{u₁ + 1} G').lift ((localizingClosureProEtale Λ X).ι ⋙ F)
        (fun K : (localizingClosureProEtale Λ X).FullSubcategory ↦
          hF K.obj K.property)).IsTriangulated ∧
      ∀ I : Type (u₁ + 1), PreservesColimitsOfShape (Discrete I)
        ((localizingClosureOfSize.{u₁ + 1} G').lift ((localizingClosureProEtale Λ X).ι ⋙ F)
          (fun K : (localizingClosureProEtale Λ X).FullSubcategory ↦
            hF K.obj K.property)) := by
  sorry

end AlgebraicGeometry.ProEtale

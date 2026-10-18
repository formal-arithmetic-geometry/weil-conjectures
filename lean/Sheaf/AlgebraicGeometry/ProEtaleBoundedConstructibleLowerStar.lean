/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.Paper.BoundedConstructiblePushforwardRestriction
public import Sheaf.Paper.CondensedModuleDerivedPushpull

/-!
# Restricting derived pushforward to bounded constructible complexes

Source: Weil conjectures blueprint, main-20261015, six-functors basics,
`sk-def-sfb-dc-restricted-functors/def-sfb-dc-lower-star.md`
(blueprint: def-sfb-dc-lower-star).

The preservation hypothesis is explicit, allowing any commutative condensed ring for which
the given pushforward preserves bounded constructible complexes. The existing finiteness
theorem supplies this hypothesis for the listed ell-adic coefficients.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The restriction of the ambient total derived module pushforward to the bounded
constructible full subcategories, with its preservation hypothesis supplied explicitly.
On objects it equips the ambient image with its preservation witness; on morphisms it uses
the ambient pushforward. Source: main-20261015 blueprint,
`sk-def-sfb-dc-restricted-functors/def-sfb-dc-lower-star.md`
(blueprint: def-sfb-dc-lower-star). -/
noncomputable def boundedConstructibleLowerStarAtMorphism
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y)
    (h : ∀ K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1}) (condensedRingObj Λ X.left)),
      boundedConstructible (condensedRingObj Λ X.left) K →
        boundedConstructible (condensedRingObj Λ Y.left)
          ((moduleObjectDerivedPushforward Λ f.left).obj K)) :
    BoundedConstructible (condensedRingObj Λ X.left) ⥤
      BoundedConstructible (condensedRingObj Λ Y.left) :=
  (boundedConstructible (condensedRingObj Λ Y.left)).lift
    ((boundedConstructible (condensedRingObj Λ X.left)).ι ⋙ moduleObjectDerivedPushforward Λ f.left)
    (fun K ↦ h K.obj K.property)

/-- The restricted pushforward commutes with the full-subcategory inclusions. The
comparison is the canonical identity isomorphism from `ObjectProperty.liftCompιIso`.
Source: main-20261015 blueprint,
`sk-def-sfb-dc-restricted-functors/def-sfb-dc-lower-star.md`, final sentence
(blueprint: def-sfb-dc-lower-star). -/
noncomputable def boundedConstructibleLowerStarAtMorphismCompatibility
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y)
    (h : ∀ K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1}) (condensedRingObj Λ X.left)),
      boundedConstructible (condensedRingObj Λ X.left) K →
        boundedConstructible (condensedRingObj Λ Y.left)
          ((moduleObjectDerivedPushforward Λ f.left).obj K)) :
    boundedConstructibleLowerStarAtMorphism Λ ℓ f h ⋙
        (boundedConstructible (condensedRingObj Λ Y.left)).ι ≅
      (boundedConstructible (condensedRingObj Λ X.left)).ι ⋙
        moduleObjectDerivedPushforward Λ f.left :=
  ObjectProperty.liftCompιIso _ _ _

/-- The restriction for one morphism agrees with the existing restriction whenever global
preservation is available. The comparison is induced by their canonical inclusion comparisons,
so it reuses the existing functor and compatibility, without assuming global preservation in
`boundedConstructibleLowerStarAtMorphism` itself. Source: main-20261015 blueprint,
`sk-def-sfb-dc-restricted-functors/def-sfb-dc-lower-star.md`, restriction and final sentence
(blueprint: def-sfb-dc-lower-star). -/
noncomputable def boundedConstructibleLowerStarAtMorphismGlobalIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y)
    (h : ∀ K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1}) (condensedRingObj Λ X.left)),
      boundedConstructible (condensedRingObj Λ X.left) K →
        boundedConstructible (condensedRingObj Λ Y.left)
          ((moduleObjectDerivedPushforward Λ f.left).obj K))
    (H : PreservesBoundedConstructiblePushforwards Λ k) :
    boundedConstructibleLowerStarAtMorphism Λ ℓ f h ≅
      boundedConstructibleLowerStarOfPreserves Λ H f :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (boundedConstructibleLowerStarAtMorphismCompatibility Λ ℓ f h ≪≫
      (boundedConstructibleLowerStarOfPreservesCompatibility Λ H f).symm)

end AlgebraicGeometry.ProEtale.CondensedRing

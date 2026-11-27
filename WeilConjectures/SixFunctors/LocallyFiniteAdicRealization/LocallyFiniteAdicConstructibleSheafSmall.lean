/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicRealizationData
import WeilConjectures.AlgebraicGeometry.Native.NativeAdicConstructibilityEncoding
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleModuleObjectsEssentiallySmall

/-! # LocallyFiniteAdicConstructibleSheafSmall

Native constructible sheaves form an essentially small family.

## Implementation details

Forgetting the constant coefficient action identifies native internal modules with modules
in abelian sheaves over `abRing` (the normalized native encoding `NativeEncoding.encoding`,
with `encoding_constructible_iff` comparing constructibility on Noetherian `X`); the
result then follows from `constructibleModuleObjects_essentiallySmall`.

## References

* [Bhatt--Scholze, Section 6.8, Definitions 6.8.3, 6.8.6 and 6.8.8]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
attribute [local instance] CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Sheaf.braidedCategory

attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped Obj

namespace WeilConjectures.LocallyFiniteAdicRealization

/-- A small family of native constructible sheaves, before passage to complexes: the
native constructible full subcategory is essentially small. -/
theorem nativeConstructibleSheaf_essentiallySmall
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsNoetherian X] :
    ObjectProperty.EssentiallySmall.{u + 1} (ProEtale.adicConstructibleSheaf l X) := by
  let P := ProEtale.adicConstructibleSheaf l X
  let Q : ObjectProperty _ := ProEtale.IsConstructibleModuleObject
    (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj l) X)
  have : ObjectProperty.EssentiallySmall.{u + 1} Q :=
    ProEtale.constructibleModuleObjects_essentiallySmall X _
  let F := Q.lift (P.ι ⋙ ProEtale.NativeEncoding.encoding l X)
    (fun M ↦ (ProEtale.encoding_constructible_iff M.obj).mp M.property)
  have : F.Full := by dsimp only [F]; infer_instance
  have : F.Faithful := by dsimp only [F]; infer_instance
  have : EssentiallySmall.{u + 1} P.FullSubcategory :=
    essentiallySmall_of_fully_faithful F
  have h : ObjectProperty.EssentiallySmall.{u + 1} P.ι.essImage := inferInstance
  exact ObjectProperty.EssentiallySmall.of_le
    (Q := P.ι.essImage) (fun M hM ↦ ⟨⟨M, hM⟩, ⟨Iso.refl M⟩⟩)

end WeilConjectures.LocallyFiniteAdicRealization

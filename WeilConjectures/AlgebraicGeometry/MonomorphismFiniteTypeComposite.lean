/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.UnramifiedMorphism
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import WeilConjectures.AlgebraicGeometry.UnramifiedQuasiFinite

/-! # Monomorphisms with locally finite type composites

Source: Stacks Project, Morphisms, Tags 01T8, 02GE and 02V5; Schemes, Tags 01L3
and 01L4; the monomorphism argument in Spaces, Tag 0265
(blueprint: lem-trf-monomorphism-finite-type-composite-lqf).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Hom

/-- A monomorphism whose composite is locally of finite type is locally of finite type,
has an isomorphic diagonal (hence both open and closed), is separated and unramified,
and is quasi-finite at every point and locally quasi-finite in the affine-neighbourhood
sense of Stacks Tag 01TD. No quasi-compactness or separatedness of `g` is assumed.

Source: Stacks Project, Morphisms, Tags 01T8, 02GE and 02V5; Schemes, Tags 01L3
and 01L4; Spaces, Tag 0265
(blueprint: lem-trf-monomorphism-finite-type-composite-lqf).

Proof:
1. Apply clause (a) of lemma-nagata-finite-type-to-separated-target, namely
   `locallyOfFiniteType_of_comp`, to obtain local finite type of `f` (Tag 01T8).
2. In the self-fibre-product of `f`, the projections have equal composites with `f`.
   Monicity makes the projections equal. The diagonal followed by the first projection
   is the identity. Conversely, the two projections of the first projection followed
   by the diagonal agree with those of the identity. The fibre-product universal
   property (def-pc-fibre-product) gives the other inverse identity (Tag 01L3).
3. An isomorphism is both an open and a closed immersion (def-weil-open-immersion,
   def-weil-closed-immersion). Thus the diagonal is both. The closed diagonal means
   separatedness (def-weil-proper-morphism, Tag 01L4). The open diagonal and step 1
   give unramifiedness (def-weil-unramified-morphism, Tag 02GE).
4. Apply lem-weil-pbc-unramified-quasi-finite-at-points to step 3 (Tag 02V5).
   It supplies affine neighbourhoods whose ring map is finite type and quasi-finite
   at the prime of each point, exactly pqf-def-quasifinite (1). This is local
   quasi-finiteness by pqf-def-quasifinite (2). -/
theorem monomorphism_properties_of_locallyOfFiniteType_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Mono f] [LocallyOfFiniteType (f ≫ g)] :
    LocallyOfFiniteType f ∧
    IsIso (pullback.diagonal f) ∧
    IsOpenImmersion (pullback.diagonal f) ∧
    IsClosedImmersion (pullback.diagonal f) ∧
    IsSeparated f ∧
    IsUnramified f ∧
    (∀ x : X, IsQuasiFiniteAtPoint f x) ∧
    IsLocallyQuasiFinite f := by
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f g
  have : IsIso (pullback.diagonal f) := inferInstance
  have : IsOpenImmersion (pullback.diagonal f) := inferInstance
  have : IsClosedImmersion (pullback.diagonal f) := inferInstance
  have hunramified : IsUnramified f := ⟨inferInstance, inferInstance⟩
  have hqf : IsLocallyQuasiFinite f := isLocallyQuasiFinite_of_unramified f hunramified
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    hunramified, hqf, hqf⟩

end AlgebraicGeometry.Scheme.Hom

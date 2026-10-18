/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q72
-/
module

public import Sheaf.Paper.OrientedConstructibleSheaf
public import Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor

/-!
# Transport of oriented constructibility to the vanishing-site presentation

Source: Lu--Zheng, definition following Theorem 4.27, printed p. 38; ILO XI §§1.1--1.9
(blueprint: def-trf-oriented-constructible-sheaf).

The recorded general oriented product uses the actual base-change functor of the second
scheme map. The vanishing site uses the identity functor in its second slot. Pullback along
an identity is canonically isomorphic to the identity, so these presentations agree. We
transport module sheaves through that concrete normalization and apply the existing general
constructibility predicate; no stratification or local-constancy predicate is duplicated.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.OrientedNearbyCycles

namespace AlgebraicGeometry.OrientedConstructibleSheaf

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical projection from pullback along the identity on the transported étale site.
Every component is the first projection `V ×[S] S → V`, an isomorphism.
Source: ILO XI §1.1, §4.3 (blueprint: def-trf-oriented-constructible-sheaf). -/
def identityBaseChangeProjection (S : Scheme.{u}) :
    etaleBaseChange.{u, v} (𝟙 S) ⟶ 𝟭 (EtaleSite.{u, v} S) where
  app V := AsSmall.up.map (MorphismProperty.Over.homMk
    (pullback.fst (AsSmall.down.obj V).hom (𝟙 S))
    (by simpa using pullback.condition (f := (AsSmall.down.obj V).hom) (g := 𝟙 S)))
  naturality V W k := by
    change AsSmall.up.map _ ≫ AsSmall.up.map _ = AsSmall.up.map _ ≫ AsSmall.up.map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    ext
    simp

/-- Normalize the second structural arrow of an oriented triple by `V ×[S] S ≅ V`.
The outer entries and middle entry are unchanged. This concrete equivalence of the triple
sites respects all three covering types, including the cartesian type-(c) square.
Source: ILO XI §§1.1, 1.7, 4.3 (blueprint: def-trf-oriented-constructible-sheaf). -/
def vanishingNormalization {X S : Scheme.{u}} (f : X ⟶ S) :
    ProductSite.{u, v} f (𝟙 S) ⥤ VanishingSite.{u, v} f :=
  Comma.map (F₁ := 𝟭 (EtaleSite.{u, v} X × EtaleSite.{u, v} S))
    (F₂ := 𝟭 (EtaleSite.{u, v} S))
    ((Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv)
    (NatTrans.prod' (𝟙 (etaleBaseChange.{u, v} f)) (identityBaseChangeProjection S) ≫
      (Functor.leftUnitor _).inv)

/-- Read a vanishing-topos module as a module on the general oriented product with second
map `𝟙 S`. Scalar restriction uses the canonical constant-commutative-ring comparison;
precomposition uses the concrete normalization of triples; sheafification realizes the
same sheaf since this normalization preserves coverings. Finally use the existing equivalence
from fixed-ring module sheaves to constant-ring modules. Its inverse is determined by the
scalar-restriction functor in `constant_ring_module_sheaves`.
Source: ILO XI §§1.1, 1.7, 4.3; Stacks 03CY
(blueprint: def-trf-oriented-constructible-sheaf). -/
def vanishingModuleTransport {X S : Scheme.{u}} (f : X ⟶ S)
    (Λ : Type v) [CommRing Λ] :
    (vanishingDatum.{u, v} f).modules (Coeff.{u, v} Λ) ⥤ Modules f (𝟙 S) Λ :=
  SheafOfModules.restrictScalars (realizationRingIso (vanishingTopology f) (Coeff Λ)).inv ⋙
    constantRingModuleRestriction (vanishingTopology f) (Coeff Λ) ⋙
    sheafToPresheaf (vanishingTopology f) (ModuleCat.{max (u + 1) v} (Coeff Λ)) ⋙
    (Functor.whiskeringLeft _ _ _).obj (vanishingNormalization f).op ⋙
    presheafToSheaf (productTopology f (𝟙 S)) (ModuleCat.{max (u + 1) v} (Coeff Λ)) ⋙
    (constant_ring_module_sheaves (productTopology f (𝟙 S)) (Coeff Λ)).1.choose.inverse

/-- The existing oriented-product constructibility predicate on the vanishing-topos
presentation, transported along the canonical identity-base-change normalization.
Both scheme stratifications and their finite locally constant module values are exactly
those in `IsConstructible`, with no extra geometric or coefficient assumptions.
Source: Lu--Zheng, definition after Theorem 4.27, printed p. 38; ILO XI §4.3
(blueprint: def-trf-oriented-constructible-sheaf). -/
def IsConstructibleVanishing {X S : Scheme.{u}} (f : X ⟶ S)
    (Λ : Type v) [CommRing Λ] [Finite Λ]
    (F : (vanishingDatum.{u, v} f).modules (Coeff.{u, v} Λ)) : Prop :=
  IsConstructible f (𝟙 S) Λ ((vanishingModuleTransport f Λ).obj F)

end AlgebraicGeometry.OrientedConstructibleSheaf

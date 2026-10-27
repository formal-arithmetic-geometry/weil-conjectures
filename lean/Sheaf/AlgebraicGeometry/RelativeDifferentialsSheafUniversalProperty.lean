/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q63
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Kaehler.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import Sheaf.CategoryTheory.RingedSiteModules

/-! # The universal property of the sheaf of relative differentials

Source: Stacks Project, Morphisms, Tags 01UR, 01UT, 01UO and 01US
(blueprint: lem-sfb-relative-differentials-sheaf-universal-property).

The relative derivations are the existing `PresheafOfModules.Derivation'` for
`f.pullbackPresheafToPresheaf`. Additivity is expressed on every open section, so no
second group structure on derivations is chosen. The map is the existing canonical
postcomposition with `relativeDifferentialsDerivation`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Hom

/-- Composition with the universal derivation is an additive bijection, natural in
all module sheaves and compatible with every open restriction.

Source: Stacks Project, Morphisms, Tags 01UR, 01UT, 01UO and 01US
(blueprint: lem-sfb-relative-differentials-sheaf-universal-property).

Proof: The existing `relativeDifferentialsHomEquiv` identifies the displayed map
with an equivalence, giving bijectivity for an arbitrary module sheaf. Addition and
zero of sheaf morphisms are computed sectionwise, giving the additive identities.
Naturality follows from sectionwise associativity of composition. Finally, the
inverse of `relativeDifferentialsRestrictIso` is `relativeDifferentialsToRestrict`;
its section formula `relativeDifferentialsToRestrict_app_d` sends `d a` to
`d ((j.appIso W).inv a)`. Applying the component of the restricted morphism gives
the restriction identity. -/
theorem relativeDifferentials_sheaf_universal_property
    {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules) :
    Function.Bijective (fun α : f.relativeDifferentials ⟶ M ↦
      f.relativeDifferentialsDerivation.postcomp α.val) ∧
    (∀ (α β : f.relativeDifferentials ⟶ M) (W : X.Opens) (a : Γ(X, W)),
      (f.relativeDifferentialsDerivation.postcomp (α + β).val).d (X := op W) a =
        (f.relativeDifferentialsDerivation.postcomp α.val).d (X := op W) a +
          (f.relativeDifferentialsDerivation.postcomp β.val).d (X := op W) a) ∧
    (∀ (W : X.Opens) (a : Γ(X, W)),
      (f.relativeDifferentialsDerivation.postcomp (0 : f.relativeDifferentials ⟶ M).val).d
        (X := op W) a = 0) ∧
    (∀ (N : X.Modules) (h : M ⟶ N) (α : f.relativeDifferentials ⟶ M),
      f.relativeDifferentialsDerivation.postcomp (α ≫ h).val =
        (f.relativeDifferentialsDerivation.postcomp α.val).postcomp h.val) ∧
    (∀ (U : Scheme.{u}) (j : U ⟶ X) [IsOpenImmersion j]
        (α : f.relativeDifferentials ⟶ M) (W : U.Opens) (a : Γ(U, W)),
      ((j ≫ f).relativeDifferentialsDerivation.postcomp
        ((f.relativeDifferentialsRestrictIso j).inv ≫
          (Modules.restrictFunctor j).map α).val).d (X := op W) a =
        (f.relativeDifferentialsDerivation.postcomp α.val).d
          (X := op (j ''ᵁ W)) ((j.appIso W).inv a)) := by
  refine ⟨(f.relativeDifferentialsHomEquiv M).bijective, ?_, ?_, ?_, ?_⟩
  · intro α β W a
    rfl
  · intro W a
    rfl
  · intro N h α
    ext W a
    rfl
  · intro U j _ α W a
    change α.val.app (op (j ''ᵁ W))
        ((f.relativeDifferentialsToRestrict j).val.app (op W)
          ((j ≫ f).relativeDifferentialsDerivation.d a)) = _
    rw [f.relativeDifferentialsToRestrict_app_d j a]
    rfl

end AlgebraicGeometry.Scheme.Hom

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G4
-/
module

public import Sheaf.AlgebraicGeometry.PicardCanonicalBaseChange

/-! # Composition of pulled pairings

Source: Stacks Project, Tag 0095, tensor formula; Tag 0096, adjunction.
(blueprint: lem-sc-picard-pairing-composition).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

/-- Pulling a pairing twice agrees with pulling it along the composite, after the
specified composition comparison on each argument.
Source: Stacks Project, Tag 0095, tensor formula; Tag 0096, adjunction.
(blueprint: lem-sc-picard-pairing-composition)

Proof: Eliminate e, reducing t to k followed by l. Expand the transported
comparison definitions, and use naturality of picardTensorComparison at the
inner pairing to cancel its intervening hom/inv factors. The remaining identity
is the ordinary pullback identity with pullbackComp on its two arguments.
For ordinary pullback, the composition comparison sends a generator
r tensor (s tensor m) to r times k-sharp(s) tensor m. This map is characterized
by the pullback/pushforward adjunction, so it is the specified pullbackComp.
For generators r tensor (s tensor m) and r' tensor (s' tensor n), pulling the
pairing twice multiplies the outer coefficients r*r', then the inner coefficients
s*s', then applies the composite ring map to g(m tensor n). Pulling along the
composite instead first forms r*k-sharp(s) and r'*k-sharp(s'), then multiplies
these and the image of g(m tensor n). The ring-map law and commutativity identify
the results. The unit comparison maps r tensor a to r*k-sharp(a), so it obeys
the same composition rule. Generators determine the presheaf maps; these
equalities therefore extend to sheafification. The monoidal structure of
ordinary pullback is obtained by localization of that presheaf construction,
so these are precisely its specified tensor maps. Transport the identity back
through picardTensorComparison. Its naturality cancels the remaining comparison
factors and its composition conjugation is picardTensorCompIso. Reinsert e to
obtain the equality-comparison factors. No finiteness, flatness or invertibility
condition on g is used. The generator and universal-property computations
include zero modules, zero pairings, empty schemes and identity morphisms. -/
theorem picardPairing_comp
    {X Y Z : Scheme.{u}} (k : Z ⟶ Y) (l : Y ⟶ X) (t : Z ⟶ X)
    (e : k ≫ l = t) (M N : X.Modules)
    (g : M ⊗ N ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (picardTensorObjIso k ((tensorPullback l).obj M) ((tensorPullback l).obj N)).inv ≫
      (tensorPullback k).map
        ((picardTensorObjIso l M N).inv ≫ (tensorPullback l).map g ≫
          (picardTensorUnitIso l).hom) ≫ (picardTensorUnitIso k).hom =
    (((picardTensorCompIso k l M).hom ≫
        (eqToIso (congrArg (fun s ↦ (tensorPullback s).obj M) e)).hom) ⊗ₘ
      ((picardTensorCompIso k l N).hom ≫
        (eqToIso (congrArg (fun s ↦ (tensorPullback s).obj N) e)).hom)) ≫
      (picardTensorObjIso t M N).inv ≫ (tensorPullback t).map g ≫
        (picardTensorUnitIso t).hom := by sorry

end AlgebraicGeometry.Scheme.Modules

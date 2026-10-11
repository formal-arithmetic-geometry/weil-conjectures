/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Topology.Sheaves.Flasque
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom

/-! # Flasqueness of internal Hom into an injective module

Source: Stacks Project, Cohomology, Tag 01EA, the extension-by-zero argument applied
 to the restricted source module (blueprint: lem-sc-ext-coherent-hom-injective-flasque).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- On a Noetherian scheme, internal Hom from a coherent module into an injective module
has flasque underlying abelian sheaf. Source: Stacks Project, Cohomology, Tag 01EA,
with the same extension-by-zero argument for Hom
(blueprint: lem-sc-ext-coherent-hom-injective-flasque).

Proof:
1. For an open `V`, sections of internal Hom are maps `F|_V ⟶ I|_V`
   (`def-pur-sheaf-hom`). The extension-by-zero adjunction identifies these with
   maps `j_{V!}(F|_V) ⟶ I` (`lem-weil-pbc-module-extension-by-zero-adjunction`, clause 2).
2. For `U' ⊆ U`, the canonical map `j_{U'!}(F|_{U'}) ⟶ j_{U!}(F|_U)` is the identity
   at stalks in `U'` and has zero source elsewhere (the stalk clause of the same node).
   It is monic by the stalkwise exactness criterion
   (`lem-weil-pbc-module-stalk-exact`, clause 5, applied to the complex starting with zero).
3. Injectivity of `I` (`def-sp-injective-resolutions`) makes precomposition with this
   monomorphism surjective. Under the adjunction bijections, this is restriction of
   Hom sections: on `U'` the canonical map is the identity on the restricted `F`.
4. All restriction maps are therefore surjective, which is flasqueness
   (`def-sc-zariski-flasque`). -/
theorem isFlasque_homObj_of_coherent_injective (X : Scheme.{u})
    [IsNoetherian X]
    (F I : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (hF : RingedSpace.IsCoherent X.toRingedSpace F) [Injective I] :
    TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj
        (SheafOfModules.homObj (R := X.sheaf) F I)) := by
  sorry

end AlgebraicGeometry

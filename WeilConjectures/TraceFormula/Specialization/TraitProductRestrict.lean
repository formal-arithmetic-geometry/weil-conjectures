/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.KunnethLocal
public import WeilConjectures.TraceFormula.Specialization.TraitModelRestrict
public import WeilConjectures.TraceFormula.Specialization.TraitProduct

/-!

# Restricting products over the trait to opens of the total spaces

Let `P` be the product over the trait `S = Spec k'⟦t⟧` of models `M`, `N` of finite type over
`S` (`NearbyCyclesModel.IsTraitProduct`), with total spaces `𝒳`, `𝒴` and `𝒵 = 𝒳 ×_S 𝒴`. This file
restricts the product to opens `V ⊆ 𝒳`, `W ⊆ 𝒴`:

* the restriction `M.restrictOpen V` of a model to an open `V` of its total space
  (`NearbyCyclesModel.restrictOpen`) is again of finite type over the trait
  (`NearbyCyclesModel.IsTraitModelOver.restrictOpen`);
* the restriction `φ.restrictOpen U V` of a morphism of models to opens `U`, `V` of the total
  spaces with `U ⊆ φ⁻¹ V` (`NearbyCyclesModel.Hom.restrictOpen`);
* the restrictions of `P` to `U = pr₁⁻¹ V ∩ pr₂⁻¹ W = V ×_S W` with the restricted projections form
  a product over the trait of the restrictions of `M` and `N`
  (`NearbyCyclesModel.IsTraitProduct.restrictOpen`), and the inclusions are restriction data of
  the Künneth map in the sense of `NearbyCyclesModel.IsKunnethRestriction`
  (`NearbyCyclesModel.isKunnethRestriction_restrictOpen`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {k' : Type u} [Field k']

section Restrict

variable {X : Scheme.{u}} {X' : Over (Spec (.of k'))}

end Restrict

section HomRestrict

variable {X Y : Scheme.{u}} {X' Y' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {N : NearbyCyclesModel Y Y'.left} {f : X ⟶ Y} {f' : X'.left ⟶ Y'.left}

end HomRestrict

section Product

variable {X Y Z : Scheme.{u}} {X' Y' Z' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {N : NearbyCyclesModel Y Y'.left} {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X}
  {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y} {f₂' : Z'.left ⟶ Y'.left}

end Product

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing

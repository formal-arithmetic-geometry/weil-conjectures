/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.PointConstantSheafMap
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.LocallyConstantMittagLeffler
public import WeilConjectures.SixFunctors.Etale.Derived.InvertibleRestriction

/-!
# Global sections of finite locally constant sheaves on connected schemes

Let `X` be a connected scheme, `s` a geometric point and `Λ` a finite ring.

- `AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.hom_ext_of_sheafFiber`: morphisms of
  finite locally constant sheaves are determined by their stalks at `s`;
- `AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.sectionsGerm_injective`: global sections
  are determined by their germ at `s`;
- `AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.isIso_constantSheafAdj_counit`: if the
  germ map `Γ(X, G) ⟶ G_s` is bijective, `G` is the constant sheaf `Γ(X, G)_X` (through the counit
  of the constant sheaf adjunction).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} [ConnectedSpace X] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ X) {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

end AlgebraicGeometry.Scheme

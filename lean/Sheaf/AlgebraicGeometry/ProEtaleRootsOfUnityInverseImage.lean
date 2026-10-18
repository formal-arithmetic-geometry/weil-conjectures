/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.AlgebraicGeometry.ProEtaleStructureSheaf

/-! # Inverse-image comparison for pro-etale roots of unity

Source: Stacks Project, Tag 03PK (blueprint: def-pur-roots-of-unity-inverse-image).

## Main definitions

- `proEtaleRootsOfUnityDirectImageMap`: pullback of roots along the projection.
- `proEtaleRootsOfUnityInverseImageMap`: its inverse-image adjunct.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Pullback of roots along the fibre-product projection uniquely determines a sheaf map.
Source: Stacks Project, Tag 03PK (blueprint: def-pur-roots-of-unity-inverse-image).
Proof: on `V`, pull units back by the global-sections ring map of `pullback.fst V.hom f`.
Ring homomorphisms preserve multiplication, powers and one, so this is a group homomorphism
on roots. The pullback projection commutes with every arrow `V' → V`; functoriality of
global sections gives naturality. The roots-section equivalences and injectivity of their
inclusions imply uniqueness sectionwise, hence uniqueness as a sheaf map. -/
theorem existsUnique_proEtaleRootsOfUnityDirectImageMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : ℕ) :
    ∃! b : proEtaleRootsOfUnitySheaf Y N ⟶
        (proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}).obj
          (proEtaleRootsOfUnitySheaf X N),
      ∀ (V : Y.ProEtᵒᵖ) (x : (proEtaleRootsOfUnitySheaf Y N).obj.obj V),
        proEtaleRootsOfUnitySections X N ((proEtaleBaseChange f).op.obj V)
            (b.hom.app V x) =
          Additive.ofMul (restrictRootsOfUnity
            (pullback.fst V.unop.hom f).appTop.hom N
              (Additive.toMul (proEtaleRootsOfUnitySections Y N V x))) := by
  sorry

/-- The direct-image root map `β`, fixed uniquely by the fibre-product projection formula.
Source: Stacks Project, Tag 03PK (blueprint: def-pur-roots-of-unity-inverse-image). -/
noncomputable def proEtaleRootsOfUnityDirectImageMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : ℕ) :
    proEtaleRootsOfUnitySheaf Y N ⟶
      (proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}).obj
        (proEtaleRootsOfUnitySheaf X N) :=
  (existsUnique_proEtaleRootsOfUnityDirectImageMap f N).exists.choose

/-- The comparison `c` is the adjoint of `β`, using the recorded inverse-image adjunction.
Source: Stacks Project, Tag 03PK (blueprint: def-pur-roots-of-unity-inverse-image). -/
noncomputable def proEtaleRootsOfUnityInverseImageMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : ℕ) :
    (proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj
        (proEtaleRootsOfUnitySheaf Y N) ⟶ proEtaleRootsOfUnitySheaf X N :=
  ((proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv _ _).symm
    (proEtaleRootsOfUnityDirectImageMap f N)

end AlgebraicGeometry.Scheme

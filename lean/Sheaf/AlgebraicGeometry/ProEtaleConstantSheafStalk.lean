/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk
public import Sheaf.Paper.ProEtaleLocallyConstantSheaf
import Mathlib.CategoryTheory.Limits.Connected

/-!
# Stalks of constant module sheaves on the pro-etale site

Source: Bhatt--Scholze, The pro-etale topology for schemes, Sections 6.5 and 6.8;
Stacks Project, Tags 0F6B, 0F6C, 00Y8(3), and 03CY
(blueprint: lem-weil-proetale-constant-sheaf-stalk).

The additive germ map is specified by the actual sheafification unit and the
coprojection at `(Y,y)`. Scalar compatibility uses the constant-ring germ map;
thus bijectivity expresses an isomorphism over the original coefficient ring.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]

/-- The pointed neighbourhood `(Y,y)`. Source: Stacks Project, before Tag 0F6B
(blueprint: lem-weil-proetale-constant-sheaf-stalk). -/
noncomputable def proEtaleConstantGermNeighbourhood (y : Spec (.of Ω) ⟶ Y) :
    ProEtaleGeometricNeighbourhood y :=
  StructuredArrow.mk (Y := ProEt.mk (𝟙 Y)) (Over.homMk y (Category.comp_id y))

/-- The coefficient homomorphism sending a scalar to its constant germ at `(Y,y)`.
Source: Stacks Project, Tags 00Y8(3), 03CY
(blueprint: lem-weil-proetale-constant-sheaf-stalk). -/
noncomputable def proEtaleConstantRingGerm (y : Spec (.of Ω) ⟶ Y)
    (A : Type u) [CommRing A] :
    ULift.{u + 1, u} A →+* proEtaleGeometricStalkRing y
      ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1, u} A))) :=
  ((colimit.ι (proEtaleGeometricStalkRingDiagram y
    ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj
      (CommRingCat.of (ULift.{u + 1, u} A))))
        (op (proEtaleConstantGermNeighbourhood y))).hom).comp
    (((CategoryTheory.toSheafify (ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).app
        (op (ProEt.mk (𝟙 Y)))).hom)

/-- The canonical additive germ map: sheafify a constant section, then take its
class in the pointed-neighbourhood colimit at `(Y,y)`.
Source: Stacks Project, Tags 00Y8(3), 03CY
(blueprint: lem-weil-proetale-constant-sheaf-stalk). -/
noncomputable def proEtaleConstantModuleGerm (y : Spec (.of Ω) ⟶ Y)
    (A : Type u) [CommRing A] (M : ModuleCat.{u + 1} (ULift.{u + 1, u} A)) :
    M →+ proEtaleGeometricModuleStalk y
      ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1, u} A))) (proEtaleConstantModuleSheaf Y A M) :=
  ((colimit.ι
    ((proEtaleGeometricNeighbourhoodForget y).op ⋙
      (proEtaleConstantModuleSheaf Y A M).val.presheaf)
        (op (proEtaleConstantGermNeighbourhood y))).hom).comp
    (((CategoryTheory.toSheafify (ProEt.topology Y)
      (proEtaleConstantModulePresheaf Y.ProEt A M).presheaf).app
        (op (ProEt.mk (𝟙 Y)))).hom)

/-- The canonical constant-section map is an isomorphism of coefficient modules:
it is an additive bijection and respects scalars via the constant-ring germ map.
Consequently its stalk is finite whenever the constant module is finite.
Source: Bhatt--Scholze, Sections 6.5, 6.8; Stacks Project, Tags 0F6B, 0F6C,
00Y8(3), 03CY (blueprint: lem-weil-proetale-constant-sheaf-stalk).

Proof: (1) The module-sheafification interface identifies the underlying abelian
sheaf and its unit with abelian sheafification, with the sheafified scalar action
(`lem-pc-sites-module-sheafification-interface`).
(2) The opposite pointed-neighbourhood category is nonempty and filtered, hence
connected (`def-weil-proetale-geometric-stalk`). Its constant diagram has colimit M;
the coprojection at `(Y,y)` is an isomorphism
(`lem-weil-pbc-colimit-constant-connected-diagram`).
(3) Sheafification preserves this geometric stalk, by lifting geometric points to
covers (0F6C) and compatibility with fibre products, then 00Y8(3)
(`lem-cbc-proetale-sheafification-geometric-stalk`). Composing the constant-diagram
coprojection with the map induced by the actual unit gives exactly the germ map
above, so that map is bijective.
(4) Represent a scalar and module section together at `(Y,y)`. The module unit
sends `a • m` to the product of the ring-unit image of `a` with the module-unit
image of `m`. The common-refinement stalk action preserves this equality. Thus
the additive bijection is coefficient-linear. Its inverse respects addition and
scalar multiplication by injectivity, so it is a module isomorphism. Transporting
a finite underlying set across this bijection proves the last assertion. -/
theorem proEtaleConstantModuleGerm_bijective (y : Spec (.of Ω) ⟶ Y)
    (A : Type u) [CommRing A] (M : ModuleCat.{u + 1} (ULift.{u + 1, u} A)) :
    Function.Bijective (proEtaleConstantModuleGerm y A M) ∧
      (∀ (a : ULift.{u + 1, u} A) (m : M),
        proEtaleConstantModuleGerm y A M (a • m) =
          proEtaleConstantRingGerm y A a • proEtaleConstantModuleGerm y A M m) ∧
      (Finite M → Finite (proEtaleGeometricModuleStalk y
        ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj
          (CommRingCat.of (ULift.{u + 1, u} A))) (proEtaleConstantModuleSheaf Y A M))) := by
  sorry

end AlgebraicGeometry.Scheme

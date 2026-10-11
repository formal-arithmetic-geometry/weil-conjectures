module

public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct

/-!
# Universal property of the sheaf tensor product

Source: literature/stacks-project/sites-modules.tex, Section 03EK, display after Tag 0GMW
(blueprint: lem-pc-sites-sheaf-tensor-bilinear-universal)
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace SheafOfModules

set_option autoImplicit false

attribute [local instance] monoidalCategory

/-- Composition with the pure-tensor map `F × G → F ⊗_O G` is a bijection from
`Hom_O(F ⊗_O G, H)` to the set of morphisms of sheaves of sets `F × G → H` that are
`O(U)`-bilinear on sections over every `U`. A bilinear morphism is a family `β` of
`O(U)`-bilinear maps (curried linear maps) compatible with the restriction maps; the
pure-tensor map sends `(x, y)` over `U` to the image of `x ⊗ y` under the sheafification
unit of the presheaf tensor product, identified with `F ⊗ G` by
`tensorObjIsoSheafification`. The statement says that every such `β` is the composite of
exactly one morphism `F ⊗ G ⟶ H` with the pure-tensor map (naturality in `H` holds by
definition of the composite).
Source: literature/stacks-project/sites-modules.tex, Section 03EK, display after Tag 0GMW
(blueprint: lem-pc-sites-sheaf-tensor-bilinear-universal)
Proof: sectionwise, `O(U)`-bilinear maps `F(U) × G(U) → H(U)` correspond to `O(U)`-linear
maps `F(U) ⊗_{O(U)} G(U) → H(U)` (Tag 00CV), compatibly with restrictions, so restriction-
compatible bilinear families correspond to morphisms from the presheaf tensor product
[def-pur-presheaf-tensor-product] into `H`; since `H` is a sheaf, these factor uniquely
through the sheafification [def-weil-presheaf-modules-sheafification], which is `F ⊗_O G`
[def-pur-sheaf-tensor-product]. The resulting correspondence is composition with the
pure-tensor map and is natural in `H`.
-/
theorem tensor_bilinear_universal {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    (F G H : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (β : ∀ U : Cᵒᵖ,
      F.val.obj U →ₗ[R.obj.obj U] G.val.obj U →ₗ[R.obj.obj U] H.val.obj U)
    (hβ : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (x : F.val.obj U) (y : G.val.obj U),
      β V (F.val.map f x) (G.val.map f y) = H.val.map f (β U x y)) :
    ∃! φ : F ⊗ G ⟶ H, ∀ (U : Cᵒᵖ) (x : F.val.obj U) (y : G.val.obj U),
      φ.val.app U ((tensorObjIsoSheafification F G).inv.val.app U
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj)).unit.app
            (F.val ⊗ G.val)).app U (x ⊗ₜ[R.obj.obj U] y))) = β U x y := by
  sorry

end SheafOfModules

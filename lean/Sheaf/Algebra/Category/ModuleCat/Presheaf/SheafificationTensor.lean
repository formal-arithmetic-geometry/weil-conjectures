/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct

/-!
# Module sheafification commutes with tensor products

Source: Stacks Project, Modules on Sites, Tag 0GMW, lemma-sheafification-tensor
(blueprint: lem-pc-sites-module-sheafification-tensor).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace PresheafOfModules

set_option autoImplicit false

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  {O : Cᵒᵖ ⥤ CommRingCat.{u}} {R : Sheaf J CommRingCat.{u}}

/-- The canonical tensor comparison is an isomorphism, natural in both presheaf modules.
The locally bijective ring map identifies `R` with the sheafification of `O`. The displayed
pure-tensor identity specifies the canonical comparison, using the sheafification units.
Source: Stacks Project, Tag 0GMW (blueprint: lem-pc-sites-module-sheafification-tensor).

Proof:
1. Sectionwise pure tensors of the module sheafification maps define a balanced map from
   the presheaf tensor to the tensor of the associated modules. The action and linearity
   come from lem-pc-sites-module-sheafification-interface.
2. Sheafify this map using the interface and def-pur-sheaf-tensor-product to obtain the
   morphism from the sheafified presheaf tensor to the sheaf tensor.
3. Extend the original pure-tensor pairing uniquely to the associated modules, using
   lem-pc-sites-module-sheafification-bilinear-extension. The universal property in
   lem-pc-sites-sheaf-tensor-bilinear-universal gives the inverse morphism.
4. Precompose both composites with the sheafification units. They agree with identities
   on pure tensors. Uniqueness of sheafification and of bilinear extension makes both
   composites identities. The same characterization commutes with morphisms in both
   factors, giving the natural isomorphism and the displayed pure-tensor identity. -/
theorem exists_sheafificationTensorIso
    (α : (O ⋙ forget₂ CommRingCat.{u} RingCat.{u}) ⟶
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α] :
    letI := SheafOfModules.monoidalCategory R
    ∃ e : (sheafification α).prod (sheafification α) ⋙ tensor _ ≅
        tensor (PresheafOfModules.{u} (O ⋙ forget₂ CommRingCat.{u} RingCat.{u})) ⋙
          sheafification α,
      ∀ (F G : PresheafOfModules.{u} (O ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
        (U : Cᵒᵖ) (f : F.obj U) (g : G.obj U),
        (e.inv.app (F, G)).val.app U
          (((sheafificationAdjunction α).unit.app (F ⊗ G)).app U
            (f ⊗ₜ[O.obj U] g)) =
        (SheafOfModules.tensorObjIsoSheafification
          ((sheafification α).obj F) ((sheafification α).obj G)).inv.val.app U
            (((sheafificationAdjunction
              (𝟙 ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj)).unit.app
              (((sheafification α).obj F).val ⊗ ((sheafification α).obj G).val)).app U
                ((((sheafificationAdjunction α).unit.app F).app U f) ⊗ₜ[R.obj.obj U]
                  (((sheafificationAdjunction α).unit.app G).app U g))) := by
  sorry

/-- With an already sheafified first factor, tensoring commutes with module sheafification,
including restriction of scalars along the ring sheafification map. The isomorphism of
bifunctors expresses naturality in the sheaf and the presheaf simultaneously.
Source: Stacks Project, Tag 0GMW (blueprint: lem-pc-sites-module-sheafification-tensor).

Proof: apply the preceding comparison to the restricted underlying presheaf of `G` and
`F`. The counit of lem-pc-sites-module-sheafification-interface identifies the associated
module of the restricted `G` with `G`: its underlying abelian sheaf is the sheafification
of a sheaf, hence its unit is invertible by def-weil-pbc-sheafification. The inverse is
linear by the interface's factorization property. Substitute this counit isomorphism in
Step 4's tensor comparison. Naturality of the counit and that comparison gives naturality
in `G` and `F`. -/
theorem nonempty_sheafTensorSheafificationIso
    (α : (O ⋙ forget₂ CommRingCat.{u} RingCat.{u}) ⟶
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α] :
    letI := SheafOfModules.monoidalCategory R
    Nonempty
      ((𝟭 (SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))).prod
          (sheafification α) ⋙ tensor _ ≅
        ((SheafOfModules.forget _ ⋙ restrictScalars α).prod
          (𝟭 (PresheafOfModules.{u} (O ⋙ forget₂ CommRingCat.{u} RingCat.{u})))) ⋙
            tensor _ ⋙ sheafification α) := by
  sorry

end PresheafOfModules

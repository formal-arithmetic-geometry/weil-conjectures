/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.Ring.Limits
/-!
# Existence of bilinear extensions through module sheafification

Source: Stacks Project, Modules on Sites, Tag 0GMW.
-/

@[expose] public section
universe u v w
open CategoryTheory
namespace PresheafOfModules
/-- A restriction-compatible bilinear family extends to the module sheafifications.
Source: Stacks Project, Modules on Sites, Tag 0GMW, the sheafification step of the
construction of tensor products.
(blueprint: lem-pc-sites-module-sheafification-bilinear-extension-existence)

Proof: Forget the module structures. The underlying maps of the two module
sheafification units are locally bijective maps of presheaves of sets, so their
product is locally bijective. Since the underlying presheaf of sets of `H` is a
sheaf, the natural map `(x,y) ↦ β X x y` extends uniquely to a natural map from
the product of the underlying sheafifications to `H`. Its unit equation is the
factorization equation. To prove additivity in the first variable, compare its
value on `(x + x', y)` with the sum of its values on `(x,y)` and `(x',y)`.
On a common covering sieve, all three sections lift along the module units;
naturality, the unit equation, and additivity of `β` make their restrictions
agree. Separatedness of `H` gives equality. The second-variable argument uses
lifts of `x,y,y'` in the same way. For scalar compatibility, also lift the scalar
along the locally surjective ring map `α`, on a common refinement of the covers
lifting the module sections. The units respect the scalar actions; linearity of
`β` over `O` proves both scalar identities on this cover, and separatedness gives
the identities over `R`. Thus the natural set map defines a curried `R`-linear
map at every object, with exactly the required naturality and unit equations. -/
theorem exists_bilinear_sheafification_extension
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J AddCommGrpCat.{max u v w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    (O : Cᵒᵖ ⥤ CommRingCat.{max u v w}) (R : Sheaf J CommRingCat.{max u v w})
    (α : (O ⋙ forget₂ CommRingCat.{max u v w} RingCat.{max u v w}) ⟶
      ((sheafCompose J (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})).obj R).obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    (F G : PresheafOfModules.{max u v w} (O ⋙ forget₂ CommRingCat.{max u v w} RingCat.{max u v w}))
    (H : SheafOfModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})).obj R))
    (β : ∀ X : Cᵒᵖ, F.obj X →ₗ[O.obj X] G.obj X →ₗ[O.obj X]
      ((restrictScalars α).obj H.val).obj X)
    (hβ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : F.obj X) (y : G.obj X),
      β Y (F.map f x) (G.map f y) = H.val.map f (β X x y)) :
    ∃ γ : ∀ X : Cᵒᵖ,
      ((sheafification α).obj F).val.obj X →ₗ[R.obj.obj X]
        ((sheafification α).obj G).val.obj X →ₗ[R.obj.obj X] H.val.obj X,
      (∀ {X Y : Cᵒᵖ} (f : X ⟶ Y)
        (x : ((sheafification α).obj F).val.obj X)
        (y : ((sheafification α).obj G).val.obj X),
        γ Y (((sheafification α).obj F).val.map f x)
          (((sheafification α).obj G).val.map f y) = H.val.map f (γ X x y)) ∧
      (∀ (X : Cᵒᵖ) (x : F.obj X) (y : G.obj X),
        γ X (((sheafificationAdjunction α).unit.app F).app X x)
          (((sheafificationAdjunction α).unit.app G).app X y) = β X x y) := by
  sorry
end PresheafOfModules

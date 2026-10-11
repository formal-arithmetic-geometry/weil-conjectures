/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-!
# Gluing morphisms of sheaves of modules on a covering family

Source: Stacks Project, Modules on Sites, Lemma 03EM, using Sites Lemma 04TQ
(blueprint: lem-pur-sheaf-hom-cover-gluing).
-/

@[expose] public section

universe w v v₁ u₁ u

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

/-- (blueprint: lem-pur-sheaf-hom-cover-gluing) Compatible local linear maps glue uniquely.
Source: Stacks Project, Modules on Sites, Lemma 03EM, via Sites Lemma 04TQ.

The hypothesis `hcompatible` states equality on every object of the localized overlap site.
The conclusion states equality on every object over each cover member, hence equality of the
restricted morphisms. The pullback hypotheses require only the fiber products used here.

Proof: Work in `C/U` (def-pur-localized-ringed-site). For `V → U`, pull back the cover to
`V ×_U Uᵢ → V`. Apply the local maps to the restrictions of a section of `F(V)`.
Compatibility identifies their values on pairwise overlaps. The sheaf axiom for `G` gives a
unique section of `G(V)` (def-weil-sheaf-of-modules-category). Uniqueness applied to sums and
restriction maps makes these assignments additive and natural. Their restrictions are the
original local maps, again by sheaf uniqueness; the same argument identifies any other glued
map with this one. Finally, for a scalar in `O(V)`, local linearity identifies the restrictions
of the image of a scalar multiple with the scalar multiple of the image. Sheaf uniqueness
makes these equal globally. Thus the glued map is `O|_U`-linear. -/
theorem existsUnique_hom_of_cover
    {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    (R : Cᵒᵖ ⥤ CommRingCat.{u})
    (hR : Presheaf.IsSheaf J (R ⋙ forget₂ CommRingCat RingCat.{u}))
    (F G : SheafOfModules.{v} ⟨R ⋙ forget₂ CommRingCat RingCat.{u}, hR⟩)
    (U : C) (I : Type w) (Uᵢ : I → C) (f : ∀ i : I, Uᵢ i ⟶ U)
    [∀ (V : C) (g : V ⟶ U) (i : I), HasPullback g (f i)]
    (hcover : Sieve.ofArrows Uᵢ f ∈ J U)
    (φᵢ : ∀ i : I, F.over (Uᵢ i) ⟶ G.over (Uᵢ i))
    (hcompatible : ∀ (i j : I) (W : C) (a : W ⟶ pullback (f i) (f j)),
      (φᵢ i).val.app (op (Over.mk (a ≫ pullback.fst (f i) (f j)))) =
        (φᵢ j).val.app (op (Over.mk (a ≫ pullback.snd (f i) (f j))))) :
    ∃! φ : F.over U ⟶ G.over U,
      ∀ (i : I) (V : C) (a : V ⟶ Uᵢ i),
        φ.val.app (op (Over.mk (a ≫ f i))) = (φᵢ i).val.app (op (Over.mk a)) := by
  sorry

end SheafOfModules

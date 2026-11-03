/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.EpiMono

/-! # Rigidity of a restricted represented functor

Source: the supported-Hom argument in the latest blueprint's proof of
`lem-pur-gysin-structure` (blueprint: lem-pur-restricted-coyoneda-rigidity).
-/

@[expose] public section

set_option autoImplicit false

universe u₁ u₂ u₃ v₁ v₂ v₃

namespace CategoryTheory

/-- A natural operation on a restricted represented functor is the identity if it fixes
precomposition by an epimorphism at the representing object. The epimorphism is required
only before applying the fully faithful functor; its image need not be epimorphic.
Source: the supported-Hom identification in `lem-pur-gysin-structure.proof.md`, and
the Yoneda argument in `lem-pur-coordinate-gysin-support-counit`.
(blueprint: lem-pur-restricted-coyoneda-rigidity).

Proof: evaluate the operation on the inverse of the given representation isomorphism.
Compose with its hom to obtain an endomorphism of F(B), and lift it through F. The
normalization and faithfulness say that its lift fixes q. Cancel the epimorphism q,
so this endomorphism is the identity. Every map from F(B) to G(K) is the inverse of
the representation isomorphism followed by the image of a map R to K, by fullness
of G. Naturality now identifies its image under the operation with itself. This
also covers an empty category of test maps, and does not require additive structure. -/
theorem restrictedCoyoneda_rigidity
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E]
    (F : C ⥤ D) [F.Full] [F.Faithful] (G : E ⥤ D) [G.Full]
    {A B : C} (q : A ⟶ B) [Epi q] (R : E) (e : G.obj R ≅ F.obj B)
    (t : ∀ K : E, (F.obj B ⟶ G.obj K) → (F.obj B ⟶ G.obj K))
    (ht : ∀ {K L : E} (g : K ⟶ L) (f : F.obj B ⟶ G.obj K),
      t L (f ≫ G.map g) = t K f ≫ G.map g)
    (hq : F.map q ≫ t R e.inv = F.map q ≫ e.inv) :
    ∀ (K : E) (f : F.obj B ⟶ G.obj K), t K f = f := by
  let a : B ⟶ B := F.preimage (t R e.inv ≫ e.hom)
  have ha : q ≫ a = q := by
    apply F.map_injective
    simp only [Functor.map_comp, a, Functor.map_preimage]
    rw [← Category.assoc, hq]
    simp
  have ha' : a = 𝟙 B := (cancel_epi q).1 (by simpa using ha)
  have htR : t R e.inv = e.inv := by
    have h := congrArg F.map ha'
    simp only [a, Functor.map_preimage, Functor.map_id] at h
    apply (cancel_mono e.hom).1
    simpa using h
  intro K f
  let g : R ⟶ K := G.preimage (e.hom ≫ f)
  have hg : G.map g = e.hom ≫ f := G.map_preimage _
  have h := ht g e.inv
  rw [hg, htR] at h
  simpa using h

end CategoryTheory

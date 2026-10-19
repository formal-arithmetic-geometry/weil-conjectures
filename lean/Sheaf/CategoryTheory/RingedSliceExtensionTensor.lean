/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Sheaf.CategoryTheory.RingedSliceExtensionTensorHomData

/-!
# Tensor projection formula for a ringed-site slice

Source: Stacks Project, Modules on Sites, Tag 0E8I, lemma-j-shriek-and-tensor
(blueprint: lem-weil-pbc-ringed-slice-extension-tensor).

Both sheaf tensors are written as sheafified presheaf tensors, exactly as in
`SheafOfModules.tensorObjIsoSheafification`. This permits a site object universe independent
of the coefficient universe and does not require a chosen monoidal structure on sheaves.
-/

@[expose] public section

universe uC u

open CategoryTheory

namespace SheafOfModules

private theorem iso_of_hom_data
    {D : Type uC} [Category.{u} D] {E : Type (max u uC)} [Category.{u} E]
    (A B : D ⥤ E)
    (e : ∀ X : D, ∀ H : E, ((A.obj X ⟶ H) ≃ (B.obj X ⟶ H)))
    (hH : ∀ (X : D) (H K : E) (φ : A.obj X ⟶ H) (h : H ⟶ K),
      e X K (φ ≫ h) = e X H φ ≫ h)
    (hX : ∀ (X Y : D) (H : E) (f : X ⟶ Y) (φ : A.obj Y ⟶ H),
      e X H (A.map f ≫ φ) = B.map f ≫ e Y H φ) :
    Nonempty (A ≅ B) := by
  let hom : ∀ X : D, A.obj X ⟶ B.obj X := fun X =>
    (e X (B.obj X)).symm (𝟙 _)
  let inv : ∀ X : D, B.obj X ⟶ A.obj X := fun X =>
    e X (A.obj X) (𝟙 _)
  have hhom : ∀ X : D, hom X ≫ inv X = 𝟙 _ := by
    intro X
    apply (e X (A.obj X)).injective
    rw [hH]
    simp [hom, inv]
  have hinv : ∀ X : D, inv X ≫ hom X = 𝟙 _ := by
    intro X
    have hh := hH X (A.obj X) (B.obj X) (𝟙 _) (hom X)
    rw [← hh]
    simp [hom]
  have hn : ∀ {X Y : D} (f : X ⟶ Y),
      A.map f ≫ hom Y = hom X ≫ B.map f := by
    intro X Y f
    apply (e X (B.obj Y)).injective
    rw [hX, hH]
    simp [hom]
  let c : ∀ X : D, A.obj X ≅ B.obj X := fun X =>
    { hom := hom X, inv := inv X, hom_inv_id := hhom X, inv_hom_id := hinv X }
  exact ⟨NatIso.ofComponents c (by intro X Y f; exact hn f)⟩

/-- Extension by zero commutes with tensoring by a restricted module, naturally in both
module variables. The domain of both functors is the product of the slice module category
and the original module category, in that order. Extension is the direct-sum presheaf
extension followed by module sheafification; each tensor is also sheafified sectionwise.

Source: Stacks Project, Modules on Sites, Tag 0E8I, lemma-j-shriek-and-tensor
(blueprint: lem-weil-pbc-ringed-slice-extension-tensor).

Proof:
1. Relocalization identifies internal Hom of restricted modules with restricted internal
   Hom, sectionwise by the same linear maps. Restrictions and scalar multiplication agree;
   precomposition and postcomposition commute with this identification
   (`def-pur-sheaf-hom`, `def-pur-localized-ringed-site`, Stacks 0E8H).
2. For a test module H, extension adjunction and tensor-Hom adjunction give
   Hom(j_!(G tensor F|U), H) = Hom(G, Hom(F|U,H|U)), naturally in all variables
   (`lem-pur-site-restriction-module-adjunction-exact`,
   `lem-pc-sheaf-modules-tensor-closed`).
3. Apply step 1, then the inverse extension adjunction and inverse tensor-Hom adjunction,
   obtaining Hom(j_!G tensor F,H), still naturally in G,F,H.
4. If E is this Hom equivalence from A to B, set u = E(id_A) : B -> A and
   v = E.symm(id_B) : A -> B. Test-object naturality gives E(q) = u followed by q
   and E.symm(r) = v followed by r. The inverse equivalence identities give that u,v
   are inverse, hence the required isomorphism.
5. For simultaneous parameter maps a : A -> A' and b : B -> B', parameter naturality
   gives a after u = u' after b. Composing with the inverses gives v' after a = b after v.
   These component isomorphisms therefore form the displayed natural isomorphism. -/
theorem ringedSlice_extension_tensor
    {C : Type uC} [Category.{u} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u}) (U : C)
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify (J.over U) AddCommGrpCat.{u}] :
    Nonempty (
      ((forget.{u} (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U)).prod
          (overFunctor.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) U ⋙ forget.{u}
          (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U)) ⋙
        MonoidalCategory.tensor
          (C := PresheafOfModules.{u} ((R.over U).obj ⋙ forget₂ CommRingCat RingCat)) ⋙
        PresheafOfModules.sheafification (J := J.over U)
          (R := ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U) (𝟙 _) ⋙
        extensionByZeroPresheaf.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) U ⋙
        PresheafOfModules.sheafification (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
          R).obj)) ≅
      (((extensionByZeroPresheaf.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) U ⋙
          PresheafOfModules.sheafification (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
          R).obj) ⋙
          forget.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).prod (forget.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) ⋙
        MonoidalCategory.tensor (C := PresheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat
          RingCat)).obj R).obj) ⋙
        PresheafOfModules.sheafification (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
          R).obj))) := by
  obtain ⟨e, hH, hX⟩ := ringedSlice_extension_tensor_hom_data J R U
  exact iso_of_hom_data (ringedSliceTensorLeft J R U)
    (ringedSliceTensorRight J R U) e hH hX

end SheafOfModules

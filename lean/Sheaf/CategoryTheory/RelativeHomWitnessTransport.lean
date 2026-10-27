module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.EssentialImage

/-!
# Relative Hom bijections independent of fully faithful witnesses

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower,
lem-weil-finite-duality-site-comparison.proof.md, locally closed comparison;
Stacks Project, Categories, Tag 0037, definition-adjoint and adjunction maps.
(blueprint: lem-sf-relative-hom-witness-transport)
-/

@[expose] public section

set_option autoImplicit false

universe uA vA uP vP uQ vQ

namespace CategoryTheory

/-- Transport relative Hom functions from image objects to the full essential image.
The displayed lambdas are exactly the functions `b^α`; `bar` is their common bijection.
Its final two clauses compare identity transposes only when their objects lie in the
specified domains, without asserting an adjunction on a larger category.

Source: blueprint locally closed exceptional comparison, expanded Steps 6–7;
Stacks Project, Categories, Tag 0037, definition-adjoint and ensuing adjunction maps.
(blueprint: lem-sf-relative-hom-witness-transport)

Proof (the node's seven steps):
1. The inverse of the transported function sends `u` to
   `E.map α.inv ≫ (b L Y).symm (α.hom ≫ u)`. Cancel the two isomorphisms and
   the two composites of `b` and its inverse to prove bijectivity.
2. Naturality of `q` moves `E.map α.hom` past `q.inv`. Apply the assumed image
   normalization and naturality of `a`, then cancel `α`. Thus the transported
   value at `z` is `a K Y (q.hom.app K ≫ z) ≫ θ.hom.app Y`.
3. Bijectivity of the Hom maps of `C` lifts `α ≪≫ β.symm` and its inverse.
   Injectivity and functoriality show that the lifts compose to identities;
   injectivity also gives uniqueness of the lifted isomorphism.
4. The formula in step 2 contains no witness, giving equality for two witnesses.
   Use it to define `bar`; naturality of `q`, `a` and `θ` gives its two naturality laws.
5. In step 2 substitute `(a K Y).symm g` and apply the inverse bijection to get
   the stated inverse formula.
6. For another natural relative family `d`, naturality at `α` and its prescribed
   identity-witness value give `α.hom ≫ d K Y z = b L Y (E.map α.hom ≫ z)`.
   Compose with `α.inv` and conclude equality with `bar` for every object and arrow.
7. Transpose identities, as in lem-weil-pbc-adjunction-of-natural-bijection
   (`Adjunction.mkOfHomEquiv`): step 2 with the identity of `F K` gives the unit
   comparison, and with `(a (J Y) Y).symm (𝟙 (J Y))` gives the counit comparison.
   The category laws used in steps 1–4 are those of def-nagata-category.
-/
theorem relative_hom_witness_transport
    {A : Type uA} [Category.{vA} A]
    {P : Type uP} [Category.{vP} P]
    {Q : Type uQ} [Category.{vQ} Q]
    (C : A ⥤ P)
    (hC : ∀ L L' : A, Function.Bijective (C.map : (L ⟶ L') → _))
    (D : ObjectProperty Q) (F E : P ⥤ Q) (J G : D.FullSubcategory ⥤ P)
    (q : F ≅ E)
    (a : ∀ (K : P) (Y : D.FullSubcategory), (F.obj K ⟶ Y.obj) ≃ (K ⟶ J.obj Y))
    (b : ∀ (L : A) (Y : D.FullSubcategory),
      (E.obj (C.obj L) ⟶ Y.obj) ≃ (C.obj L ⟶ G.obj Y))
    (ha_left : ∀ {K' K : P} (f : K' ⟶ K) (Y : D.FullSubcategory)
      (h : F.obj K ⟶ Y.obj), a K' Y (F.map f ≫ h) = f ≫ a K Y h)
    (ha_right : ∀ (K : P) {Y Y' : D.FullSubcategory} (v : Y ⟶ Y')
      (h : F.obj K ⟶ Y.obj), a K Y' (h ≫ v.hom) = a K Y h ≫ J.map v)
    (hb_left : ∀ {L' L : A} (f : L' ⟶ L) (Y : D.FullSubcategory)
      (z : E.obj (C.obj L) ⟶ Y.obj),
      b L' Y (E.map (C.map f) ≫ z) = C.map f ≫ b L Y z)
    (hb_right : ∀ (L : A) {Y Y' : D.FullSubcategory} (v : Y ⟶ Y')
      (z : E.obj (C.obj L) ⟶ Y.obj), b L Y' (z ≫ v.hom) = b L Y z ≫ G.map v)
    (θ : J ≅ G)
    (hθ : ∀ (L : A) (Y : D.FullSubcategory) (h : F.obj (C.obj L) ⟶ Y.obj),
      b L Y (q.inv.app (C.obj L) ≫ h) = a (C.obj L) Y h ≫ θ.hom.app Y) :
    (∀ (K : P) (L : A) (α : C.obj L ≅ K) (Y : D.FullSubcategory),
      Function.Bijective (fun z : E.obj K ⟶ Y.obj ↦
        α.inv ≫ b L Y (E.map α.hom ≫ z)) ∧
      ∀ h : F.obj K ⟶ Y.obj,
        α.inv ≫ b L Y (E.map α.hom ≫ q.inv.app K ≫ h) = a K Y h ≫ θ.hom.app Y) ∧
    (∀ (K : P) (L L' : A) (α : C.obj L ≅ K) (β : C.obj L' ≅ K),
      (∃! t : L ≅ L', C.mapIso t = α ≪≫ β.symm) ∧
      ∀ Y : D.FullSubcategory,
        (fun z : E.obj K ⟶ Y.obj ↦ α.inv ≫ b L Y (E.map α.hom ≫ z)) =
          (fun z : E.obj K ⟶ Y.obj ↦ β.inv ≫ b L' Y (E.map β.hom ≫ z))) ∧
    ∃ bar : ∀ (K : C.EssImageSubcategory) (Y : D.FullSubcategory),
        (E.obj K.obj ⟶ Y.obj) ≃ (K.obj ⟶ G.obj Y),
      (∀ (K : C.EssImageSubcategory) (L : A) (α : C.obj L ≅ K.obj)
        (Y : D.FullSubcategory) (z : E.obj K.obj ⟶ Y.obj),
        bar K Y z = α.inv ≫ b L Y (E.map α.hom ≫ z)) ∧
      (∀ (K : C.EssImageSubcategory) (Y : D.FullSubcategory) (h : F.obj K.obj ⟶ Y.obj),
        bar K Y (q.inv.app K.obj ≫ h) = a K.obj Y h ≫ θ.hom.app Y) ∧
      (∀ {K' K : C.EssImageSubcategory} (f : K' ⟶ K) (Y : D.FullSubcategory)
        (z : E.obj K.obj ⟶ Y.obj),
        bar K' Y (E.map f.hom ≫ z) = f.hom ≫ bar K Y z) ∧
      (∀ (K : C.EssImageSubcategory) {Y Y' : D.FullSubcategory} (v : Y ⟶ Y')
        (z : E.obj K.obj ⟶ Y.obj), bar K Y' (z ≫ v.hom) = bar K Y z ≫ G.map v) ∧
      (∀ (K : C.EssImageSubcategory) (Y : D.FullSubcategory) (g : K.obj ⟶ J.obj Y),
        (bar K Y).symm (g ≫ θ.hom.app Y) = q.inv.app K.obj ≫ (a K.obj Y).symm g) ∧
      (∀ d : ∀ (K : C.EssImageSubcategory) (Y : D.FullSubcategory),
          (E.obj K.obj ⟶ Y.obj) ≃ (K.obj ⟶ G.obj Y),
        (∀ {K' K : C.EssImageSubcategory} (f : K' ⟶ K) (Y : D.FullSubcategory)
          (z : E.obj K.obj ⟶ Y.obj),
          d K' Y (E.map f.hom ≫ z) = f.hom ≫ d K Y z) →
        (∀ (K : C.EssImageSubcategory) {Y Y' : D.FullSubcategory} (v : Y ⟶ Y')
          (z : E.obj K.obj ⟶ Y.obj), d K Y' (z ≫ v.hom) = d K Y z ≫ G.map v) →
        (∀ (L : A) (Y : D.FullSubcategory), d (C.toEssImage.obj L) Y = b L Y) →
        d = bar) ∧
      (∀ (K : C.EssImageSubcategory) (hF : D (F.obj K.obj)),
        bar K ⟨F.obj K.obj, hF⟩ (q.inv.app K.obj) =
          a K.obj ⟨F.obj K.obj, hF⟩ (𝟙 (F.obj K.obj)) ≫ θ.hom.app ⟨F.obj K.obj, hF⟩) ∧
      (∀ (Y : D.FullSubcategory) (hJ : C.essImage (J.obj Y)),
        bar ⟨J.obj Y, hJ⟩ Y (q.inv.app (J.obj Y) ≫ (a (J.obj Y) Y).symm (𝟙 (J.obj Y))) =
          θ.hom.app Y) := by
  classical
  have _hb_left := @hb_left
  have _hb_right := @hb_right
  -- Compose the given equivalence with pre- and postcomposition by the comparison isos.
  let e (K : P) (Y : D.FullSubcategory) :
      (E.obj K ⟶ Y.obj) ≃ (K ⟶ G.obj Y) :=
    ((q.app K).symm.homFromEquiv.trans (a K Y)).trans (θ.app Y).homToEquiv
  have he (K : P) (Y : D.FullSubcategory) (z : E.obj K ⟶ Y.obj) :
      e K Y z = a K Y (q.hom.app K ≫ z) ≫ θ.hom.app Y := rfl
  have hn (K : P) (L : A) (α : C.obj L ≅ K) (Y : D.FullSubcategory)
      (h : F.obj K ⟶ Y.obj) :
      α.inv ≫ b L Y (E.map α.hom ≫ q.inv.app K ≫ h) =
        a K Y h ≫ θ.hom.app Y := by
    rw [← Category.assoc (E.map α.hom), q.inv.naturality α.hom,
      Category.assoc, hθ, ha_left]
    simp only [← Category.assoc, α.inv_hom_id, Category.id_comp]
  have ht (K : P) (L : A) (α : C.obj L ≅ K) (Y : D.FullSubcategory)
      (z : E.obj K ⟶ Y.obj) :
      α.inv ≫ b L Y (E.map α.hom ≫ z) = e K Y z := by
    simpa only [he, ← Category.assoc (q.inv.app K),
      q.inv_hom_id_app, Category.id_comp]
      using hn K L α Y (q.hom.app K ≫ z)
  have en (K : P) (Y : D.FullSubcategory) (h : F.obj K ⟶ Y.obj) :
      e K Y (q.inv.app K ≫ h) = a K Y h ≫ θ.hom.app Y := by
    simp only [he, ← Category.assoc, q.hom_inv_id_app, Category.id_comp]
  refine ⟨?_, ?_, ?_⟩
  · intro K L α Y
    refine ⟨?_, hn K L α Y⟩
    simpa only [ht] using (e K Y).bijective
  · intro K L L' α β
    obtain ⟨hCF⟩ := (Functor.FullyFaithful.nonempty_iff_map_bijective C).mpr hC
    constructor
    · refine ⟨hCF.isoEquiv.symm (α ≪≫ β.symm),
        hCF.isoEquiv.apply_symm_apply _, ?_⟩
      intro t ht'
      exact hCF.isoEquiv.injective (ht'.trans (hCF.isoEquiv.apply_symm_apply _).symm)
    · intro Y
      funext z
      rw [ht, ht]
  · refine ⟨fun K Y ↦ e K.obj Y, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro K L α Y z
      exact (ht K.obj L α Y z).symm
    · intro K Y h
      exact en K.obj Y h
    · intro K' K f Y z
      simp only [he]
      rw [← Category.assoc (q.hom.app K'.obj), ← q.hom.naturality f.hom,
        Category.assoc, ha_left, Category.assoc]
    · intro K Y Y' v z
      simp only [he]
      rw [← Category.assoc (q.hom.app K.obj), ha_right, Category.assoc,
        θ.hom.naturality v, ← Category.assoc]
    · intro K Y g
      apply (e K.obj Y).injective
      rw [Equiv.apply_symm_apply, en, Equiv.apply_symm_apply]
    · intro d hd_left _hd_right hd_image
      funext K Y
      apply Equiv.ext
      intro z
      obtain ⟨L, ⟨α⟩⟩ := K.property
      have hd := hd_left
        (ObjectProperty.homMk α.hom : C.toEssImage.obj L ⟶ K) Y z
      change d (C.toEssImage.obj L) Y (E.map α.hom ≫ z) = α.hom ≫ d K Y z at hd
      have hi := (congrArg (fun u : C.obj L ⟶ G.obj Y ↦ α.inv ≫ u) hd).symm
      simp only [← Category.assoc, α.inv_hom_id, Category.id_comp] at hi
      calc
        d K Y z = α.inv ≫ d (C.toEssImage.obj L) Y (E.map α.hom ≫ z) := hi
        _ = α.inv ≫ b L Y (E.map α.hom ≫ z) := by
          exact congrArg (fun t ↦ α.inv ≫ t (E.map α.hom ≫ z)) (hd_image L Y)
        _ = e K.obj Y z := ht K.obj L α Y z
    · intro K hF
      simpa only [Category.comp_id] using en K.obj ⟨F.obj K.obj, hF⟩ (𝟙 _)
    · intro Y hJ
      rw [en, Equiv.apply_symm_apply, Category.id_comp]

end CategoryTheory

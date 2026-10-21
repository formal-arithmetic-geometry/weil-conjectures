/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
Authors: SHEAF group NR
-/
module

public import Sheaf.Paper.SupportedExteriorClasses
public import Sheaf.Paper.PurityFrameClass
public import Sheaf.Paper.PurityConventions
public import Sheaf.Paper.SupportedCup
public import Sheaf.Paper.SupportedCupFunctoriality
public import Sheaf.AlgebraicGeometry.ProEtaleSupportedExteriorProduct
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Sheaf.Paper.SupportedHomAdjunctionTranspose
import Sheaf.Paper.SupportedHomPullback
import Sheaf.Paper.SupportedCohomologyHom
import Sheaf.AlgebraicGeometry.SupportedExteriorProduct

/-!
# Exterior products of frame classes

Source: blueprint main-20261015, sec-smooth-purity/sk-thm-regular, proof Step 5
(blueprint: lem-pur-exterior-product-frame).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v w v₁ w₁

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.ProEtale

namespace WeilConjectures.PurityFiniteSetting

/-- Read the published ordered boundary product on its specified closed subscheme.
An isomorphism over X is exactly the condition that the functions generate that
closed subscheme's ideal. Source: Step 5, frame classes
(blueprint: lem-pur-exterior-product-frame). -/
def exteriorFrameClass (P : PurityFiniteSetting.{u}) {Z X : Scheme.{u}}
    (aX : X ⟶ Spec (.of P.field.k)) (i : Z ⟶ X) (c : ℕ) (f : Fin c → Γ(X, ⊤))
    (e : X.zeroLocusSubscheme (Set.range f) ≅ Z)
    (he : e.hom ≫ i = X.zeroLocusSubschemeι (Set.range f)) :
    P.FunctorialCupH true i (2 * (c : ℤ)) c :=
  (P.functorialCupSingle true X).map
    (P.frameClosedCoefficientIso (X.zeroLocusSubschemeι (Set.range f)) i e he).inv ≫
      P.frameBoundaryProduct X aX c f

/-- The chosen square for the actual pullback. Source: Step 5, pulled-back supports
(blueprint: lem-pur-exterior-product-frame). -/
def exteriorFrameSquare {Z X Y : Scheme.{u}} (i : Z ⟶ X) (v : Y ⟶ X) :
    ChosenCartesianSquare (pullback.fst i v) (pullback.snd i v) i v where
  w := pullback.condition
  isoPullback := Iso.refl _
  hom_fst := by simp
  hom_snd := by simp

/-- Concatenate the two pulled-back tuples, retaining the first block's order.
Source: Step 5, the product frame (blueprint: lem-pur-exterior-product-frame). -/
def exteriorFrameTuple (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of P.field.k)) (aY : Y ⟶ Spec (.of P.field.k))
    {c d : ℕ} (f : Fin c → Γ(X, ⊤)) (g : Fin d → Γ(Y, ⊤)) :
    Fin (c + d) → Γ(pullback aX aY, ⊤) :=
  Fin.addCases (fun k ↦ (pullback.fst aX aY).appTop (f k))
    (fun k ↦ (pullback.snd aX aY).appTop (g k))

/-- The supported cup after two specified Cartesian pullbacks, before the
product projections are substituted. Source: Step 5, middle expression
(blueprint: lem-pur-exterior-product-frame). -/
def exteriorFrameCupCore (P : PurityFiniteSetting.{u})
    {X Y Z W T Z' W' Q : Scheme.{u}}
    (aX : X ⟶ Spec (.of P.field.k)) (aY : Y ⟶ Spec (.of P.field.k))
    (aT : T ⟶ Spec (.of P.field.k))
    (i : Z ⟶ X) (j : W ⟶ Y) (i' : Z' ⟶ T) (j' : W' ⟶ T) (q : Q ⟶ T)
    [IsClosedImmersion i] [IsClosedImmersion j]
    [IsClosedImmersion i'] [IsClosedImmersion j'] [IsClosedImmersion q]
    (p₁ : T ⟶ X) (p₂ : T ⟶ Y) (v₁ : Z' ⟶ Z) (v₂ : W' ⟶ W)
    (s₁ : ChosenCartesianSquare v₁ i' i p₁) (s₂ : ChosenCartesianSquare v₂ j' j p₂)
    (e : Q ≅ pullback i' j') (he : e.hom ≫ cupIntersection i' j' = q)
    (a b r s : ℤ) (α : P.FunctorialCupH true i a r) (β : P.FunctorialCupH true j b s) :
    P.FunctorialCupH true q (a + b) (r + s) :=
  P.functorialCupChangeSupport true q (cupIntersection i' j') e.inv
    (by rw [← he, Iso.inv_hom_id_assoc]) (a + b) (r + s)
    (P.functorialCup true aT i' j' a b r s
      (P.functorialCupPullback true i i' p₁ v₁ s₁ aX a r α)
      (P.functorialCupPullback true j j' p₂ v₂ s₂ aY b s β))

/-- Cup of the projection pullbacks, with precisely the two pulled-back supports.
The given support isomorphism is unique over the ambient scheme, because the
intersection immersion is monic. Source: Step 5, middle expression
(blueprint: lem-pur-exterior-product-frame). -/
def exteriorFrameCup (P : PurityFiniteSetting.{u}) {X Y Z W : Scheme.{u}}
    (aX : X ⟶ Spec (.of P.field.k)) (aY : Y ⟶ Spec (.of P.field.k))
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
    (e : pullback (i ≫ aX) (j ≫ aY) ≅
      pullback (pullback.snd i (pullback.fst aX aY))
        (pullback.snd j (pullback.snd aX aY)))
    (he : e.hom ≫ cupIntersection (pullback.snd i (pullback.fst aX aY))
      (pullback.snd j (pullback.snd aX aY)) = Etale.supportedProductImmersion aX aY i j)
    (a b r s : ℤ) (α : P.FunctorialCupH true i a r) (β : P.FunctorialCupH true j b s) :
    P.FunctorialCupH true (Etale.supportedProductImmersion aX aY i j) (a + b) (r + s) :=
  P.exteriorFrameCupCore aX aY (pullback.fst aX aY ≫ aX) i j
    (pullback.snd i (pullback.fst aX aY)) (pullback.snd j (pullback.snd aX aY))
    (Etale.supportedProductImmersion aX aY i j)
    (pullback.fst aX aY) (pullback.snd aX aY)
    (pullback.fst i (pullback.fst aX aY)) (pullback.fst j (pullback.snd aX aY))
    (exteriorFrameSquare i (pullback.fst aX aY))
    (exteriorFrameSquare j (pullback.snd aX aY)) e he a b r s α β

/-- Transport only the integer degree and twist indices in the supported Hom model.
This is equality elimination, with no functoriality assertion or chosen map.
Source: Step 5, the identities 2c + 2d = 2(c + d) and c + d = c + d
(blueprint: lem-pur-exterior-product-frame). -/
def exteriorFrameReindex (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) {a b r s : ℤ} (ha : a = b) (hr : r = s)
    (α : P.FunctorialCupH pro i a r) : P.FunctorialCupH pro i b s :=
  ha ▸ hr ▸ α

/-- The frame on the product is the ordered concatenation of the two pulled-back
frames. Its ideal is the product support ideal, and its boundary-product class
is both the supported cup of the pulled-back classes and their specified
pro-etale supported exterior product. The isomorphisms in the conclusion only
identify presentations of the same closed subscheme; their equations over the
ambient scheme determine them uniquely. No frame independence or purity
comparison is asserted.

Source: blueprint main-20261015, sec-smooth-purity/sk-thm-regular, proof Step 5
(blueprint: lem-pur-exterior-product-frame).

Proof (the five DAG steps):
1. Smooth relative dimensions persist under base change and add under
   composition (lem-sbc-smooth-relative-dimension-permanence), so the product
   pair is smooth. On affine charts the product ideal is I tensor O plus
   O tensor J; its generators are exactly the displayed concatenation. The
   two pulled-back closed supports intersect scheme-theoretically in Q.
2. Kummer classes and the individual support boundaries commute with
   pullback (lem-pur-supported-cup-functoriality). Thus the factors for the
   concatenated frame are precisely the two pulled-back lists of factors.
3. Associativity of the specified supported cup regroups that ordered list
   into two blocks, without interchanging factors. Tensor associativity gives
   the same twist multiplication. Empty blocks are supported units.
4. The closed coefficient exchanges of lem-pur-supported-hom-pullback
   preserve restriction of 1. The exterior coefficient map sends 1 to
   1 tensor 1, and cup multiplication sends this back to 1. The epic
   constant restriction therefore identifies the exterior comparison with
   the inverse cup coefficient multiplication. Flatness identifies their
   ordinary and derived realizations (def-pur-supported-cup).
5. By lem-pur-supported-hom-adjunction-transpose the Hom representative is
   the shifted supported-adjunction transpose. Apply the specified
   supportedExteriorProductOverField to the two transposed classes. Its
   adjoint is the tensor of their pulled-back adjoints preceded by the
   coefficient comparison of Step 4. This is exactly the supported cup
   representative, including its shift comparison. Both degrees are even,
   so no signs occur. The unit normalization covers either empty tuple. -/
theorem exteriorProduct_frame (P : PurityFiniteSetting.{u})
    {X Y Z W : Scheme.{u}}
    (aX : X ⟶ Spec (.of P.field.k)) (aY : Y ⟶ Spec (.of P.field.k))
    (dX dY c d : ℕ) [SmoothOfRelativeDimension dX aX]
    [SmoothOfRelativeDimension dY aY] [IsSeparated aX] [IsSeparated aY]
    [LocallyOfFiniteType aX] [LocallyOfFiniteType aY] [QuasiCompact aX] [QuasiCompact aY]
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
    [Smooth (i ≫ aX)] [Smooth (j ≫ aY)]
    (_hc : ∀ z : Z, ringKrullDim (X.presheaf.stalk (i z)) =
      ringKrullDim (Z.presheaf.stalk z) + (c : WithBot ℕ∞))
    (_hd : ∀ w : W, ringKrullDim (Y.presheaf.stalk (j w)) =
      ringKrullDim (W.presheaf.stalk w) + (d : WithBot ℕ∞))
    (f : Fin c → Γ(X, ⊤)) (g : Fin d → Γ(Y, ⊤))
    (ef : X.zeroLocusSubscheme (Set.range f) ≅ Z)
    (hf : ef.hom ≫ i = X.zeroLocusSubschemeι (Set.range f))
    (eg : Y.zeroLocusSubscheme (Set.range g) ≅ W)
    (hg : eg.hom ≫ j = Y.zeroLocusSubschemeι (Set.range g))
    (_hQ : ∀ q : ↥(pullback (i ≫ aX) (j ≫ aY) : Scheme.{u}),
      ringKrullDim ((pullback aX aY).presheaf.stalk
        (Etale.supportedProductImmersion aX aY i j q)) =
      ringKrullDim ((pullback (i ≫ aX) (j ≫ aY)).presheaf.stalk q) +
        ((c + d : ℕ) : WithBot ℕ∞)) :
    ∃ (eh : (pullback aX aY).zeroLocusSubscheme
        (Set.range (P.exteriorFrameTuple aX aY f g)) ≅ pullback (i ≫ aX) (j ≫ aY))
      (e : pullback (i ≫ aX) (j ≫ aY) ≅
        pullback (pullback.snd i (pullback.fst aX aY))
          (pullback.snd j (pullback.snd aX aY)))
      (hh : eh.hom ≫ Etale.supportedProductImmersion aX aY i j =
        (pullback aX aY).zeroLocusSubschemeι
          (Set.range (P.exteriorFrameTuple aX aY f g)))
      (he : e.hom ≫ cupIntersection (pullback.snd i (pullback.fst aX aY))
        (pullback.snd j (pullback.snd aX aY)) = Etale.supportedProductImmersion aX aY i j),
      P.exteriorFrameClass (pullback.fst aX aY ≫ aX)
          (Etale.supportedProductImmersion aX aY i j) (c + d)
          (P.exteriorFrameTuple aX aY f g) eh hh =
        P.exteriorFrameReindex true _ (by push_cast; ring) (by push_cast; rfl)
          (P.exteriorFrameCup aX aY i j e he (2 * (c : ℤ)) (2 * (d : ℤ)) c d
            (P.exteriorFrameClass aX i c f ef hf) (P.exteriorFrameClass aY j d g eg hg)) ∧
      P.exteriorFrameClass (pullback.fst aX aY ≫ aX)
          (Etale.supportedProductImmersion aX aY i j) (c + d)
          (P.exteriorFrameTuple aX aY f g) eh hh =
        P.exteriorFrameReindex true _ (by push_cast; ring) (by push_cast; rfl)
          (P.exteriorFrameExternal aX aY i j (2 * (c : ℤ)) (2 * (d : ℤ)) c d
            (P.exteriorFrameClass aX i c f ef hf) (P.exteriorFrameClass aY j d g eg hg)) := by
  sorry

end WeilConjectures.PurityFiniteSetting

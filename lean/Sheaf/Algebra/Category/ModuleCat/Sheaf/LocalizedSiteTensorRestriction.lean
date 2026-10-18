/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q151
-/
module

public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

/-!
# Tensor products and restriction to a localized ringed site

Source: Stacks Project, Modules on Sites, Tags 03EL and 03DH
(blueprint: lem-sfb-localized-site-tensor-restriction).
-/

@[expose] public section

universe uC vC r m

open CategoryTheory Opposite

namespace SheafOfModules

/-- Restriction to a localized ringed site commutes naturally with tensor products,
with the comparison sending each sheafified pure tensor to the same pure tensor.
Source: Stacks Project, Modules on Sites, Tags 03EL and 03DH
(blueprint: lem-sfb-localized-site-tensor-restriction).

Proof:
1. The restriction of the sectionwise tensor presheaf equals the tensor presheaf of
   the restrictions: at `V → U` both have sections `F(V) ⊗ G(V)` and the same
   restriction maps. This identification is natural in both factors, by
   `def-pur-localized-ringed-site` and `def-pur-sheaf-tensor-product`.
2. Apply `lem-cbc-sieve-slice-sheafification` to the underlying abelian presheaf.
   By `def-weil-presheaf-modules-sheafification`, module sheafification has this
   underlying abelian sheafification. The comparison from slice sheafification
   to restricted sheafification commutes with the two units.
3. Transport the module action through this comparison. The unit equation shows
   that the transported action extends the original presheaf action. Uniqueness
   of the extending action in module sheafification makes the comparison linear.
4. Invert that comparison to obtain the isomorphism below. Its unit equation on
   `x ⊗ y` gives the pure-tensor formula. Naturality of the presheaf identification
   and of slice sheafification gives the equation for arbitrary `f` and `g`.
No finiteness, flatness, fibre products or subcanonicity is used. -/
theorem exists_localizedSiteTensorRestriction
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [HasWeakSheafify J AddCommGrpCat.{m}]
    (A : Sheaf J CommRingCat.{r}) (U : C)
    [(J.over U).HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{m}]
    [HasWeakSheafify (J.over U) AddCommGrpCat.{m}] :
    ∃ e : ∀ F G : ringedSiteModules.{m}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A),
        ((siteSheafTensorRight G).obj F).over U ≅
          (siteSheafTensorRight (A := A.over U) (G.over U)).obj (F.over U),
      (∀ (F F' G G' : ringedSiteModules.{m}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))
          (f : F ⟶ F') (g : G ⟶ G'),
        (((siteSheafTensorRight G).map f ≫ siteSheafTensorSecondMap F' g).over U) ≫
            (e F' G').hom =
          (e F G).hom ≫
            (siteSheafTensorRight (A := A.over U) (G.over U)).map (f.over U) ≫
              siteSheafTensorSecondMap (A := A.over U) (F'.over U) (g.over U)) ∧
      (∀ (F G : ringedSiteModules.{m}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))
          (V : Over U) (x : F.val.obj (op V.left)) (y : G.val.obj (op V.left)),
        ((e F G).hom.val.app (op V)) (siteSheafTensorTmul F G (op V.left) x y) =
          siteSheafTensorTmul (A := A.over U) (F.over U) (G.over U) (op V) x y) := by
  sorry

end SheafOfModules

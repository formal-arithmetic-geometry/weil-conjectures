/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IdealModuleQuotients
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import Mathlib.CategoryTheory.Sites.PreservesSheafification

/-! # Sheaf tensor with an ideal quotient

Source: Stacks Project, Modules on Sites, Tags 03EK and 03CY; the quotient identification
and naturality squares extracted in the DAG proof.
(blueprint: lem-weil-pbc-sheaf-tensor-ideal-quotient).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.RingedSiteIdeal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Tensor with the quotient ring is the sheaf quotient by the local ideal product.
The S-module structure is recorded as an S-module Q with an R-linear identification e
with the already constructed quotient. Linearity of a for S is expressed on pure sections:
the S-action on the tensor is multiplication in its second factor. This determines the
entire action by pure-section extensionality. All tensor objects and pure sections are
those of the existing sheaf tensor, not sectionwise tensors substituted for sheaves.

Source: Stacks 03EK, 03CY (blueprint: lem-weil-pbc-sheaf-tensor-ideal-quotient).
Proof:
1. Apply underlying-set compatibility of sheafification and the local-section criterion
   (lem-pc-sites-sheafification-underlying-sets and
   lem-weil-pbc-site-sheafification-sections-local). Quotient sections lift locally and
   equality can be checked after refinement on common restriction cones.
2. The local finite-sum prescription is a submodule subsheaf: intersect covers for sums,
   pull back covers for restrictions, and compose covers for gluing. It equals the
   intersection construction localProduct. The sheafified quotient projection has kernel
   IF and is epic by local representatives and separatedness; use
   def-weil-presheaf-modules-sheafification and def-weil-sheaf-of-modules-category.
3. The quotient presheaf action [r][f]=[rf] is well defined. Apply
   lem-pc-sites-module-sheafification-interface to obtain the canonical S-action on Q.
4. Locally lift s to r, pair f and s by [rf], and glue. Differences of lifts lie locally
   in I. The balanced pairing factors through the sectionwise tensor and sheafifies,
   using def-pur-sheaf-tensor-product and the module sheafification adjunction.
5. Define u(f)=pure(f,1). Balancing kills ideal multiples and hence locally finite sums.
   Thus u descends through the quotient presheaf and sheafifies to b:Q→F⊗S, using
   def-weil-pbc-ringed-tensor-section-calculus.
6. Check ab=1 on quotient representatives and ba=1 on pure tensors after locally lifting
   their scalar factor. Pure-section extensionality and separatedness give the inverses.
   The same calculation with two locally lifted scalar factors proves S-linearity.
7. The formula au=q and invertibility of a give epimorphy and the stated kernel of u.
8. A module map h preserves local ideal sums. Sheafify [f]↦[h(f)]. It is S-linear, and
   both naturality composites send pure(f,[r]) to [r h(f)].
9. For I'⊆I, sheafify the quotient transitions t and v. The tensor transition is exactly
   id⊗t; both comparison composites send pure(f,[r]) to [rf]. On the units the equation
   follows from t(1)=1. No points, flatness, fibre products, or global lifts are used. -/
theorem sheaf_tensor_ideal_quotient
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) :
    ∃ (a : ∀ (I : RingedSiteIdeal R) (F : SheafOfModules.{u} (siteModuleRings R)),
        quotientTensor I F ≅ moduleQuotient I F)
      (uMap : ∀ (I : RingedSiteIdeal R) (F : SheafOfModules.{u} (siteModuleRings R)),
        F ⟶ quotientTensor I F)
      (Q : ∀ (I : RingedSiteIdeal R) (_ : SheafOfModules.{u} (siteModuleRings R)),
        SheafOfModules.{u} (siteModuleRings (ringQuotient I)))
      (e : ∀ (I : RingedSiteIdeal R) (F : SheafOfModules.{u} (siteModuleRings R)),
        (SheafOfModules.RingedTensor.restriction (ringProjection I)).obj (Q I F) ≅
          moduleQuotient I F),
      ∀ (I : RingedSiteIdeal R) (F : SheafOfModules.{u} (siteModuleRings R)),
      Presheaf.IsSheaf J (localProduct I F).toPresheafOfModules.presheaf ∧
      (∀ (U : C) (f : F.val.obj (op U)), f ∈ (localProduct I F).obj (op U) ↔
        ∃ S : Sieve U, S ∈ J U ∧ ∀ (V : C) (g : V ⟶ U), S g →
          ∃ (n : ℕ) (i : Fin n → I.sections V) (x : Fin n → F.val.obj (op V)),
            F.val.map g.op f = ∑ k : Fin n, (i k).val • x k) ∧
      (∀ (W : Cᵒᵖ) (f : F.val.obj W),
        (uMap I F).val.app W f =
          SheafOfModules.RingedTensor.pure R F (quotientCoefficient I) W f
            (1 : (ringQuotient I).obj.obj W)) ∧
      (∀ (W : Cᵒᵖ) (f : F.val.obj W) (r : R.obj.obj W),
        (a I F).hom.val.app W
          (SheafOfModules.RingedTensor.pure R F (quotientCoefficient I) W f
            ((ringProjection I).hom.app W r)) =
          (moduleProjection I F).val.app W (r • f)) ∧
      (∀ (W : Cᵒᵖ) (f : F.val.obj W),
        (a I F).inv.val.app W ((moduleProjection I F).val.app W f) =
          SheafOfModules.RingedTensor.pure R F (quotientCoefficient I) W f
            (1 : (ringQuotient I).obj.obj W)) ∧
      (∀ (W : Cᵒᵖ) (f : F.val.obj W) (s t : (ringQuotient I).obj.obj W),
        (e I F).inv.val.app W ((a I F).hom.val.app W
          (SheafOfModules.RingedTensor.pure R F (quotientCoefficient I) W f (s * t))) =
        s • @id ((Q I F).val.obj W)
          ((e I F).inv.val.app W ((a I F).hom.val.app W
            (SheafOfModules.RingedTensor.pure R F (quotientCoefficient I) W f t)))) ∧
      uMap I F ≫ (a I F).hom = moduleProjection I F ∧
      Epi (uMap I F) ∧
      (∀ (W : Cᵒᵖ) (f : F.val.obj W),
        (uMap I F).val.app W f = 0 ↔ f ∈ (localProduct I F).obj W) ∧
      (∀ (G : SheafOfModules.{u} (siteModuleRings R)) (h : F ⟶ G),
        ∃ (qh : moduleQuotient I F ⟶ moduleQuotient I G) (hS : Q I F ⟶ Q I G),
          moduleProjection I F ≫ qh = h ≫ moduleProjection I G ∧
          (e I F).hom ≫ qh =
            (SheafOfModules.RingedTensor.restriction (ringProjection I)).map hS ≫
              (e I G).hom ∧
          (a I F).hom ≫ qh =
            (SheafOfModules.monoidalCategory R).tensorHom h (𝟙 (quotientCoefficient I)) ≫
              (a I G).hom) ∧
      (∀ (I' : RingedSiteIdeal R) (hI : IsContained I' I),
        ∃ (tM : quotientCoefficient I' ⟶ quotientCoefficient I)
          (v : moduleQuotient I' F ⟶ moduleQuotient I F),
          (∀ (W : Cᵒᵖ) (s : (ringQuotient I').obj.obj W),
            tM.val.app W s = (ringTransition hI).hom.app W s) ∧
          moduleProjection I' F ≫ v = moduleProjection I F ∧
          (a I' F).hom ≫ v =
            (SheafOfModules.monoidalCategory R).tensorHom (𝟙 F) tM ≫ (a I F).hom ∧
          uMap I' F ≫ (SheafOfModules.monoidalCategory R).tensorHom (𝟙 F) tM = uMap I F) := by
  sorry

end CategoryTheory.RingedSiteIdeal

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q26
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-!
# Coproducts of module sheaves inside their products

Source: Stacks Project, Modules on Sites, Tag 03DB, lemma-limits-colimits and its proof;
the explicit locally finite-coordinate construction in the DAG proof
(blueprint: lem-pur-module-sheaf-coproduct-local-support).
-/

@[expose] public section

universe u r

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Source: Stacks Project, Modules on Sites, Tag 03DB, lemma-limits-colimits;
the explicit local-coordinate construction in the DAG proof
(blueprint: lem-pur-module-sheaf-coproduct-local-support).

The subsheaf is presented by a sectionwise injective module-sheaf map `m` into the
product. Its sectionwise range is exactly the displayed local finite-support predicate.
This determines the subsheaf, including its inherited restrictions and module operations,
up to the unique isomorphism over the product. The diagonal and off-diagonal equations
say that the maps `ι i` factor the coordinate insertions. The last two clauses identify
the monomorphism from the chosen coproduct and its sectionwise image with this subsheaf.

Proof (the nine steps of the node):
1. By lem-weil-pbc-module-sheaves-limits-sectionwise, the product of the sheaves `H i`
is computed sectionwise, with coordinatewise restrictions and module operations.
2. Pulling a witnessing cover back proves stability under restriction. The identity
cover with empty support witnesses zero. Negation and scalar multiplication preserve
a witness. For addition use the common pullback refinement of the two covers and the
union of their finite supports. Thus the specified tuples form a subpresheaf of modules.
3. Glue a matching family in the product. Compose its cover with each section's
witnessing cover; the glued tuple has finite support on each composite member. Uniqueness
comes from the product sheaf. Empty covering families are included by unique gluing.
4. A coordinate insertion has support contained in its singleton on the identity cover,
so it factors through the subsheaf; it is linear and commutes with restrictions.
5. Given maps `H i ⟶ T`, on each witnessing cover member sum their values over its
finite support. On overlaps enlarge both supports to their union; the resulting sums
agree, since the additional coordinates vanish. Glue these sums in `T`.
6. Two witnesses give the same glued section: pass to their common pullback refinement,
enlarge to the union of their supports, and apply separatedness. For empty covers use
the uniqueness of the empty gluing.
7. Pull back witnesses to prove naturality. Common refinements and unions prove
additivity; semilinearity of restriction and linearity of the given maps prove scalar
compatibility. The glued map is therefore a module-sheaf morphism.
8. On a coordinate insertion its value is the prescribed map. Conversely, every section
is locally the finite sum of its coordinate insertions, so linearity and separatedness
force uniqueness. This proves the Hom bijection and the discrete colimit property
of def-weil-pbc-category-colimit, also for an empty index set.
9. The two coproduct universal properties identify the chosen coproduct with this
subsheaf, commuting with insertions. Its canonical map to the product is the composite
of this isomorphism with `m`, hence is monic and has exactly the same sectionwise image.
-/
theorem moduleSheaf_coproduct_localSupport
    {C : Type u} [SmallCategory C] (K : Precoverage C)
    (hK : K.IsSiteForCoverings) [HasPullbacks C]
    (R : Sheaf K.toGrothendieck RingCat.{r})
    (hcomm : ∀ (V : Cᵒᵖ) (a b : R.obj.obj V), a * b = b * a)
    [HasSheafify K.toGrothendieck AddCommGrpCat.{u}]
    [K.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (I : Type u) (H : I → ringedSiteModules.{u} R) :
    ∃ (S : ringedSiteModules.{u} R) (m : S ⟶ ∏ᶜ H) (ι : ∀ i : I, H i ⟶ S),
      Mono m ∧
      (∀ V : Cᵒᵖ, Function.Injective (m.val.app V)) ∧
      (∀ (V : C) (h : (∏ᶜ H).val.obj (op V)),
        h ∈ Set.range (m.val.app (op V)) ↔
          ∃ (A : Type u) (U : A → C) (a : ∀ α : A, U α ⟶ V),
            Presieve.ofArrows U a ∈ K V ∧
            ∃ B : A → Finset I, ∀ (α : A) (i : I), i ∉ B α →
              (H i).val.map (a α).op ((Pi.π H i).val.app (op V) h) = 0) ∧
      (∀ i : I, ι i ≫ m ≫ Pi.π H i = 𝟙 (H i)) ∧
      (∀ (i j : I), i ≠ j → ι i ≫ m ≫ Pi.π H j = 0) ∧
      Nonempty (IsColimit (Cofan.mk S ι)) ∧
      (∀ T : ringedSiteModules.{u} R,
        Function.Bijective (fun f : S ⟶ T ↦ fun i : I ↦ ι i ≫ f)) ∧
      Mono (Sigma.desc (fun i : I ↦ ι i ≫ m)) ∧
      (∀ V : Cᵒᵖ,
        Set.range ((Sigma.desc (fun i : I ↦ ι i ≫ m)).val.app V) =
          Set.range (m.val.app V)) := by
  sorry

end CategoryTheory

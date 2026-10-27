/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q52
-/
module

public import Sheaf.CategoryTheory.GradedRingedSite
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension
import Sheaf.CategoryTheory.ModuleSheafificationRestriction

/-! # Open extension by zero for graded left module sheaves

Source: Stacks Project, sdga.tex, section-localize-graded and Tag 0FRA,
specialized to the open site and degree-zero left-module maps.
(blueprint: lem-sfb-graded-open-extension-adjunction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w
open CategoryTheory Opposite TopologicalSpace
namespace CategoryTheory.GradedRingedSite

variable {X : Type u} [TopologicalSpace X]
variable {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{max u w}}
/-- Sheafification on the small open site in a larger module universe.
Source: Stacks, module sheafification, with the fixed size convention
(blueprint: lem-sfb-graded-open-extension-adjunction). -/
instance opensHasSheafify :
    HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u w} :=
  hasSheafifyEssentiallySmallSite (Opens.grothendieckTopology X) AddCommGrpCat.{max u w}

/-- The small-open-site instance in any larger coefficient universe, transported
from its small model by Mathlib's existing site equivalence theorem.
Source: Stacks, size convention and module sheafification
(blueprint: lem-sfb-graded-open-extension-adjunction). -/
instance opensLocallyBijective :
    (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u w} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
    (Opens.grothendieckTopology X)

variable (A : Algebra.{u, u, w, max u w} R) (U : Opens X)

/-- The existing degreewise extension presheaf followed by module sheafification.
On an open site there is at most one arrow to U: this is L(V) for V contained in U,
and zero otherwise, with exactly the restrictions in the statement.
Source: Stacks, construction preceding Tag 0FRA
(blueprint: lem-sfb-graded-open-extension-adjunction). -/
def openExtensionDegree (q : ℤ) :
    Module.{u, u, w, max u w} (A.over U) ⥤ ringedSiteModules.{max u w} (rings R) :=
  evaluation (A.over U) q ⋙
    SheafOfModules.extensionByZeroPresheaf.{max u w} (rings R) U ⋙
    PresheafOfModules.sheafification.{max u w} (𝟙 (rings R).obj)

/-- The presheaf unit on the summand associated to V contained in U, transported
through a degreewise comparison to a proposed graded extension functor.
Source: Stacks, construction preceding Tag 0FRA
(blueprint: lem-sfb-graded-open-extension-adjunction). -/
def openExtensionUnit
    (E : Module.{u, u, w, max u w} (A.over U) ⥤ Module.{u, u, w, max u w} A)
    (e : ∀ q : ℤ, E ⋙ evaluation A q ≅ openExtensionDegree A U q)
    (L : Module.{u, u, w, max u w} (A.over U)) (q : ℤ) (V : (Opens X)ᵒᵖ) (φ : V.unop ⟶ U)
    (x : (L.degree q).val.obj (op (Over.mk φ))) : ((E.obj L).degree q).val.obj V :=
  ((e q).app L).inv.val.app V
    (((PresheafOfModules.sheafificationAdjunction.{max u w} (𝟙 (rings R).obj)).unit.app
      ((SheafOfModules.extensionByZeroPresheaf.{max u w} (rings R) U).obj (L.degree q))).app V
        (DirectSum.of (fun ψ : V.unop ⟶ U ↦
          (L.degree q).val.obj (op (Over.mk ψ))) φ x))

/-- Degreewise module sheafification of the specified zero-extension presheaves carries
its induced graded action, restricts canonically to L, and is left adjoint to restriction;
the Hom bijection is restriction using precisely this canonical identification.
Source: Stacks Project, Tag 0FRA, section-localize-graded, left-module analogue
(blueprint: lem-sfb-graded-open-extension-adjunction).

Proof:
1. The existing extension presheaf gives P degreewise: restrictions whose source lies
outside U have zero domain; all others are those of L. Sheafify each degree using
`def-weil-presheaf-modules-sheafification`, including its functoriality and linear unit.
2. Compose the presheaf action with the unit in the output degree. Extend the resulting
bilinear pairing uniquely by `lem-pc-sites-module-sheafification-bilinear-extension`.
The algebra degree is already a sheaf, hence its own sheafification. The resulting action
satisfies the displayed unit-section formula.
3. Restriction to every open commutes with module sheafification by
`lem-weil-pbc-module-sheafification-restriction`. Restricted units still detect equality.
On U the presheaf is L, so its unit is invertible and identifies the actions.
4. For local algebra sections a,b the two associativity maps out of a restricted
sheafification agree on unit sections by associativity on P. Restricted uniqueness gives
associativity everywhere. The same argument gives the identity law; bilinearity is step 2.
5. Naturality of the presheaf action and uniqueness of bilinear extension show that
sheafified maps preserve the action. Sheafification uniqueness gives the functor laws.
6. Extend h : L → M|U by zero as a presheaf map P → M. Its unique sheafification
factorization preserves the action: the two bilinear action squares agree on unit
sections, so bilinear-extension uniqueness makes them equal everywhere.
7. Restricting that factorization gives h. Conversely extending a restricted g returns
g, since their composites with the units agree inside U and have zero domain elsewhere.
The same uniqueness applied to composites proves naturality in both variables. -/
theorem exists_openExtensionAdjunction :
    ∃ (E : Module.{u, u, w, max u w} (A.over U) ⥤ Module.{u, u, w, max u w} A)
      (e : ∀ q : ℤ, E ⋙ evaluation A q ≅ openExtensionDegree A U q)
      (ρ : E ⋙ restriction A U ≅ 𝟭 (Module.{u, u, w, max u w} (A.over U)))
      (adj : E ⊣ restriction A U),
      (∀ (L : Module.{u, u, w, max u w} (A.over U)) (i q : ℤ) (V : (Opens X)ᵒᵖ)
        (φ : V.unop ⟶ U) (a : (A.degree i).val.obj V)
        (x : (L.degree q).val.obj (op (Over.mk φ))),
        (E.obj L).act i q V a (openExtensionUnit A U E e L q V φ x) =
          openExtensionUnit A U E e L (i + q) V φ
            (L.act i q (op (Over.mk φ)) a x)) ∧
      (∀ (L : Module.{u, u, w, max u w} (A.over U)) (q : ℤ) (V : (Opens X)ᵒᵖ)
        (φ : V.unop ⟶ U) (x : (L.degree q).val.obj (op (Over.mk φ))),
        ((ρ.hom.app L).degree q).val.app (op (Over.mk φ))
          (openExtensionUnit A U E e L q V φ x) = x) ∧
      (∀ (L : Module.{u, u, w, max u w} (A.over U)) (M : Module.{u, u, w, max u w} A)
        (g : E.obj L ⟶ M),
        adj.homEquiv L M g = ρ.inv.app L ≫ (restriction A U).map g) := by
  sorry

end CategoryTheory.GradedRingedSite

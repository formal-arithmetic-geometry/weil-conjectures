/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# Injective module sheaves restrict surjectively along site monomorphisms

Source: Stacks Project, Cohomology on Sites, Tag 093X, label
`lemma-restriction-along-monomorphism-surjective`
(blueprint: lem-pur-ringed-site-injective-mono-restriction).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace CategoryTheory

/-- For a sheaf of modules over a sheaf of commutative rings on a small site, an
injective module sheaf has surjective restriction along every monomorphism in the
site.

Source: Stacks Project, Cohomology on Sites, Tag 093X, label
`lemma-restriction-along-monomorphism-surjective`
(blueprint: lem-pur-ringed-site-injective-mono-restriction).

Proof:
1. For each object U, form the free module presheaf P_U on yoneda U using
   `lem-weil-pbc-free-yoneda-presheaf-module`. Sheafify it by
   `def-weil-presheaf-modules-sheafification`, obtaining L_U. The sheafification
   adjunction and `PresheafOfModules.freeYonedaEquiv` identify Hom(L_U, F) with
   F(U), by evaluation at the identity generator after the sheafification unit.
   Conversely, s in F(U) gives the presheaf map e_phi to F(phi)(s), then its
   unique sheafification extension. The common universe contains all sums.
2. Define a : P_W to P_T by e_phi to e_(m composed with phi). For g : V' to V,
   restricting r e_phi and then applying a gives O(g)(r) e_(m phi g), the same
   as applying a and restricting. This verifies semilinear naturality.
3. Monicity of m makes phi to m phi injective on each Hom(V, W). The coefficient
   of a(x) at m phi is x_phi, so a is componentwise injective and hence monic
   by objectwise cancellation. No natural coordinate retraction is required.
4. By `lem-weil-pbc-ringed-site-module-sheafification-exact`, module
   sheafification for this actual O preserves finite limits, hence sends a
   to a monomorphism L_W to L_T.
5. By `def-sp-injective-resolutions`, injectivity of I extends every map
   L_W to I across that monomorphism. Under step 1's identification this is
   restriction: the map associated to t in I(T), precomposed with a, sends
   e_id_W to e_m and then to I(m)(t). Naturality of the sheafification unit
   makes the presheaf and sheaf composites agree. Extending the map for any
   s in I(W) and evaluating at e_id_T yields the required preimage. All
   extensions are in the module-sheaf category of
   `def-weil-sheaf-of-modules-category`, never the underlying abelian category.
-/
theorem injective_ringed_site_mono_restriction
    {C : Type u} [SmallCategory C]
    (J : Precoverage C) (_hJ : J.IsSiteForCoverings)
    (O : Sheaf J.toGrothendieck CommRingCat.{u})
    (I : ringedSiteModules.{u}
      ((sheafCompose J.toGrothendieck (forget₂ CommRingCat.{u} RingCat.{u})).obj O)) [Injective I]
    {W T : C} (m : W ⟶ T) [Mono m] :
    Function.Surjective (I.val.map m.op).hom := by
  let R := (sheafCompose J.toGrothendieck
    (forget₂ CommRingCat.{u} RingCat.{u})).obj O
  let adj := PresheafOfModules.sheafificationAdjunction.{u} (𝟙 R.obj)
  let M := (SheafOfModules.forget R ⋙
    PresheafOfModules.restrictScalars (𝟙 R.obj)).obj I
  have : Injective M := Injective.injective_of_adjoint adj I
  let a := (PresheafOfModules.free R.obj).map (yoneda.map m)
  have : Mono a := PresheafOfModules.mono_of_injective (fun {V} ↦ by
    change Function.Injective (Finsupp.mapDomain (fun f : V.unop ⟶ W ↦ f ≫ m))
    exact Finsupp.mapDomain_injective (fun f g h ↦ (cancel_mono m).mp h))
  intro s
  let b : (PresheafOfModules.free R.obj).obj (yoneda.obj W) ⟶ M :=
    PresheafOfModules.freeYonedaEquiv.symm s
  obtain ⟨g, hg⟩ := Injective.factors b a
  refine ⟨PresheafOfModules.freeYonedaEquiv g, ?_⟩
  have h := congrArg PresheafOfModules.freeYonedaEquiv hg
  rw [Equiv.apply_symm_apply] at h
  change M.map m.op (PresheafOfModules.freeYonedaEquiv g) = s
  rw [← h]
  change M.map m.op (g.app (op T) (ModuleCat.freeMk (𝟙 T))) =
    g.app (op W) (a.app (op W) (ModuleCat.freeMk (𝟙 W)))
  rw [← PresheafOfModules.naturality_apply g m.op]
  simp [a, PresheafOfModules.free, PresheafOfModules.freeObj,
    ModuleCat.free_map_apply, ModuleCat.freeDesc_apply]

end CategoryTheory

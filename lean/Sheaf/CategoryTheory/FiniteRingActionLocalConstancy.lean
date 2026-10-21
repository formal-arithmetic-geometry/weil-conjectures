/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q56
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal

/-!
# Local constancy of a finite ring action

Source: Stacks Project, Modules on Sites, Tag 093S, finite-operation refinement;
Sites, Tag 00WK (blueprint: lem-sp-finite-ring-action-local-constancy).
-/

@[expose] public section

set_option autoImplicit false

universe uC vC

open CategoryTheory

namespace SheafOfModules

/-- A module sheaf over a finite constant ring is locally a finite constant module if
its underlying set sheaf is finite locally constant.

Source: Stacks Project, Modules on Sites, Tag 093S, finite-operation refinement, and
Sites, Tag 00WK (blueprint: lem-sp-finite-ring-action-local-constancy).

Proof:
1. Fix an object and a cover trivializing the underlying set sheaf by a finite set S.
   Work on each slice. Constant sheaves restrict to slice constants compatibly with
   their unit sections (lem-cbc-sieve-slice-sheafification). Let sigma_s be the sections
   labelled by S; their restrictions retain these labels.
2. Apply local representation (lem-weil-pbc-site-sheafification-sections-local) to zero,
   all sums sigma_s + sigma_t, and all scalar multiples lambda sigma_s. The two sets
   of labels and scalars are finite. Successive base changes and compositions of
   covers give a common refinement on which each section has a label. Including zero
   handles S empty: its representation can give an empty covering.
3. On a member W, the actual image of S in F(W) is a finite Lambda-submodule M:
   zero, addition and scalar multiplication are closed, and negatives use scalar -1.
   Restrictions define a natural linear map from the constant module presheaf M
   to F restricted to W. No injectivity of the labels in F(W) is required.
4. Module sheafification extends this map to a map of module sheaves
   (lem-pc-sites-module-sheafification-interface). Slice compatibility identifies the
   coefficient sheaf with the restricted constant ring. Forgetting to sets identifies
   this map with set sheafification (lem-pc-sites-sheafification-underlying-sets).
5. The presheaf map is locally surjective by local representation of labels. It is
   locally injective by local equality of labels in set sheafification, using
   lem-weil-pbc-site-sheafification-sections-local. Distinct labels can become equal
   on an empty-covered object; the resulting empty cover suffices. Thus the sheaf map
   is an isomorphism by lem-cbc-set-presheaf-sheafification-local-bijection.
6. The inverse is linear and natural by cancellation with the bijective linear map.
   Compose with the initial covers and relocalize (def-pur-localized-ringed-site).
   This proves the claim without points or nonempty objects, including the zero ring.

The constant module on the slice is the restriction of the recorded
`CategoryTheory.commutativeSiteConstantModuleFunctor`: module sheafification of the
identity-restriction constant module presheaf along the constant commutative ring
sheafification unit with commutativity forgotten. Constant sheafification commutes
with localization by lem-cbc-sieve-slice-sheafification. Site objects and morphisms
have independent universes; coefficient sets and modules lie in their maximum. -/
theorem finite_ring_action_local_constancy
    {C : Type uC} [Category.{vC} C]
    (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    (Λ : Type (max uC vC)) [CommRing Λ] [Finite Λ]
    (F : CategoryTheory.ringedSiteModules.{max uC vC}
      ((sheafCompose J.toGrothendieck
        (forget₂ CommRingCat.{max uC vC} RingCat.{max uC vC})).obj
          ((constantSheaf J.toGrothendieck CommRingCat.{max uC vC}).obj
            (CommRingCat.of Λ))))
    (hF : ∀ U : C, ∃ S : Presieve U, S ∈ J U ∧
      ∀ (V : C) (f : V ⟶ U), S f →
        ∃ X : Type (max uC vC), Finite X ∧
          Nonempty
            ((((sheafCompose J.toGrothendieck
                (CategoryTheory.forget AddCommGrpCat.{max uC vC})).obj
              ((SheafOfModules.toSheaf _).obj F)).over V) ≅
              (constantSheaf (J.toGrothendieck.over V) (Type (max uC vC))).obj X)) :
    ∀ U : C, ∃ S : Presieve U, S ∈ J U ∧
      ∀ (V : C) (f : V ⟶ U), S f →
        ∃ M : ModuleCat.{max uC vC} Λ, Finite M ∧
          Nonempty (F.over V ≅
            ((commutativeSiteConstantModuleFunctor J.toGrothendieck Λ).obj M).over V) := sorry

end SheafOfModules

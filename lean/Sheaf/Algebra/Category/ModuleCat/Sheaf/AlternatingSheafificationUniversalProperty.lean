/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteExteriorPower
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteAlternatingFamily
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Sites.LeftExact

/-! # Alternating maps extend through module sheafification

Source: Stacks Project, Modules on Sites, Tag 03CY, extended in finitely many variables
using Sites, Tags 00WH and 00WJ, and Algebra, Tag 00DM.
(blueprint: lem-sfb-alternating-sheafification-universal-property)
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace PresheafOfModules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Wedge evaluation is the natural bijection between linear maps from the sheafified
exterior power and restriction-compatible alternating maps on the original presheaf.
The locally bijective coefficient map to a sheaf presents its ring sheafification.
Source: Stacks 03CY, finite-variable extension using 00WH, 00WJ and 00DM
(blueprint: lem-sfb-alternating-sheafification-universal-property).

Proof:
1. The module sheafification interface identifies the underlying abelian sheaf with
abelian sheafification. Forgetting to sets commutes with abelian and ring sheafification
[lem-pc-sites-module-sheafification-interface,
lem-pc-sites-sheafification-underlying-sets]. Left exact set sheafification preserves
all finite products, including the empty product
[lem-weil-pbc-sheafification-sets-exact]. Thus maps out of these products are determined
by precomposition with the units.
2. Extend the given map of underlying presheaves of sets from P^n to F uniquely to
(P^#)^n by this finite-product identification and the adjunction
[def-weil-pbc-sheafification]. This also applies when n = 0.
3. Compare the two additivity maps on (P^#)^(n+1), the two scalar-action maps on
A^# times (P^#)^n, and the repeated-slot map with zero on (P^#)^(n-1).
Their composites with the units agree by the original multilinearity and alternation.
The uniqueness in step 1 proves multilinearity over A^# and alternation of the extension.
At n = 0 all these conditions are vacuous; repeated slots arise only when n is at least 2.
4. Apply the sectionwise exterior universal property
[lem-trf-exterior-power-universal-property, def-weil-pbc-exterior-algebra]. The resulting
linear maps commute with restrictions because both composites agree on every pure wedge.
5. Module sheafification [lem-pc-sites-module-sheafification-interface] factors this
presheaf map uniquely through the exterior sheaf. Conversely wedge evaluation gives
the original alternating family. Equality after the units, then on all pure wedges,
and finally the module sheafification adjunction prove these constructions inverse.
6. Postcomposition by v evaluates as v applied to the family. Precomposition by the
exterior map of g^# evaluates on the tuple g(x), since g^# commutes with the units.
These give both displayed naturality identities. In degree zero the empty wedge is 1,
and the associated sectionwise linear map is a ↦ a times the given compatible element.
No lifts of local sections are chosen. -/
theorem alternating_sheafification_universal_property
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J AddCommGrpCat.{max u v w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    (A : Cᵒᵖ ⥤ CommRingCat.{max u v w}) (B : Sheaf J CommRingCat.{max u v w})
    (α : (A ⋙ forget₂ CommRingCat.{max u v w} RingCat.{max u v w}) ⟶
      ((sheafCompose J (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})).obj B).obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α] (n : ℕ) :
    ∃ e : ∀ (P : PresheafOfModules.{max u v w}
        (A ⋙ forget₂ CommRingCat.{max u v w} RingCat.{max u v w}))
      (F : ringedSiteModules.{max u v w}
        ((sheafCompose J (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})).obj B)),
      (SheafOfModules.siteExteriorPower (B := B) ((sheafification.{max u v w} α).obj P) n ⟶ F) ≃
        SiteAlternatingFamily (A := A) P ((restrictScalars α).obj F.val) n,
      (∀ (P : PresheafOfModules.{max u v w}
        (A ⋙ forget₂ CommRingCat.{max u v w} RingCat.{max u v w}))
        (F : ringedSiteModules.{max u v w}
          ((sheafCompose J (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})).obj B))
        (h : SheafOfModules.siteExteriorPower (B := B)
          ((sheafification.{max u v w} α).obj P) n ⟶ F)
        (U : Cᵒᵖ) (x : Fin n → P.obj U),
        (e P F h).val U x = h.val.app U
          (SheafOfModules.siteExteriorWedge (B := B)
            ((sheafification.{max u v w} α).obj P) n U
            (fun i ↦ ((sheafificationAdjunction.{max u v w} α).unit.app P).app U (x i)))) ∧
      (∀ (P : PresheafOfModules.{max u v w}
        (A ⋙ forget₂ CommRingCat.{max u v w} RingCat.{max u v w}))
        (F G : ringedSiteModules.{max u v w}
          ((sheafCompose J (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})).obj B))
        (v : F ⟶ G)
        (h : SheafOfModules.siteExteriorPower (B := B)
          ((sheafification.{max u v w} α).obj P) n ⟶ F)
        (U : Cᵒᵖ) (x : Fin n → P.obj U),
        (e P G (h ≫ v)).val U x = v.val.app U ((e P F h).val U x)) ∧
      (∀ (P' P : PresheafOfModules.{max u v w}
        (A ⋙ forget₂ CommRingCat.{max u v w} RingCat.{max u v w}))
        (g : P' ⟶ P)
        (F : ringedSiteModules.{max u v w}
          ((sheafCompose J (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})).obj B))
        (h : SheafOfModules.siteExteriorPower (B := B)
          ((sheafification.{max u v w} α).obj P) n ⟶ F)
        (U : Cᵒᵖ) (x : Fin n → P'.obj U),
        (e P' F (SheafOfModules.siteExteriorHom (B := B)
          ((sheafification.{max u v w} α).map g) n ≫ h)).val U x =
          (e P F h).val U (fun i ↦ g.app U (x i))) := by
  sorry

end PresheafOfModules

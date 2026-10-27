/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.CategoryTheory.SpecialCocontinuousCoverings
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Adjunction.Whiskering
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.CategoryTheory.SiteExtensionByZeroPresheafAdjoint
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import WeilConjectures.CategoryTheory.SiteExtensionByZeroPresheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-!
# The localized coefficient counit criterion for module lower shriek

Source: Stacks Project, Modules on Sites, Tag 0798, remark-when-shriek-equal,
equation-compare-on-localizations
(blueprint: lem-sfb-module-shriek-forgetful-counit-criterion).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe c d vc vd r

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

section Comparison

variable {C : Type c} [Category.{vc} C] {D : Type d} [Category.{vd} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (F : C ⥤ D) [F.IsContinuous J K]
  (R : Sheaf K CommRingCat.{max c d vc vd r})
  (L : ringedSiteModules.{max c d vc vd r}
      ((F.sheafPushforwardContinuous RingCat.{max c d vc vd r} J K).obj
        ((sheafCompose K
        (forget₂ CommRingCat.{max c d vc vd r} RingCat.{max c d vc vd r})).obj R)) ⥤
    ringedSiteModules.{max c d vc vd r}
      ((sheafCompose K
        (forget₂ CommRingCat.{max c d vc vd r} RingCat.{max c d vc vd r})).obj R))
  (adjL : L ⊣ SheafOfModules.pushforward.{max c d vc vd r} (F := F)
    (R := (sheafCompose K
      (forget₂ CommRingCat.{max c d vc vd r} RingCat.{max c d vc vd r})).obj R)
    (𝟙 ((F.sheafPushforwardContinuous RingCat.{max c d vc vd r} J K).obj
      ((sheafCompose K
        (forget₂ CommRingCat.{max c d vc vd r} RingCat.{max c d vc vd r})).obj R))))
  (A : Sheaf J AddCommGrpCat.{max c d vc vd r} ⥤
    Sheaf K AddCommGrpCat.{max c d vc vd r})
  (adjA : A ⊣ F.sheafPushforwardContinuous AddCommGrpCat.{max c d vc vd r} J K)

/-- The comparison is the abelian adjunct of the underlying module unit.

Source: Stacks Project, Tag 0798, remark-when-shriek-equal
(blueprint: lem-sfb-module-shriek-forgetful-counit-criterion).
Whiskering the adjunction constructs a natural transformation directly; its component
is `adjA.homEquiv.symm` applied to the underlying component of `adjL.unit`.
All precomposition and scalar maps here are the canonical ones, with identity ring map. -/
def moduleShriekForgetfulComparison :
    SheafOfModules.toSheaf.{max c d vc vd r}
        ((F.sheafPushforwardContinuous RingCat.{max c d vc vd r} J K).obj
          ((sheafCompose K
            (forget₂ CommRingCat.{max c d vc vd r} RingCat.{max c d vc vd r})).obj R)) ⋙ A ⟶
      L ⋙ SheafOfModules.toSheaf.{max c d vc vd r}
        ((sheafCompose K
        (forget₂ CommRingCat.{max c d vc vd r} RingCat.{max c d vc vd r})).obj R) :=
  ((adjA.whiskerRight _).homEquiv _ _).symm
    (Functor.whiskerRight adjL.unit (SheafOfModules.toSheaf _))

end Comparison

/-- Invertible localized coefficient counits make the actual forgetting comparison invertible.

Source: Stacks Project, Tag 0798, remark-when-shriek-equal,
equation-compare-on-localizations
(blueprint: lem-sfb-module-shriek-forgetful-counit-criterion).

The actual covering-site axioms are `hJ` and `hK`. The two Stacks continuity clauses
are `hcover` and `hpullback`. The global continuity instance is their sheaf-theoretic
consequence, exposed to type precomposition. The slice continuity instance records the
induced continuous functors stipulated in the node. Slice cocontinuity follows from the
global cocontinuity instance. All site universes remain independent, and coefficients
live in their maximum with the arbitrary additional level `r`.

Proof:
1. Module and abelian extension by zero are the same underlying direct-sum presheaf,
   followed by sheafification. Use lem-pur-site-restriction-module-adjunction-exact,
   lem-weil-pbc-site-extension-by-zero-presheaf-adjoint, def-weil-extension-by-zero-presheaf,
   def-weil-pbc-site-extension-by-zero-presheaf and def-weil-presheaf-modules-sheafification.
   For E_U = J_U(R'|U) and Q_U = J_FU(R|FU), their underlying sheaves are the
   corresponding abelian extensions, preserving each summand inclusion.
2. The evaluation bijections of lem-trf-ringed-site-restriction-generator-data identify
   Hom(L E_U,N) with N(FU) and Hom(Q_U,N). Co-Yoneda
   (lem-weil-pbc-coyoneda-iso-of-natural-hom-bijection) gives e_U : L E_U ≅ Q_U.
   Its adjunct b_U sends r in the summand a to r times the summand F(a).
3. The localization adjunctions, the global abelian adjunction and the slice adjunction
   identify Hom(A J_U S,N) with Hom(J_FU A_U S,N), for S = R'|U. Restriction commutes
   sectionwise with precomposition (def-pur-localized-ringed-site). Co-Yoneda gives
   the unit-normalized isomorphism lambda_U : A J_U S ≅ J_FU A_U S.
4. Put B = R|FU and c_U = adjU.counit.app B. The adjunct of J_FU(c_U) lambda_U
   reduces, by the slice triangle identity, to the pulled-back localization unit of B.
   The explicit summand formula in lem-weil-pbc-site-extension-by-zero-presheaf-adjoint
   identifies this with the underlying b_U. Thus forgetting e_U after gamma_E_U is
   exactly J_FU(c_U) lambda_U, by injectivity of the global adjunction bijection.
5. The counit hypothesis and functoriality make this composite invertible, and therefore
   gamma_E_U invertible. No equivalence of slice sites is used.
6. By lem-weil-pbc-module-sheaves-colimits-forgetful the forgetful functors preserve
   coproducts and cokernels. Left adjoints preserve these colimits by their Hom universal
   properties, so both sides of gamma do too. Naturality identifies gamma on a coproduct
   of E_U with the coproduct of the invertible components, including the empty coproduct.
7. Use lem-trf-ringed-site-restriction-generator-data on M and then on the kernel of an
   epimorphism H_0 -> M to present M as the cokernel of H_1 -> H_0, both H_i sums of E_U.
   Naturality gives a square with invertible vertical arrows on H_1 and H_0. Its inverse
   square induces the inverse on cokernels. The forward induced map is gamma_M by
   naturality at H_0 -> M and uniqueness of cokernel factorization. -/
theorem isIso_moduleShriekForgetfulComparison_of_localizedCounit
    {C : Type c} [Category.{vc} C] {D : Type d} [Category.{vd} D]
    (J : Precoverage C) (K : Precoverage D)
    (hJ : J.IsSiteForCoverings) (hK : K.IsSiteForCoverings)
    (F : C ⥤ D)
    (hcover : ∀ (X : C) (P : Presieve X), P ∈ J X → P.map F ∈ K (F.obj X))
    (hpullback : ∀ (X Y Z : C) (P : Presieve X), P ∈ J X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), P f → PreservesLimit (cospan f g) F)
    [F.IsContinuous J.toGrothendieck K.toGrothendieck]
    [F.IsCocontinuous J.toGrothendieck K.toGrothendieck]
    (R : Sheaf K.toGrothendieck CommRingCat.{max c d vc vd r})
    (L : ringedSiteModules.{max c d vc vd r}
        ((F.sheafPushforwardContinuous RingCat.{max c d vc vd r}
          J.toGrothendieck K.toGrothendieck).obj
          ((sheafCompose K.toGrothendieck
            (forget₂ CommRingCat.{max c d vc vd r} RingCat.{max c d vc vd r})).obj R)) ⥤
      ringedSiteModules.{max c d vc vd r}
        ((sheafCompose K.toGrothendieck
          (forget₂ CommRingCat.{max c d vc vd r} RingCat.{max c d vc vd r})).obj R))
    [L.Additive]
    (adjL : L ⊣ SheafOfModules.pushforward.{max c d vc vd r} (F := F)
      (R := (sheafCompose K.toGrothendieck
        (forget₂ CommRingCat.{max c d vc vd r} RingCat.{max c d vc vd r})).obj R)
      (𝟙 ((F.sheafPushforwardContinuous RingCat.{max c d vc vd r}
        J.toGrothendieck K.toGrothendieck).obj
        ((sheafCompose K.toGrothendieck
          (forget₂ CommRingCat.{max c d vc vd r} RingCat.{max c d vc vd r})).obj R))))
    (A : Sheaf J.toGrothendieck AddCommGrpCat.{max c d vc vd r} ⥤
      Sheaf K.toGrothendieck AddCommGrpCat.{max c d vc vd r})
    (adjA : A ⊣ F.sheafPushforwardContinuous AddCommGrpCat.{max c d vc vd r}
      J.toGrothendieck K.toGrothendieck)
    [∀ U : C, (Over.post (X := U) F).IsContinuous
      (J.toGrothendieck.over U) (K.toGrothendieck.over (F.obj U))]
    (AU : ∀ U : C,
      Sheaf (J.toGrothendieck.over U) AddCommGrpCat.{max c d vc vd r} ⥤
        Sheaf (K.toGrothendieck.over (F.obj U)) AddCommGrpCat.{max c d vc vd r})
    (adjU : ∀ U : C, AU U ⊣
      (Over.post (X := U) F).sheafPushforwardContinuous
        AddCommGrpCat.{max c d vc vd r}
        (J.toGrothendieck.over U) (K.toGrothendieck.over (F.obj U)))
    (hcounit : ∀ U : C, IsIso ((adjU U).counit.app
      (((sheafCompose K.toGrothendieck
        (forget₂ CommRingCat.{max c d vc vd r} RingCat.{max c d vc vd r} ⋙
          forget₂ RingCat.{max c d vc vd r} AddCommGrpCat.{max c d vc vd r})).obj R).over
            (F.obj U)))) :
    IsIso (moduleShriekForgetfulComparison.{c, d, vc, vd, r} F R L adjL A adjA) := by
  sorry

end CategoryTheory

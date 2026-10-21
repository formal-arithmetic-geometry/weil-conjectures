/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.CategoryTheory.SystemScalarCoherence
public import Sheaf.CategoryTheory.RingedKoszulCompletionReflector
public import Sheaf.Paper.WeilCompletedTensorReflector
import Sheaf.CategoryTheory.RingedCompleteTriangulated
import Sheaf.CategoryTheory.RingedCechKoszulDualLimit
import Sheaf.CategoryTheory.UnitPowerCompleteness
import Mathlib.Algebra.Homology.BifunctorShift

/-! # Finite-free scalar extension and Koszul completion

Source: Stacks Project, algebraization.tex, Tags 099B and 0A0E; the finite-free
scalar-extension argument extracted from blueprint `prop-weil-pbc-scalar-extension`,
steps 6--7 (blueprint: lem-weil-pbc-finite-free-completion-transport).

The four statements give existence and uniqueness of the unit-normalized comparison,
preservation of local completeness, integer-shift compatibility, the actual tensor-unit
normalization, and balanced tensor composition. Binary composition iterates to any finite
tower. No basis is part of the comparison data.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
variable [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ ringedSiteModules.{u}
  (derivedChangeRingIndependentCoefficients J R))]
variable [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ ringedSiteModules.{u}
  (derivedChangeRingIndependentCoefficients J S))]

/-- The unique unit-normalized finite-free completion comparison and preservation of
local derived completeness. Its uniqueness makes the comparison independent of a basis
and of the presentation of the unit-power relation.

Source: Stacks Project, algebraization.tex, Tags 099B and 0A0E, finite-free scalar
argument (blueprint: lem-weil-pbc-finite-free-completion-transport).

The coproduct in `hfree` is the finite direct sum of rank-one module sheaves; its
isomorphism is only asserted, not chosen. `D` and `E` are the existing strict Koszul
limit presentations, with their actual degree-zero units. The principal ideal is the
categorical image of multiplication, including sections divisible only locally.
We use standard derived localizations of module sheaves and arbitrary chosen standard-size
localizations of their strict tower categories; none of the complexes is bounded.

Proof:
1. Put s=a(t). On any complex P, finite-free scalar tensor is exact, so represents its
   derived tensor. Balanced multiplication identifies the entire augmented tensor tower
   P tensor [R --t^m--> R] with CP tensor [S --s^m--> S]. It respects differentials,
   transitions (t,1), and augmentations (1 in degree zero), and descends through Q.
   Use lem-weil-pbc-finite-free-strict-tower-transport and lem-pur-derived-change-of-rings.
2. The strict-tower comparison commutes with total derived inverse limit, including
   its augmentation. The Koszul reflector identifies the limits and their units, giving
   kappa^s with kappa^s C(etaR)=etaS,s, independently of the basis.
3. Apply lem-weil-pbc-ringed-cech-koszul-dual-limit and lem-pur-unit-power-completeness.
   The localization inverses v^-1=w*v^(e-1)/s and s^-1=w^-1*v^-e identify the two
   augmented Cech complexes by identity in degree zero. Their reflectors therefore have
   a unit-preserving isomorphism. Compose it with kappa^s to obtain kappa.
4. The reflector criterion says eta is invertible exactly on complete objects; the unit
   equation therefore proves preservation. For complete L, precomposition by C(etaR)
   is bijective, by its factorization through kappa and the S-reflector unit. This makes
   every unit-normalized comparison equal to kappa, proving the asserted uniqueness.
5. For shifts, precompose the shift square by C(etaR) and use shift-compatible units;
   both composites become etaS[1] c. The shifted target is complete, so cancel using
   step 4. Iterate in both directions for every integer.
6. Multiplication C(N) -> N for the identity map gives the tensor-unit comparison.
   Its composite with C(etaR) is etaR at C(N), by naturality, so step 4 identifies it.
7. In a tower R -> S -> T, balanced associativity has formula
   c tensor (b tensor x) -> c*image(b) tensor x. Both successive and direct completion
   comparisons become etaT alpha after precomposition by C_b C_a(etaR). The composite
   map is finite free and its parameter is a unit times a positive power. Cancel by
   step 4 and iterate this binary equation for all finite towers. -/
theorem finiteFreeCompletionTransport
    (A : SystemScalarModel.{u, u, u} a)
    (hfree : ∃ d : ℕ, Nonempty
      ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).obj
          (SheafOfModules.unit (derivedChangeRingIndependentCoefficients J S)) ≅
        ∐ (fun _ : Fin d ↦
          SheafOfModules.unit (derivedChangeRingIndependentCoefficients J R))))
    (t : (R.obj ⋙ forget CommRingCat).sections)
    (v w : (S.obj ⋙ forget CommRingCat).sections) (e : ℕ)
    (hw : ∀ U : Cᵒᵖ, IsUnit (w.val U)) (he : 1 ≤ e)
    (hparam : ∀ U : Cᵒᵖ, a.hom.app U (t.val U) = w.val U * v.val U ^ e)
    (D : RingedKoszulLimitPresentation R 1 (fun _ ↦ t))
    (E : RingedKoszulLimitPresentation S 1 (fun _ ↦ v)) :
    (∃! κ : D.completion ⋙ A.model.T ≅ A.model.T ⋙ E.completion,
      ∀ M : ringedSiteDerived R,
        A.model.T.map (D.unit M) ≫ κ.hom.app M = E.unit (A.model.T.obj M)) ∧
    ∀ M : ringedSiteDerived R,
      IsLocallyDerivedRingedIdealComplete R
        (image (ringedKoszulScalar R t)) (image.ι (ringedKoszulScalar R t)) M →
      IsLocallyDerivedRingedIdealComplete S
        (image (ringedKoszulScalar S v)) (image.ι (ringedKoszulScalar S v))
        (A.model.T.obj M) := by
  sorry

/-- The normalized comparison commutes with all canonical cochain shifts. The shift
structures on completion are specified by their compatibility with the actual units,
as supplied by `ringedCompleteTriangulated`.

Source: Stacks Project, Tags 099B and 0A0E, scalar-extension shift normalization
(blueprint: lem-weil-pbc-finite-free-completion-transport).
Proof: precompose the shift square with C(etaR) at M[n]. Naturality of the scalar shift,
shift compatibility of etaR and etaS, and the two normalization equations reduce both
sides to etaS at CM shifted by n after the scalar shift. The target is complete by
lem-sfb-ringed-complete-triangulated. The Hom bijection of the Koszul reflector cancels
C(etaR), as in step 4 of finiteFreeCompletionTransport. This works for every integer n. -/
theorem finiteFreeCompletionTransport_shift
    (A : SystemScalarModel.{u, u, u} a)
    (t : (R.obj ⋙ forget CommRingCat).sections)
    (v : (S.obj ⋙ forget CommRingCat).sections)
    (D : RingedKoszulLimitPresentation R 1 (fun _ ↦ t))
    (E : RingedKoszulLimitPresentation S 1 (fun _ ↦ v))
    [A.model.T.CommShift ℤ] [D.completion.CommShift ℤ] [E.completion.CommShift ℤ]
    (ηR : 𝟭 (ringedSiteDerived R) ⟶ D.completion)
    (ηS : 𝟭 (ringedSiteDerived S) ⟶ E.completion)
    (hηR : ∀ M : ringedSiteDerived R, ηR.app M = D.unit M)
    (hηS : ∀ M : ringedSiteDerived S, ηS.app M = E.unit M)
    [NatTrans.CommShift ηR ℤ] [NatTrans.CommShift ηS ℤ]
    (κ : D.completion ⋙ A.model.T ≅ A.model.T ⋙ E.completion)
    (hκ : ∀ M : ringedSiteDerived R,
      A.model.T.map (D.unit M) ≫ κ.hom.app M = E.unit (A.model.T.obj M)) :
    NatTrans.CommShift κ.hom ℤ := by
  sorry

/-- At the identity coefficient map, the normalized comparison is the actual tensor-unit
comparison, whose ordinary formula is scalar multiplication.

Source: Stacks Project, Tags 099B and 0A0E, scalar-extension identity normalization
(blueprint: lem-weil-pbc-finite-free-completion-transport).
Proof: write u for systemScalarModelDerivedUnit; systemScalarModelDerivedUnit_rep
identifies it with multiplication on complexes. Naturality of u and of the completion
unit shows C(eta) followed by u at Lambda M then Lambda(u^-1 at M) equals eta at CM.
The target is complete. Uniqueness from the reflector Hom bijection, as in step 4 of
finiteFreeCompletionTransport, identifies this map with kappa. -/
theorem finiteFreeCompletionTransport_id
    (A : SystemScalarModel.{u, u, u} (𝟙 R))
    (t : (R.obj ⋙ forget CommRingCat).sections)
    (D : RingedKoszulLimitPresentation R 1 (fun _ ↦ t))
    (κ : D.completion ⋙ A.model.T ≅ A.model.T ⋙ D.completion)
    (hκ : ∀ M : ringedSiteDerived R,
      A.model.T.map (D.unit M) ≫ κ.hom.app M = D.unit (A.model.T.obj M))
    (M : ringedSiteDerived R) :
    κ.hom.app M =
      (systemScalarModelDerivedUnit.{u, u, u} rfl A).hom.app (D.completion.obj M) ≫
        D.completion.map ((systemScalarModelDerivedUnit.{u, u, u} rfl A).inv.app M) := by
  sorry

/-- Successive normalized completion comparisons agree with the direct comparison under
balanced derived tensor associativity. Iteration gives the equation for every finite tower.

Source: Stacks Project, Tags 099B and 0A0E, scalar-extension tower normalization
(blueprint: lem-weil-pbc-finite-free-completion-transport).
Proof: systemScalarModelDerivedComposition is the canonical balanced associator, with
its pure-tensor formula and universal cochain comparison fixed by the recorded coherence
node. Precompose both sides with C_b C_a(etaR). The two normalization equations on the
left and naturality of etaT reduce it to alpha followed by etaT. Naturality of alpha
and the direct normalization give the same map on the right. Transport precomposition
along alpha to C_ba(etaR). Its Hom map into the complete target is injective by the
Koszul reflector and the direct normalized comparison. Cancel to obtain the equation.
For successive finite-free maps the composite is finite free and
ba(t)=b(w)*u^e*z^(ef), with a unit coefficient and ef>=1, so the existence theorem
supplies all three comparisons. Induction on length gives every finite tower. -/
theorem finiteFreeCompletionTransport_comp
    {T : Sheaf J CommRingCat.{u}} (b : S ⟶ T)
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ ringedSiteModules.{u}
      (derivedChangeRingIndependentCoefficients J T))]
    (A : SystemScalarModel.{u, u, u} a) (B : SystemScalarModel.{u, u, u} b)
    (F : SystemScalarModel.{u, u, u} (a ≫ b))
    (t : (R.obj ⋙ forget CommRingCat).sections)
    (v : (S.obj ⋙ forget CommRingCat).sections)
    (z : (T.obj ⋙ forget CommRingCat).sections)
    (D : RingedKoszulLimitPresentation R 1 (fun _ ↦ t))
    (E : RingedKoszulLimitPresentation S 1 (fun _ ↦ v))
    (G : RingedKoszulLimitPresentation T 1 (fun _ ↦ z))
    (κa : D.completion ⋙ A.model.T ≅ A.model.T ⋙ E.completion)
    (κb : E.completion ⋙ B.model.T ≅ B.model.T ⋙ G.completion)
    (κab : D.completion ⋙ F.model.T ≅ F.model.T ⋙ G.completion)
    (ha : ∀ M : ringedSiteDerived R,
      A.model.T.map (D.unit M) ≫ κa.hom.app M = E.unit (A.model.T.obj M))
    (hb : ∀ N : ringedSiteDerived S,
      B.model.T.map (E.unit N) ≫ κb.hom.app N = G.unit (B.model.T.obj N))
    (hab : ∀ M : ringedSiteDerived R,
      F.model.T.map (D.unit M) ≫ κab.hom.app M = G.unit (F.model.T.obj M))
    (M : ringedSiteDerived R) :
    B.model.T.map (κa.hom.app M) ≫ κb.hom.app (A.model.T.obj M) ≫
        G.completion.map ((systemScalarModelDerivedComposition.{u, u, u} rfl A B F).hom.app M) =
      (systemScalarModelDerivedComposition.{u, u, u} rfl A B F).hom.app (D.completion.obj M) ≫
        κab.hom.app M := by
  sorry

end CategoryTheory

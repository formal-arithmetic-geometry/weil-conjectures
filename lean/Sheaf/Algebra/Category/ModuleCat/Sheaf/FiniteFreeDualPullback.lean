/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.CategoryTheory.Sites.CoverPreserving
import Sheaf.CategoryTheory.SiteInverseImageTensor
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.Paper.LocalizeRingedSiteMorphism
import Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Paper.LocalizeRingedSiteMorphismGeneral

/-!
# Pullback of the dual of a finite locally free module on a ringed site

Source: Stacks Project, Modules on Sites, Tags 0GMX and 0FNY; the Powers and duals
paragraph of `det-prop-sfb-cartesian-coefficients-twists`, main-20261015
(blueprint: lem-pur-ringed-site-finite-free-dual-pullback).

The coefficient morphism `a : R → u_* S` is the adjunct of the source's
`c : f⁻¹ R → S`. The module pullback is Mathlib's left adjoint, hence the same
sheafified relative tensor product. Its adjunction unit sends a section to its
pulled-back section. The equation below characterizes the canonical comparison
by evaluation on these sections, exactly as in Stacks 0GMX. In particular it
specializes to the stated Kronecker-delta formula for every local dual basis.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

set_option autoImplicit false

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {U : C ⥤ D} [U.IsContinuous J K]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  {R : Sheaf J CommRingCat.{max u v w}} {S : Sheaf K CommRingCat.{max u v w}}
  (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
    (U.sheafPushforwardContinuous RingCat J K).obj
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))

/-- Mathlib's module pullback with its existence proof supplied explicitly.
This transparent abbreviation permits the statement to assert existence of the
adjoint instead of imposing it as a further hypothesis. Source: Stacks Project,
Modules on Sites, Tags 03D7 and 0GMX
(blueprint: lem-pur-ringed-site-finite-free-dual-pullback). -/
noncomputable abbrev ringedSitePullbackFunctor
    (hAdj : (pushforward.{max u v w} a).IsRightAdjoint) :=
  @pullback _ _ _ _ _ _ _ _ _ _ a hAdj

/-- A section pulled back along a ringed site morphism, using the unit of the
module pullback adjunction. This is the image `1 ⊗ f⁻¹(m)` in the sheafified tensor
product. Source: Stacks Project, Modules on Sites, Tag 0GMX
(blueprint: lem-pur-ringed-site-finite-free-dual-pullback). -/
noncomputable def ringedSitePullbackSection
    (hAdj : (pushforward.{max u v w} a).IsRightAdjoint)
    (M : ringedSiteModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (V : C)
    (m : M.val.obj (op V)) : ((ringedSitePullbackFunctor a hAdj).obj M).val.obj (op (U.obj V)) :=
  ((@pullbackPushforwardAdjunction _ _ _ _ _ _ _ _ _ _ a hAdj).unit.app M).val.app
    (op V) m

/-- The evaluation comparison is invertible for a finite locally free module,
contravariantly natural, and carries pulled-back dual bases to dual bases.
Source: Stacks Project, Modules on Sites, Tags 0GMX, 0FNY, 03EL and 04J0
(blueprint: lem-pur-ringed-site-finite-free-dual-pullback).

The comparison is specified, rather than taken as an arbitrary morphism: for
all local functionals `φ` and sections `m`, its evaluation on their pullbacks
is the coefficient image of `φ(m)`. The equation holds after every restriction,
since `V` is arbitrary. With `φ = eⱼ∨` and `m = eₖ` it says exactly that the
value is `δⱼₖ * 1`. The finite-free cover uses arbitrary ranks, including zero.

Proof:
1. Pull back evaluation, apply the canonical relative tensor comparison of
lem-weil-pbc-ringed-topoi-module-pullback-tensor, and identify the pullback of
R with S by `s ⊗ r ↦ s c(r)`, whose inverse is `s ↦ s ⊗ 1`.
Transpose the resulting pairing using lem-pc-sheaf-modules-tensor-closed.
On unit images of sections this gives the displayed evaluation equation.
2. The finite-free cover pulls back to a cover because U preserves covers and
finite limits. By lem-weil-pbc-localize-ringed-site-morphism, pullback commutes
with localization. Restriction of internal Hom is internal Hom of restrictions:
both have the same linear maps over each further localized object. Evaluation
and the tensor comparison commute with these identifications.
3. On a rank-r trivialization a functional is determined by its r values on the
basis, and the inverse sends these values to their finite linear combination
of coordinate functionals. These formulas commute with restrictions, giving
the free rank-r identification of the dual, also for r = 0.
4. Finite-limit preservation and tensor balancing identify the pullback of R^r
with S^r: `s ⊗ (aⱼ) ↦ (s c(aⱼ))`, inverse `(bⱼ) ↦ ∑ⱼ bⱼ ⊗ eⱼ`.
The pulled evaluation sends the two pulled bases to the Kronecker-delta matrix,
so the local comparison is the identity matrix and is invertible.
5. Local inverses agree on overlaps because they invert the same comparison.
Glue by lem-pur-sheaf-hom-cover-gluing. Both composites are identities locally,
hence globally by uniqueness in the same gluing theorem.
6. For b : L → M, the evaluations of the two naturality composites both send
(φ,x) to φ(b(x)). The tensor-Hom bijection is injective, so the composites agree.
The defining evaluation equation also determines the comparison uniquely,
since the adjunction-unit images generate pullback locally and linearly.
No flatness or nonzero-ring hypothesis is used. -/
theorem finite_free_dual_pullback
    [HasFiniteLimits C] [HasFiniteLimits D] [PreservesFiniteLimits U]
    (_hcover : CoverPreserving J K U)
    [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{max u v w}]
    [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}] :
    ∃ hAdj : (pushforward.{max u v w} a).IsRightAdjoint,
    ∃! δ : ∀ L : ringedSiteModules.{max u v w}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R),
        (ringedSitePullbackFunctor a hAdj).obj (homObj L (unit _)) ⟶
          homObj ((ringedSitePullbackFunctor a hAdj).obj L) (unit _),
      (∀ (L : ringedSiteModules.{max u v w}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
          (V : C) (φ : (homObj L (unit _)).val.obj (op V)) (m : L.val.obj (op V)),
        (((δ L).val.app (op (U.obj V))
          (ringedSitePullbackSection a hAdj (homObj L (unit _)) V φ)).app
            (op (Over.mk (𝟙 (U.obj V)))))
          (ringedSitePullbackSection a hAdj L V m) =
            a.hom.app (op V) (φ.app (op (Over.mk (𝟙 V))) m)) ∧
      (∀ L M : ringedSiteModules.{max u v w}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R),
        ∀ b : L ⟶ M,
          (ringedSitePullbackFunctor a hAdj).map (homObjMap b (𝟙 (unit _))) ≫ δ L =
            δ M ≫ homObjMap ((ringedSitePullbackFunctor a hAdj).map b) (𝟙 (unit _))) ∧
      (∀ L : ringedSiteModules.{max u v w}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R),
        (∃ (I : Type (max u v w)) (V : I → C) (r : I → ℕ),
          Sieve.ofArrows V (fun i ↦ terminal.from (V i)) ∈ J (⊤_ C) ∧
            ∀ i : I, Nonempty (L.over (V i) ≅
              free (R := ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over (V i))
                (ULift.{max u v w} (Fin (r i))))) → IsIso (δ L)) := by
  sorry

end SheafOfModules

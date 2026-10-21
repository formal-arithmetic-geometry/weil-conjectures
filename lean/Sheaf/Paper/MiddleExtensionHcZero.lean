/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.Paper.AdicMiddleExtensionConstructible
public import Sheaf.Paper.CommonStageCompactWeilCohomology
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import Sheaf.Paper.MiddleExtensionSectionRestriction

/-! # Degree-zero compact-support vanishing for ordinary adic middle extensions

Source: blueprint main-20261015, sec-deligne-laumon-a1/sk-p-dl-a1-perverse,
lem-fd-stalk-at-origin.proof.md, second paragraph; Milne, Lectures on Etale
Cohomology, Definition 18.1, pp. 118–119, and Remark 29.7, p. 166
(blueprint: lem-a1-middle-extension-hc0).

The ordinary image and its induced Weil structure are the recorded constructible
middle extension. Cohomology uses the completed integral, rationalized, common-stage
construction after the recorded forgetful functor, for every compactification.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- Separatedness of the geometric structure morphism is inherited by base change.
This exposes the ordinary pullback instance through the recorded bundled fibre.
Source: Stacks 01KU; the geometric base-change step of the blueprint lissity argument
(blueprint: lem-a1-middle-extension-hc0). -/
instance middleExtensionCurve_geometricStructureIsSeparated {D : FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) :
    IsSeparated ((D.geometricFiber c.C).left ↘ Spec (.of D.k)) :=
  inferInstanceAs (IsSeparated
    (pullback.snd c.C.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- A closed subset proper over the geometric base cannot be the whole smooth affine
connected curve. This is the geometric support obstruction used below.
Source: Milne, Remark 29.7, p. 166; Stacks Tags 01J4 and 0CYL
(blueprint: lem-a1-middle-extension-hc0). -/
private theorem middleExtensionCurve_closedSubset_ne_top
    {D : FiniteFieldDatum.{u}} (c : MiddleExtensionCurve D)
    [IsAffine c.C.left] [SmoothOfRelativeDimension 1 c.C.hom]
    [GeometricallyConnected c.C.hom]
    (Z : TopologicalSpace.Closeds (D.geometricFiber c.C).left)
    (hZ : IsClosedSubsetProperOver (D.geometricFiber c.C).hom Z) : Z ≠ ⊤ := by
  let X := (D.geometricFiber c.C).left
  let f := (D.geometricFiber c.C).hom
  have : IsAffine X := inferInstanceAs
    (IsAffine (pullback c.C.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have : SmoothOfRelativeDimension 1 f := inferInstanceAs
    (SmoothOfRelativeDimension 1
      (pullback.snd c.C.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have : GeometricallyConnected f := inferInstanceAs
    (GeometricallyConnected
      (pullback.snd c.C.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have : ConnectedSpace X := GeometricallyConnected.connectedSpace_of_subsingleton f
  have hdim : topologicalKrullDim X = 1 :=
    topologicalKrullDim_eq_of_smoothOfRelativeDimension f 1
  have hnp : ¬ IsProper f := by
    intro hp
    have hd := (isFinite_of_isProper_of_isAffine f).2
    rw [hdim] at hd
    exact (by norm_num : ¬ (1 : WithBot ℕ∞) ≤ 0) hd
  intro htop
  subst Z
  have hp := (closed_subset_proper_over_base_properties f ⊤).2.1.mp hZ
    X (𝟙 X) (Set.range_id)
  exact hnp (by simpa using hp)

/-- The ordinary middle extension of a lisse Weil sheaf from a dense open of a
smooth geometrically connected affine curve has zero degree-zero compact cohomology.
There is no purity, weight, or ramification hypothesis.
Source: blueprint lem-fd-stalk-at-origin.proof.md, second paragraph; Milne,
Definition 18.1 and Remark 29.7 (blueprint: lem-a1-middle-extension-hc0).

Proof:
1. Affine scalar extension is affine. Separatedness and finite type survive base
change (lem-pod-separated-finite-type-base-change), as does smooth relative
dimension one (lem-sbc-smooth-relative-dimension-permanence). Geometric connectedness
makes C nonempty and connected, and its dimension is one
(lem-sbc-smooth-fixed-dimension-over-field).
2. The smooth connected curve is Noetherian and integral
(lem-sc-smooth-connected-curve-local-rings, def-pc-integral-scheme). The projection
to C0 is open (lem-sc-scheme-over-field-universally-open), so the inverse image U
of the dense open U0 is dense, nonempty and irreducible, hence connected
(def-weil-irreducible-components).
3. The affine coordinate ring is Noetherian (pqf-lem-affine-open-locnoeth), hence
so is the underlying space (lem-sc-affine-noetherian-underlying-space). Its open
U is quasi-compact (lem-sfb-noetherian-space-compact-subsets), locally Noetherian
(pqf-def-locnoeth), and therefore Noetherian. The restricted diagonal makes U
separated over k, and l is invertible there because l differs from char(k).
4. If C were proper, its affineness would make it finite over k and of dimension
zero (lem-sc-proper-affine-finite), a contradiction. Since C is reduced, no closed
subset proper over k can be all of C (def-weil-pbc-closed-subset-proper-over-base).
5. The ordinary image G=j_*F is constructible
(lem-a1-adic-middle-extension-constructible). The injective section comparison of
lem-a1-constructible-degree-zero-proper-support sends any class c in H_c^0(C,G)
to a section s vanishing outside a closed subset Z proper over k. Open-restriction
compatibility and the formula (j_*F)(V)=F(V times_C U) identify s|U with a lisse
adic section t from the coefficient unit to F (def-wf-middle-extension).
6. The nonempty open C minus Z meets U. At a geometric point above a point in
this intersection the fibre of t is zero. The lisse geometric fibre equivalence
on the connected Noetherian separated U is faithful and carries the coefficient
unit to the trivial line (cor-galois-lisse-representations), so t is zero.
7. Ordinary direct-image global sections are determined by their restriction to
U: at each sheaf stage (j_*F)(C)=F(U), and all components are pullbacks of this
section (def-wf-middle-extension). This injective identification persists level
by level in the adic tower, under rationalization, common finite extensions and
idempotent summands. Thus s is zero; injectivity of the section comparison makes
c zero. Every class is zero, as claimed.
-/
theorem subsingleton_adicMiddleExtension_hcZero
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type (u + 1)) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (c : MiddleExtensionCurve D) [IsAffine c.C.left]
    [SmoothOfRelativeDimension 1 c.C.hom] [GeometricallyConnected c.C.hom]
    (F : adicMiddleExtensionLisse l Ω c hl)
    (theta : (sfCommonStageWeilFrobeniusPullback D l hl c.U Ω).obj
      (adicMiddleExtensionInput l Ω c hl F) ≅ adicMiddleExtensionInput l Ω c hl F)
    (compactification : Compactification (D.geometricFiber c.C).hom) :
    Subsingleton (adicCompactCohomology D l hl (D.geometricFiber c.C).left Ω
      compactification ((sfCommonStageWeilForget D l hl c.C Ω).obj
        (adicMiddleExtensionWeil l Ω c hl F theta)) 0) := by
  classical
  let X := (D.geometricFiber c.C).left
  let f := (D.geometricFiber c.C).hom
  have hZ (Z : TopologicalSpace.Closeds X)
      (hZ : IsClosedSubsetProperOver f Z) : Z ≠ ⊤ :=
    middleExtensionCurve_closedSubset_ne_top c Z hZ
  let G : sfCommonStageHeart l X Ω :=
    ⟨adicMiddleExtensionObject l Ω c hl F, (adicMiddleExtension_heart l Ω c hl F).1⟩
  obtain ⟨N⟩ := a1ConstructibleDegreeZeroProperSupport l D hl Ω X compactification
  have section_zero (z : N.compact.obj G.obj) :
      N.sections.hom.app G (ULift.up (N.comparison.app G.obj z)) =
        (0 : A1ConstructibleSections l D hl Ω X G.obj) := by
    obtain ⟨Z, hproper, hzero⟩ := N.support G z
    let V : X.Opens := ⟨(Z : Set X)ᶜ, Z.isClosed.isOpen_compl⟩
    have hV : (V : Set X).Nonempty := by
      by_contra hempty
      apply hZ Z hproper
      apply SetLike.coe_injective
      apply Set.eq_univ_of_forall
      intro x
      by_contra hx
      exact hempty ⟨x, hx⟩
    exact adicMiddleExtension_section_eq_zero_of_restriction D l hl Ω c F V hV
      (N.sections.hom.app G (ULift.up (N.comparison.app G.obj z))) hzero
  have compact_unique (a b : N.compact.obj G.obj) : a = b := by
    apply N.injective G
    apply ULift.up_injective
    apply (N.sections.app G).toEquiv.injective
    exact (section_zero a).trans (section_zero b).symm
  refine ⟨fun a b ↦ ?_⟩
  have h := compact_unique
    ((N.compactValue G.obj).inv (ULift.up a))
    ((N.compactValue G.obj).inv (ULift.up b))
  have h' := congrArg (fun z ↦ (N.compactValue G.obj).hom z) h
  have h'' : ULift.up a = ULift.up b := by
    simpa only [← ConcreteCategory.comp_apply, Iso.inv_hom_id,
      ConcreteCategory.id_apply] using h'
  exact ULift.up_injective h''

end WeilConjectures

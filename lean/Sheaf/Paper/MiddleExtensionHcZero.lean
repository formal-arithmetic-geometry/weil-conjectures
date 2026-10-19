/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.Paper.AdicMiddleExtensionConstructible
public import Sheaf.Paper.CurveWeilMiddleExtension
public import Sheaf.Paper.CommonStageCompactWeilCohomology
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings
import Sheaf.Paper.GaloisLisseRepresentations
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.RepresentationTheory.Rep.Basic
import Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence
import Sheaf.Paper.LisseAdicFiberFunctors
import Sheaf.Paper.LisseModuleSheaves
import Sheaf.Paper.LisseTensorScalarExtension
import Sheaf.RepresentationTheory.LAdic
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Irreducible
import Sheaf.Paper.CommonStageCurveWeilMiddleExtension
import Sheaf.Paper.ConstructibleDegreeZeroProperSupport

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
  sorry

end WeilConjectures

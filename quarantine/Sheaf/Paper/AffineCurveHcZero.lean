/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q95
-/
module

public import Sheaf.Paper.OrdinaryCompactCohomology
public import Sheaf.Paper.RealSheavesSetup
public import Sheaf.Paper.CommonStageLisse
import Sheaf.Paper.LisseAdicSheaves
import Sheaf.Paper.GaloisLisseRepresentations
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.RepresentationTheory.Rep.Basic
import Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence
import Sheaf.Paper.LisseAdicFiberFunctors
import Sheaf.Paper.LisseModuleSheaves
import Sheaf.Paper.LisseTensorScalarExtension
import Sheaf.RepresentationTheory.LAdic
import Mathlib.RingTheory.FiniteType
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.Paper.DegreeZeroCompactSupportSections

/-! # Degree-zero compact-support vanishing on a lisse affine curve

Source: blueprint main-20261015, sec-purity-real-sheaves/sk-p-real-rankin,
lem-a1-affine-hc0 (blueprint: lem-a1-affine-hc0).

## Main definitions

* `RealSheaves.Setup.cohomologyFieldDatum` retains the chapter's chosen fields.
* The three `geometricCurve` instances expose standard pullback properties.

## Main statements

* `RealSheaves.Setup.subsingleton_affineCurveHcZero` states the vanishing of H_c^0.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace RealSheaves

/-- The chapter's field choices, in the finite-field interface used by cohomology.
Every field and algebra structure is the existing chosen one.
Source: blueprint d-real-setup and lem-a1-affine-hc0
(blueprint: lem-a1-affine-hc0). -/
abbrev Setup.cohomologyFieldDatum (S : Setup.{u, u}) : WeilConjectures.FiniteFieldDatum.{u} where
  p := S.p
  a := S.a
  q := S.q
  prime := S.p_prime
  exponent_pos := S.a_pos
  cardinality_eq := rfl
  k₀ := S.k₀
  card_base := Nat.card_eq_fintype_card.trans S.card_eq
  k := S.k

/-- Finite type on the geometric fibre is the standard pullback instance.
Source: blueprint scalar-extension step (blueprint: lem-a1-affine-hc0). -/
instance Setup.geometricCurveLocallyOfFiniteType (S : Setup.{u, u})
    (U₀ : Over (Spec (.of S.k₀))) [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom] :
    LocallyOfFiniteType ((S.cohomologyFieldDatum.geometricFiber U₀).left ↘
      Spec (.of S.cohomologyFieldDatum.k)) :=
  inferInstanceAs (LocallyOfFiniteType
    (pullback.snd U₀.hom (Spec.map (CommRingCat.ofHom (algebraMap S.k₀ S.k)))))

/-- Quasi-compactness on the geometric fibre is the standard pullback instance.
Source: blueprint scalar-extension step (blueprint: lem-a1-affine-hc0). -/
instance Setup.geometricCurveQuasiCompact (S : Setup.{u, u})
    (U₀ : Over (Spec (.of S.k₀))) [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom] :
    QuasiCompact ((S.cohomologyFieldDatum.geometricFiber U₀).left ↘
      Spec (.of S.cohomologyFieldDatum.k)) :=
  inferInstanceAs (QuasiCompact
    (pullback.snd U₀.hom (Spec.map (CommRingCat.ofHom (algebraMap S.k₀ S.k)))))

/-- Separatedness on the geometric fibre is the standard pullback instance.
Source: blueprint scalar-extension step (blueprint: lem-a1-affine-hc0). -/
instance Setup.geometricCurveIsSeparated (S : Setup.{u, u})
    (U₀ : Over (Spec (.of S.k₀))) [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [IsSeparated U₀.hom] :
    IsSeparated ((S.cohomologyFieldDatum.geometricFiber U₀).left ↘
      Spec (.of S.cohomologyFieldDatum.k)) :=
  inferInstanceAs (IsSeparated
    (pullback.snd U₀.hom (Spec.map (CommRingCat.ofHom (algebraMap S.k₀ S.k)))))

/-- On a smooth geometrically connected affine curve, a lisse Weil sheaf has zero
compactly supported cohomology in degree zero, in the completed common-stage model.
Source: blueprint main-20261015, lem-a1-affine-hc0; Milne, Etale Cohomology lectures,
Definition 18.1 and Remark 29.7 (blueprint: lem-a1-affine-hc0).

Proof:
1. The chapter curve convention gives a nonempty smooth separated finite-type curve
with connected geometric fibre. Affine scalar extension is affine of finite type;
the finite-type algebra over the field is Noetherian
(lem-weil-pbc-finite-type-algebra-noetherian).
2. Smooth relative dimension one survives scalar extension
(lem-sbc-smooth-relative-dimension-permanence); the nonempty geometric fibre has
dimension one (lem-sbc-smooth-fixed-dimension-over-field), and is reduced
(sbc-lem-smooth-geometrically-reduced). If it were proper, proper plus affine would
make it finite and zero-dimensional (lem-sc-proper-affine-finite), a contradiction.
3. The degree-zero compact-support comparison
(lem-a1-degree-zero-compact-support-sections) realizes the underlying lisse adic
sheaf and injects the specified H_c^0 into its ordinary sections. Each image section
has a closed support whose reduced induced subscheme is proper over the base field.
4. The lisse fibre equivalence (cor-galois-lisse-representations) is faithful and
sends the unit to the trivial line. A nonzero section therefore has nonzero fibre
at every geometric point. Every scheme point has such a geometric lift, so the
support of a nonzero section is the entire geometric curve.
5. Since the curve is reduced, full reduced support is the curve itself. Properness
of the support contradicts step 2. Every image section is zero, and injectivity
then forces every class in the specified H_c^0 to be zero.
-/
theorem Setup.subsingleton_affineCurveHcZero
    (S : Setup.{u, u}) (U₀ : Over (Spec (.of S.k₀)))
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom] [IsSeparated U₀.hom]
    [IsAffine U₀.left] (hU : S.IsCurve U₀.left)
    (F : WeilConjectures.sfCommonStageWeilSheaf S.cohomologyFieldDatum S.l S.l_ne_p U₀ S.Qbar)
    (hF : WeilConjectures.HasCommonStageLisseLattice S.l S.Qbar
      (S.cohomologyFieldDatum.geometricFiber U₀).left
      ((WeilConjectures.sfCommonStageWeilForget
        S.cohomologyFieldDatum S.l S.l_ne_p U₀ S.Qbar).obj F.obj))
    (c : Compactification (S.cohomologyFieldDatum.geometricFiber U₀).hom) :
    Subsingleton ((WeilConjectures.qbarWeilSheafCohomology
      S.cohomologyFieldDatum S.l S.l_ne_p S.Qbar U₀ c F 0).2) := by
  sorry

end RealSheaves

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RealSheavesSetup
public import WeilConjectures.AlgebraicGeometry.RealWeilSheaves
public import WeilConjectures.AlgebraicGeometry.CoefficientHeart
public import WeilConjectures.AlgebraicGeometry.CondensedLisseMonodromy
public import WeilConjectures.AlgebraicGeometry.EtaleWeilFundamentalRepresentation
public import WeilConjectures.AlgebraicGeometry.CondensedStrictWeilComplex
public import WeilConjectures.AlgebraicGeometry.LisseQlbarRepresentations
public import WeilConjectures.AlgebraicGeometry.CondensedMonodromyFrobenius
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.WeilGroup
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.LinearAlgebra
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Scalars
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.GeometricallyConnectedAlgebraicClosure
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.RealCondensedFibreFunctoriality
import WeilConjectures.GroupTheory.WeilGroup

/-! # Ordinary condensed sections as geometric invariants

Source: latest blueprint, sec-purity-real-sheaves/sk-lem-wrp-hc2/p-real-sections.md
and p-real-sections.proof.md (blueprint: p-real-sections).

Sections are taken before imposing the Weil condition. The map is the actual geometric
fibre of a module map from the coefficient unit, evaluated at its unit vector.

## Main definitions and statements

* `RealSheaves.sectionContext`: the actual geometric curve with its derived properties.
* `RealSheaves.sectionRestriction`: the canonical restriction of Weil groups.
* `RealSheaves.sectionRepresentation`: the recorded Weil representation on the actual fibre.
* `RealSheaves.ordinarySections`: literal sections of the underlying module sheaf.
* `RealSheaves.realSections`: the canonical, linear and Frobenius-equivariant identification.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedLisseMonodromy
open scoped CategoryTheory.Obj

namespace RealSheaves

/-- The geometric properties implied by the standing curve convention.
Source: p-real-sections.proof.md, step 1 (blueprint: p-real-sections).
Proof: Smoothness and finite type survive extension to k. A smooth scheme over a field is
regular and locally Noetherian. Finite type supplies quasi-compactness, and separatedness
survives base change. The connectedness is part of IsCurve. Since ell differs from the
characteristic, ell is invertible in every residue field. Connectedness over an algebraic
closure is equivalent to geometric connectedness over the base field. -/
theorem curveSectionGeometry (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))] (hC : D.IsCurve C₀) :
    IsRegular (D.geometricCurve C₀) ∧ IsNoetherian (D.geometricCurve C₀) ∧
      (D.geometricCurve C₀).IsSeparated ∧
      (∀ z : D.geometricCurve C₀,
        Nonempty (Invertible (D.l : (D.geometricCurve C₀).residueField z))) ∧
      LocallyOfFiniteType (pullback.snd (C₀ ↘ Spec (.of D.k₀))
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) ∧
      QuasiCompact (pullback.snd (C₀ ↘ Spec (.of D.k₀))
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) ∧
      IsSeparated (pullback.snd (C₀ ↘ Spec (.of D.k₀))
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) ∧
      GeometricallyConnected (C₀ ↘ Spec (.of D.k₀)) := by
  have : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  let f := C₀ ↘ Spec (.of D.k₀)
  let g := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  have : Smooth f := hC.2.2.1
  have : LocallyOfFiniteType f := hC.2.2.2.1
  have : QuasiCompact f := hC.2.2.2.2.1
  have : IsSeparated f := hC.2.1
  have : LocallyOfFiniteType (pullback.snd f g) := inferInstance
  have : QuasiCompact (pullback.snd f g) := inferInstance
  have : IsSeparated (pullback.snd f g) := inferInstance
  have : IsLocallyNoetherian (D.geometricCurve C₀) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f g)
  have : CompactSpace (D.geometricCurve C₀) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f g)
  have : IsNoetherian (D.geometricCurve C₀) := {}
  have hreg := IsRegular.of_smooth (pullback.snd f g)
  have hsep := Scheme.isSeparated_of_isSeparated_hom (pullback.snd f g)
  have hunit : IsUnit (D.l : D.k₀) :=
    (CharP.cast_ne_zero_of_ne_of_prime D.k₀ (Fact.out : D.l.Prime)
      (Fact.out : ringChar D.k₀ ≠ D.l)).isUnit
  refine ⟨hreg, inferInstance, hsep, ?_, inferInstance, inferInstance,
    inferInstance, ?_⟩
  · intro z
    let φ := ((Scheme.ΓSpecIso (.of D.k₀)).inv ≫
      (pullback.fst f g ≫ f).appTop ≫ (D.geometricCurve C₀).Γevaluation z).hom
    exact ⟨(show IsUnit (D.l : (D.geometricCurve C₀).residueField z) by
      simpa using hunit.map φ).invertible⟩
  · exact (geometricallyConnected_iff_connectedSpace_of_isAlgClosed
      (Ω := D.k) C₀).mpr hC.2.2.2.2.2.2

/-- A nonempty open remains a curve in the chapter's precise sense.
Source: p-real-sections.proof.md, step 1 (blueprint: p-real-sections).
Proof: Separatedness, smoothness and local finite type restrict to opens. The ambient
curve is Noetherian, which makes each open quasi-compact. It is geometrically connected
by the algebraic-closure criterion, hence connected, and regular, hence integral; its pure
dimension one is smooth relative dimension one, which restricts to the open. A nonempty
open of a smooth geometrically connected scheme is geometrically connected, hence connected
and integral, so its sole irreducible component has dimension one; the algebraic-closure
criterion turns geometric connectedness back into connectedness after base change. -/
theorem openSectionCurve (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))] (hC : D.IsCurve C₀)
    (U₀ : C₀.Opens) (hU : Nonempty U₀) : D.IsCurve U₀.toScheme := by
  have : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  let f := C₀ ↘ Spec (.of D.k₀)
  have : Smooth f := hC.2.2.1
  have : LocallyOfFiniteType f := hC.2.2.2.1
  have : QuasiCompact f := hC.2.2.2.2.1
  have : IsSeparated f := hC.2.1
  have : GeometricallyConnected f :=
    (geometricallyConnected_iff_connectedSpace_of_isAlgClosed (Ω := D.k) C₀).mpr
      hC.2.2.2.2.2.2
  have : ConnectedSpace C₀ := GeometricallyConnected.connectedSpace_of_subsingleton f
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian C₀ := {}
  have := IsRegular.of_smooth f
  have := IsRegular.isIntegral C₀
  have hp := hC.2.2.2.2.2.1 Set.univ
    (by simp only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff])
  have hd : topologicalKrullDim C₀ = (1 : WithBot ℕ∞) :=
    ((Homeomorph.Set.univ C₀).isHomeomorph.topologicalKrullDim_eq _).symm.trans hp
  have : SmoothOfRelativeDimension 1 f :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq f 1).mpr hd
  have : Nonempty U₀.toScheme := hU
  have : GeometricallyConnected (U₀.ι ≫ f) := WeilGroup.geometricallyConnected_comp U₀.ι
  have : ConnectedSpace U₀.toScheme :=
    GeometricallyConnected.connectedSpace_of_subsingleton (U₀.ι ≫ f)
  have := IsRegular.of_smooth (U₀.ι ≫ f)
  have := IsRegular.isIntegral U₀.toScheme
  have : SmoothOfRelativeDimension 1 (U₀.ι ≫ f) :=
    smoothOfRelativeDimension_comp 0 1 U₀.ι f
  have hsU : IsSeparated (U₀.ι ≫ f) := inferInstance
  have hmU : Smooth (U₀.ι ≫ f) := inferInstance
  have hftU : LocallyOfFiniteType (U₀.ι ≫ f) := inferInstance
  have hqcU : QuasiCompact (U₀.ι ≫ f) := inferInstance
  refine ⟨hU, hsU, hmU, hftU, hqcU, ?_, ?_⟩
  · intro Z hZ
    have hZ : Z = Set.univ := by
      simpa only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] using hZ
    subst Z
    exact ((Homeomorph.Set.univ U₀.toScheme).isHomeomorph.topologicalKrullDim_eq _).trans
      ((smoothOfRelativeDimension_iff_topologicalKrullDim_eq (U₀.ι ≫ f) 1).mp inferInstance)
  · exact (geometricallyConnected_iff_connectedSpace_of_isAlgClosed
      (Ω := D.k) U₀.toScheme).mp
      (show GeometricallyConnected (U₀.ι ≫ f) from inferInstance)

/-- The existing monodromy context on the actual chosen geometric curve; all its data
are fixed, and only its geometric properties come from curveSectionGeometry.
The residue-field inverse is determined uniquely; choice postpones only its existence proof.
Source: p-real-sections.proof.md, step 1 (blueprint: p-real-sections). -/
@[irreducible] def sectionContext (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))] (hC : D.IsCurve C₀) : Context D.l D.k where
  X := D.geometricCurve C₀
  overBase := ⟨pullback.snd (C₀ ↘ Spec (.of D.k₀))
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))⟩
  connected := hC.2.2.2.2.2.2
  regular := (curveSectionGeometry D C₀ hC).1
  finiteType := (curveSectionGeometry D C₀ hC).2.2.2.2.1
  quasiCompact := (curveSectionGeometry D C₀ hC).2.2.2.2.2.1
  separated := (curveSectionGeometry D C₀ hC).2.2.2.2.2.2.1
  noetherian := (curveSectionGeometry D C₀ hC).2.1
  absoluteSeparated := (curveSectionGeometry D C₀ hC).2.2.1
  invertible := fun z ↦ Classical.choice ((curveSectionGeometry D C₀ hC).2.2.2.1 z)

/-- The context's scheme is exactly the recorded geometric curve.
Source: p-real-sections.md, C = C₀ times k (blueprint: p-real-sections).
Proof: Project the X field of the displayed sectionContext construction. -/
theorem sectionContext_scheme (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))] (hC : D.IsCurve C₀) :
    (sectionContext D C₀ hC).X = D.geometricCurve C₀ := by
  with_unfolding_all rfl

/-- The canonical inclusion of the geometric open, using the recorded fibre products
and their explicit context identifications.
Source: p-real-sections.md, U = U₀ times k (blueprint: p-real-sections). -/
@[irreducible] def sectionOpenMap (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))] (hC : D.IsCurve C₀) (U₀ : C₀.Opens) (hU : Nonempty U₀) :
    (sectionContext D U₀.toScheme (openSectionCurve D C₀ hC U₀ hU)).X ⟶
      (sectionContext D C₀ hC).X :=
  eqToHom (sectionContext_scheme D U₀.toScheme (openSectionCurve D C₀ hC U₀ hU)) ≫
    pullback.map _ _ _ _ U₀.ι (𝟙 _) (𝟙 _) (by simp) (by simp) ≫
      eqToHom (sectionContext_scheme D C₀ hC).symm

/-- The arithmetic projection, including the explicit context identification.
Source: p-real-sections.md, common geometric point (blueprint: p-real-sections). -/
@[irreducible] def sectionProjection (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))] (hC : D.IsCurve C₀) :
    (sectionContext D C₀ hC).X ⟶ C₀ :=
  eqToHom (sectionContext_scheme D C₀ hC) ≫
    pullback.fst (C₀ ↘ Spec (.of D.k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))

/-- The actual geometric Frobenius, conjugated by the explicit context identification.
Source: p-real-sections.md, geometric Frobenius convention (blueprint: p-real-sections). -/
@[irreducible] def sectionCurveFrobenius (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))] (hC : D.IsCurve C₀) :
    (sectionContext D C₀ hC).X ≅ (sectionContext D C₀ hC).X :=
  eqToIso (sectionContext_scheme D C₀ hC) ≪≫ D.weilFrobenius C₀ hC ≪≫
    (eqToIso (sectionContext_scheme D C₀ hC)).symm

/-- The actual Weil group at the arithmetic image of the given geometric point.
Source: def-wf-weil-group and p-real-sections.md (blueprint: p-real-sections). -/
abbrev SectionWeilGroup (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))] (hC : D.IsCurve C₀)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ (sectionContext D C₀ hC).X) :=
  haveI := (curveSectionGeometry D C₀ hC).2.2.2.2.2.2.2
  FiniteEtale.weilGroup (C₀ ↘ Spec (.of D.k₀)) (x ≫ sectionProjection D C₀ hC)
    (Aut (FiniteEtale.fiber (x ≫ sectionProjection D C₀ hC)))

/-- Its degree map counts geometric Frobenius, with degree one rather than minus one.
Source: def-wf-weil-group and p-real-sections.md (blueprint: p-real-sections). -/
abbrev sectionDegree (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))] (hC : D.IsCurve C₀)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ (sectionContext D C₀ hC).X) :
    SectionWeilGroup D C₀ hC x →* Multiplicative ℤ :=
  haveI := (curveSectionGeometry D C₀ hC).2.2.2.2.2.2.2
  FiniteEtale.weilGroupDeg (C₀ ↘ Spec (.of D.k₀)) (x ≫ sectionProjection D C₀ hC)
    (Aut (FiniteEtale.fiber (x ≫ sectionProjection D C₀ hC)))

/-- Actual lisse pullback with the two derived geometric contexts made explicit.
Source: p-real-sections.md, restriction to U (blueprint: p-real-sections). -/
abbrev sectionPullback (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))] (hC : D.IsCurve C₀) (U₀ : C₀.Opens) (hU : Nonempty U₀)
    (S : CompatibleSystem D.l D.k) :=
  S.toSystem.pullback D.l (D := sectionContext D C₀ hC)
    (E := sectionContext D U₀.toScheme (openSectionCurve D C₀ hC U₀ hU))
      (sectionOpenMap D C₀ hC U₀ hU)

/-- The actual restricted module, exposed through its lisse-object interface.
Source: p-real-sections.md, F restricted to U (blueprint: p-real-sections). -/
@[irreducible] def sectionRestrictionObject (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))] (hC : D.IsCurve C₀) (U₀ : C₀.Opens) (hU : Nonempty U₀)
    (S : CompatibleSystem D.l D.k) (L : Lisse D.l ((sectionContext D C₀ hC).X)) :
    Lisse D.l ((sectionContext D U₀.toScheme (openSectionCurve D C₀ hC U₀ hU)).X) :=
  (sectionPullback D C₀ hC U₀ hU S).obj L

/-- Actual Frobenius pullback on lisse objects in the fixed geometric context.
Source: p-real-sections.md, Weil isomorphism (blueprint: p-real-sections). -/
abbrev sectionFrobPullback (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))] (hC : D.IsCurve C₀) (S : CompatibleSystem D.l D.k) :=
  S.toSystem.pullback D.l (D := sectionContext D C₀ hC) (E := sectionContext D C₀ hC)
    (sectionCurveFrobenius D C₀ hC).hom

/-- The canonical identification of the restricted geometric fibre with the original fibre.
Source: p-real-sections.proof.md, step 3 (blueprint: p-real-sections). -/
abbrev sectionPullbackFibre (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))] (hC : D.IsCurve C₀) (U₀ : C₀.Opens) (hU : Nonempty U₀)
    (S : CompatibleSystem D.l D.k) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ (sectionContext D U₀.toScheme (openSectionCurve D C₀ hC U₀ hU)).X) :=
  S.toSystem.pullbackFibre D.l (D := sectionContext D C₀ hC)
    (E := sectionContext D U₀.toScheme (openSectionCurve D C₀ hC U₀ hU))
      (sectionOpenMap D C₀ hC U₀ hU) x

/-- Canonical restriction on full finite-etale fibre automorphism groups, as a homomorphism.
Source: p-real-sections.md, restriction at the common point (blueprint: p-real-sections). -/
def sectionPiMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    Aut (FiniteEtale.fiber x) →* Aut (FiniteEtale.fiber (x ≫ f)) :=
  (Aut.autMulEquivOfIso (FiniteEtale.pullbackFiberIso f x)).toMonoidHom.comp
    (((Functor.whiskeringLeft Y.FiniteEtale X.FiniteEtale FintypeCat).obj
      (FiniteEtale.pullback f)).mapAut (FiniteEtale.fiber x))

/-- The canonical geometric open commutes with arithmetic projection.
Source: p-real-sections.md, common geometric generic point (blueprint: p-real-sections).
Proof: Cancel the context identifications and apply the defining fibre-product square. -/
theorem sectionOpen_projection (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))] (hC : D.IsCurve C₀)
    (U₀ : C₀.Opens) (hU : Nonempty U₀)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶
      (sectionContext D U₀.toScheme (openSectionCurve D C₀ hC U₀ hU)).X) :
    (x ≫ sectionProjection D U₀.toScheme (openSectionCurve D C₀ hC U₀ hU)) ≫ U₀.ι =
      (x ≫ sectionOpenMap D C₀ hC U₀ hU) ≫ sectionProjection D C₀ hC := by
  simp [sectionOpenMap, sectionProjection]

/-- The two arithmetic images of the common point agree by the fibre-product equation.
Source: p-real-sections.md, common geometric generic point (blueprint: p-real-sections). -/
def sectionArithmeticPath (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))] (hC : D.IsCurve C₀)
    (U₀ : C₀.Opens) (hU : Nonempty U₀)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶
      (sectionContext D U₀.toScheme (openSectionCurve D C₀ hC U₀ hU)).X) :=
  eqToIso (congrArg FiniteEtale.fiber (sectionOpen_projection D C₀ hC U₀ hU x))

/-- Restriction of arithmetic fundamental groups, with the common-point comparison inserted.
Source: p-real-sections.md, the map underlying r (blueprint: p-real-sections). -/
def sectionArithmeticMap (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))] (hC : D.IsCurve C₀)
    (U₀ : C₀.Opens) (hU : Nonempty U₀)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ (sectionContext D U₀.toScheme (openSectionCurve D C₀ hC U₀ hU)).X) :
    Aut (FiniteEtale.fiber
      (x ≫ sectionProjection D U₀.toScheme (openSectionCurve D C₀ hC U₀ hU))) →*
      Aut (FiniteEtale.fiber
        ((x ≫ sectionOpenMap D C₀ hC U₀ hU) ≫ sectionProjection D C₀ hC)) :=
  (Aut.autMulEquivOfIso (sectionArithmeticPath D C₀ hC U₀ hU x)).toMonoidHom.comp
    (sectionPiMap U₀.ι (x ≫ sectionProjection D U₀.toScheme (openSectionCurve D C₀ hC U₀ hU)))

/-- Arithmetic restriction preserves the defining constant-cover Frobenius condition.
Source: p-real-sections.proof.md, step 5 (blueprint: p-real-sections).
Proof: The pullback of C₀ × Spec A is U₀ × Spec A for every finite etale base algebra A.
The canonical fibre bijection commutes with its Frobenius automorphism. Thus a pair
(g,n) satisfying the Weil condition maps to (r(g),n) satisfying the same condition. -/
theorem sectionRestriction_mem (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))] (hC : D.IsCurve C₀) (U₀ : C₀.Opens) (hU : Nonempty U₀)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ (sectionContext D U₀.toScheme (openSectionCurve D C₀ hC U₀ hU)).X)
    (w : SectionWeilGroup D U₀.toScheme (openSectionCurve D C₀ hC U₀ hU) x) :
    (sectionArithmeticMap D C₀ hC U₀ hU x w.val.1, w.val.2) ∈
      SectionWeilGroup D C₀ hC (x ≫ sectionOpenMap D C₀ hC U₀ hU) := by
  have : GeometricallyConnected (C₀ ↘ Spec (.of D.k₀)) :=
    (curveSectionGeometry D C₀ hC).2.2.2.2.2.2.2
  have : GeometricallyConnected (U₀.toScheme ↘ Spec (.of D.k₀)) :=
    (curveSectionGeometry D U₀.toScheme (openSectionCurve D C₀ hC U₀ hU)).2.2.2.2.2.2.2
  let p := C₀ ↘ Spec (.of D.k₀)
  let pU := U₀.toScheme ↘ Spec (.of D.k₀)
  have hj : U₀.ι ≫ p = pU := rfl
  let s := x ≫ sectionProjection D U₀.toScheme (openSectionCurve D C₀ hC U₀ hU)
  let τ := sectionArithmeticPath D C₀ hC U₀ hU x
  let β := FiniteEtale.pullbackFiberIso U₀.ι s
  have hmap (P : C₀.FiniteEtale)
      (y : (FiniteEtale.fiber s).obj ((FiniteEtale.pullback U₀.ι).obj P)) :
      (sectionArithmeticMap D C₀ hC U₀ hU x w.val.1).hom.app P
          (τ.hom.app P (β.hom.app P y)) =
        τ.hom.app P (β.hom.app P (w.val.1.hom.app _ y)) := by
    change τ.hom.app P (β.hom.app P (w.val.1.hom.app _
      (β.inv.app P (τ.inv.app P (τ.hom.app P (β.hom.app P y)))))) = _
    have hτ (z : (FiniteEtale.fiber (s ≫ U₀.ι)).obj P) :
        τ.inv.app P (τ.hom.app P z) = z := by
      simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using
        ConcreteCategory.congr_hom (τ.hom_inv_id_app P) z
    have hβ : β.inv.app P (β.hom.app P y) = y := by
      simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using
        ConcreteCategory.congr_hom (β.hom_inv_id_app P) y
    rw [hτ, hβ]
  apply (FiniteEtale.mem_weilGroup_iff _ _ _).mpr
  intro A z
  obtain ⟨z', rfl⟩ : ∃ z', τ.hom.app _ z' = z :=
    ⟨τ.inv.app _ z, ConcreteCategory.congr_hom (τ.inv_hom_id_app _) z⟩
  obtain ⟨y, rfl⟩ := (FiniteEtale.constantCoverFiberMap_bijective
    U₀.ι hj s A).2 z'
  have hw := (FiniteEtale.mem_weilGroup_iff _ _ _).mp w.property A y
  change w.val.1.hom.app (FiniteEtale.constantCover pU A) y =
    (FiniteEtale.geometricFrobenius pU s A ^ Multiplicative.toAdd w.val.2) y at hw
  have hn := ConcreteCategory.congr_hom (w.val.1.hom.naturality
    (FiniteEtale.constantCoverToPullback U₀.ι hj A)) y
  simp only [ConcreteCategory.comp_apply] at hn
  change (sectionArithmeticMap D C₀ hC U₀ hU x w.val.1).hom.app _ _ = _
  rw [← FiniteEtale.pullbackFiberIso_constantCoverToPullback U₀.ι hj s A y]
  rw [hmap]
  rw [hn]
  rw [FiniteEtale.pullbackFiberIso_constantCoverToPullback U₀.ι hj s A,
    hw, FiniteEtale.constantCoverFiberMap_geometricFrobenius_zpow,
    FiniteEtale.app_geometricFrobenius_zpow,
    FiniteEtale.pullbackFiberIso_constantCoverToPullback U₀.ι hj s A]

/-- The canonical Weil restriction: its underlying pair is (r(g),n), never an arbitrary map.
Source: p-real-sections.md, restriction r (blueprint: p-real-sections). -/
def sectionRestriction (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))] (hC : D.IsCurve C₀) (U₀ : C₀.Opens) (hU : Nonempty U₀)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ (sectionContext D U₀.toScheme (openSectionCurve D C₀ hC U₀ hU)).X) :
    SectionWeilGroup D U₀.toScheme (openSectionCurve D C₀ hC U₀ hU) x →*
      SectionWeilGroup D C₀ hC (x ≫ sectionOpenMap D C₀ hC U₀ hU) :=
  (((sectionArithmeticMap D C₀ hC U₀ hU x).prodMap (MonoidHom.id _)).comp
    (SectionWeilGroup D U₀.toScheme (openSectionCurve D C₀ hC U₀ hU) x).subtype).codRestrict
      (SectionWeilGroup D C₀ hC (x ≫ sectionOpenMap D C₀ hC U₀ hU))
      (sectionRestriction_mem D C₀ hC U₀ hU x)

/-- Frobenius commutes with the geometric open inclusion.
Source: p-real-sections.proof.md, step 6 (blueprint: p-real-sections).
Proof: On the fibre product both composites act as the open inclusion on the first
factor and geometric field Frobenius on the second factor. The universal property
of the fibre product therefore identifies them. -/
theorem sectionOpen_frobenius (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))] (hC : D.IsCurve C₀) (U₀ : C₀.Opens) (hU : Nonempty U₀) :
    (sectionCurveFrobenius D U₀.toScheme (openSectionCurve D C₀ hC U₀ hU)).hom ≫
        sectionOpenMap D C₀ hC U₀ hU =
      sectionOpenMap D C₀ hC U₀ hU ≫ (sectionCurveFrobenius D C₀ hC).hom := by
  simp only [sectionCurveFrobenius, Setup.weilFrobenius,
    WeilConjectures.FiniteFieldDatum.geometricFrobenius, Setup.weilFieldDatum,
    WeilConjectures.FiniteFieldDatum.galoisMap, AlgebraicGeometry.baseChangeMap,
    pullback.map, Over.mk_left, Over.mk_hom, Category.comp_id,
    FiniteField.geometricFrobeniusAlgEquivOfAlgebraic_eq_inv, RingEquiv.toRingHom_eq_coe,
    AlgEquiv.toRingEquiv_toRingHom, Over.homMk_left, AlgEquiv.symm_toRingEquiv,
    RingEquiv.symm_mk, AlgEquiv.toEquiv_eq_coe, AlgEquiv.symm_toEquiv_eq_symm,
    Iso.trans_hom, eqToIso.hom, Iso.symm_hom, eqToIso.inv, sectionOpenMap,
    Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  apply (cancel_epi (eqToHom
    (sectionContext_scheme D U₀.toScheme (openSectionCurve D C₀ hC U₀ hU)))).mpr
  simp only [← Category.assoc]
  apply (cancel_mono (eqToHom (sectionContext_scheme D C₀ hC).symm)).mpr
  apply pullback.hom_ext <;> simp [Category.assoc]

/-- Canonical restriction of a Weil isomorphism along a commuting scheme square,
in the two recorded geometric contexts.
Source: p-real-sections.proof.md, step 6 (blueprint: p-real-sections). -/
@[irreducible] def contextRestrictedWeil (l : ℕ) [Fact l.Prime]
    {k : Type u} [Field k] (C E : Context l k) (S : CompatibleSystem l k)
    (hC : C.X ≅ C.X) (hE : E.X ≅ E.X) (j : E.X ⟶ C.X)
    (sq : hE.hom ≫ j = j ≫ hC.hom) (L : Lisse l C.X)
    (θ : (S.toSystem.pullback l (D := C) (E := C) hC.hom).obj L ≅ L) :
    (S.toSystem.pullback l (D := E) (E := E) hE.hom).obj
      ((S.toSystem.pullback l (D := C) (E := E) j).obj L) ≅
        (S.toSystem.pullback l (D := C) (E := E) j).obj L :=
  ObjectProperty.isoMk _
    ((CondensedRing.upperStarSquareComparison (Profinite.padicAlgClRingObj l)
      (CommSq.mk sq)).symm.app L.obj ≪≫
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) j).mapIso
          ((ObjectProperty.ι _).mapIso θ))

/-- Restrict the actual Weil isomorphism, using the canonical pullback-square comparison.
Source: p-real-sections.md, phi restricted to U (blueprint: p-real-sections). -/
@[irreducible] def sectionRestrictedWeil (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))] (hC : D.IsCurve C₀) (U₀ : C₀.Opens) (hU : Nonempty U₀)
    (S : CompatibleSystem D.l D.k) (L : Lisse D.l ((sectionContext D C₀ hC).X))
    (θ : (sectionFrobPullback D C₀ hC S).obj L ≅ L) :=
  contextRestrictedWeil D.l (sectionContext D C₀ hC)
    (sectionContext D U₀.toScheme (openSectionCurve D C₀ hC U₀ hU)) S
    (sectionCurveFrobenius D C₀ hC)
    (sectionCurveFrobenius D U₀.toScheme (openSectionCurve D C₀ hC U₀ hU))
    (sectionOpenMap D C₀ hC U₀ hU) (sectionOpen_frobenius D C₀ hC U₀ hU) L θ

/-- The published Weil representation conjugated to the actual condensed fibre, in a
specified geometric comparison context. No representation is selected from mere existence.
Source: sk-d-real-weil, fibre dictionary (blueprint: p-real-sections). -/
@[irreducible] def contextSectionRepresentation (l : ℕ) [Fact l.Prime]
    {k : Type u} [Field k] (C : Context l k) (S : CompatibleSystem l k) (h : C.X ≅ C.X)
    (L : Lisse l C.X) (θ : (S.toSystem.pullback l h.hom).obj L ≅ L)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ C.X)
    {W : Type (u + 1)} [Group W] (d : Monodromy.DegreeDatum W)
    (E : EtaleWeilDegreeData h x W d) :
    Representation (Coeff.{u} l) W ((fibre l x).obj L) :=
  (((S.comparison C).beta l x L).symm.conjRingEquiv.toMonoidHom).comp
    (etaleFundamentalRep l (Coeff.{u} l) h x d E (S.weil l C h L θ))

/-- Geometric Frobenius fixes the arithmetic image of every geometric point.
Source: p-real-sections.md, chosen arithmetic Weil lift (blueprint: p-real-sections).
Proof: Geometric Frobenius on the base change acts only on the algebraic-closure
factor. The first projection is therefore unchanged, and composition with x preserves
this equality. This is a geometric identity, not an additional hypothesis. -/
theorem sectionFrobeniusProjection (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))] (hC : D.IsCurve C₀)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ (sectionContext D C₀ hC).X) :
    (x ≫ (sectionCurveFrobenius D C₀ hC).hom) ≫ sectionProjection D C₀ hC =
      x ≫ sectionProjection D C₀ hC := by
  simp [sectionCurveFrobenius, sectionProjection, Setup.weilFrobenius,
    WeilConjectures.FiniteFieldDatum.geometricFrobenius,
    WeilConjectures.FiniteFieldDatum.galoisMap, AlgebraicGeometry.baseChangeMap,
    Setup.weilFieldDatum, pullback.map]

/-- The actual condensed Weil representation, transported along the normalized fibre
comparison of the recorded dictionary. Its geometric action and degree-one operator
are fixed by etaleFundamentalRep, not supplied as arbitrary representation data.
Source: sk-d-real-weil and p-real-sections.md (blueprint: p-real-sections). -/
@[irreducible] def sectionRepresentation (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))] (hC : D.IsCurve C₀)
    (S : CompatibleSystem D.l D.k) (L : Lisse D.l ((sectionContext D C₀ hC).X))
    (θ : (sectionFrobPullback D C₀ hC S).obj L ≅ L)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ (sectionContext D C₀ hC).X)
    (d : Monodromy.DegreeDatum (SectionWeilGroup D C₀ hC x))
    (E : EtaleWeilDegreeData (sectionCurveFrobenius D C₀ hC) x _ d) :=
  contextSectionRepresentation D.l (sectionContext D C₀ hC) S (sectionCurveFrobenius D C₀ hC)
    L θ x d E

/-- Literal ordinary sections of the underlying condensed module sheaf at the terminal
pro-etale object; no Weil-fixed-point condition is imposed.
Source: p-real-sections.md, meaning of H⁰ (blueprint: p-real-sections). -/
@[irreducible] def ordinarySections (l : ℕ) [Fact l.Prime] {X : Scheme.{u}}
    (L : Lisse l X) : Ab.{u + 1} :=
  L.obj.X.obj.obj (Opposite.op (Scheme.ProEt.mk (𝟙 X)))

attribute [local semireducible] ordinarySections in
/-- A section s gives the module map a ↦ a s, using the free regular module's universal
property and terminal-object evaluation for the underlying abelian sheaf.
Source: p-real-sections.proof.md, step 2 (blueprint: p-real-sections). -/
def ordinarySectionHom (l : ℕ) [Fact l.Prime] {X : Scheme.{u}} (L : Lisse l X)
    (s : ordinarySections l L) : Sections l L :=
  Mod.regularLift L.obj
    ((Sheaf.unitHomEvalAddEquiv (J := Scheme.ProEt.topology X)
      (Scheme.ProEt.isTerminalMkId X) L.obj.X).symm s)

attribute [local semireducible] ordinarySections in
/-- A module map from the regular module gives a literal section by evaluating at 1.
Source: p-real-sections.proof.md, step 2 (blueprint: p-real-sections). -/
def ordinaryHomSection (l : ℕ) [Fact l.Prime] {X : Scheme.{u}} (L : Lisse l X)
    (b : Sections l L) : ordinarySections l L :=
  Sheaf.unitHomEval (J := Scheme.ProEt.topology X) (Scheme.ProEt.mk (𝟙 X))
    (Mod.regularHomAddEquiv L.obj b)

attribute [local semireducible] ordinarySections in
/-- The actual generic germ: the pro-etale inverse-image unit at the canonical lift of
the terminal object, followed by the published underlying-fibre comparison. This avoids
any choice of trivialization of the fibre of the rank-one coefficient module.
Source: p-real-sections.md, canonical identification by germs (blueprint: p-real-sections). -/
def ordinarySectionGerm (l : ℕ) [Fact l.Prime] {X : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (L : Lisse l X) (s : ordinarySections l L) : (fibre l x).obj L :=
  (rawAbIso l x L.obj).hom
    ((ProEtale.germ Ab.{u + 1} x L.obj.X (V := Scheme.ProEt.mk (𝟙 X))
      (MorphismProperty.Over.homMk
        (pullback.lift (f := 𝟙 X) (g := x) x (𝟙 _) (by simp))
        (pullback.lift_snd _ _ _))) s)

attribute [local semireducible] sectionRestrictionObject in
/-- The generic germ followed by the canonical open-pullback fibre identification.
Source: p-real-sections.md, canonical identification (blueprint: p-real-sections). -/
@[irreducible] def sectionGenericGerm (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))] (hC : D.IsCurve C₀) (U₀ : C₀.Opens) (hU : Nonempty U₀)
    (S : CompatibleSystem D.l D.k) (L : Lisse D.l ((sectionContext D C₀ hC).X))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ (sectionContext D U₀.toScheme (openSectionCurve D C₀ hC U₀ hU)).X)
    (b : ordinarySections D.l (sectionRestrictionObject D C₀ hC U₀ hU S L)) :=
  (sectionPullbackFibre D C₀ hC U₀ hU S x).hom.app L
    (ordinarySectionGerm D.l x (sectionRestrictionObject D C₀ hC U₀ hU S L) b)

/-- Constant-coefficient multiplication on actual ordinary sections.
Source: p-real-sections.md, Lambda-linearity (blueprint: p-real-sections). -/
@[irreducible] def ordinarySectionScalar (l : ℕ) [Fact l.Prime] {X : Scheme.{u}}
    (L : Lisse l X) (c : Coeff.{u} l) (b : ordinarySections l L) :
    ordinarySections l L :=
  ordinaryHomSection l L (sectionScalar l X c ≫ ordinarySectionHom l L b)

attribute [local semireducible] sectionRestrictionObject in
/-- Actual Frobenius pullback followed by the given restricted Weil isomorphism.
Source: p-real-sections.md, residual Frobenius on sections (blueprint: p-real-sections). -/
@[irreducible] def ordinarySectionFrobenius (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))] (hC : D.IsCurve C₀) (U₀ : C₀.Opens) (hU : Nonempty U₀)
    (S : CompatibleSystem D.l D.k) (L : Lisse D.l ((sectionContext D C₀ hC).X))
    (θ : (sectionFrobPullback D C₀ hC S).obj L ≅ L)
    (b : ordinarySections D.l (sectionRestrictionObject D C₀ hC U₀ hU S L)) :
    ordinarySections D.l (sectionRestrictionObject D C₀ hC U₀ hU S L) :=
  ordinaryHomSection D.l (sectionRestrictionObject D C₀ hC U₀ hU S L)
    (sectionFrobenius D.l
      (sectionContext D U₀.toScheme (openSectionCurve D C₀ hC U₀ hU)) S
      (sectionCurveFrobenius D U₀.toScheme (openSectionCurve D C₀ hC U₀ hU))
      (sectionRestrictionObject D C₀ hC U₀ hU S L)
      (sectionRestrictedWeil D C₀ hC U₀ hU S L θ)
      (ordinarySectionHom D.l (sectionRestrictionObject D C₀ hC U₀ hU S L) b))

/-- Ordinary global sections on the open are the geometric-kernel invariants of the generic
fibre, through the geometric generic germ and compatibly with coefficient scalars. This is the
germ/scalar half of `p-real-sections`, steps 2--4.

Source: p-real-sections.md, displayed formula; p-real-sections.proof.md, steps 2--4
(blueprint: p-real-sections; split node: real-sections-germ-scalar).

Proof: (1) Evaluation at 1 identifies ordinary sections with Hom_Mod(Λ_U,L|_U): a section s
gives a ↦ a s|_T on every T, and a module map b satisfies b_T(a) = a b_U(1)|_T; the two
formulas are inverse (sk-def-sfb-module-objects, sk-def-sfb-pulled-back-coefficients).
(2) The fully faithful geometric fibre dictionary of thm-lisse-qlbar-representations on the
connected normal Noetherian open identifies this Hom group with Hom_P(Λ,V); the unit
representation is trivial since its scalar c_g satisfies c_g^2 = c_g. The restricted fibre is
the same V with the action through the restriction map, by the open-immersion comparison of
lem-real-condensed-fibre-functoriality, so the composite is the geometric generic germ.
(3) Evaluation at 1 identifies Hom_P(Λ,V) with V^P, with inverse v ↦ (a ↦ a v); both are
Λ-linear, which gives the germ formula and the scalar formula. -/
theorem realSections_germ_scalar (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))] (hC : D.IsCurve C₀) (U₀ : C₀.Opens) (hU : Nonempty U₀)
    (S : CompatibleSystem D.l D.k) (hS : WeilCompatibility D.l S)
    (L : Lisse D.l ((sectionContext D C₀ hC).X))
    (θ : (sectionFrobPullback D C₀ hC S).obj L ≅ L)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ (sectionContext D U₀.toScheme (openSectionCurve D C₀ hC U₀ hU)).X)
    (hx : IsGenericPoint (x.base default)
      (Set.univ : Set (sectionContext D U₀.toScheme (openSectionCurve D C₀ hC U₀ hU)).X))
    (d : Monodromy.DegreeDatum
      (SectionWeilGroup D C₀ hC (x ≫ sectionOpenMap D C₀ hC U₀ hU)))
    (hd : d.deg = sectionDegree D C₀ hC (x ≫ sectionOpenMap D C₀ hC U₀ hU))
    (E : EtaleWeilDegreeData (sectionCurveFrobenius D C₀ hC) (x ≫ sectionOpenMap D C₀ hC U₀ hU) _ d)
    (hgeom : ∀ g : Aut (FiniteEtale.fiber (x ≫ sectionOpenMap D C₀ hC U₀ hU)),
      (E.geom g).val.val.1 = FiniteEtale.fiberAutBaseChange (sectionProjection D C₀ hC)
        (x ≫ sectionOpenMap D C₀ hC U₀ hU) g)
    (hpath : FiniteEtale.pullbackPathIso (sectionProjection D C₀ hC) E.path ≪≫
      eqToIso (congrArg FiniteEtale.fiber
        (sectionFrobeniusProjection D C₀ hC (x ≫ sectionOpenMap D C₀ hC U₀ hU))) =
          d.degreeOneElement.val.1) :
    ∃ e : ordinarySections D.l (sectionRestrictionObject D C₀ hC U₀ hU S L) ≃+
      Representation.invariants
        (((sectionRepresentation D C₀ hC S L θ (x ≫ sectionOpenMap D C₀ hC U₀ hU) d E).comp
          (sectionRestriction D C₀ hC U₀ hU x)).comp
            (sectionDegree D U₀.toScheme (openSectionCurve D C₀ hC U₀ hU) x).ker.subtype),
      (∀ b, (e b).val = sectionGenericGerm D C₀ hC U₀ hU S L x b) ∧
      (∀ (c : Coeff.{u} D.l) b,
        (e (ordinarySectionScalar D.l (sectionRestrictionObject D C₀ hC U₀ hU S L) c b)).val =
          c • (e b).val) := by
  sorry

/-- The normalized Weil comparison transports the section Frobenius and identifies all
open degree-one lifts on invariant vectors. This is the residual-action argument of
`p-real-sections` steps 5--6. Dense-open surjectivity and the exact Weil-group sequence
make the degree-one operator independent of the lift; fibre functoriality and the unit
Weil structure identify it with evaluation of the section Frobenius.
(blueprint: p-real-sections; split node: real-sections-frobenius). -/
theorem realSections_frobenius (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))] (hC : D.IsCurve C₀) (U₀ : C₀.Opens) (hU : Nonempty U₀)
    (S : CompatibleSystem D.l D.k) (hS : WeilCompatibility D.l S)
    (L : Lisse D.l ((sectionContext D C₀ hC).X))
    (θ : (sectionFrobPullback D C₀ hC S).obj L ≅ L)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ (sectionContext D U₀.toScheme (openSectionCurve D C₀ hC U₀ hU)).X)
    (hx : IsGenericPoint (x.base default)
      (Set.univ : Set (sectionContext D U₀.toScheme (openSectionCurve D C₀ hC U₀ hU)).X))
    (d : Monodromy.DegreeDatum
      (SectionWeilGroup D C₀ hC (x ≫ sectionOpenMap D C₀ hC U₀ hU)))
    (hd : d.deg = sectionDegree D C₀ hC (x ≫ sectionOpenMap D C₀ hC U₀ hU))
    (E : EtaleWeilDegreeData (sectionCurveFrobenius D C₀ hC) (x ≫ sectionOpenMap D C₀ hC U₀ hU) _ d)
    (hgeom : ∀ g : Aut (FiniteEtale.fiber (x ≫ sectionOpenMap D C₀ hC U₀ hU)),
      (E.geom g).val.val.1 = FiniteEtale.fiberAutBaseChange (sectionProjection D C₀ hC)
        (x ≫ sectionOpenMap D C₀ hC U₀ hU) g)
    (hpath : FiniteEtale.pullbackPathIso (sectionProjection D C₀ hC) E.path ≪≫
      eqToIso (congrArg FiniteEtale.fiber
        (sectionFrobeniusProjection D C₀ hC (x ≫ sectionOpenMap D C₀ hC U₀ hU))) =
          d.degreeOneElement.val.1)
    (e : ordinarySections D.l (sectionRestrictionObject D C₀ hC U₀ hU S L) ≃+
      Representation.invariants
        (((sectionRepresentation D C₀ hC S L θ (x ≫ sectionOpenMap D C₀ hC U₀ hU) d E).comp
          (sectionRestriction D C₀ hC U₀ hU x)).comp
            (sectionDegree D U₀.toScheme (openSectionCurve D C₀ hC U₀ hU) x).ker.subtype))
    (he : ∀ b, (e b).val = sectionGenericGerm D C₀ hC U₀ hU S L x b)
    (hs : ∀ (c : Coeff.{u} D.l) b,
      (e (ordinarySectionScalar D.l (sectionRestrictionObject D C₀ hC U₀ hU S L) c b)).val =
        c • (e b).val) :
    (∀ b, (e (ordinarySectionFrobenius D C₀ hC U₀ hU S L θ b)).val =
      sectionRepresentation D C₀ hC S L θ (x ≫ sectionOpenMap D C₀ hC U₀ hU) d E
        d.degreeOneElement (e b).val) ∧
    (∀ (γU : SectionWeilGroup D U₀.toScheme (openSectionCurve D C₀ hC U₀ hU) x),
      sectionDegree D U₀.toScheme (openSectionCurve D C₀ hC U₀ hU) x γU =
        Multiplicative.ofAdd 1 → ∀ b,
        sectionRepresentation D C₀ hC S L θ (x ≫ sectionOpenMap D C₀ hC U₀ hU) d E
          (sectionRestriction D C₀ hC U₀ hU x γU) (e b).val =
        sectionRepresentation D C₀ hC S L θ (x ≫ sectionOpenMap D C₀ hC U₀ hU) d E
          d.degreeOneElement (e b).val) := by
  sorry

/-- Ordinary global sections are geometric invariants, canonically and Frobenius-equivariantly.

Source: p-real-sections.md, displayed formula and final sentence
(blueprint: p-real-sections).

Proof: (1) Smooth base change and normality give connected normal Noetherian C and U.
(2) Evaluation at 1 identifies ordinary sections with Hom_Mod(Λ_U,L|_U): a section s
maps a to a s, and a module map is recovered from its value at 1.
(3) The fully faithful geometric fibre dictionary of thm-lisse-qlbar-representations
identifies these Hom groups with Hom_P(Λ,V); the unit representation is trivial.
Pullback compatibility identifies the restricted fibre with the same V.
(4) Evaluation at 1 identifies Hom_P(Λ,V) with V^P; its inverse sends v to (a ↦ a v).
The composite is the geometric generic germ and is linear.
(5) Dense-open surjectivity identifies P_U-invariants with P_C-invariants and maps
Weil groups surjectively, respecting degree. The degree kernel is normal, so all
lifts of degree one induce the same residual automorphism on these invariants.
(6) Naturality of the pullback comparison and path transport identifies phi Phi^*
on sections with rho(gamma). The canonical coefficient-unit Weil structure acts
as 1, so evaluation at 1 commutes with these operators. The hypothesis hS records
the normalized Weil-operator compatibility of the chosen geometric dictionary.
No section is required
to be Frobenius-fixed, and no phi-stable integral lattice is used. -/
theorem realSections (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))] (hC : D.IsCurve C₀) (U₀ : C₀.Opens) (hU : Nonempty U₀)
    (S : CompatibleSystem D.l D.k) (hS : WeilCompatibility D.l S)
    (L : Lisse D.l ((sectionContext D C₀ hC).X))
    (θ : (sectionFrobPullback D C₀ hC S).obj L ≅ L)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ (sectionContext D U₀.toScheme (openSectionCurve D C₀ hC U₀ hU)).X)
    (hx : IsGenericPoint (x.base default)
      (Set.univ : Set (sectionContext D U₀.toScheme (openSectionCurve D C₀ hC U₀ hU)).X))
    (d : Monodromy.DegreeDatum
      (SectionWeilGroup D C₀ hC (x ≫ sectionOpenMap D C₀ hC U₀ hU)))
    (hd : d.deg = sectionDegree D C₀ hC (x ≫ sectionOpenMap D C₀ hC U₀ hU))
    (E : EtaleWeilDegreeData (sectionCurveFrobenius D C₀ hC) (x ≫ sectionOpenMap D C₀ hC U₀ hU) _ d)
    (hgeom : ∀ g : Aut (FiniteEtale.fiber (x ≫ sectionOpenMap D C₀ hC U₀ hU)),
      (E.geom g).val.val.1 = FiniteEtale.fiberAutBaseChange (sectionProjection D C₀ hC)
        (x ≫ sectionOpenMap D C₀ hC U₀ hU) g)
    (hpath : FiniteEtale.pullbackPathIso (sectionProjection D C₀ hC) E.path ≪≫
      eqToIso (congrArg FiniteEtale.fiber
        (sectionFrobeniusProjection D C₀ hC (x ≫ sectionOpenMap D C₀ hC U₀ hU))) =
          d.degreeOneElement.val.1) :
    ∃ e : ordinarySections D.l (sectionRestrictionObject D C₀ hC U₀ hU S L) ≃+
      Representation.invariants
        (((sectionRepresentation D C₀ hC S L θ (x ≫ sectionOpenMap D C₀ hC U₀ hU) d E).comp
          (sectionRestriction D C₀ hC U₀ hU x)).comp
            (sectionDegree D U₀.toScheme (openSectionCurve D C₀ hC U₀ hU) x).ker.subtype),
      (∀ b, (e b).val = sectionGenericGerm D C₀ hC U₀ hU S L x b) ∧
      (∀ (c : Coeff.{u} D.l) b,
        (e (ordinarySectionScalar D.l (sectionRestrictionObject D C₀ hC U₀ hU S L) c b)).val =
          c • (e b).val) ∧
      (∀ b, (e (ordinarySectionFrobenius D C₀ hC U₀ hU S L θ b)).val =
        sectionRepresentation D C₀ hC S L θ (x ≫ sectionOpenMap D C₀ hC U₀ hU) d E
          d.degreeOneElement (e b).val) ∧
      (∀ (γU : SectionWeilGroup D U₀.toScheme (openSectionCurve D C₀ hC U₀ hU) x),
        sectionDegree D U₀.toScheme (openSectionCurve D C₀ hC U₀ hU) x γU =
          Multiplicative.ofAdd 1 → ∀ b,
          sectionRepresentation D C₀ hC S L θ (x ≫ sectionOpenMap D C₀ hC U₀ hU) d E
            (sectionRestriction D C₀ hC U₀ hU x γU) (e b).val =
          sectionRepresentation D C₀ hC S L θ (x ≫ sectionOpenMap D C₀ hC U₀ hU) d E
            d.degreeOneElement (e b).val) := by
  have h₁ := realSections_germ_scalar (D := D) (C₀ := C₀) (hC := hC) (U₀ := U₀)
    (hU := hU) (S := S) (hS := hS) (L := L) (θ := θ) (x := x) (hx := hx)
    (d := d) (hd := hd) (E := E) (hgeom := hgeom) (hpath := hpath)
  obtain ⟨e, he, hs⟩ := h₁
  have h₂ := realSections_frobenius (D := D) (C₀ := C₀) (hC := hC) (U₀ := U₀)
    (hU := hU) (S := S) (hS := hS) (L := L) (θ := θ) (x := x) (hx := hx)
    (d := d) (hd := hd) (E := E) (hgeom := hgeom) (hpath := hpath)
    (e := e) (he := he) (hs := hs)
  obtain ⟨hf, hdeg⟩ := h₂
  exact ⟨e, he, hs, hf, hdeg⟩

end RealSheaves

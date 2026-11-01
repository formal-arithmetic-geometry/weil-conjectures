/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExactOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
public import WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseInverseImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedLisseEvaluationModel
public import WeilConjectures.CategoryTheory.ZetaWeil.SectionRingGlobalSections
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.WeilObject.Sheaf.Stalk
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeMate
public import WeilConjectures.Compactification.Refinement

/-! # Semilinear transport of ordinary condensed cohomology

Source: the first isomorphisms in the ordinary and compact-support composites of
`def-weil-global-geometric-frobenius` in blueprint latest.
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport)

All categories below are ordinary unbounded derived categories of internal module
objects. Scalar sections mean actual terminal sections with restriction to Λ(*).
Compactification comparisons are specified by their proper-refinement normalization;
fixed-compactification exchange is specified by its open-adjunction mate. These
normalizations determine the maps, rather than merely asking for some isomorphisms.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

-- Avoid the imported max-universe site-size instance leaving a universe metavariable.
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [local instance 10000] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Published derived tensor inverse image, retaining its canonical coefficient map.
Source: blueprint, module-derived push/pull.
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport) -/
abbrev L {T U : Scheme.{u}} (f : T ⟶ U) := moduleObjectDerivedPullback Λ f

/-- The actual scalar map Λ(*) → Γ(T,Λ_T), induced by the strong monoidal p_T^*.
Source: blueprint, pullback from the point and scalar sections.
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport) -/
def scalarMap (T : Scheme.{u}) : condensedScalarRing Λ →+*
    Evaluation.A.{u} (Scheme.ProEt.topology T) (condensedRingObj Λ T) (ProEt.mk (𝟙 T)) := by
  letI : PreservesFiniteLimits (upperStarFromPoint T) := by
    unfold upperStarFromPoint pointUpperStar
    infer_instance
  letI := Functor.additive_of_preserves_binary_products (upperStarFromPoint T)
  exact (InternalAbelianSheafModule.sectionGlobalEval.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
      (condensedRingObj Λ T) (ProEt.mk (𝟙 T))).comp
    ((MonObj.Γ.mapFunctor (upperStarFromPoint T)).comp
      (InternalAbelianSheafModule.sectionGlobalEquiv.{u + 1, u + 1, u}
        (coherentTopology Profinite.{u})
        Λ (⊤_ Profinite.{u}) terminalIsTerminal).symm.toRingHom)

/-- Terminal module sections, followed by the specified restriction of scalars.
Source: blueprint, definition of Γ_s in this lemma.
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport) -/
def sections (T : Scheme.{u}) :
    Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T) ⥤
      ModuleCat.{u + 1} (condensedScalarRing Λ) :=
  Evaluation.sections.{u} (Scheme.ProEt.topology T) (condensedRingObj Λ T) (ProEt.mk (𝟙 T)) ⋙
    ModuleCat.restrictScalars (scalarMap Λ T)

/-- Derived scalar sections; on an algebraically closed point these are canonically
termwise sections, as asserted by the exactness clause of the theorem below.
Source: blueprint, exact point sections.
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport) -/
abbrev Γ (T : Scheme.{u}) := (sections Λ T).rightDerivedFunctor

/-- The unit/compositor/counit pullback comparison of a commutative square.
Source: the displayed adjoint defining e_* in the node.
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport) -/
def square {T' T U' U : Scheme.{u}} (h : T' ⟶ T) (a' : T' ⟶ U')
    (a : T ⟶ U) (b : U' ⟶ U) (w : h ≫ a = a' ≫ b) :
    L Λ b ⋙ L Λ a' ≅ L Λ a ⋙ L Λ h :=
  (leftDerivedUpperStarComp Λ a' b).symm ≪≫
    eqToIso (congrArg (fun f : T' ⟶ U ↦ L Λ f) w.symm) ≪≫
    leftDerivedUpperStarComp Λ h a

/-- A semilinear isomorphism square with precisely the geometric hypotheses of the node.
The isomorphisms are in schemes, not in Over k.
Source: blueprint, the hypotheses of condensed cohomology transport.
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport) -/
structure Geometry (k : Type u) [Field k] where
  X : Scheme.{u}
  X' : Scheme.{u}
  a : X ⟶ Spec (.of k)
  a' : X' ⟶ Spec (.of k)
  b : Spec (.of k) ≅ Spec (.of k)
  h : X' ≅ X
  comm : h.hom ≫ a = a' ≫ b.hom
  separated : IsSeparated a
  finiteType : LocallyOfFiniteType a
  quasiCompact : QuasiCompact a
  separated' : IsSeparated a'
  finiteType' : LocallyOfFiniteType a'
  quasiCompact' : QuasiCompact a'

attribute [instance] Geometry.separated Geometry.finiteType Geometry.quasiCompact
  Geometry.separated' Geometry.finiteType' Geometry.quasiCompact'

/-- Reverse the two scheme isomorphisms, with their actual inverse square.
Source: blueprint, inverse-pair compatibility.
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport) -/
def Geometry.symm {k : Type u} [Field k] (q : Geometry k) : Geometry k where
  X := q.X'
  X' := q.X
  a := q.a'
  a' := q.a
  b := q.b.symm
  h := q.h.symm
  comm := by
    apply (cancel_epi q.h.hom).1
    simpa [Category.assoc] using
      (congrArg (fun f : q.X' ⟶ Spec (.of k) ↦ f ≫ q.b.inv) q.comm).symm
  separated := q.separated'
  finiteType := q.finiteType'
  quasiCompact := q.quasiCompact'
  separated' := q.separated
  finiteType' := q.finiteType
  quasiCompact' := q.quasiCompact

set_option maxHeartbeats 0 in
-- This type contains many occurrences of the full published derived-functor interfaces.
/-- The two allowed coefficients, using the finite-subextension-valued condensed
algebraic closure rather than all continuous algebraic-closure-valued maps.
Source: blueprint, condensed E and Ω conventions.
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport) -/
def coefficient (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (closure : Bool) : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  if closure then Profinite.padicAlgClRingObj ℓ else Profinite.continuousMapRingObj E

end AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport

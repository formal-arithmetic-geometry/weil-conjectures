/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StackQuasiCoherentAlgebra
public import WeilConjectures.CategoryTheory.CochainCoefficientUniverseTransport
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Abelian.RightDerived

/-! # Module functors on the big étale site of a fibred groupoid

Source: Stacks Project, Sheaves on Stacks, Tags 06TP, 06TV, 06WE and 075H
(blueprint: def-sfb-stack-big-etale-module-functors).

The total category and regular-function presheaf are the existing ones. Direct image
is the right adjoint to literal precomposition, hence is characterized uniquely by
its adjunction, rather than chosen from an unconstrained existence assertion.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The total-category big étale topology, including all scheme tests and arrows.
Source: Stacks Tag 06TP (blueprint: def-sfb-stack-big-etale-module-functors). -/
abbrev moduliBigEtaleTopology {S : Scheme.{u}} (F : BasedCategory.{v, w} (Over S)) :=
  (Scheme.etalePrecoverage.comap (moduliSchemeForget F)).toGrothendieck

/-- Regular functions satisfy étale descent on the total fibred category.
Source: Stacks Tag 06TV (blueprint: def-sfb-stack-big-etale-module-functors).
Proof: lift a covering and its overlaps cartesianly to the fibred category, apply
étale descent for regular functions on schemes, and transport through ULift. -/
theorem moduliBigEtaleStructure_isSheaf {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F) :
    Presheaf.IsSheaf (moduliBigEtaleTopology F) (moduliStructurePresheaf F) := by
  sorry

/-- The usual regular-function ring sheaf, with the canonical ambient-universe lift.
Source: Stacks Tag 06TV (blueprint: def-sfb-stack-big-etale-module-functors). -/
def moduliBigEtaleRings {S : Scheme.{u}} (F : BasedCategory.{v, w} (Over S))
    (hF : IsFibredInGroupoids F) :
    Sheaf (moduliBigEtaleTopology F) RingCat.{max (u + 1) v w} :=
  (sheafCompose (moduliBigEtaleTopology F)
    (forget₂ CommRingCat.{max (u + 1) v w} RingCat.{max (u + 1) v w})).obj
    ⟨moduliStructurePresheaf F, moduliBigEtaleStructure_isSheaf F hF⟩

/-- All module sheaves, without a cartesian or quasi-coherent condition.
Source: Stacks Tag 06WE (blueprint: def-sfb-stack-big-etale-module-functors). -/
abbrev ModuliBigEtaleModules {S : Scheme.{u}} (F : BasedCategory.{v, w} (Over S))
    (hF : IsFibredInGroupoids F) :=
  ringedSiteModules.{max (u + 1) v w} (moduliBigEtaleRings F hF)

/-- Sheafification exists in the common ambient universe.
Source: Stacks Tag 06WE (blueprint: def-sfb-stack-big-etale-module-functors).
Proof: the total site is small in max (u+1) v w. The two plus constructions take
matching families in this universe and give additive sheafification. -/
@[instance] theorem moduliBigEtale_hasSheafify {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) :
    HasSheafify (moduliBigEtaleTopology F) AddCommGrpCat.{max (u + 1) v w} := by
  sorry

/-- The sheafification equivalences are exactly the locally bijective maps.
Source: Stacks Tag 06WE (blueprint: def-sfb-stack-big-etale-module-functors).
Proof: the plus-construction unit is locally bijective. Local lifts and local
uniqueness show that every locally bijective map sheafifies to an isomorphism;
the converse follows from the units and the same local lifting criterion. -/
@[instance] theorem moduliBigEtale_wEqualsLocallyBijective {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) :
    (moduliBigEtaleTopology F).WEqualsLocallyBijective
      AddCommGrpCat.{max (u + 1) v w} := by
  sorry

/-- The abelian structure is exactly Mathlib's sheaf-of-modules structure.
Source: Stacks Tag 06WE (blueprint: def-sfb-stack-big-etale-module-functors). -/
instance moduliBigEtale_abelian {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F) :
    Abelian (ModuliBigEtaleModules F hF) :=
  letI : HasSheafify (moduliBigEtaleTopology F)
    AddCommGrpCat.{max (u + 1) v w} := moduliBigEtale_hasSheafify F
  letI : (moduliBigEtaleTopology F).WEqualsLocallyBijective
    AddCommGrpCat.{max (u + 1) v w} := moduliBigEtale_wEqualsLocallyBijective F
  inferInstance

/-- Module sheaves on this small ringed site admit injective resolutions.
Source: Stacks Tag 06WE (blueprint: def-sfb-stack-big-etale-module-functors).
Proof: sheafified free modules on representable sections form a small generating
family; filtered colimits are exact by local lifting. Thus the module category is
Grothendieck abelian and has enough injectives. Resolve successive cokernels. -/
@[instance] theorem moduliBigEtale_hasInjectiveResolutions {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F) :
    HasInjectiveResolutions (ModuliBigEtaleModules F hF) := by
  sorry

/-- A functor over schemes preserves the big étale sheaf condition by precomposition.
Source: Stacks Tag 06WE (blueprint: def-sfb-stack-big-etale-module-functors).
Proof: a covering projects to an étale covering; cartesian lifts identify its
matching diagrams with the same scheme covering. Apply the target sheaf condition. -/
theorem moduliBigEtale_continuous {S : Scheme.{u}}
    {D C : BasedCategory.{v, w} (Over S)} (hD : IsFibredInGroupoids D)
    (hC : IsFibredInGroupoids C) (a : BasedFunctor D C) :
    a.toFunctor.IsContinuous (moduliBigEtaleTopology D) (moduliBigEtaleTopology C) := by
  sorry

/-- Precomposition of the structure sheaf along the given based functor.
Source: Stacks Tag 06WE (blueprint: def-sfb-stack-big-etale-module-functors). -/
def moduliBigEtalePrecompositionRings {S : Scheme.{u}}
    {D C : BasedCategory.{v, w} (Over S)} (hD : IsFibredInGroupoids D)
    (hC : IsFibredInGroupoids C) (a : BasedFunctor D C) :
    Sheaf (moduliBigEtaleTopology D) RingCat.{max (u + 1) v w} :=
  letI := moduliBigEtale_continuous hD hC a
  (a.toFunctor.sheafPushforwardContinuous RingCat
    (moduliBigEtaleTopology D) (moduliBigEtaleTopology C)).obj
      (moduliBigEtaleRings C hC)

/-- The structural comparison is induced by the equality of projections to schemes.
Source: Stacks Tag 06WE (blueprint: def-sfb-stack-big-etale-module-functors). -/
def moduliBigEtaleRingIso {S : Scheme.{u}}
    {D C : BasedCategory.{v, w} (Over S)} (hD : IsFibredInGroupoids D)
    (hC : IsFibredInGroupoids C) (a : BasedFunctor D C) :
    moduliBigEtaleRings D hD ≅ moduliBigEtalePrecompositionRings hD hC a :=
  letI := moduliBigEtale_continuous hD hC a
  (fullyFaithfulSheafToPresheaf (moduliBigEtaleTopology D)
    RingCat.{max (u + 1) v w}).preimageIso
    (eqToIso (congrArg (fun B : D.obj ⥤ Scheme.{u} ↦
      B.op ⋙ Scheme.Γ ⋙
        SheafOfModules.CochainUniverseTransport.ringFunctor.{u, max (u + 1) v w, 0} ⋙
          forget₂ CommRingCat RingCat)
      ((congrArg (fun B ↦ B ⋙ Over.forget S) a.w).symm.trans
        (Functor.assoc a.toFunctor C.p (Over.forget S)))))

/-- Literal precomposition, with the canonical equality of the section rings.
Source: Stacks Tag 06WE (blueprint: def-sfb-stack-big-etale-module-functors). -/
def moduliBigEtalePrecomposition {S : Scheme.{u}}
    {D C : BasedCategory.{v, w} (Over S)} (hD : IsFibredInGroupoids D)
    (hC : IsFibredInGroupoids C) (a : BasedFunctor D C) :
    ModuliBigEtaleModules C hC ⥤ ModuliBigEtaleModules D hD :=
  letI := moduliBigEtale_continuous hD hC a
  SheafOfModules.pushforward (moduliBigEtaleRingIso hD hC a).hom

/-- The canonical right adjoint exists; its value is compatible sections on each
2-fibre product with a scheme test, as in Stacks 06WE and 075H.
(blueprint: def-sfb-stack-big-etale-module-functors).
Proof: for a target test z, take compatible sections on D ×_C z. Restriction of a
section family gives restriction along test arrows, and pullback of regular functions
gives the scalar action. Étale descent gives a module sheaf. A map from M to this
sheaf is equivalent, by evaluating on identity tests and restricting, to a map from
the precomposition of M to N. These mutually inverse operations are natural. -/
@[instance] theorem moduliBigEtalePrecomposition_isLeftAdjoint {S : Scheme.{u}}
    {D C : BasedCategory.{v, w} (Over S)} (hD : IsFibredInGroupoids D)
    (hC : IsFibredInGroupoids C) (a : BasedFunctor D C) :
    (moduliBigEtalePrecomposition hD hC a).IsLeftAdjoint := by
  sorry

/-- Direct image, uniquely determined up to natural isomorphism by its adjunction.
Source: Stacks Tags 06WE, 075H (blueprint: def-sfb-stack-big-etale-module-functors). -/
def moduliBigEtaleDirectImage {S : Scheme.{u}}
    {D C : BasedCategory.{v, w} (Over S)} (hD : IsFibredInGroupoids D)
    (hC : IsFibredInGroupoids C) (a : BasedFunctor D C) :
    ModuliBigEtaleModules D hD ⥤ ModuliBigEtaleModules C hC :=
  (moduliBigEtalePrecomposition hD hC a).rightAdjoint

/-- Direct image is additive, since its adjunction preserves finite products.
Source: Stacks Tag 06WE (blueprint: def-sfb-stack-big-etale-module-functors).
Proof: the right adjoint preserves products and the terminal zero object. In an
additive category, addition is defined by the diagonal and codiagonal of a biproduct;
preservation of these diagrams proves additivity. -/
@[instance] theorem moduliBigEtaleDirectImage_additive {S : Scheme.{u}}
    {D C : BasedCategory.{v, w} (Over S)} (hD : IsFibredInGroupoids D)
    (hC : IsFibredInGroupoids C) (a : BasedFunctor D C) :
    (moduliBigEtaleDirectImage hD hC a).Additive := by
  sorry

/-- Higher direct images are computed by injective resolutions in all module sheaves.
Source: Stacks Tag 075H (blueprint: def-sfb-stack-big-etale-module-functors). -/
def moduliBigEtaleHigherImage {S : Scheme.{u}}
    {D C : BasedCategory.{v, w} (Over S)} (hD : IsFibredInGroupoids D)
    (hC : IsFibredInGroupoids C) (a : BasedFunctor D C) (i : ℕ) :
    ModuliBigEtaleModules D hD ⥤ ModuliBigEtaleModules C hC :=
  (moduliBigEtaleDirectImage hD hC a).rightDerived i

/-- A functor over schemes preserves the big étale sheaf condition by precomposition.
Source: Stacks Tag 06WE (blueprint: def-sfb-stack-big-etale-module-functors).
Proof: a covering projects to an étale covering; cartesian lifts identify its
matching diagrams with the same scheme covering. Apply the target sheaf condition. -/
theorem moduliBigEtaleWide_continuous {S : Scheme.{u}}
    {D : BasedCategory.{v, max v w} (Over S)} {C : BasedCategory.{v, w} (Over S)}
    (hD : IsFibredInGroupoids D)
    (hC : IsFibredInGroupoids C) (a : BasedFunctor D C) :
    a.toFunctor.IsContinuous (moduliBigEtaleTopology D) (moduliBigEtaleTopology C) := by
  sorry

/-- Precomposition of the structure sheaf along the given based functor.
Source: Stacks Tag 06WE (blueprint: def-sfb-stack-big-etale-module-functors). -/
def moduliBigEtaleWidePrecompositionRings {S : Scheme.{u}}
    {D : BasedCategory.{v, max v w} (Over S)} {C : BasedCategory.{v, w} (Over S)}
    (hD : IsFibredInGroupoids D)
    (hC : IsFibredInGroupoids C) (a : BasedFunctor D C) :
    Sheaf (moduliBigEtaleTopology D) RingCat.{max (u + 1) v w} :=
  letI := moduliBigEtaleWide_continuous hD hC a
  (a.toFunctor.sheafPushforwardContinuous RingCat
    (moduliBigEtaleTopology D) (moduliBigEtaleTopology C)).obj
      (moduliBigEtaleRings C hC)

/-- The structural comparison is induced by the equality of projections to schemes.
Source: Stacks Tag 06WE (blueprint: def-sfb-stack-big-etale-module-functors). -/
def moduliBigEtaleWideRingIso {S : Scheme.{u}}
    {D : BasedCategory.{v, max v w} (Over S)} {C : BasedCategory.{v, w} (Over S)}
    (hD : IsFibredInGroupoids D)
    (hC : IsFibredInGroupoids C) (a : BasedFunctor D C) :
    moduliBigEtaleRings D hD ≅ moduliBigEtaleWidePrecompositionRings hD hC a :=
  letI := moduliBigEtaleWide_continuous hD hC a
  (fullyFaithfulSheafToPresheaf (moduliBigEtaleTopology D)
    RingCat.{max (u + 1) v w}).preimageIso
    (eqToIso (congrArg (fun B : D.obj ⥤ Scheme.{u} ↦
      B.op ⋙ Scheme.Γ ⋙
        SheafOfModules.CochainUniverseTransport.ringFunctor.{u, max (u + 1) v w, 0} ⋙
          forget₂ CommRingCat RingCat)
      ((congrArg (fun B ↦ B ⋙ Over.forget S) a.w).symm.trans
        (Functor.assoc a.toFunctor C.p (Over.forget S)))))

/-- Literal precomposition, with the canonical equality of the section rings.
Source: Stacks Tag 06WE (blueprint: def-sfb-stack-big-etale-module-functors). -/
def moduliBigEtaleWidePrecomposition {S : Scheme.{u}}
    {D : BasedCategory.{v, max v w} (Over S)} {C : BasedCategory.{v, w} (Over S)}
    (hD : IsFibredInGroupoids D)
    (hC : IsFibredInGroupoids C) (a : BasedFunctor D C) :
    ModuliBigEtaleModules C hC ⥤ ModuliBigEtaleModules D hD :=
  letI := moduliBigEtaleWide_continuous hD hC a
  SheafOfModules.pushforward (moduliBigEtaleWideRingIso hD hC a).hom

/-- The canonical right adjoint exists; its value is compatible sections on each
2-fibre product with a scheme test, as in Stacks 06WE and 075H.
(blueprint: def-sfb-stack-big-etale-module-functors).
Proof: for a target test z, take compatible sections on D ×_C z. Restriction of a
section family gives restriction along test arrows, and pullback of regular functions
gives the scalar action. Étale descent gives a module sheaf. A map from M to this
sheaf is equivalent, by evaluating on identity tests and restricting, to a map from
the precomposition of M to N. These mutually inverse operations are natural. -/
@[instance] theorem moduliBigEtaleWidePrecomposition_isLeftAdjoint {S : Scheme.{u}}
    {D : BasedCategory.{v, max v w} (Over S)} {C : BasedCategory.{v, w} (Over S)}
    (hD : IsFibredInGroupoids D)
    (hC : IsFibredInGroupoids C) (a : BasedFunctor D C) :
    (moduliBigEtaleWidePrecomposition hD hC a).IsLeftAdjoint := by
  sorry

/-- Direct image, uniquely determined up to natural isomorphism by its adjunction.
Source: Stacks Tags 06WE, 075H (blueprint: def-sfb-stack-big-etale-module-functors). -/
def moduliBigEtaleWideDirectImage {S : Scheme.{u}}
    {D : BasedCategory.{v, max v w} (Over S)} {C : BasedCategory.{v, w} (Over S)}
    (hD : IsFibredInGroupoids D)
    (hC : IsFibredInGroupoids C) (a : BasedFunctor D C) :
    ModuliBigEtaleModules D hD ⥤ ModuliBigEtaleModules C hC :=
  (moduliBigEtaleWidePrecomposition hD hC a).rightAdjoint

/-- Direct image is additive, since its adjunction preserves finite products.
Source: Stacks Tag 06WE (blueprint: def-sfb-stack-big-etale-module-functors).
Proof: the right adjoint preserves products and the terminal zero object. In an
additive category, addition is defined by the diagonal and codiagonal of a biproduct;
preservation of these diagrams proves additivity. -/
@[instance] theorem moduliBigEtaleWideDirectImage_additive {S : Scheme.{u}}
    {D : BasedCategory.{v, max v w} (Over S)} {C : BasedCategory.{v, w} (Over S)}
    (hD : IsFibredInGroupoids D)
    (hC : IsFibredInGroupoids C) (a : BasedFunctor D C) :
    (moduliBigEtaleWideDirectImage hD hC a).Additive := by
  sorry

/-- Higher direct images are computed by injective resolutions in all module sheaves.
Source: Stacks Tag 075H (blueprint: def-sfb-stack-big-etale-module-functors). -/
def moduliBigEtaleWideHigherImage {S : Scheme.{u}}
    {D : BasedCategory.{v, max v w} (Over S)} {C : BasedCategory.{v, w} (Over S)}
    (hD : IsFibredInGroupoids D)
    (hC : IsFibredInGroupoids C) (a : BasedFunctor D C) (i : ℕ) :
    ModuliBigEtaleModules D hD ⥤ ModuliBigEtaleModules C hC :=
  (moduliBigEtaleWideDirectImage hD hC a).rightDerived i

end CategoryTheory

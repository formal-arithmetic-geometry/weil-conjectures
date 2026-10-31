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

/-! # Module functors on the big fppf site of a fibred groupoid

Source: Stacks Project, Sheaves on Stacks, Tags 06TP, 06TV, 06WE and 075G
(blueprint: def-sfb-stack-fppf-module-functors).

The total category and regular-function presheaf are the existing ones. Direct image
is the right adjoint to literal precomposition, hence is characterized uniquely by
its adjunction, rather than chosen from an unconstrained existence assertion.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- All module sheaves, without a cartesian or quasi-coherent condition.
Source: Stacks Tag 06WE (blueprint: def-sfb-stack-fppf-module-functors). -/
abbrev ModuliFppfModules {S : Scheme.{u}} (F : BasedCategory.{v, w} (Over S))
    (hF : IsFibredInGroupoids F) :=
  ringedSiteModules.{max (u + 1) v w} (moduliModuleRings F hF)

/-- Sheafification exists in the common ambient universe.
Source: Stacks Tag 06WE (blueprint: def-sfb-stack-fppf-module-functors).
Proof: the total site is small in max (u+1) v w. The two plus constructions take
matching families in this universe and give additive sheafification. -/
@[instance] theorem moduliFppf_hasSheafify {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) :
    HasSheafify (moduliFppfTopology F) AddCommGrpCat.{max (u + 1) v w} := by
  sorry

/-- The sheafification equivalences are exactly the locally bijective maps.
Source: Stacks Tag 06WE (blueprint: def-sfb-stack-fppf-module-functors).
Proof: the plus-construction unit is locally bijective. Local lifts and local
uniqueness show that every locally bijective map sheafifies to an isomorphism;
the converse follows from the units and the same local lifting criterion. -/
@[instance] theorem moduliFppf_wEqualsLocallyBijective {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) :
    (moduliFppfTopology F).WEqualsLocallyBijective
      AddCommGrpCat.{max (u + 1) v w} := by
  sorry

/-- The abelian structure is exactly Mathlib's sheaf-of-modules structure.
Source: Stacks Tag 06WE (blueprint: def-sfb-stack-fppf-module-functors). -/
instance moduliFppf_abelian {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F) :
    Abelian (ModuliFppfModules F hF) :=
  letI : HasSheafify (moduliFppfTopology F)
    AddCommGrpCat.{max (u + 1) v w} := moduliFppf_hasSheafify F
  letI : (moduliFppfTopology F).WEqualsLocallyBijective
    AddCommGrpCat.{max (u + 1) v w} := moduliFppf_wEqualsLocallyBijective F
  inferInstance

/-- Module sheaves on this small ringed site admit injective resolutions.
Source: Stacks Tag 06WE (blueprint: def-sfb-stack-fppf-module-functors).
Proof: sheafified free modules on representable sections form a small generating
family; filtered colimits are exact by local lifting. Thus the module category is
Grothendieck abelian and has enough injectives. Resolve successive cokernels. -/
@[instance] theorem moduliFppf_hasInjectiveResolutions {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F) :
    HasInjectiveResolutions (ModuliFppfModules F hF) := by
  sorry

/-- A functor over schemes preserves the big fppf sheaf condition by precomposition.
Source: Stacks Tag 06WE (blueprint: def-sfb-stack-fppf-module-functors).
Proof: a covering projects to an fppf covering; cartesian lifts identify its
matching diagrams with the same scheme covering. Apply the target sheaf condition. -/
theorem moduliFppf_continuous {S : Scheme.{u}}
    {D C : BasedCategory.{v, w} (Over S)} (hD : IsFibredInGroupoids D)
    (hC : IsFibredInGroupoids C) (a : BasedFunctor D C) :
    a.toFunctor.IsContinuous (moduliFppfTopology D) (moduliFppfTopology C) := by
  sorry

/-- Precomposition of the structure sheaf along the given based functor.
Source: Stacks Tag 06WE (blueprint: def-sfb-stack-fppf-module-functors). -/
def moduliFppfPrecompositionRings {S : Scheme.{u}}
    {D C : BasedCategory.{v, w} (Over S)} (hD : IsFibredInGroupoids D)
    (hC : IsFibredInGroupoids C) (a : BasedFunctor D C) :
    Sheaf (moduliFppfTopology D) RingCat.{max (u + 1) v w} :=
  letI := moduliFppf_continuous hD hC a
  (a.toFunctor.sheafPushforwardContinuous RingCat
    (moduliFppfTopology D) (moduliFppfTopology C)).obj
      (moduliModuleRings C hC)

/-- The structural comparison is induced by the equality of projections to schemes.
Source: Stacks Tag 06WE (blueprint: def-sfb-stack-fppf-module-functors). -/
def moduliFppfRingIso {S : Scheme.{u}}
    {D C : BasedCategory.{v, w} (Over S)} (hD : IsFibredInGroupoids D)
    (hC : IsFibredInGroupoids C) (a : BasedFunctor D C) :
    moduliModuleRings D hD ≅ moduliFppfPrecompositionRings hD hC a :=
  letI := moduliFppf_continuous hD hC a
  (fullyFaithfulSheafToPresheaf (moduliFppfTopology D)
    RingCat.{max (u + 1) v w}).preimageIso
    (eqToIso (congrArg (fun B : D.obj ⥤ Scheme.{u} ↦
      B.op ⋙ Scheme.Γ ⋙
        SheafOfModules.CochainUniverseTransport.ringFunctor.{u, max (u + 1) v w, 0} ⋙
          forget₂ CommRingCat RingCat)
      ((congrArg (fun B ↦ B ⋙ Over.forget S) a.w).symm.trans
        (Functor.assoc a.toFunctor C.p (Over.forget S)))))

/-- Literal precomposition, with the canonical equality of the section rings.
Source: Stacks Tag 06WE (blueprint: def-sfb-stack-fppf-module-functors). -/
def moduliFppfPrecomposition {S : Scheme.{u}}
    {D C : BasedCategory.{v, w} (Over S)} (hD : IsFibredInGroupoids D)
    (hC : IsFibredInGroupoids C) (a : BasedFunctor D C) :
    ModuliFppfModules C hC ⥤ ModuliFppfModules D hD :=
  letI := moduliFppf_continuous hD hC a
  SheafOfModules.pushforward (moduliFppfRingIso hD hC a).hom

/-- The canonical right adjoint exists; its value is compatible sections on each
2-fibre product with a scheme test, as in Stacks 06WE and 075G.
(blueprint: def-sfb-stack-fppf-module-functors).
Proof: for a target test z, take compatible sections on D ×_C z. Restriction of a
section family gives restriction along test arrows, and pullback of regular functions
gives the scalar action. Fppf descent gives a module sheaf. A map from M to this
sheaf is equivalent, by evaluating on identity tests and restricting, to a map from
the precomposition of M to N. These mutually inverse operations are natural. -/
@[instance] theorem moduliFppfPrecomposition_isLeftAdjoint {S : Scheme.{u}}
    {D C : BasedCategory.{v, w} (Over S)} (hD : IsFibredInGroupoids D)
    (hC : IsFibredInGroupoids C) (a : BasedFunctor D C) :
    (moduliFppfPrecomposition hD hC a).IsLeftAdjoint := by
  sorry

/-- Direct image, uniquely determined up to natural isomorphism by its adjunction.
Source: Stacks Tags 06WE, 075G (blueprint: def-sfb-stack-fppf-module-functors). -/
def moduliFppfDirectImage {S : Scheme.{u}}
    {D C : BasedCategory.{v, w} (Over S)} (hD : IsFibredInGroupoids D)
    (hC : IsFibredInGroupoids C) (a : BasedFunctor D C) :
    ModuliFppfModules D hD ⥤ ModuliFppfModules C hC :=
  (moduliFppfPrecomposition hD hC a).rightAdjoint

/-- Direct image is additive, since its adjunction preserves finite products.
Source: Stacks Tag 06WE (blueprint: def-sfb-stack-fppf-module-functors).
Proof: the right adjoint preserves products and the terminal zero object. In an
additive category, addition is defined by the diagonal and codiagonal of a biproduct;
preservation of these diagrams proves additivity. -/
@[instance] theorem moduliFppfDirectImage_additive {S : Scheme.{u}}
    {D C : BasedCategory.{v, w} (Over S)} (hD : IsFibredInGroupoids D)
    (hC : IsFibredInGroupoids C) (a : BasedFunctor D C) :
    (moduliFppfDirectImage hD hC a).Additive := by
  sorry

/-- Higher direct images are computed by injective resolutions in all module sheaves.
Source: Stacks Tag 075G (blueprint: def-sfb-stack-fppf-module-functors). -/
def moduliFppfHigherImage {S : Scheme.{u}}
    {D C : BasedCategory.{v, w} (Over S)} (hD : IsFibredInGroupoids D)
    (hC : IsFibredInGroupoids C) (a : BasedFunctor D C) (i : ℕ) :
    ModuliFppfModules D hD ⥤ ModuliFppfModules C hC :=
  (moduliFppfDirectImage hD hC a).rightDerived i

end CategoryTheory

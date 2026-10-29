/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralConstantModelRealization
public import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksData

/-! # Exact conservative transport of integral complexes to the constant small site

Source: integral-models proof (1), Stacks Tags 00YV and 099I.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.InternalCompletionTransport

open IntegralModelsStacks

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- The constant coefficient on the large pro-etale site.
Source: integral-models proof (1)
(auxiliary; not a blueprint node). -/
abbrev constantRing := condensedRingObj
  (discreteObj (Padic.coefficientExtensionIntegers l E)) X

/-- The constant section ring on the equivalent small site.
Source: integral-models proof (1)
(auxiliary; not a blueprint node). -/
abbrev ring := smallRing X (constantRing l E X)

/-- First residue map on the small site.
Source: integral-models proof (1)
(auxiliary; not a blueprint node). -/
abbrev residue := smallMap X (residueMap l E X)

/-- Derived restriction to constant coefficients, followed by the exact section equivalence.
Every functor is the prescribed restriction, rather than a chosen equivalence.
Source: integral-models proof (1)
(auxiliary; not a blueprint node). -/
def functor : DerivedCategory (AdicCompletion.Modules l E X) ⥤
    ConstantCompletion.D (ring l E X) :=
  let := HasDerivedCategory.standard (ConstantCompletion.Mod (ring l E X))
  (Mod.comap (coefficientMap
    (IntegralConstantModel.pointComparison l E).inv.hom X)).mapDerivedCategory ⋙
    restriction l E X ⋙ (smallModules X (constantRing l E X)).mapDerivedCategory

/-- Comparison with the representative-based smallDerivedObject in the target.
Proof: the exact functor localization comparison evaluated at objPreimage, followed
by its image of objObjPreimageIso. Source: Stacks Tag 05RU
(auxiliary; not a blueprint node). -/
def objectIso (K : DerivedCategory (AdicCompletion.Modules l E X)) :
    (functor l E X).obj K ≅ smallDerivedObject X _
      ((restriction l E X).obj
        ((Mod.comap (coefficientMap
          (IntegralConstantModel.pointComparison l E).inv.hom X)).mapDerivedCategory.obj K)) := by
  let := HasDerivedCategory.standard (ConstantCompletion.Mod (ring l E X))
  let L := (restriction l E X).obj
    ((Mod.comap (coefficientMap
      (IntegralConstantModel.pointComparison l E).inv.hom X)).mapDerivedCategory.obj K)
  let F := smallModules X (constantRing l E X)
  exact F.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso L).symm ≪≫
    F.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage L)

/-- Completeness is invariant under isomorphism.
Source: Stacks Tag 0999. Proof: derived restriction and derived internal Hom
carry an isomorphism to an isomorphism, preserving zero objects on every slice.
(auxiliary; not a blueprint node). -/
theorem complete_iso {K L : ConstantCompletion.D (ring l E X)} (e : K ≅ L) :
    ConstantCompletion.IsComplete (residue l E X) K ↔
      ConstantCompletion.IsComplete (residue l E X) L := by
  let := HasDerivedCategory.standard (ConstantCompletion.Mod (ring l E X))
  let (U : Scheme.coefficientProEtaleSiteModel.{u, u} X) :=
    HasDerivedCategory.standard (ConstantCompletion.Mod ((ring l E X).over U))
  have h {K L : ConstantCompletion.D (ring l E X)} (e : K ≅ L)
      (hK : ConstantCompletion.IsComplete (residue l E X) K) :
      ConstantCompletion.IsComplete (residue l E X) L := by
    intro U f hf
    let H := (Functor.curry.obj (derivedInternalHom _ ((ring l E X).over U))).obj
      (op ((DerivedCategory.singleFunctor _ 0).obj
        (ringedSectionLocalization ((ring l E X).over U)
          (ringedSliceSection (ring l E X) U f))))
    exact (((ringedDerivedRestriction (ring l E X) U ⋙ H).mapIso e).isZero_iff).mp
      (hK U f hf)
  exact ⟨h e, h e.symm⟩

end AlgebraicGeometry.ProEtale.InternalCompletionTransport

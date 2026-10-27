/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Sheaf.Paper.EmbeddedFiniteCoefficientRealization
public import Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.Paper.EmbeddedFiniteHeartMonoidalPresentation
import Sheaf.Paper.EmbeddedFiniteHeartConstructibility
import Sheaf.Paper.ProEtaleConstantModuleConstructibility

/-! # Heart comparison for embedded finite-field coefficients

Source: integral-models proof, first paragraph; Stacks Tags 03ET, 00YV and 06YQ.
(blueprint: lem-sfb-embedded-finite-field-presentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SixFunctors
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralModelsEmbedded

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar

set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] integralModel_coefficientMonObj in
/-- The embedded finite-field presentation and the intrinsic presentation have a common
coefficient-sized section-module encoding. The embedded encoding is strong monoidal;
the specified derived realization is the induced functor under these encodings.

Source: integral-models proof, first paragraph, clauses (1) and (2); Stacks Tags
099L, 03ET, 00YV, 06YQ and 09AL
(blueprint: lem-sfb-embedded-finite-field-presentation).

Proof: identify the constant-function scalar map with the sheafification of the
constant presheaf map. Its finite clopen fibre cover proves local surjectivity, and
separatedness proves local injectivity. Consequently this specified map and its
inverse image are ring isomorphisms. Extension along it is inverse scalar restriction.
Reconstruct sectionwise module actions, restrict to constant scalar sections, and
use the intrinsic associated-module-sheaf equivalence. Reindex along AsSmall.down;
the constant-sheaf comparison identifies its coefficient ring with the constant
lifted field on the coefficient-sized site. This constructs both equivalences.
Sectionwise balanced pure tensors give the strong monoidal structure on the first;
the unit and tensor coherence follow from the same pure-tensor equations. Each
factor is additive and exact. Uniqueness of derived functors identifies the given
left-derived scalar extension and right-derived intrinsic realization with the
termwise induced functor, yielding the displayed natural isomorphism.
For constructibility retain each finite constructible stratum and each local
trivializing cover. The functors preserve the finite scalar matrices and their
cokernels, so finite constant scalar models correspond to finite locally constant
module sheaves. Conversely every such finite module over the finite field is
finitely presented and gives the same matrix model. Geometric stalk finiteness
is exactly finiteness of that module. These identifications commute with the
stratum inverse images and preserve isomorphisms, proving the final equivalence.
The empty scheme uses a one-piece empty stratification and rank-zero models. -/
theorem finiteFieldPresentation
    (X : Scheme.{u}) [IsNoetherian X] (A : Type) [Field A]
    [TopologicalSpace A] [IsTopologicalRing A] [Finite A] [DiscreteTopology A] :
    letI : HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
      CategoryTheory.siteAbelianHasSheafify.{u + 1, u, u + 1} _
    letI : (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
      CategoryTheory.siteAbelianWEqualsLocallyBijective.{u + 1, u, u + 1} _
    let R := ConstantCompletion.constant
      (Scheme.coefficientProEtaleModelTopology.{u, u} X) (ULift.{u + 1, 0} A)
    letI := SheafOfModules.monoidalCategory R
    letI : HasDerivedCategory (ConstantCompletion.Mod R) := HasDerivedCategory.standard _
    letI : HasDerivedCategory (Scheme.proEtaleRingModules X
        (Scheme.proEtaleConstantRing X (ULift.{u, 0} A))) := HasDerivedCategory.standard _
    ∃ E : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (discreteObj A) X) ≌ ConstantCompletion.Mod R,
      ∃ H : Scheme.proEtaleRingModules X
          (Scheme.proEtaleConstantRing X (ULift.{u, 0} A)) ≌ ConstantCompletion.Mod R,
        ∃ (_ : E.functor.Additive) (_ : H.functor.Additive),
          Nonempty E.functor.Monoidal ∧
          Nonempty (finiteRealization X A ⋙ H.functor.mapDerivedCategory ≅
            E.functor.mapDerivedCategory) ∧
          ∀ (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
              (condensedRingObj (discreteObj A) X))
            (N : Scheme.proEtaleRingModules X
              (Scheme.proEtaleConstantRing X (ULift.{u, 0} A))),
            (E.functor.obj M ≅ H.functor.obj N) →
            (IsConstantModelConstructible (discreteObj A) X M ↔
              Scheme.IsConstructibleProEtaleModuleSheaf X (ULift.{u, 0} A) N) := by
  let : HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
    CategoryTheory.siteAbelianHasSheafify.{u + 1, u, u + 1} _
  let : (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    CategoryTheory.siteAbelianWEqualsLocallyBijective.{u + 1, u, u + 1} _
  let R := ConstantCompletion.constant
    (Scheme.coefficientProEtaleModelTopology.{u, u} X) (ULift.{u + 1, 0} A)
  let := SheafOfModules.monoidalCategory R
  let : HasDerivedCategory (ConstantCompletion.Mod R) := HasDerivedCategory.standard _
  let : HasDerivedCategory (Scheme.proEtaleRingModules X
      (Scheme.proEtaleConstantRing X (ULift.{u, 0} A))) := HasDerivedCategory.standard _
  obtain ⟨hI, H, hH, hm⟩ := finiteHeartMonoidalPresentation X A
  let := hI
  let := hH
  let S := Mod.extendScalars (C := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (finiteScalarMap X A)
  let I := integralModelIntrinsicRealization X A
  have : S.IsEquivalence := finiteScalarExtension_isEquivalence X A
  have : I.IsEquivalence := hI
  let F := S ⋙ I
  have : F.IsEquivalence := inferInstance
  let E := F.asEquivalence.trans H
  have : E.functor.Additive := inferInstanceAs (F ⋙ H.functor).Additive
  refine ⟨E, H, inferInstance, hH, hm, ?_, ?_⟩
  · change Nonempty ((S.leftDerivedFunctor ⋙ I.rightDerivedFunctor) ⋙
      H.functor.mapDerivedCategory ≅ (F ⋙ H.functor).mapDerivedCategory)
    exact ⟨Functor.isoWhiskerRight
        (Functor.isoWhiskerRight S.leftDerivedFunctorIsoMapDerivedCategory
            I.rightDerivedFunctor ≪≫
          Functor.isoWhiskerLeft S.mapDerivedCategory I.rightDerivedFunctorIsoMapDerivedCategory)
        H.functor.mapDerivedCategory ≪≫
      Functor.isoWhiskerRight (Functor.mapDerivedCategoryCompIso S I).symm
        H.functor.mapDerivedCategory ≪≫
      (Functor.mapDerivedCategoryCompIso F H.functor).symm⟩
  · intro M N e
    have j : F.obj M ≅ N := H.functor.preimageIso e
    refine (finiteHeartConstructibility X A M).trans ?_
    rw [Scheme.proEtaleModuleRestriction_constructible_iff,
      Scheme.proEtaleModuleRestriction_constructible_iff]
    let k := (Scheme.proEtaleModuleRestriction X (ULift.{u, 0} A)).mapIso j
    exact ⟨fun h ↦ isConstructible_of_iso k h,
      fun h ↦ isConstructible_of_iso k.symm h⟩

end AlgebraicGeometry.ProEtale.IntegralModelsEmbedded

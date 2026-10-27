/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q66
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.CompactSupportRealizationCoordinates
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.Compactification.RefinementCategory
public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import Sheaf.Paper.CompactSupportReductionTower
public import Sheaf.Paper.IntegralCompactSupportUniformRestriction
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Paper.RingedCoefficientProjectionCocycle
public import Sheaf.SixFunctors.OpenTensorNormalization
public import Sheaf.Paper.CondensedERealization
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import Sheaf.Paper.CondensedFlatCoefficientCalculus
public import Sheaf.SixFunctors.IntegralSystemOperations
public import Sheaf.SixFunctors.IntegralSystemCanonicalBridge
public import Sheaf.Paper.CondensedCompactSupportProjection
public import Sheaf.SixFunctors.IntegralCompactificationSystemRealization
public import Sheaf.SixFunctors.IntegralCompactificationComparisonBridge
public import Sheaf.Paper.CompactSupportCondensedRealization
public import Sheaf.Paper.CompletedCoefficientPresentationTransport
public import Sheaf.Paper.SfCbcExtensionZeroCompletion
public import Sheaf.Paper.SfCbcCompactSupportCompositionLimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek
public import Sheaf.SixFunctors.GeneratorReductionStatement
import Sheaf.Paper.CompactSupportRealizationIdentity

/-!
# Factor normalization of compact-support realization

Source: Bhatt--Scholze, Definition 6.7.6, Lemma 6.7.14, Proposition 6.8.14(2)
and Remark 6.8.15 (context); the agent-formulated normalization of the parent
compact-support comparison, construction Steps 2--5, 6 and 13.
(blueprint: lem-zl-compact-support-realization-factor-normalization).

The maps are constructed on whole derived systems. The proper factors are counit
mates and the open factors are unit mates. The statements retain the specified
reconstruction unit, complete-category coordinates and actual internal modules.

## Main statements

- `integralComparison_normalization`, `single_realization`, `structural_conjugacy`.
- `realization_factor_normalization`, `coefficient_factorization`.
- `coefficient_proper_transpose`, `coefficient_proper_isIso`.
- `realization_identity_open`, `coefficient_identity_open`, `factorization_naturality`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] HasDerivedCategory.ofHasKInjectiveResolutions
  _root_.instCategoryDerivedCategory
  CategoryTheory.Functor.leftDerivedFunctorIsoMapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctorIsoMapDerivedCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint
attribute [local irreducible] HasDerivedCategory.standard
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Mod.monoidalCategory
  CategoryTheory.Sheaf.monoidalCategory
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open WeilConjectures
open scoped CategoryTheory.Obj
attribute [instance] CondensedERealization.At.encodingAdditive
  CondensedERealization.At.encodingInverseAdditive

namespace WeilConjectures.CompactSupportFactorNormalization
open IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The realized inverse q, followed in order by the actual proper and open factors.
Source: the first displayed factorization, proof Step 5
(blueprint: lem-zl-compact-support-realization-factor-normalization). -/
def factorization (o : Operations l E) (m : RealizationModel l E o)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (AX : CondensedERealization.At l E X) (AZ : CondensedERealization.At l E c.Z)
    (AY : CondensedERealization.At l E Y) (K : Integral l E X) :=
  (realize l E Y AY).map (integralInverse l E o m c K) ≫
    (properRealization l E c.g AZ AY).app ((ringedOpen l E c.i).obj K) ≫
      (CondensedRing.lowerStar
        (Profinite.continuousCoefficientRingObj E) c.g).rightDerivedFunctor.map
          (openRealization l E c.i AX AZ K)



set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The parent's actual strict-tower limit in the simultaneous-system coordinates.
Source: proof Steps 2 and 5
(blueprint: lem-zl-compact-support-realization-factor-normalization). -/
def parentCoordinates (o : Operations l E) (b : CanonicalBridge l E o)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : CompactSupportCondensedRealization.IntegralModel l E c (calculus l E))
    (K : CondensedERealization.Integral l E X) :=
  (CompactSupportCondensedRealization.limitPresentation l E c (calculus l E) M).hom.app K ≫
    (coefficientSequenceLimit l E Y).map
      ((systemPresentation l E o b c).inv.app
        ((calculus l E X).reduction.obj ((purCoefficientModel l E X).functor.obj K.obj)))

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The first displayed factorization, in the parent's coefficient coordinates.
The lattice comparisons are the fixed scalar-extension normalization of J.
Source: proof Step 5 (blueprint: lem-zl-compact-support-realization-factor-normalization). -/
def parentFactorization (o : Operations l E) (m : RealizationModel l E o)
    (b : CanonicalBridge l E o) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : CompactSupportCondensedRealization.IntegralModel l E c (calculus l E))
    (AX : CondensedERealization.At l E X) (AZ : CondensedERealization.At l E c.Z)
    (AY : CondensedERealization.At l E Y) (K : CondensedERealization.Integral l E X) :=
  (latticeComparison l E Y AY).inv.app
      ((CompactSupportCondensedRealization.integralSupport l E c (calculus l E) M).obj K) ≫
    (realize l E Y AY).map (parentCoordinates l E o b c M K) ≫
      factorization l E o m c AX AZ AY ((purCoefficientModel l E X).functor.obj K.obj) ≫
        (CondensedRing.rightDerivedLowerShriekOfCompactification
          (Profinite.continuousCoefficientRingObj E) c).map
            ((latticeComparison l E X AX).hom.app K)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Transport the family's own comparison along equality of its reduction calculus.
No comparison is chosen: the realization and all family laws retain the same component.
Source: parent construction Steps 2--5
(blueprint: lem-zl-compact-support-realization-factor-normalization). -/
def normalizedFamilyAt (D₀ : FiniteFieldDatum.{u}) [Fact (l ≠ D₀.p)]
    (C : CompactSupportCondensedRealization.ComparisonFamily l D₀.k)
    (h : (C.coefficient E).reduction = calculus l E)
    (X Y : CondensedERealization.Base D₀.k) (f : X.scheme ⟶ Y.scheme)
    [f.IsOver (Spec (.of D₀.k))] (c : Compactification f) :
    CompactSupportCondensedRealization.RealizationAt l E D₀.k
      (C.coefficient E).realization (calculus l E) X Y f c :=
  h ▸ (C.coefficient E).atCompactification X Y f c

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Factor normalization of the actual components of one simultaneous comparison family.
Its reduction is the fixed calculus, and its realization has the displayed formula
on the common-window domain. Finite scalar, refinement and shift laws are those of C.
Source: parent construction Steps 2--5 and the first displayed equality
(blueprint: lem-zl-compact-support-realization-factor-normalization). -/
def IsFactorNormalized (D₀ : FiniteFieldDatum.{u}) [Fact (l ≠ D₀.p)]
    (C : CompactSupportCondensedRealization.ComparisonFamily l D₀.k) : Prop :=
  ∀ (F : Type u) [NormedField F] [NormedAlgebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F],
    ∃ h : (C.coefficient F).reduction = calculus l F,
      ∀ (o : Operations l F) (m : RealizationModel l F o) (b : CanonicalBridge l F o)
        (X Y : CondensedERealization.Base D₀.k) (f : X.scheme ⟶ Y.scheme)
        [f.IsOver (Spec (.of D₀.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
        (c : Compactification f) [QuasiCompact c.i] (AZ : CondensedERealization.At l F c.Z)
        (K : CondensedERealization.Integral l F X.scheme) (lo hi a z : ℤ),
        Domain l F o c ((purCoefficientModel l F X.scheme).functor.obj K.obj) lo hi a z →
          IsIso (integralComparison l F o m c
            ((purCoefficientModel l F X.scheme).functor.obj K.obj)) ∧
          IsIso ((properRealization l F c.g AZ
            ((C.coefficient F).realization.atObject Y)).app
              ((ringedOpen l F c.i).obj ((purCoefficientModel l F X.scheme).functor.obj K.obj))) ∧
          IsIso ((openRealizationInverse l F c.i
            ((C.coefficient F).realization.atObject X) AZ).app
              ((purCoefficientModel l F X.scheme).functor.obj K.obj)) ∧
          (normalizedFamilyAt l F D₀ C h X Y f c).realization.hom.app
              (ScalarLocalization.mk K) =
            parentFactorization l F o m b c
              (normalizedFamilyAt l F D₀ C h X Y f c).integral
              ((C.coefficient F).realization.atObject X) AZ
              ((C.coefficient F).realization.atObject Y) K

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- A simultaneous comparison family with precisely the factor normalization.
The witnesses for the factorization, coefficient squares, refinements and shifts
are components and laws of this same family.
Source: Bhatt--Scholze 6.7.6, 6.7.14, 6.8.14(2), Remark 6.8.15 (context);
parent construction Steps 2--5
(blueprint: lem-zl-compact-support-realization-factor-normalization).
Proof: choose the parent's reduction to be calculus. Proper coefficient projection,
strict open scalar extension and the reconstruction unit are invertible on the
retained domain. The triangle identity identifies inverse L(b)u with the proper
limit comparison followed by L of the open reduction mate and inverse unit.
Rationalize this map, apply J and paste the specified proper and open mates to
construct each component of a single family. Whole-system generator squares give
its structural laws; coefficient projection cocycles and mate pasting give its finite
scalar, refinement and shift laws. The lattice comparisons identify those very
components with parentFactorization, rather than separate endpoint isomorphisms. -/
theorem realization_factor_normalization (D₀ : FiniteFieldDatum.{u}) [Fact (l ≠ D₀.p)] :
    ∃ C : CompactSupportCondensedRealization.ComparisonFamily l D₀.k,
      IsFactorNormalized l D₀ C := by
  sorry




private theorem pasteScalar_app
    {C D H C' D' H' : Type*}
    [Category C] [Category D] [Category H] [Category C'] [Category D'] [Category H']
    (j : C ⥤ D) (r : D ⥤ H) (j' : C' ⥤ D') (r' : D' ⥤ H')
    (tx : C ⥤ C') (tz : D ⥤ D') (ty : H ⥤ H')
    (p : r ⋙ ty ⟶ tz ⋙ r') (q : j ⋙ tz ⟶ tx ⋙ j') (K : C) :
    (CompactSupportCondensedRealization.pasteScalar j r j' r' tx tz ty p q).app K =
      p.app (j.obj K) ≫ r'.map (q.app K) := by
  simp only [CompactSupportCondensedRealization.pasteScalar, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.id_comp, Category.comp_id]

private theorem pull_push_mate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {EX : A ⥤ B} {RX : B ⥤ A} {EY : C ⥤ D} {RY : D ⥤ C}
    (sx : EX ⊣ RX) (sy : EY ⊣ RY)
    {LA : C ⥤ A} {GA : A ⥤ C} {LB : D ⥤ B} {GB : B ⥤ D}
    (ga : LA ⊣ GA) (gb : LB ⊣ GB) (κ : GB ⋙ RY ≅ RX ⋙ GA) :
    (mateEquiv ga gb (Adjunction.pullIsoOfComapIso sx sy ga gb κ).inv).natTrans =
      Adjunction.pushHomOfComapIso sx sy κ := by
  have h := iterated_mateEquiv_conjugateEquiv_symm ga gb sy sx
    (TwoSquare.mk _ _ _ _ κ.inv)
  exact congrArg TwoSquare.natTrans ((mateEquiv ga gb).eq_symm_apply.mp h.symm)

private theorem pull_push_counit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {EX : A ⥤ B} {RX : B ⥤ A} {EY : C ⥤ D} {RY : D ⥤ C}
    (sx : EX ⊣ RX) (sy : EY ⊣ RY)
    {LA : C ⥤ A} {GA : A ⥤ C} {LB : D ⥤ B} {GB : B ⥤ D}
    (ga : LA ⊣ GA) (gb : LB ⊣ GB) (κ : GB ⋙ RY ≅ RX ⋙ GA) (d : A) :
    LB.map ((Adjunction.pushHomOfComapIso sx sy κ).app d) ≫
        gb.counit.app (EX.obj d) =
      (Adjunction.pullIsoOfComapIso sx sy ga gb κ).inv.app (GA.obj d) ≫
        EX.map (ga.counit.app d) := by
  rw [← pull_push_mate sx sy ga gb κ]
  exact mateEquiv_counit ga gb
    (TwoSquare.mk _ _ _ _ (Adjunction.pullIsoOfComapIso sx sy ga gb κ).inv) d

attribute [local irreducible] CondensedRing.derivedComapLowerStarIso
  CondensedRing.derivedComapUpperStarIso

section CoefficientProjection
open CompactSupportCondensedRealization
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (α : Λ ⟶ Λ') [IsMonHom α] [FlatCoefficientMap α]

/-- The second displayed factorization holds in the actual target internal-module
category, before restriction or taking any point realization.
Source: parent construction Steps 6 and 13; proof Steps 6--8
(blueprint: lem-zl-compact-support-realization-factor-normalization).
Proof: unfold the specified compact-support projection as the proper/open paste.
The proper factor is the counit mate of inverse pullback/scalar balancing, and the
open factor is the scalar/open isomorphism normalized by the actual open unit.
The associators have identity components, giving the displayed ordered composite. -/
theorem coefficient_factorization {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (K : DerivedCategory (CategoryTheory.Mod
      (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (condensedProjection α c).app K =
      (CondensedRing.derivedPushHom α c.g).app
          ((CondensedRing.openImmersionLowerShriek Λ c.i).mapDerivedCategory.obj K) ≫
        (CondensedRing.lowerStar Λ' c.g).rightDerivedFunctor.map
          ((CondensedRing.derivedOpenImmersionShriekIso α c.i).hom.app K) := by
  exact pasteScalar_app _ _ _ _ _ _ _ _ _ K

/-- The proper projection is specified by its target-coefficient counit transpose,
with precisely the canonical pullback/tensor balancing map.
Source: proof Steps 6--7 (blueprint: lem-zl-compact-support-realization-factor-normalization).
Proof: the definition of derivedPushHom is the mate of derivedPullIso inverse.
Apply the counit equation of the mate correspondence. This gives the equation in
the target module category; scalar restriction and finite evaluation are not used. -/
theorem coefficient_proper_transpose {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (L : DerivedCategory (CategoryTheory.Mod
      (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
    (CondensedRing.upperStar Λ' g).leftDerivedFunctor.map
        ((CondensedRing.derivedPushHom α g).app L) ≫
      (CondensedRing.derivedUpperStarLowerStarAdjunction Λ' g).counit.app
        ((condensedScalar α Z).obj L) =
    (CondensedRing.derivedPullIso α g).inv.app
        ((CondensedRing.lowerStar Λ g).rightDerivedFunctor.obj L) ≫
      (condensedScalar α Z).map
        ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ g).counit.app L) := by
  exact pull_push_counit
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap α _))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap α _))
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ g)
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ' g)
    (CondensedRing.derivedComapLowerStarIso α g) L

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The inverse open scalar comparison is exactly the open-unit adjunct.
Source: proof Steps 6 and 8
(blueprint: lem-zl-compact-support-realization-factor-normalization).
Proof: restriction/scalar balancing is canonical identity on underlying sheaves.
Its open-adjunction mate is the inverse scalar/open comparison. The triangle
identities identify its restriction with identity; extension by zero determines it. -/
theorem coefficient_open_unit {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (K : DerivedCategory (CategoryTheory.Mod
      (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (CondensedRing.derivedOpenImmersionShriekIso α j).inv.app K =
      ((fieldOpenAdjunction Λ' j).homEquiv _ _).symm
        ((condensedScalar α X).map ((fieldOpenAdjunction Λ j).unit.app K) ≫
          (CondensedRing.derivedPullIso α j).hom.app
            ((CondensedRing.openImmersionLowerShriek Λ j).mapDerivedCategory.obj K)) := by
  sorry

end CoefficientProjection

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Proper projection is invertible both for a finite coefficient extension and for
extension to the finite-subextension-valued algebraic closure ring.
Source: proof Steps 6--8
(blueprint: lem-zl-compact-support-realization-factor-normalization).
Proof: finite extension is finite free, so direct image commutes with its finite
coordinate sums and the coordinate map equals the counit mate. For the closure,
present the bounded-below constructible input by a bounded-below complex and express
extension as the filtered colimit over finite subextensions. Properness implies
qcqs, so the recorded pushforward continuity theorem identifies that colimit with
the target. Naturality of balancing and the counit identifies this map with the
actual closure-linear mate. This proves invertibility in the internal-module category. -/
theorem coefficient_proper_isIso (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (F : Type u) [NormedField F] [NormedAlgebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (i : E →ₐ[ℚ_[l]] F) (a : E →ₐ[ℚ_[l]] PadicAlgCl l)
    (Z Y : CondensedERealization.Base k) (g : Z.scheme ⟶ Y.scheme)
    [g.IsOver (Spec (.of k))] [IsProper g]
    (L : CondensedERealization.Constructible E Z.scheme) :
    IsIso ((CondensedRing.derivedPushHom
      (CompactSupportCondensedRealization.fieldMap l E F i) g).app L.obj) ∧
    IsIso ((CondensedRing.derivedPushHom
      (CompactSupportCondensedRealization.omegaMap l E a) g).app L.obj) := by
  sorry

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Naturality of q and its inverse on two objects in the common finite window.
Source: proof Step 9 (blueprint: lem-zl-compact-support-realization-factor-normalization).
Proof: the proper and open mates are natural transformations, as is the reconstruction
unit. Apply naturality to their composite, then cancel its invertible components for
the inverse square. Zero objects and the empty scheme use the same equations. -/
theorem integral_naturality (o : Operations l E) (m : RealizationModel l E o)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K K' : Integral l E X) (v : K ⟶ K') (lo hi a b : ℤ)
    (_hK : Domain l E o c K lo hi a b) (_hK' : Domain l E o c K' lo hi a b) :
    (word l E c).map v ≫ integralComparison l E o m c K' =
      integralComparison l E o m c K ≫ (support l E o c).map v ∧
    (support l E o c).map v ≫ integralInverse l E o m c K' =
      integralInverse l E o m c K ≫ (word l E c).map v := by
  sorry



set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The inverse q is the normalized single-compactification comparison of the recorded
expression realization, including its reconstruction unit on the input.
Source: proof Steps 2--4
(blueprint: lem-zl-compact-support-realization-factor-normalization).
Proof: expand the compactSupport, openNormalization and inputNormalization equations
of Realizations. Naturality moves the input reconstruction unit across the open
reduction mate. The triangle identity cancels the intervening system counit. The
result is exactly integralInverse; this identifies the fixed maps before evaluation. -/
theorem single_realization (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (o : Operations l E) (R : Realizations l E D o)
    (U V : Over (Spec (.of D.k))) (f : U ⟶ V) (c : Compactification f.left)
    (ge : (Expression.compactSupport f c
      (Expression.var (X := fun _ : PUnit.{u + 1} ↦ U) PUnit.unit)).geometric)
    (K : Integral l E U.left)
    (hK : (Expression.compactSupport f c
      (Expression.var (X := fun _ : PUnit.{u + 1} ↦ U) PUnit.unit)).domain l E o (fun _ ↦ K)) :
    (R.comparison (.compactSupport f c (.var PUnit.unit)) ge).hom.app
        ⟨(fun _ ↦ K), hK⟩ =
      integralInverse l E o R.realizationModel c K := by
  sorry

set_option linter.unusedVariables false in
/-- All actual proper/open units, counits, interchanges, compositors and their finite
contexts are conjugated by the normalized comparisons. For one compactification,
single_realization identifies the comparison here with q inverse.
Source: proof Steps 3--4
(blueprint: lem-zl-compact-support-realization-factor-normalization).
Proof: generator reduction squares hold in the whole derived-system category.
Apply the derived limit, compose with the normalization counits, and use triangle
identities. The independently defined canonical pair gives the actual ringed map.
Cancel the comparison isomorphism. Closure under composition, inverse isomorphisms
and finite outer contexts gives every displayed structural map, without evaluating. -/
theorem structural_conjugacy (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (o : Operations l E) (R : Realizations l E D o)
    {I : Type u} [Finite I] {X : I → Over (Spec (.of D.k))}
    {W : Over (Spec (.of D.k))} (e t : Expression _ I X W)
    (ge : e.geometric) (gt : t.geometric)
    (K : (e.domain l E o).FullSubcategory) (ht : t.domain l E o K.obj)
    (s : e.systemObj l E o ((inputReduction l E X).obj K.obj) ⟶
      t.systemObj l E o ((inputReduction l E X).obj K.obj))
    (r : (e.evaluate (integralInterpretation l E)).obj K.obj ⟶
      (t.evaluate (integralInterpretation l E)).obj K.obj)
    (_hpair : CanonicalPair l E o R.compositors R.openComparisons R.canonicalBridge
      R.properOpen R.ringedModels R.ringedOpenComparisons R.ringedProperOpen
      ((inputReduction l E X).obj K.obj) K.obj e t s r) :
    (R.comparison e ge).inv.app K ≫ (coefficientSequenceLimit l E W.left).map s ≫
      (R.comparison t gt).hom.app ⟨K.obj, ht⟩ = r := by
  rw [R.coherence e t ge gt K ht s r _hpair]
  simp

/-- The proper identity unitor is fixed on the pullback-identity section coordinates.
Source: proof Step 9 (blueprint: lem-zl-compact-support-realization-factor-normalization).
Proof: direct image along the identity evaluates at V times_W W. Restriction along
the inverse pullback-identity isomorphism identifies its sections with those at V.
Its inverse uses the forward isomorphism. These are linear, natural and inverse;
faithfulness of underlying sections proves uniqueness. -/
theorem ordinaryPushIdentity_existsUnique (W : Scheme.{u}) :
    ∃! e : proEtaleRingModuleDirectImage (𝟙 W)
        ((PurCompactSupport.completed l E).ring W) ((PurCompactSupport.completed l E).ring W)
        ((PurCompactSupport.completed l E).pull (𝟙 W)) ≅ 𝟭 _,
      ∀ (M : proEtaleRingModules W ((PurCompactSupport.completed l E).ring W))
        (V : W.ProEt)
        (x : ((proEtaleRingModuleDirectImage (𝟙 W)
          ((PurCompactSupport.completed l E).ring W) ((PurCompactSupport.completed l E).ring W)
          ((PurCompactSupport.completed l E).pull (𝟙 W))).obj M).val.obj (op V)),
        ((e.hom.app M).val.app (op V)).hom x =
          M.val.map ((MorphismProperty.Over.pullbackId @WeaklyEtale.{u} ⊤ W).inv.app V).op x := by
  refine ⟨CompactSupportRealizationFactorization.ordinaryPushId l E W, ?_, ?_⟩
  · intro M V x
    rfl
  · intro e he
    apply Iso.ext
    ext M V x
    exact (he M V.unop x).trans (by rfl)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The identity pullback unitor is the conjugate of the section-normalized proper unitor.
Source: proof Step 9 (blueprint: lem-zl-compact-support-realization-factor-normalization). -/
def integralPullIdentity (W : Scheme.{u}) : ringedPull l E (𝟙 W) ≅ 𝟭 _ :=
  (conjugateIsoEquiv Adjunction.id (ringedAdj l E (𝟙 W))).symm
    (Functor.rightDerivedFunctorNatIso (ordinaryPushIdentity_existsUnique l E W).exists.choose ≪≫
      (𝟭 _).rightDerivedFunctorIsoMapDerivedCategory ≪≫
      Functor.mapDerivedCategoryIdIso _).symm

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The open identity unitor is fixed by the actual open adjunction.
Source: proof Step 9 (blueprint: lem-zl-compact-support-realization-factor-normalization). -/
def integralOpenIdentity (W : Scheme.{u}) : ringedOpen l E (𝟙 W) ≅ 𝟭 _ :=
  ((ringedOpenAdj l E (𝟙 W)).ofNatIsoRight (integralPullIdentity l E W)).leftAdjointUniq
    Adjunction.id

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The identity open factor of J is identity under the canonical open unitors.
Source: proof Step 9 (blueprint: lem-zl-compact-support-realization-factor-normalization).
Proof: both maps are adjuncts of the same identity open unit under scalar balancing.
The identity-on-sections unitors identify that unit with identity. Uniqueness of
adjuncts proves the equality, including the zero object and the empty scheme. -/
theorem realization_identity_open (W : Scheme.{u}) (A : CondensedERealization.At l E W)
    (K : Integral l E W) :
    openRealization l E (𝟙 W) A A K ≫
        (CondensedRing.derivedOpenImmersionLowerShriekId
          (Profinite.continuousCoefficientRingObj E) W).hom.app ((realize l E W A).obj K) =
      (realize l E W A).map ((integralOpenIdentity l E W).hom.app K) := by
  sorry

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The identity open coefficient factor is identity under the same fixed unitors.
Consequently the scalar compact-support paste for a proper compactification reduces
to its specified proper coefficient projection.
Source: proof Step 9 (blueprint: lem-zl-compact-support-realization-factor-normalization).
Proof: the open scalar isomorphism is the mate of scalar/restriction balancing. For
the identity open its unit is identity under the canonical open unitors, so the mate
is identity under those unitors. Naturality of the proper factor gives the assertion. -/
theorem coefficient_identity_open
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [CategoryTheory.MonObj Λ] [CategoryTheory.IsCommMonObj Λ]
    [CategoryTheory.MonObj Λ'] [CategoryTheory.IsCommMonObj Λ']
    (α : Λ ⟶ Λ') [CategoryTheory.IsMonHom α]
    [CompactSupportCondensedRealization.FlatCoefficientMap α] (W : Scheme.{u})
    (K : DerivedCategory (CategoryTheory.Mod
      (Sheaf (ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W))) :
    (CondensedRing.derivedOpenImmersionShriekIso α (𝟙 W)).hom.app K ≫
        (CondensedRing.derivedOpenImmersionLowerShriekId Λ' W).hom.app
          ((CompactSupportCondensedRealization.condensedScalar α W).obj K) =
      (CompactSupportCondensedRealization.condensedScalar α W).map
        ((CondensedRing.derivedOpenImmersionLowerShriekId Λ W).hom.app K) := by
  sorry



set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Naturality of the rational realization factorization on the common-window domain.
Source: proof Step 9 (blueprint: lem-zl-compact-support-realization-factor-normalization).
Proof: inverse q is natural by integral_naturality. The proper comparison is a mate
natural transformation and the inverse open comparison is natural on this domain
because its components are invertible. Functoriality pastes their three squares. -/
theorem factorization_naturality (o : Operations l E) (m : RealizationModel l E o)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (AX : CondensedERealization.At l E X) (AZ : CondensedERealization.At l E c.Z)
    (AY : CondensedERealization.At l E Y) (K K' : Integral l E X) (v : K ⟶ K')
    (lo hi a b : ℤ) (_hK : Domain l E o c K lo hi a b)
    (_hK' : Domain l E o c K' lo hi a b) :
    (realize l E Y AY).map ((support l E o c).map v) ≫
        factorization l E o m c AX AZ AY K' =
      factorization l E o m c AX AZ AY K ≫
        (CondensedRing.rightDerivedLowerShriekOfCompactification
          (Profinite.continuousCoefficientRingObj E) c).map ((realize l E X AX).map v) := by
  sorry



set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The completed composition in inverse-q coordinates retains the system counit.
Source: proof Step 4 (blueprint: lem-zl-compact-support-realization-factor-normalization).
Proof: use single_realization to identify each direct identification with inverse q
followed by the fixed strict-quotient presentation. Substitute these in the bridge
formula. Its system counit cancels the middle reconstruction unit by the triangle
identity. What remains is the independently constructed integral compositor. -/
theorem completed_bridge (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (o : Operations l E) (R : Realizations l E D o)
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
    {f : X ⟶ Y} {g : Y ⟶ Z}
    [f.IsOver (Spec (.of D.k))] [g.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (t : Compactification.Triangle f g)
    [QuasiCompact t.cf.i] [QuasiCompact t.cg.i] [QuasiCompact t.cfg.i] [QuasiCompact t.q]
    (af : sfCbcModelExtension t.cf.i (Padic.coefficientExtensionIntegers l E) ⊣
      (sfCbcMorphism t.cf.i).modulePull
        (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))
    (ag : sfCbcModelExtension t.cg.i (Padic.coefficientExtensionIntegers l E) ⊣
      (sfCbcMorphism t.cg.i).modulePull
        (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))
    (ah : sfCbcModelExtension t.cfg.i (Padic.coefficientExtensionIntegers l E) ⊣
      (sfCbcMorphism t.cfg.i).modulePull
        (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))
    (K : sfIntegralConstructibleCategory l E X) (lo hi a b : ℤ)
    (_hK : IntegralCompactificationBridge.bridgeDomain l E D.k
      (IntegralCompactificationBridge.coefficientPrimeUnit l D hl) o t K lo hi a b) :
    IntegralCompactificationBridge.completedComparison l E D.k
        (IntegralCompactificationBridge.coefficientPrimeUnit l D hl) t af ag ah K =
      GeneratorReduction.inverseOrZero
        (GeneratorReduction.inverseOrZero
          (integralComparison l E o R.realizationModel t.cg
            ((sfCompactSupportFiniteIntegralFunctor l D.k
              (IntegralCompactificationBridge.coefficientPrimeUnit l D hl) t.cf E).obj K).obj) ≫
          (sfQcqsCompactSupportRealization l E D.k
            (IntegralCompactificationBridge.coefficientPrimeUnit l D hl) t.cg).hom.app
              ((sfCompactSupportFiniteIntegralFunctor l D.k
                (IntegralCompactificationBridge.coefficientPrimeUnit l D hl) t.cf E).obj K)) ≫
      (coefficientSequenceLimit l E Z).map
        ((IntegralCompactificationBridge.systemWord l E o t.cg).map
          ((calculus l E Y).reduction.map (GeneratorReduction.inverseOrZero
            (GeneratorReduction.inverseOrZero
              (integralComparison l E o R.realizationModel t.cf K.obj) ≫
              (sfQcqsCompactSupportRealization l E D.k
                (IntegralCompactificationBridge.coefficientPrimeUnit l D hl) t.cf).hom.app K)))) ≫
      (coefficientSequenceLimit l E Z).map
        ((IntegralCompactificationBridge.systemWord l E o t.cg).map
          ((calculus l E Y).adjunction.counit.app
            ((IntegralCompactificationBridge.systemWord l E o t.cf).obj
              ((calculus l E X).reduction.obj K.obj)))) ≫
      (coefficientSequenceLimit l E Z).map
        (IntegralCompactificationBridge.systemBeta l E o R t
          ((calculus l E X).reduction.obj K.obj)) ≫
      GeneratorReduction.inverseOrZero
        (integralComparison l E o R.realizationModel t.cfg K.obj) ≫
      (sfQcqsCompactSupportRealization l E D.k
        (IntegralCompactificationBridge.coefficientPrimeUnit l D hl) t.cfg).hom.app K := by
  sorry

end WeilConjectures.CompactSupportFactorNormalization

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q63
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.EtaleCoefficientSystemAdjoint
public import Sheaf.Paper.CoefficientSystemDerivedComparison
public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import WeilConjectures.AlgebraicGeometry.EtaleSheafClopenProduct
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Basic
import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Clopen decomposition of strict étale coefficient systems

Source: Zheng, Constructions 5.14--5.15 and Lemma 5.16, pp. 34--35;
Stacks Tags 0A5B, 03DI, 03DJ and 015F
(blueprint: lem-pur-clopen-strict-system-support).

The ordinary and derived categories below are the published strict-system categories.
The comparison data are conclusions, with explicit ordinary and representative
normalizations. Natural isomorphisms include their action on every morphism.
The index `n : ℕ` denotes the positive quotient exponent `n+1`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace AlgebraicGeometry
open SheafOfModules

/-- Cache the published size witness for the small étale site.
Source: Zheng Construction 4.1 (blueprint: lem-pur-clopen-strict-system-support). -/
instance (priority := 4000) strictClopenEtaleSmall (T : Scheme.{u}) :
    EssentiallySmall.{u + 1} T.Etale := Scheme.Etale.essentiallySmall T

/-- Cache the existing additive witness at the concrete étale site sizes.
Source: Zheng Construction 4.1
(blueprint: lem-pur-clopen-strict-system-support). -/
instance (priority := 4000) strictClopenInverseAdditive
    {O : Type (u + 1)} [CommRing O] {ell : O}
    {T U : Scheme.{u}} {f : T ⟶ U} (A : StrictEtaleOrdinaryImage O ell f) :
    A.inverse.Additive := A.systemInverseAdditive

/-- Cache the existing additive witness at the concrete étale site sizes.
Source: Zheng Construction 4.1
(blueprint: lem-pur-clopen-strict-system-support). -/
instance (priority := 4000) strictClopenDirectAdditive
    {O : Type (u + 1)} [CommRing O] {ell : O}
    {T U : Scheme.{u}} {f : T ⟶ U} (A : StrictEtaleOrdinaryImage O ell f) :
    A.rightSystem.Additive := A.systemRightAdditive

/-- Cache the existing additive witness at the concrete étale site sizes.
Source: Zheng Construction 4.1
(blueprint: lem-pur-clopen-strict-system-support). -/
instance (priority := 4000) strictClopenLevelInverseAdditive
    {O : Type (u + 1)} [CommRing O] {ell : O}
    {T U : Scheme.{u}} {f : T ⟶ U} (A : StrictEtaleOrdinaryImage O ell f) (n : ℕ) :
    ((A.lift n).modules).Additive := A.inverseAdditive n

/-- Cache the existing additive witness at the concrete étale site sizes.
Source: Zheng Construction 4.1
(blueprint: lem-pur-clopen-strict-system-support). -/
instance (priority := 4000) strictClopenLevelDirectAdditive
    {O : Type (u + 1)} [CommRing O] {ell : O}
    {T U : Scheme.{u}} {f : T ⟶ U} (A : StrictEtaleOrdinaryImage O ell f) (n : ℕ) :
    (A.right n).Additive := A.rightAdditive n

variable (O : Type (u + 1)) [CommRing O] (ell : O)
  {I : Type u} [Finite I] {X Y : Scheme.{u}} {g : X ⟶ Y}
  (Xi : I → Scheme.{u}) (j : ∀ i, Xi i ⟶ X)
  [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
  (c : Compactification g) (S : StrictEtaleCompactSupport O ell c)
  (Si : ∀ i, StrictEtaleCompactSupport O ell (c.precomp (j i)))

/-- Ordinary clopen decomposition and its two component adjunctions, using the actual
geometric inverse/direct image lifts. Exactness and reconstruction are asserted as
fields, rather than imposed on the geometric input.
Source: Stacks 0A5B, first proof paragraph; Zheng Construction 4.1
(blueprint: lem-pur-clopen-strict-system-support). -/
structure StrictEtaleClopenOrdinaryData where
  image : ∀ i, StrictEtaleOrdinaryImage O ell (j i)
  reverseAdj : ∀ i, (image i).rightSystem ⊣ (image i).inverse
  reverseLevelAdj : ∀ i n, (image i).right n ⊣ ((image i).lift n).modules
  equivalence : strictEtaleCoefficientSystem X O ell ≌
    (∀ i, strictEtaleCoefficientSystem (Xi i) O ell)
  restriction : equivalence.functor ≅ Functor.pi' (fun i ↦ (image i).inverse)
  reconstruction : equivalence.inverse ≅
    Functor.pi (fun i ↦ (image i).rightSystem) ⋙ Pi.functor I

/-- Canonical comparison equations for `StrictEtaleClopenOrdinaryData`.
Source: Zheng Constructions 5.14--5.15 and Lemma 5.16; Stacks 0A5B and 03DI
(blueprint: lem-pur-clopen-strict-system-support). -/
def StrictEtaleClopenOrdinaryCoherence
    (record : StrictEtaleClopenOrdinaryData O ell Xi j) : Prop :=
  -- insertionExact
  (∀ i, PreservesFiniteLimits (record.image i).rightSystem ∧
    PreservesFiniteColimits (record.image i).rightSystem) ∧
  -- levelInsertionExact
  (∀ i n, PreservesFiniteLimits ((record.image i).right n) ∧
    PreservesFiniteColimits ((record.image i).right n)) ∧
  -- offComponent
  (∀ i k, i ≠ k → ∀ M,
    IsZero ((record.image k).inverse.obj ((record.image i).rightSystem.obj M))) ∧
  -- componentCounit
  (∀ i, IsIso (record.image i).systemAdj.counit) ∧
  -- levelComponentCounit
  (∀ i n, IsIso ((record.image i).levelAdj n).counit) ∧
  -- insertionUnit
  (∀ i M,
    (record.reverseAdj i).unit.app M ≫ (record.image i).systemAdj.counit.app M = 𝟙 M) ∧
  -- levelInsertionUnit
  (∀ i n M,
    (record.reverseLevelAdj i n).unit.app M ≫ ((record.image i).levelAdj n).counit.app M = 𝟙 M) ∧
  -- evaluatedUnit
  (∀ i n M,
    (coefficientEvaluation (J := (Xi i).smallEtaleTopology) (O := O) (ell := ell) n).map
        ((record.reverseAdj i).unit.app M) ≫
      ((record.image i).inverseEvaluation n).hom.app ((record.image i).rightSystem.obj M) ≫
      ((record.image i).lift n).modules.map (((record.image i).rightEvaluation n).hom.app M) =
    (record.reverseLevelAdj i n).unit.app (M.level n)) ∧
  -- evaluatedCounit
  (∀ i n M,
    ((record.image i).rightEvaluation n).hom.app ((record.image i).inverse.obj M) ≫
      ((record.image i).right n).map (((record.image i).inverseEvaluation n).hom.app M) ≫
      (record.reverseLevelAdj i n).counit.app (M.level n) =
    (coefficientEvaluation (J := X.smallEtaleTopology) (O := O) (ell := ell) n).map
      ((record.reverseAdj i).counit.app M)) ∧
  -- emptyZero
  (IsEmpty I → ∀ M : strictEtaleCoefficientSystem X O ell, IsZero M)

/-- Canonical comparison equations for `StrictEtaleClopenOrdinaryData`.
Source: Zheng Constructions 5.14--5.15 and Lemma 5.16; Stacks 0A5B and 03DI
(blueprint: lem-pur-clopen-strict-system-support). -/
def StrictEtaleClopenOrdinary :=
  { record : StrictEtaleClopenOrdinaryData O ell Xi j //
    StrictEtaleClopenOrdinaryCoherence O ell Xi j record }

variable (R : StrictEtaleClopenOrdinary O ell Xi j)

/-- Derived clopen decomposition is the localization of the ordinary one, including
both orders of adjunction and their finite evaluations. The functors here are actual
unbounded derived functors, not independently chosen finite-level maps. The scalar
field retains the quotient tensor/restriction comparisons, pinned by their ordinary
unit, K-flat representative, and adjunction-mate equations in CoefficientScalarImage.
Source: Stacks 015F; Zheng Lemma 4.10
(blueprint: lem-pur-clopen-strict-system-support). -/
structure StrictEtaleClopenDerivedData where
  image : ∀ i, CoefficientEvaluationImage
    (J := X.smallEtaleTopology) (K := (Xi i).smallEtaleTopology)
    O ell _ _ _ (R.val.image i) S.PX (Si i).PX
  scalar : ∀ i, CoefficientScalarImage.{u + 1, u, u + 1, u, u + 1, u + 2}
    (J := X.smallEtaleTopology) (K := (Xi i).smallEtaleTopology)
    O ell _ _ _ (R.val.image i) S.PX (Si i).PX (image i)
  reverseAdj : ∀ i, (image i).system.direct ⊣ (image i).system.inverse
  reverseLevelAdj : ∀ i n, ((image i).level n).direct ⊣ ((image i).level n).inverse
  directFactors : ∀ i, DerivedCategory.Q ⋙ (image i).system.direct ≅
    (R.val.image i).rightSystem.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  levelDirectFactors : ∀ i n, DerivedCategory.Q ⋙ ((image i).level n).direct ≅
    ((R.val.image i).right n).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  equivalence : DerivedCategory (strictEtaleCoefficientSystem X O ell) ≌
    (∀ i, DerivedCategory (strictEtaleCoefficientSystem (Xi i) O ell))
  restriction : equivalence.functor ≅ Functor.pi' (fun i ↦ (image i).system.inverse)
  reconstruction : equivalence.inverse ≅
    Functor.pi (fun i ↦ (image i).system.direct) ⋙ Pi.functor I

/-- Canonical comparison equations for `StrictEtaleClopenDerivedData`.
Source: Zheng Constructions 5.14--5.15 and Lemma 5.16; Stacks 0A5B and 03DI
(blueprint: lem-pur-clopen-strict-system-support). -/
def StrictEtaleClopenDerivedCoherence
    (record : StrictEtaleClopenDerivedData O ell Xi j c S Si R) : Prop :=
  -- offComponent
  (∀ i k, i ≠ k → ∀ M,
    IsZero ((record.image k).system.inverse.obj ((record.image i).system.direct.obj M))) ∧
  -- directLocalization
  (∀ i K, (record.directFactors i).hom.app K ≫
    (record.image i).system.directUnit.app K = 𝟙 _) ∧
  -- levelDirectLocalization
  (∀ i n K, (record.levelDirectFactors i n).hom.app K ≫
    ((record.image i).level n).directUnit.app K = 𝟙 _) ∧
  -- insertionTranspose
  (∀ i P K
    (h : ((R.val.image i).rightSystem.mapHomologicalComplex (.up ℤ)).obj P ⟶ K),
    (record.reverseAdj i).homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj K)
        ((record.directFactors i).hom.app P ≫ DerivedCategory.Q.map h) =
      DerivedCategory.Q.map
        (((R.val.reverseAdj i).mapHomologicalComplex (.up ℤ)).homEquiv P K h) ≫
        (record.image i).system.inverseFactors.inv.app K) ∧
  -- levelInsertionTranspose
  (∀ i n P K
    (h : (((R.val.image i).right n).mapHomologicalComplex (.up ℤ)).obj P ⟶ K),
    (record.reverseLevelAdj i n).homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj K)
        ((record.levelDirectFactors i n).hom.app P ≫ DerivedCategory.Q.map h) =
      DerivedCategory.Q.map
        (((R.val.reverseLevelAdj i n).mapHomologicalComplex (.up ℤ)).homEquiv P K h) ≫
        ((record.image i).level n).inverseFactors.inv.app K) ∧
  -- evaluatedUnit
  (∀ i n M,
    ((Si i).PX.evaluation n).map ((record.reverseAdj i).unit.app M) ≫
      ((record.image i).inverseEvaluation n).hom.app ((record.image i).system.direct.obj M) ≫
      ((record.image i).level n).inverse.map (((record.image i).directEvaluation n).hom.app M) =
    (record.reverseLevelAdj i n).unit.app (((Si i).PX.evaluation n).obj M)) ∧
  -- evaluatedCounit
  (∀ i n M,
    ((record.image i).directEvaluation n).hom.app ((record.image i).system.inverse.obj M) ≫
      ((record.image i).level n).direct.map (((record.image i).inverseEvaluation n).hom.app M) ≫
      (record.reverseLevelAdj i n).counit.app ((S.PX.evaluation n).obj M) =
    (S.PX.evaluation n).map ((record.reverseAdj i).counit.app M)) ∧
  -- emptyZero
  (IsEmpty I → ∀ M : DerivedCategory (strictEtaleCoefficientSystem X O ell),
    IsZero M)

/-- Canonical comparison equations for `StrictEtaleClopenDerivedData`.
Source: Zheng Constructions 5.14--5.15 and Lemma 5.16; Stacks 0A5B and 03DI
(blueprint: lem-pur-clopen-strict-system-support). -/
def StrictEtaleClopenDerived :=
  { record : StrictEtaleClopenDerivedData O ell Xi j c S Si R //
    StrictEtaleClopenDerivedCoherence O ell Xi j c S Si R record }

variable (D : StrictEtaleClopenDerived O ell Xi j c S Si R)

/-- The open-extension compositor before and after localization, normalized by the
ordinary open-adjunction units and the geometric restriction compositor. The support
map is its image under the common total derived proper direct image.
Source: Zheng Constructions 5.14--5.15 and Lemma 5.16; Stacks 03DI
(blueprint: lem-pur-clopen-strict-system-support). -/
structure StrictEtaleClopenSupportData where
  sameTarget : ∀ i, (Si i).PY = S.PY
  sameAmbient : ∀ i, (Si i).PZ = S.PZ
  sameProper : ∀ i, HEq (Si i).properDerived S.properDerived
  right : ∀ i, S.openImage.inverse ⋙ (R.val.image i).inverse ≅ (Si i).openImage.inverse
  levelRight : ∀ i n,
    (S.openImage.lift n).modules ⋙ ((R.val.image i).lift n).modules ≅
      ((Si i).openImage.lift n).modules
  ordinary : ∀ i, (R.val.image i).rightSystem ⋙ S.val.openExtension ≅
    (Si i).val.openExtension
  level : ∀ i n, (R.val.image i).right n ⋙ S.val.levelOpen n ≅ (Si i).val.levelOpen n
  derived : ∀ i, (D.val.image i).system.direct ⋙ S.derivedOpen ≅ (Si i).derivedOpen
  levelDerived : ∀ i n, ((D.val.image i).level n).direct ⋙ S.levelDerivedOpen n ≅
    (Si i).levelDerivedOpen n
  support : ∀ i, (D.val.image i).system.direct ⋙ S.functor ≅ (Si i).functor
  levelSupport : ∀ i n, ((D.val.image i).level n).direct ⋙ S.levelFunctor n ≅
    (Si i).levelFunctor n

/-- Canonical comparison equations for `StrictEtaleClopenSupportData`.
Source: Zheng Constructions 5.14--5.15 and Lemma 5.16; Stacks 0A5B and 03DI
(blueprint: lem-pur-clopen-strict-system-support). -/
def StrictEtaleClopenSupportCoherence
    (record : StrictEtaleClopenSupportData O ell Xi j c S Si R D) : Prop :=
  -- levelRightUnderlying
  (∀ i n (M : strictEtaleLevel c.Z O ell n),
    (coefficientUnderlying (J := (Xi i).smallEtaleTopology) O ell n).map
        ((record.levelRight i n).hom.app M) ≫
        ((Si i).openImage.lift n).moduleUnderlying.hom.app M =
      ((R.val.image i).lift n).moduleUnderlying.hom.app ((S.openImage.lift n).modules.obj M) ≫
        (Scheme.etaleSetPullback (j i)).map
          ((S.openImage.lift n).moduleUnderlying.hom.app M) ≫
        (ProEtale.supportSiteEtaleComparisonComp (Type (u + 1)) (j i) c.i).inv.app
          ((coefficientUnderlying (J := c.Z.smallEtaleTopology) O ell n).obj M)) ∧
  -- rightEvaluation
  (∀ i n M,
    (coefficientEvaluation (J := (Xi i).smallEtaleTopology)
      (O := O) (ell := ell) n).map ((record.right i).hom.app M) ≫
        ((Si i).openImage.inverseEvaluation n).hom.app M =
      ((R.val.image i).inverseEvaluation n).hom.app (S.openImage.inverse.obj M) ≫
        ((R.val.image i).lift n).modules.map ((S.openImage.inverseEvaluation n).hom.app M) ≫
        (record.levelRight i n).hom.app (M.level n)) ∧
  -- unit
  (∀ i M,
    ((R.val.reverseAdj i).comp S.val.openAdjunction).unit.app M ≫
        (record.right i).hom.app (((R.val.image i).rightSystem ⋙ S.val.openExtension).obj M) ≫
        (Si i).openImage.inverse.map ((record.ordinary i).hom.app M) =
      (Si i).val.openAdjunction.unit.app M) ∧
  -- levelUnit
  (∀ i n M,
    ((R.val.reverseLevelAdj i n).comp (S.val.levelOpenAdjunction n)).unit.app M ≫
        (record.levelRight i n).hom.app (((R.val.image i).right n ⋙ S.val.levelOpen n).obj M) ≫
        ((Si i).openImage.lift n).modules.map ((record.level i n).hom.app M) =
      ((Si i).val.levelOpenAdjunction n).unit.app M) ∧
  -- ordinaryEvaluation
  (∀ i n M,
    (coefficientEvaluation (J := c.Z.smallEtaleTopology) (O := O) (ell := ell) n).map
        ((record.ordinary i).hom.app M) ≫ ((Si i).val.openEvaluation n).hom.app M =
      (S.val.openEvaluation n).hom.app ((R.val.image i).rightSystem.obj M) ≫
        (S.val.levelOpen n).map (((R.val.image i).rightEvaluation n).hom.app M) ≫
        (record.level i n).hom.app (M.level n)) ∧
  -- factors
  (∀ i K,
    (record.derived i).hom.app (DerivedCategory.Q.obj K) ≫ (Si i).val.openFactors.hom.app K =
      S.derivedOpen.map ((D.val.directFactors i).hom.app K) ≫
        S.val.openFactors.hom.app
          (((R.val.image i).rightSystem.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (record.ordinary i) (.up ℤ)).hom.app K)) ∧
  -- levelFactors
  (∀ i n K,
    (record.levelDerived i n).hom.app (DerivedCategory.Q.obj K) ≫
        ((Si i).val.levelOpenFactors n).hom.app K =
      (S.levelDerivedOpen n).map ((D.val.levelDirectFactors i n).hom.app K) ≫
        (S.val.levelOpenFactors n).hom.app
          ((((R.val.image i).right n).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (record.level i n) (.up ℤ)).hom.app K)) ∧
  -- supportMap
  (∀ i, HEq (record.support i).hom
    (Functor.whiskerRight (record.derived i).hom S.properDerived.system.direct)) ∧
  -- levelSupportMap
  (∀ i n, HEq (record.levelSupport i n).hom
    (Functor.whiskerRight (record.levelDerived i n).hom (S.properDerived.level n).direct)) ∧
  -- evaluatedSupport
  (∀ i n M,
    (S.PY.evaluation n).map ((record.support i).hom.app M) ≫
        eqToHom (congrArg (fun P ↦ (P.evaluation n).obj ((Si i).functor.obj M))
          (record.sameTarget i).symm) ≫
        ((Si i).evaluation n).hom.app M =
      (S.evaluation n).hom.app ((D.val.image i).system.direct.obj M) ≫
        (S.levelFunctor n).map (((D.val.image i).directEvaluation n).hom.app M) ≫
        (record.levelSupport i n).hom.app (((Si i).PX.evaluation n).obj M))

/-- Canonical comparison equations for `StrictEtaleClopenSupportData`.
Source: Zheng Constructions 5.14--5.15 and Lemma 5.16; Stacks 0A5B and 03DI
(blueprint: lem-pur-clopen-strict-system-support). -/
def StrictEtaleClopenSupport :=
  { record : StrictEtaleClopenSupportData O ell Xi j c S Si R D //
    StrictEtaleClopenSupportCoherence O ell Xi j c S Si R D record }

/-- Finite clopen restriction is an exact product equivalence on strict étale systems,
and on their ordinary unbounded derived categories. Zero insertion is adjoint in both
orders. The compact-support comparison is the localization of the unit-normalized
ordinary open compositor followed by the common proper derived image.
Source: Zheng Constructions 5.14--5.15 and Lemma 5.16, pp. 34--35;
Stacks 0A5B, 015F, 03DI and 03DJ
(blueprint: lem-pur-clopen-strict-system-support).

Proof plan:
1. The pairwise disjoint clopen cover is a finite scheme coproduct. Apply
lem-weil-pbc-etale-sheaf-clopen-product. Transport constant coefficient actions and
linear maps componentwise by full faithfulness. Reconstruct sections by the product
of their component sections; scalar restriction keeps the same abelian sheaves.
2. Apply this at every quotient level. The inverse Hom bijections recover precisely
the semilinear transitions and compatible families. Thus reconstruction is an exact
inverse to restriction on the actual systems of
lem-pur-coefficient-system-derived-comparison, commuting with evaluation.
3. In a product category zero insertion is both left and right adjoint to projection.
Units and counits are the coordinate identities and zero maps; reconstruction is
the finite product of these insertions. Empty coverings force every sheaf to be zero.
4. Retain CoefficientScalarImage from coefficientSystemUnboundedComparison for
these fixed evaluation images. Its derivedTensor is the quotient restriction mate
characterized on flat-term K-flat representatives; its ordinary tensor is fixed by
restrictInverse and the scalar adjunction units. No quotient flatness is required.
Localize the exact termwise functors, inverse maps, units and counits using
lem-sf-exact-functor-derived-triangulated and
lem-weil-pbc-localization-universal-property. The finite reconstruction identities
and both triangle identities descend, as does their commutation with evaluation.
5. Use lem-weil-pbc-extension-by-zero-adjunction and
lem-weil-pbc-conjugate-iso-unit-equation to identify clopen open extension with zero
insertion. Compose the adjunctions by def-weil-pbc-composite-adjunction. The geometric
restriction compositor determines the ordinary extension compositor uniquely by its
unit equation, as in lem-cbc-extension-zero-composition. Exactness follows from
lem-pur-site-restriction-module-adjunction-exact.
6. On the generators of def-weil-extension-by-zero-presheaf the compositor is the
identity on the component and zero on the complement. A semilinear transition sends
the same generator to its transition image in the same summand on both sides.
Use def-weil-presheaf-modules-sheafification to descend this equality, including
iterated sheafification. This proves transition compatibility without assuming any
quotient map flat. The same calculation gives naturality on all system morphisms.
7. Localize this actual ordinary natural isomorphism and apply the common total
proper derived image from lem-pur-etale-coefficient-system-adjoint. Its evaluated
comparison is the ordinary finite-level one by
lem-pur-coefficient-system-derived-comparison. Naturality gives the assertion on
every derived morphism. Empty components give only zero maps. No step assumes Y
separated over the ground field.
-/
theorem clopenStrictSystemSupport
    (F : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (_hl : l ≠ F.p) (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    {I : Type u} [Finite I] {X Y : Scheme.{u}}
    [X.Over (Spec (.of F.k))] [Y.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of F.k))] [QuasiCompact (X ↘ Spec (.of F.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of F.k))] [QuasiCompact (Y ↘ Spec (.of F.k))]
    (g : X ⟶ Y) [g.IsOver (Spec (.of F.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (Xi : I → Scheme.{u}) (j : ∀ i, Xi i ⟶ X)
    [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    (_hdisjoint : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
    (_hcover : (⋃ i, Set.range (j i)) = Set.univ)
    (c : Compactification g) :
    ∃ (S : StrictEtaleCompactSupport (Padic.coefficientExtensionIntegers l E)
          (Padic.coefficientExtensionUniformizer l E) c)
      (Si : ∀ i, StrictEtaleCompactSupport (Padic.coefficientExtensionIntegers l E)
          (Padic.coefficientExtensionUniformizer l E) (c.precomp (j i)))
      (R : StrictEtaleClopenOrdinary (Padic.coefficientExtensionIntegers l E)
          (Padic.coefficientExtensionUniformizer l E) Xi j)
      (D : StrictEtaleClopenDerived (Padic.coefficientExtensionIntegers l E)
          (Padic.coefficientExtensionUniformizer l E) Xi j c S Si R),
      Nonempty (StrictEtaleClopenSupport (Padic.coefficientExtensionIntegers l E)
        (Padic.coefficientExtensionUniformizer l E) Xi j c S Si R D) := by
  sorry

end AlgebraicGeometry

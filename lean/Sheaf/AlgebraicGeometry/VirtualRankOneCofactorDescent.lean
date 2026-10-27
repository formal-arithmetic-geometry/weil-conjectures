/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q44
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import Sheaf.TraceFormula.CanonicalTwoTermPerfectDeterminant
public import Sheaf.LinearAlgebra.TwoTermCofactorNaturality
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import Sheaf.LinearAlgebra.CofactorLocalDescent
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing
import WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence

/-! # Descent of the virtual-rank-one cofactor

Source: Stacks Project, Duality, Tag 0E9Y; More on Algebra, Tag 0FJM.
(blueprint: lem-sfb-virtual-rank-one-cofactor-descent).

The auxiliary predicates spell out the local wedge formula and the canonical
cohomology comparisons. Their data use the existing two-term determinant models.
Open immersions include open restrictions, refinements and scheme isomorphisms.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w v

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

variable [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

/-- Local two-term models with rank difference one; the negative rank is allowed to vary.
Source: Stacks, Tags 0E9Y and 0FJM
(blueprint: lem-sfb-virtual-rank-one-cofactor-descent). -/
def IsVirtualRankOne (X : Scheme.{u}) (L : schemeDerivedCategory X) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ P : TwoTermDeterminantModel U.toScheme,
    P.nonnegRank = P.negRank + 1 ∧
      Nonempty (DerivedCategory.Q.obj P.complex ≅ (derivedPullback U.ι).obj L)

/-- The canonical class of a section in degree zero, via cycles and derived homology.
Thus the source is exactly the cokernel of the differential, without injectivity.
Source: Stacks, Tag 0E9Y
(blueprint: lem-sfb-virtual-rank-one-cofactor-descent). -/
def TwoTermDeterminantModel.cofactorClass {X : Scheme.{u}} (P : TwoTermDeterminantModel X) :
    @id (SheafOfModules.{u} (moduleRings X.toRingedSpace)) P.nonneg ⟶
      (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
          (DerivedCategory.Q.obj P.complex) :=
  P.complex.liftCycles'
    (HomologicalComplex.doubleXIso₁ P.differential
      (by decide : (ComplexShape.up ℤ).Rel (-1) 0) (by decide)).inv 1
    (by decide : (ComplexShape.up ℤ).Rel 0 1)
    (by simp [TwoTermDeterminantModel.complex, HomologicalComplex.double_d_eq_zero₀]) ≫
      P.complex.homologyπ 0 ≫ (DerivedCategory.homologyFunctorFactors
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).inv.app P.complex

/-- The basis-and-lift formula on every open where the negative term has a basis.
The dual section is normalized by its value one on the top basis wedge.
Source: Stacks, Tag 0E9Y, displayed wedge formula
(blueprint: lem-sfb-virtual-rank-one-cofactor-descent). -/
def TwoTermDeterminantModel.IsSheafCofactor {X : Scheme.{u}}
    (P : TwoTermDeterminantModel X) (hr : P.nonnegRank = P.negRank + 1)
    (f : (DerivedCategory.homologyFunctor _ 0).obj
      (DerivedCategory.Q.obj P.complex) ⟶ P.line) : Prop :=
  ∀ (O : X.Opens) (a : Module.Basis (Fin P.negRank) Γ(X, O) Γ(P.neg, O))
    (ρ : Γ(dual (exteriorSheaf P.neg P.negRank), O)),
    ρ.app (op (Over.mk (𝟙 O))) (exteriorSheafSection P.neg P.negRank O a) =
      (1 : Γ(X, O)) →
    ∀ z : Γ(P.nonneg, O),
      (P.cofactorClass ≫ f).val.app (op O) z =
        tmulSection (X := X) (M := dual (exteriorSheaf P.neg P.negRank))
          (N := exteriorSheaf P.nonneg P.nonnegRank) ρ
          (exteriorSheafSection P.nonneg P.nonnegRank O
            (fun j ↦ Fin.snoc (α := fun _ ↦ Γ(P.nonneg, O))
              (fun k ↦ P.differential.app O (a k)) z (Fin.cast hr j)))

/-- Literal restriction in the shared module-sheaf category instances.
This is the existing restriction functor, with its source and target types explicit.
Source: Stacks, Tag 08DW
(blueprint: lem-sfb-virtual-rank-one-cofactor-descent). -/
abbrev cofactorRestriction {X Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g] :
    SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings Y.toRingedSpace) :=
  { obj := fun M ↦ (restrictFunctor g).obj M
    map := fun f ↦ (restrictFunctor g).map f }

/-- Restriction of sectionwise maps preserves their sums by definition.
Source: Stacks, Tag 08DW
(blueprint: lem-sfb-virtual-rank-one-cofactor-descent). -/
instance cofactorRestriction_additive {X Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g] :
    (cofactorRestriction g).Additive where
  map_add := rfl

/-- Ordinary pullback compared with literal restriction, fixed by its adjunction.
Source: Stacks, Tags 0095 and 08DW
(blueprint: lem-sfb-virtual-rank-one-cofactor-descent). -/
def cofactorTensorRestrictionIso {X Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g] :
    @id (SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (tensorPullback g) ≅
        cofactorRestriction g :=
  (Classical.choose (exists_tensorPullbackAdjunction g)).leftAdjointUniq
    (pullbackPushforwardAdjunction g) ≪≫ (restrictFunctorIsoPullback g).symm

/-- The termwise comparison uses the same adjunction-induced restriction map.
Source: Stacks, Tags 0095 and 08DW
(blueprint: lem-sfb-virtual-rank-one-cofactor-descent). -/
def cofactorRestrictionChainMap {X Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g]
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    CotangentPresentation.pullbackComplex g K ⟶
      ((cofactorRestriction g).mapHomologicalComplex (.up ℤ)).obj K :=
  { f := fun i ↦ (cofactorTensorRestrictionIso g).hom.app (K.X i)
    comm' := fun i j _ ↦ ((cofactorTensorRestrictionIso g).hom.naturality (K.d i j)).symm }

/-- Canonical exact pullback comparison. The equation on every K-flat representative
pins the derived comparison to the original counit, and prevents an arbitrary scalar.
The exactness fields are conclusions of the descent theorem, not geometric assumptions.
Source: Stacks, Tags 06YJ and 08DW
(blueprint: lem-sfb-virtual-rank-one-cofactor-descent). -/
structure CofactorRestrictionComparison {X Y : Scheme.{u}} (g : Y ⟶ X)
    [IsOpenImmersion g] where
  /-- Restriction is left exact. -/
  [limits : PreservesFiniteLimits (cofactorRestriction g)]
  /-- Restriction is right exact. -/
  [colimits : PreservesFiniteColimits (cofactorRestriction g)]
  /-- Derived pullback is exact restriction on the derived category. -/
  derivedIso : derivedPullback g ≅ (cofactorRestriction g).mapDerivedCategory
  /-- Its action on K-flat complexes is the fixed pullback counit. -/
  normalization : ∀ K : CochainComplex
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ,
    CochainComplex.IsKFlatTensor (R := X.sheaf) K →
      derivedIso.hom.app (DerivedCategory.Q.obj K) ≫
        (cofactorRestriction g).mapDerivedCategoryFactors.hom.app K =
      CotangentPresentation.pullbackCounit g K ≫ DerivedCategory.Q.map
        (cofactorRestrictionChainMap g K)

/-- The canonical comparison of zeroth cohomology with exact restriction.
Source: Stacks, Tag 08DW
(blueprint: lem-sfb-virtual-rank-one-cofactor-descent). -/
def CofactorRestrictionComparison.h0Iso {X Y : Scheme.{u}} {g : Y ⟶ X}
    [IsOpenImmersion g] (B : CofactorRestrictionComparison g) (L : schemeDerivedCategory X) :
    (DerivedCategory.homologyFunctor _ 0).obj ((derivedPullback g).obj L) ≅
      (cofactorRestriction g).obj ((DerivedCategory.homologyFunctor _ 0).obj L) :=
  letI := B.limits
  letI := B.colimits
  (DerivedCategory.homologyFunctor _ 0).mapIso (B.derivedIso.app L) ≪≫
    ((cofactorRestriction g).mapDerivedCategoryHomologyFunctorIso 0).symm.app L

/-- The determinant comparison from restriction to derived pullback.
Source: Stacks, Tags 0FJX and 0FJY
(blueprint: lem-sfb-virtual-rank-one-cofactor-descent). -/
def cofactorDetRestrictionIso (T : TwoTermPerfectDeterminantData.{u, w})
    {X Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g]
    (L : schemeDerivedCategory X) (hL : isTwoTermPerfect X L) :
    (cofactorRestriction g).obj (twoTermDeterminantValue (T.functor X) L hL) ≅
      twoTermDeterminantValue (T.functor Y) ((derivedPullback g).obj L)
        (T.pullback_mem g L hL) :=
  (cofactorTensorRestrictionIso g).symm.app _ ≪≫ T.pullbackIso g L hL

/-- The expression of a global arrow in any specified local model. All comparisons
are the canonical cohomology and determinant comparisons, in the direction lambda:E≅L.
Source: Stacks, Tags 0E9Y and 0FJM
(blueprint: lem-sfb-virtual-rank-one-cofactor-descent). -/
def cofactorModelExpression (T : TwoTermPerfectDeterminantData.{u, w})
    {X Y : Scheme.{u}} {g : Y ⟶ X} [IsOpenImmersion g]
    (B : CofactorRestrictionComparison g) (L : schemeDerivedCategory X)
    (hL : isTwoTermPerfect X L)
    (f : (DerivedCategory.homologyFunctor _ 0).obj L ⟶
      twoTermDeterminantValue (T.functor X) L hL)
    (P : TwoTermDeterminantModel Y)
    (e : DerivedCategory.Q.obj P.complex ≅ (derivedPullback g).obj L) :
    (DerivedCategory.homologyFunctor _ 0).obj (DerivedCategory.Q.obj P.complex) ⟶ P.line :=
  (DerivedCategory.homologyFunctor _ 0).map e.hom ≫ (B.h0Iso L).hom ≫
    (cofactorRestriction g).map f ≫ (cofactorDetRestrictionIso T g L hL).hom ≫
      (twoTermDeterminantIso (T.functor Y) (T.model_mem P)
        (T.pullback_mem g L hL) e).inv ≫ (T.modelIso P).hom

/-- A global arrow is the cofactor if its expression in every further local two-term
model has the wedge formula. This does not privilege a chosen cover.
Source: Stacks, Tags 0E9Y and 0FJM
(blueprint: lem-sfb-virtual-rank-one-cofactor-descent). -/
def IsVirtualRankOneCofactor (T : TwoTermPerfectDeterminantData.{u, w})
    (B : ∀ {X Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g],
      CofactorRestrictionComparison g)
    (X : Scheme.{u}) (L : schemeDerivedCategory X) (hL : isTwoTermPerfect X L)
    (f : (DerivedCategory.homologyFunctor _ 0).obj L ⟶
      twoTermDeterminantValue (T.functor X) L hL) : Prop :=
  ∀ (Y : Scheme.{u}) (g : Y ⟶ X) [IsOpenImmersion g]
    (P : TwoTermDeterminantModel Y) (hr : P.nonnegRank = P.negRank + 1)
    (e : DerivedCategory.Q.obj P.complex ≅ (derivedPullback g).obj L),
    P.IsSheafCofactor hr (cofactorModelExpression T (B g) L hL f P e)

/-- Descent, uniqueness, derived naturality and transport of the cofactor, with the
local formula on all models, even models absent from the original cover.
Source: Stacks, Duality, Tag 0E9Y; More on Algebra, Tag 0FJM
(blueprint: lem-sfb-virtual-rank-one-cofactor-descent).

Proof:
1. On free affine charts use lem-sfb-cofactor-local-descent. The basis and lift
changes cancel or vanish by alternation. Tilde preserves cokernels. The sheafified
exterior and dual comparisons preserve pure wedges. By lem-sc-affine-inter-principal-both,
common principal charts cover arbitrary affine intersections. Localization compatibility
then identifies the maps on intersections; lem-pur-sheaf-hom-cover-gluing glues them.
2. On affine refinements of an overlap use lem-pc-affine-qcoh-derived-equivalence
and lem-sc-derived-open-restriction-adjunction-exact to identify the derived model
comparison and its H0 map. The kernel-first normalization of
lem-trf-two-term-perfect-determinant identifies its determinant with that of
lem-sfb-two-term-cofactor-naturality. That theorem gives the cofactor identity even
when the two negative ranks differ. Sheaf uniqueness extends the identity to the overlap.
3. Transport the local maps along H0(lambda) inverse and the determinant comparison.
Step 2 makes them agree on overlaps. Sheaf-hom-cover gluing gives a unique global arrow.
This works for the empty cover of the empty scheme and needs no affine intersections.
4. Compare every additional model with the original ones on their intersections.
Step 2 gives the same formula there; uniqueness gives it everywhere. For b:L≅M apply
the same calculation to mu inverse composed with b composed with lambda, and cancel
H0(lambda). Thus det(b) w_L = w_M H0(b). This also proves cover/refinement independence.
5. Exact restriction preserves cokernels, cohomology and the wedge formula. Its
comparison is characterized on K-flat representatives by the original counit.
The determinant restriction comparison is that of the recorded canonical determinant.
The same argument for a scheme isomorphism is extension of scalars along ring
isomorphisms on affine charts. The pure-wedge and dual comparisons of
lem-trf-projective-exterior-scalar-comparisons preserve the displayed formula.
Uniqueness gives transport and its iterates. No smoothness, flatness, Noetherian,
separatedness or cotangent hypothesis has been used.
-/
theorem virtualRankOne_cofactor_descent (T : TwoTermPerfectDeterminantData.{u, w})
    (hT : T.IsCanonical) :
    ∃ B : ∀ {X Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g],
        CofactorRestrictionComparison g,
    ∃ W : ∀ (X : Scheme.{u}) (L : schemeDerivedCategory X)
        (hL : isTwoTermPerfect X L) (_hR : IsVirtualRankOne X L),
      (DerivedCategory.homologyFunctor _ 0).obj L ⟶
        twoTermDeterminantValue (T.functor X) L hL,
      (∀ (X : Scheme.{u}) (L : schemeDerivedCategory X)
        (hL : isTwoTermPerfect X L) (hR : IsVirtualRankOne X L),
        IsVirtualRankOneCofactor T B X L hL (W X L hL hR) ∧
        ∀ f, IsVirtualRankOneCofactor T B X L hL f → f = W X L hL hR) ∧
      (∀ (X : Scheme.{u}) (L M : schemeDerivedCategory X)
        (hL : isTwoTermPerfect X L) (hM : isTwoTermPerfect X M)
        (hR : IsVirtualRankOne X L) (hS : IsVirtualRankOne X M) (b : L ≅ M),
        W X L hL hR ≫ (twoTermDeterminantIso (T.functor X) hL hM b).hom =
          (DerivedCategory.homologyFunctor _ 0).map b.hom ≫ W X M hM hS) ∧
      (∀ (X Y : Scheme.{u}) (g : Y ⟶ X) [IsOpenImmersion g]
        (L : schemeDerivedCategory X) (hL : isTwoTermPerfect X L)
        (hR : IsVirtualRankOne X L),
        ∃ hS : IsVirtualRankOne Y ((derivedPullback g).obj L),
          (cofactorRestriction g).map (W X L hL hR) ≫
              (cofactorDetRestrictionIso T g L hL).hom =
            ((B g).h0Iso L).inv ≫
              W Y ((derivedPullback g).obj L) (T.pullback_mem g L hL) hS) ∧
      (∀ (X : Scheme.{u}) (P : TwoTermDeterminantModel X)
        (hr : P.nonnegRank = P.negRank + 1),
        ∃! f, P.IsSheafCofactor hr f) ∧
      (∀ (X : Scheme.{u}) (P Q : TwoTermDeterminantModel X)
        (hr : P.nonnegRank = P.negRank + 1) (hs : Q.nonnegRank = Q.negRank + 1)
        (a : DerivedCategory.Q.obj P.complex ≅ DerivedCategory.Q.obj Q.complex)
        (f : (DerivedCategory.homologyFunctor _ 0).obj
          (DerivedCategory.Q.obj P.complex) ⟶ P.line)
        (f' : (DerivedCategory.homologyFunctor _ 0).obj
          (DerivedCategory.Q.obj Q.complex) ⟶ Q.line),
        P.IsSheafCofactor hr f → Q.IsSheafCofactor hs f' →
          f ≫ (T.modelIso P).inv ≫
              (twoTermDeterminantIso (T.functor X) (T.model_mem P) (T.model_mem Q) a).hom ≫
                (T.modelIso Q).hom =
            (DerivedCategory.homologyFunctor _ 0).map a.hom ≫ f') ∧
      (∀ (X : Scheme.{u}) (L : schemeDerivedCategory X)
        (hL : isTwoTermPerfect X L) (hR : IsVirtualRankOne X L)
        (I : Type v) (U : I → X.Opens) (_hcover : iSup U = ⊤)
        (P : ∀ i, TwoTermDeterminantModel (U i).toScheme)
        (hr : ∀ i, (P i).nonnegRank = (P i).negRank + 1)
        (e : ∀ i, DerivedCategory.Q.obj (P i).complex ≅ (derivedPullback (U i).ι).obj L)
        (f : (DerivedCategory.homologyFunctor _ 0).obj L ⟶
          twoTermDeterminantValue (T.functor X) L hL),
        (∀ i, (P i).IsSheafCofactor (hr i)
          (cofactorModelExpression T (B (U i).ι) L hL f (P i) (e i))) ↔
            f = W X L hL hR) := by
  sorry

end AlgebraicGeometry

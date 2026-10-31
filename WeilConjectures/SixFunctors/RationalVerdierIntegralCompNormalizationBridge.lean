/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ScalarSixDefinitions
public import WeilConjectures.SixFunctors.ScalarSix
public import WeilConjectures.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.Algebra.Homology.InternalKFlatScalarTowerRealizationSupplement
public import WeilConjectures.CategoryTheory.ModuleObjects.InternalTensorCompositionUnitNormalization

/-! # Native condensed scalar composition normalization

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-tower/`
`thm-coef-rational-verdier.proof.md`, normalization clause
of paragraph 3, associator equation
(blueprint: lem-coef-rational-verdier-integral-comp-normalization-bridge).

Proof: the adjunction-conjugate scalar tower comparison is identified with the
ordinary balanced tensor multiplication on a native K-flat resolution.  The
internal coequalizer formulas and the unit insertion formulas are those of
`CategoryTheory.Mod.internal_tensor_composition_unit_normalization`; the
K-flat realization is independent of the chosen native resolution.  The
finite-Tor restriction follows from the preservation clause in the scalar-six
coefficient package. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The proposition carrying the canonical coequalizer multiplication and unit formulas.
`type_of%` records the proposition of the existing theorem, rather than its proof term.
Source: paragraph 3, internal tensor normalization
(blueprint: lem-coef-rational-verdier-integral-comp-normalization-bridge). -/
def nativeInternalTensorNormalization {Λ Λ' Λ'' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (b : Λ' ⟶ Λ'') (X : Scheme.{u}) : Prop :=
  type_of% (Mod.internal_tensor_composition_unit_normalization
    (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)
    (coefficientMap (Λ := Λ'.X) (Λ' := Λ''.X) b.hom.hom X))

/-- Every native K-flat computation of K identifies the comparison with the
cochain isomorphism fixed by multiplication and unit insertion on coequalizers.
Source: paragraph 3, native representative calculation
(blueprint: lem-coef-rational-verdier-integral-comp-normalization-bridge). -/
def nativeScalarComponentNormalization {Λ Λ' Λ'' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (b : Λ' ⟶ Λ'') (X : Scheme.{u})
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) : Prop :=
  ∀ (P : CochainComplex (ModuleRingedComparison.internalModules Λ.X X) ℤ),
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
    ∀ e : DerivedCategory.Q.obj P ≅ K,
    ∃ m : ((Mod.extendScalars
        (coefficientMap (Λ := Λ'.X) (Λ' := Λ''.X) b.hom.hom X)).mapHomologicalComplex
          (.up ℤ)).obj
        (((Mod.extendScalars
          (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)).mapHomologicalComplex
            (.up ℤ)).obj P) ≅
        ((Mod.extendScalars
          (coefficientMap (Λ := Λ.X) (Λ' := Λ''.X) (a ≫ b).hom.hom X)).mapHomologicalComplex
            (.up ℤ)).obj P,
      (∀ i : ℤ,
        condensedRingObj Λ''.X X ◁
            Mod.extendπ (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X) (P.X i) ≫
          Mod.extendπ (coefficientMap (Λ := Λ'.X) (Λ' := Λ''.X) b.hom.hom X)
            ((Mod.extendScalars
              (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)).obj (P.X i)) ≫
          (m.hom.f i).hom =
        (α_ (condensedRingObj Λ''.X X) (condensedRingObj Λ'.X X) (P.X i).X).inv ≫
          (condensedRingObj Λ''.X X ◁
            coefficientMap (Λ := Λ'.X) (Λ' := Λ''.X) b.hom.hom X ≫ μ) ▷ (P.X i).X ≫
          Mod.extendπ
            (coefficientMap (Λ := Λ.X) (Λ' := Λ''.X) (a ≫ b).hom.hom X) (P.X i)) ∧
      (∀ i : ℤ,
        Mod.extendπ (coefficientMap (Λ := Λ.X) (Λ' := Λ''.X) (a ≫ b).hom.hom X) (P.X i) ≫
            (m.inv.f i).hom =
          condensedRingObj Λ''.X X ◁
            ((λ_ (P.X i).X).inv ≫ η ▷ (P.X i).X ≫
              Mod.extendπ (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X) (P.X i)) ≫
            Mod.extendπ (coefficientMap (Λ := Λ'.X) (Λ' := Λ''.X) b.hom.hom X)
              ((Mod.extendScalars
                (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)).obj (P.X i))) ∧
      (scalarSixTower a b X).hom.app K ≫
          (scalarSixChange (a ≫ b) X).map e.inv ≫
          (Functor.leftDerivedFunctorCounit
            (Mod.extendScalars
              (coefficientMap (Λ := Λ.X) (Λ' := Λ''.X) (a ≫ b).hom.hom X))).app
                ((HomotopyCategory.quotient _ _).obj P) =
        (scalarSixChange a X ⋙ scalarSixChange b X).map e.inv ≫
          (scalarSixChange b X).map
            ((Functor.leftDerivedFunctorCounit
              (Mod.extendScalars
                (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X))).app
                  ((HomotopyCategory.quotient _ _).obj P)) ≫
          (Functor.leftDerivedFunctorCounit
            (Mod.extendScalars
              (coefficientMap (Λ := Λ'.X) (Λ' := Λ''.X) b.hom.hom X))).app
                ((HomotopyCategory.quotient _ _).obj
                  (((Mod.extendScalars
                    (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)).mapHomologicalComplex
                      (.up ℤ)).obj P)) ≫
          DerivedCategory.Q.map m.hom

/-- Native condensed scalar composition equals the internal tensor multiplication
associator on every native K-flat computation, also on the finite-Tor full subcategory.
Source: paragraph 3, associator equation
(blueprint: lem-coef-rational-verdier-integral-comp-normalization-bridge).

Proof: identify scalar extension with extension on K-flat complexes. Balancing
identifies tensor over S with the restricted tensor over R, so extension preserves
K-flatness even for nonflat maps. The internal tensor normalization theorem gives
multiplication, unit insertion and the unit equation degreewise. The prescribed
K-flat computation counits identify these units with the derived units. Uniqueness
of a unit-compatible comparison of left adjoints identifies its localization with
scalarSixTower. The equation for every resolution gives independence, and restriction
to the full finite-Tor category gives the quotient coefficient specializations. -/
theorem integral_comp_normalization_bridge
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (_hcd : AlgebraicGeometry.ProEtale.BaseFieldFiniteCD ell k)
    {Λ Λ' Λ'' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (_ha : ListedCoefficientMap ell a)
    (b : Λ' ⟶ Λ'') (_hb : ListedCoefficientMap ell b)
    {X : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    (∀ K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X.left),
      nativeScalarComponentNormalization a b X.left K) ∧
    (∀ K : AlgebraicGeometry.ProEtale.ConstantModelConstructibleFiniteTor Λ.X X.left,
      nativeScalarComponentNormalization a b X.left K.obj) ∧
    nativeInternalTensorNormalization a b X.left := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing

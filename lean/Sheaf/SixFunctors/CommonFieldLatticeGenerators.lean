/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import Sheaf.SixFunctors.ScalarSixPullback
public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.NumberTheory.Padics.IntegersFinite
import Sheaf.Paper.FiniteSubextensionsDirected
import Sheaf.Algebra.Homology.LocallyFreeDerivedScalars
import Sheaf.SixFunctors.IntegralModelsGenerators

/-! # Common finite coefficient fields for lattice generators

Source: blueprint main-20261015, proper base change, rational proof, paragraph (3)
(blueprint: lem-sfb-common-field-lattice-generators).

The helper definitions only specialize existing coefficient objects and functors.
The final comparison is characterized after restriction to the locally closed stratum;
its normalization uses the actual derived counit and scalar-tower isomorphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The existing condensed ring of integers, bundled for scalar change.
Source: rational proper-base-change proof (3)
(blueprint: lem-sfb-common-field-lattice-generators). -/
abbrev latticeIntegralRing (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) : ScalarSixRing.{u} :=
  ⟨Profinite.padicIntegersRingObj ell E.1⟩

/-- The existing finite-subextension-valued algebraic closure coefficient ring.
Source: rational proper-base-change proof (3)
(blueprint: lem-sfb-common-field-lattice-generators). -/
abbrev latticeClosureRing (ell : ℕ) [Fact ell.Prime] : ScalarSixRing.{u} :=
  ⟨Profinite.padicAlgClRingObj ell⟩

/-- Postcomposition by the inclusion of valuation subrings. This uses the valuation
inherited from the fixed algebraic closure, not a newly chosen absolute value.
Source: rational proper-base-change proof (3), common coefficient field
(blueprint: lem-sfb-common-field-lattice-generators). -/
def latticeIntegerInclusion (ell : ℕ) [Fact ell.Prime]
    {E F : PadicAlgCl.FiniteIntermediateField ell} (h : E ≤ F) :
    PadicAlgCl.integers ell E.1 →+* PadicAlgCl.integers ell F.1 :=
  letI : Algebra E.1 F.1 := (IntermediateField.inclusion h).toAlgebra
  letI : IsScalarTower E.1 F.1 (PadicAlgCl ell) :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  PadicAlgCl.integersMap ell E.1 F.1

/-- The continuous-function condensed-ring map induced by inclusion of integers.
Source: rational proper-base-change proof (3), coefficient tower
(blueprint: lem-sfb-common-field-lattice-generators). -/
def latticeIntegralMap (ell : ℕ) [Fact ell.Prime]
    {E F : PadicAlgCl.FiniteIntermediateField ell} (h : E ≤ F) :
    latticeIntegralRing.{u} ell E ⟶ latticeIntegralRing ell F :=
  ⟨⟨(sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (Profinite.continuousMapRingSheafMap (latticeIntegerInclusion ell h)
        (((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _))⟩⟩

/-- The canonical inclusion of integral coefficients into algebraic closure coefficients.
Source: rational proper-base-change proof (3), original generator
(blueprint: lem-sfb-common-field-lattice-generators). -/
def latticeRationalMap (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) :
    latticeIntegralRing.{u} ell E ⟶ latticeClosureRing ell :=
  ⟨⟨(sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (Profinite.padicIntegersCondensedRingToPadicSubfieldCondensedRing ell E.1) ≫
    Profinite.padicSubfieldRingObjToPadicAlgCl ell E⟩⟩

/-- The canonical degree-zero scalar comparison. Its first arrow is the universal
left-derived counit on the actual single complex; the remaining arrows identify the
homotopy quotient and the ordinary single complex after scalar extension.
Source: rational proper-base-change proof (3); Stacks Tag 06YY
(blueprint: lem-sfb-common-field-lattice-generators). -/
def latticeScalarSingleComparison {A B : ScalarSixRing.{u}} (b : A ⟶ B)
    (Z : Scheme.{u}) (M : ModuleRingedComparison.internalModules A.X Z) :
    (scalarSixChange b Z).obj ((DerivedCategory.singleFunctor _ 0).obj M) ⟶
      (DerivedCategory.singleFunctor _ 0).obj
        ((Mod.extendScalars (coefficientMap (Λ := A.X) (Λ' := B.X) b.hom.hom Z)).obj M) :=
  (Mod.extendScalars
    (coefficientMap (Λ := A.X) (Λ' := B.X) b.hom.hom Z)).leftDerivedFunctorCounit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        ((HomologicalComplex.single _ (.up ℤ) 0).obj M)) ≫
    DerivedCategory.Qh.map
      (((Mod.extendScalars
        (coefficientMap (Λ := A.X) (Λ' := B.X) b.hom.hom Z)).mapHomotopyCategoryFactors
        (.up ℤ)).hom.app ((HomologicalComplex.single _ (.up ℤ) 0).obj M)) ≫
    (DerivedCategory.quotientCompQhIso
      (ModuleRingedComparison.internalModules B.X Z)).hom.app
        (((Mod.extendScalars
          (coefficientMap (Λ := A.X) (Λ' := B.X) b.hom.hom Z)).mapHomologicalComplex (.up ℤ)).obj
            ((HomologicalComplex.single _ (.up ℤ) 0).obj M)) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex
        (Mod.extendScalars (coefficientMap (Λ := A.X) (Λ' := B.X) b.hom.hom Z))
          (.up ℤ) 0).hom.app M)

/-- The integral generator in the ordinary unbounded derived category. Since the
extension is exact, this is the degree-zero complex of the extended lattice.
Source: rational proper-base-change proof (3), notation K and G
(blueprint: lem-sfb-common-field-lattice-generators). -/
def latticeExtendedObject (H : LocallyClosedExtensionData.{u}) (G : ScalarSixGeometry.{u})
    (A : ScalarSixRing.{u}) {k : Type u} [Field k] {Z W : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
    (a : Z ⟶ W) [IsImmersion a.left]
    (L : ModuleRingedComparison.internalModules A.X Z.left) :=
  (scalarSixExtension H G A a).obj ((DerivedCategory.singleFunctor _ 0).obj L)

/-- Normalization of the common-field comparison after restriction to its stratum.
The right side first restricts the original generator, then uses scalar transitivity
and the canonical degree-zero comparison. Full faithfulness of extension by zero
makes this equation determine the comparison uniquely.
Source: rational proper-base-change proof (3), common-field proof step 5
(blueprint: lem-sfb-common-field-lattice-generators). -/
def latticeComparisonNormalized
    (H : LocallyClosedExtensionData.{u}) (D : H.DerivedCoherence)
    (G : ScalarSixGeometry.{u}) (C : ScalarSixPullbackData.{u})
    (ell : ℕ) [Fact ell.Prime] {E F : PadicAlgCl.FiniteIntermediateField ell} (h : E ≤ F)
    {k : Type u} [Field k] {Z W : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
    (a : Z ⟶ W) [IsImmersion a.left]
    (L : ModuleRingedComparison.internalModules (latticeIntegralRing ell E).X Z.left)
    (e : (scalarSixChange (latticeRationalMap ell F) W.left).obj
        (latticeExtendedObject H G (latticeIntegralRing ell F) a
          ((Mod.extendScalars (coefficientMap
            (Λ := (latticeIntegralRing ell E).X) (Λ' := (latticeIntegralRing ell F).X)
            (latticeIntegralMap ell h).hom.hom Z.left)).obj L)) ≅
      (scalarSixChange (latticeRationalMap ell E) W.left).obj
        (latticeExtendedObject H G (latticeIntegralRing ell E) a L)) : Prop :=
  (scalarSixPull (latticeClosureRing ell) a.left).map e.inv ≫
    (C.theta (latticeRationalMap ell F) a.left).inv.app _ ≫
    (scalarSixChange (latticeRationalMap ell F) Z.left).map
      ((scalarSixRestriction H D G (latticeIntegralRing ell F) a).hom.app _) =
  (C.theta (latticeRationalMap ell E) a.left).inv.app _ ≫
    (scalarSixChange (latticeRationalMap ell E) Z.left).map
      ((scalarSixRestriction H D G (latticeIntegralRing ell E) a).hom.app _) ≫
    (scalarSixTower (latticeIntegralMap ell h) (latticeRationalMap ell F)
      Z.left).inv.app _ ≫
    (scalarSixChange (latticeRationalMap ell F) Z.left).map
      (latticeScalarSingleComparison (latticeIntegralMap ell h) Z.left L)

/-- Two algebraic-closure lattice generators admit integral models over one common
finite coefficient field, with the canonically normalized scalar comparisons.

Source: blueprint main-20261015, proper-base-change rational proof, paragraph (3)
(blueprint: lem-sfb-common-field-lattice-generators).

Proof:
1. Take the compositum of the two finite subextensions, finite by
   det-def-sfb-qlbar-condensed-subextensions. Both inclusions preserve the valuation
   inherited from the fixed algebraic closure, hence restrict to continuous integer maps.
2. Pull these continuous-function condensed maps back to the two schemes. Their
   composites to the algebraic closure are the original coefficient inclusions.
3. On each trivializing pro-etale chart, scalar extension sends a finite free module
   to a free module of the same rank. Apply lem-sfb-locally-free-derived-scalars:
   the degree-zero comparison is the derived counit on this K-flat single complex.
4. Apply det-lem-integral-models-generators (3) over the common field. The ambient
   schemes are Noetherian. The normalized factorization comparison of
   lem-sfb-locally-closed-extension-coherence identifies its closed-after-open extension
   with the locally closed extension here, so the extended lattices are bounded
   constructible.
5. Use det-prop-scalar-six-pullback (2) to commute scalar change with extension by
   zero, then the degree-zero comparison of step 3. Apply algebraic-closure scalar
   change to its inverse, followed by scalar transitivity (3). Restricting to the
   stratum gives exactly latticeComparisonNormalized, since both extension comparisons
   restrict to inverse theta and the tower comparison is the scalar-adjunction conjugate.
-/
theorem common_field_lattice_generators
    (ell p : ℕ) [Fact ell.Prime] [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
    (_hne : ell ≠ p)
    (H : LocallyClosedExtensionData.{u}) (_hH : H.Coherent) (D : H.DerivedCoherence)
    (G : ScalarSixGeometry.{u}) (C : ScalarSixPullbackData.{u})
    (W Z : Fin 2 → Over (Spec (.of k)))
    [∀ i : Fin 2, LocallyOfFiniteType (W i).hom]
    [∀ i : Fin 2, QuasiCompact (W i).hom] [∀ i : Fin 2, IsSeparated (W i).hom]
    [∀ i : Fin 2, LocallyOfFiniteType (Z i).hom]
    [∀ i : Fin 2, QuasiCompact (Z i).hom]
    (a : ∀ i : Fin 2, Z i ⟶ W i) [∀ i : Fin 2, IsImmersion (a i).left]
    (E : Fin 2 → PadicAlgCl.FiniteIntermediateField ell)
    (L : ∀ i : Fin 2,
      ModuleRingedComparison.internalModules (latticeIntegralRing ell (E i)).X (Z i).left)
    (hL : ∀ i : Fin 2, IsLisseCoefficientModule
      (latticeIntegralRing ell (E i)).X (L i)) :
    ∃ (F : PadicAlgCl.FiniteIntermediateField ell) (h : ∀ i : Fin 2, E i ≤ F),
      ∀ i : Fin 2,
        IsLisseCoefficientModule (latticeIntegralRing ell F).X
          ((Mod.extendScalars (coefficientMap
            (Λ := (latticeIntegralRing ell (E i)).X) (Λ' := (latticeIntegralRing ell F).X)
            (latticeIntegralMap ell (h i)).hom.hom (Z i).left)).obj (L i)) ∧
        boundedConstructible (condensedRingObj (latticeIntegralRing ell F).X (W i).left)
          (latticeExtendedObject H G (latticeIntegralRing ell F) (a i)
            ((Mod.extendScalars (coefficientMap
              (Λ := (latticeIntegralRing ell (E i)).X) (Λ' := (latticeIntegralRing ell F).X)
              (latticeIntegralMap ell (h i)).hom.hom (Z i).left)).obj (L i))) ∧
        ∃ e : (scalarSixChange (latticeRationalMap ell F) (W i).left).obj
            (latticeExtendedObject H G (latticeIntegralRing ell F) (a i)
              ((Mod.extendScalars (coefficientMap
                (Λ := (latticeIntegralRing ell (E i)).X) (Λ' := (latticeIntegralRing ell F).X)
                (latticeIntegralMap ell (h i)).hom.hom (Z i).left)).obj (L i))) ≅
          (scalarSixChange (latticeRationalMap ell (E i)) (W i).left).obj
            (latticeExtendedObject H G (latticeIntegralRing ell (E i)) (a i) (L i)),
          latticeComparisonNormalized H D G C ell (h i) (a i) (L i) e := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing

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
import Sheaf.SixFunctors.IntegralModelsGenerators
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import Sheaf.SixFunctors.ScalarSixLisseExtensionConstructible
import Sheaf.SixFunctors.ScalarSixLisseTowerComparison

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

open MonoidalCategory MonObj in
private noncomputable def latticeExtendRegularIso {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] :
    (Mod.extendScalars φ).obj (Mod.regular R) ≅ Mod.regular S := by
  let e₀ := Mod.toBimodRegularIso (R := R)
  let B := Bimod.ofMonHom φ
  let e₁ : B.tensorBimod ((Mod.toBimod R).obj (Mod.regular R)) ≅
      B.tensorBimod (Bimod.regular (Mon.mk R)) :=
    { hom := Bimod.whiskerLeft B e₀.hom
      inv := Bimod.whiskerLeft B e₀.inv
      hom_inv_id := by rw [← Bimod.whiskerLeft_comp_bimod, Iso.hom_inv_id];
                       exact Bimod.whiskerLeft_id_bimod
      inv_hom_id := by rw [← Bimod.whiskerLeft_comp_bimod, Iso.inv_hom_id];
                       exact Bimod.whiskerLeft_id_bimod }
  let e := e₁ ≪≫ Bimod.rightUnitorBimod B
  exact Mod.isoMk
    { hom := e.hom.hom
      inv := e.inv.hom
      hom_inv_id := congrArg Bimod.Hom.hom e.hom_inv_id
      inv_hom_id := congrArg Bimod.Hom.hom e.inv_hom_id }
    e.hom.left_act_hom


private theorem latticeFreeExtend {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (hM : Mod.IsFree R M) : Mod.IsFree S ((Mod.extendScalars φ).obj M) := by
  obtain ⟨n, ⟨e⟩⟩ := hM
  exact ⟨n, ⟨(Mod.extendScalars φ).mapIso e ≪≫
    (Mod.extendScalars φ).mapBiproduct (fun _ : Fin n ↦ Mod.regular R) ≪≫
    biproduct.mapIso (fun _ ↦ latticeExtendRegularIso φ)⟩⟩

private theorem latticeLisseExtend
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (b : Λ ⟶ Λ') [IsMonHom b]
    {X : Scheme.{u}} (M : ModuleRingedComparison.internalModules Λ X)
    (hM : IsLisseCoefficientModule Λ M) :
    letI : IsCommMonObj (condensedRingObj Λ X) :=
      Functor.isCommMonObj_obj (F := upperStarFromPoint X)
    letI : IsCommMonObj (condensedRingObj Λ' X) :=
      Functor.isCommMonObj_obj (F := upperStarFromPoint X)
    IsLisseCoefficientModule Λ'
      ((Mod.extendScalars (coefficientMap (Λ := Λ) (Λ' := Λ') b X)).obj M) := by
  have (Y : Scheme.{u}) : IsCommMonObj (condensedRingObj Λ Y) :=
    Functor.isCommMonObj_obj (F := upperStarFromPoint Y)
  have (Y : Scheme.{u}) : IsCommMonObj (condensedRingObj Λ' Y) :=
    Functor.isCommMonObj_obj (F := upperStarFromPoint Y)
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨n, ⟨e⟩⟩ := latticeFreeExtend (coefficientMap (Λ := Λ) (Λ' := Λ') b (U.X i)) (hU i)
  exact ⟨n, ⟨((pullIso b (U.f i)).app M).symm ≪≫ e⟩⟩

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
  obtain ⟨F, h₀, h₁⟩ :=
    (PadicAlgCl.finiteSubextensions_directed ell).2.2.1 (E 0) (E 1)
  have h : ∀ i : Fin 2, E i ≤ F := by
    intro i
    fin_cases i
    · exact h₀
    · exact h₁
  refine ⟨F, h, fun i ↦ ?_⟩
  have hfree := latticeLisseExtend
    (Λ := (latticeIntegralRing ell (E i)).X) (Λ' := (latticeIntegralRing ell F).X)
    (latticeIntegralMap ell (h i)).hom.hom (L i) (hL i)
  refine ⟨hfree, ?_, ?_⟩
  · exact normalized_integral_extension_constructible ell p k _hne H _hH G F
      (W i) (Z i) (a i) _ hfree
  · obtain ⟨e, he⟩ := lisse_generator_normalized_tower
      (latticeIntegralMap ell (h i)) (latticeRationalMap ell F) H _hH D G C
      (W i) (Z i) (a i) (L i) (hL i)
    exact ⟨e, he⟩

end AlgebraicGeometry.ProEtale.CondensedRing

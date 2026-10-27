/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q98
-/
module

public import Sheaf.Paper.TameInertiaScalarMateData
import Sheaf.Paper.TameInertiaDerivedTensorComputation
import Sheaf.Paper.TameInertiaScalarTensorComputation
import Mathlib.Data.ZMod.Basic

/-! # The actual scalar adjunct on continuous tame-inertia invariants

Source: main-20261015, direct-image stability, paragraph (3), finite-coordinate
scalar-mate calculation (blueprint: lem-sfb-tame-inertia-scalar-mate-isomorphism).

All continuous coefficient modules, actions, complexes and comparisons come from the
recorded Koszul interface. Ordinary tensor is the existing coequalizer construction
`Mod.extendScalars`. A total left derived pair is specified by its universal property;
its adjunction is normalized by the actual ordinary scalar unit. Existence of this
structure is concluded, rather than imposed on the representations.

## Main definitions

* `tensor`, `tensorGenerator`: the existing tensor and its pure sections.
* `DerivedTensor`: the universal derived pair with its actual scalar unit.
* `tensorMap`, `mate`, `Computes`: the two actual adjuncts and their comparison.

## Main statement

* `scalar_mate_isomorphism`: the isomorphism with its degreewise multiplication formula.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Profinite.TameInertiaScalarMate

open TameInertiaKoszul

variable (E Ω : Type u) [NormedField E] [NormedField Ω] [Algebra E Ω]
  (h : Continuous (algebraMap E Ω))

variable [(coefficientRestriction E Ω h).Additive]
  [PreservesFiniteLimits (coefficientRestriction E Ω h)]
  [PreservesFiniteColimits (coefficientRestriction E Ω h)]

variable (p ℓ r : ℕ) [ActionAbelianData p r E] [ActionAbelianData p r Ω]
  [Context p r E] [Context p r Ω] [ScalarRestriction E p r Ω h]
  [RestrictionUniversal E p r Ω h]
  (dE : Realization E p ℓ r E) (dΩ : Realization E p ℓ r Ω)
  (m : CoefficientMaps E p ℓ r Ω h dE dΩ)

omit [(coefficientRestriction E Ω h).Additive]
  [PreservesFiniteLimits (coefficientRestriction E Ω h)]
  [PreservesFiniteColimits (coefficientRestriction E Ω h)]
  [RestrictionUniversal E p r Ω h] in
private theorem tensorMap_generator (M : Inputs E p ℓ r) (a : ℤ) (S : Profinite.{u})
    (z : (InternalAbelianSheafModule.sectionRings
      (coherentTopology Profinite.{u}) (ring Ω).X).obj (op S))
    (x : CondensedAction.sectionModule (ring E) ((dE.koszul.obj M).X a) S)
    (I : Indices r a) (t : S) :
    (dΩ.coordinates M a S
      (((((tensorMap E Ω h p ℓ r dE dΩ m M).f a).hom.hom.app (op S)).hom)
        (tensorGenerator E Ω h ((dE.koszul.obj M).X a) S z x)) I).down t =
    z.down t • extension E Ω (fixed E p ℓ r M) ((dE.coordinates M a S x I).down t) := by
  let f := (tensorMap E Ω h p ℓ r dE dΩ m M).f a
  let y : CondensedAction.sectionModule (ring Ω)
      ((tensor E Ω h).obj ((dE.koszul.obj M).X a)) S :=
    (((Mod.extendUnit (coefficientMap E Ω h).hom ((dE.koszul.obj M).X a)).hom.hom.app
      (op S)).hom x)
  have hu := (((Mod.extendRestrictAdjunction
    (coefficientMap E Ω h).hom).mapHomologicalComplex (.up ℤ)).homEquiv _ _).apply_symm_apply
      (m.koszul.app M)
  have hx := congrArg (fun g ↦ (((g.f a).hom.hom.app (op S)).hom x)) hu
  change (f.hom.hom.app (op S)).hom y =
    ((((m.koszul.app M).f a).hom.hom.app (op S)).hom x) at hx
  have hf := (((InternalAbelianSheafModule.sectionModuleFunctor
    (coherentTopology Profinite.{u}) (ring Ω).X).map f).val.app (op S)).hom.map_smul z y
  change (dΩ.coordinates M a S
    ((f.hom.hom.app (op S)).hom
      (show CondensedAction.sectionModule (ring Ω)
        ((tensor E Ω h).obj ((dE.koszul.obj M).X a)) S from z • y)) I).down t = _
  erw [hf]
  rw [dΩ.coordinates_scalar]
  erw [hx]
  exact congrArg (fun v ↦ z.down t • v) (m.koszul_sections M a S x I t)

private theorem derived_transpose (s : DerivedTensor E Ω h)
    (P : HomotopyCategory (CondensedAction.Modules (ring E)) (.up ℤ))
    (V : HomotopyCategory (CondensedAction.Modules (ring Ω)) (.up ℤ))
    (g : P ⟶ ((coefficientRestriction E Ω h).mapHomotopyCategory (.up ℤ)).obj V) :
    (s.adjunction.homEquiv _ _).symm
      (DerivedCategory.Qh.map g ≫
        (coefficientRestriction E Ω h).mapDerivedCategoryFactorsh.inv.app V) =
    s.comparison.app P ≫ DerivedCategory.Qh.map
      ((((Mod.extendRestrictAdjunction
        (coefficientMap E Ω h).hom).mapHomotopyCategory (.up ℤ)).homEquiv _ _).symm g) := by
  let R := coefficientRestriction E Ω h
  let a := (Mod.extendRestrictAdjunction (coefficientMap E Ω h).hom).mapHomotopyCategory (.up ℤ)
  let t := (a.homEquiv _ _).symm g
  apply (s.adjunction.homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit, Functor.map_comp]
  apply (cancel_mono (R.mapDerivedCategoryFactorsh.hom.app V)).1
  have hn := R.mapDerivedCategoryFactorsh.hom.naturality t
  change R.mapDerivedCategory.map (DerivedCategory.Qh.map t) ≫
    R.mapDerivedCategoryFactorsh.hom.app V =
    R.mapDerivedCategoryFactorsh.hom.app _ ≫
      DerivedCategory.Qh.map ((R.mapHomotopyCategory (.up ℤ)).map t) at hn
  dsimp only [R] at hn ⊢
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [hn]
  simp only [← Category.assoc]
  have hu := s.unit P
  simp only [← Category.assoc] at hu
  rw [hu, ← Functor.map_comp]
  have ht := (a.homEquiv _ _).apply_symm_apply g
  rw [Adjunction.homEquiv_unit] at ht
  erw [Category.comp_id]
  exact congrArg DerivedCategory.Qh.map ht.symm

private theorem mate_equation (s : DerivedTensor E Ω h)
    (bE : Comparison E p ℓ r E dE) (bΩ : Comparison E p ℓ r Ω dΩ)
    (hsquare : CoefficientSquare E p ℓ r Ω h dE dΩ bE bΩ m)
    (M : Inputs E p ℓ r) :
    s.functor.map (bE.kappa.hom.app M) ≫ mate E Ω h p ℓ r dE dΩ m s M =
      s.comparison.app ((HomotopyCategory.quotient _ (.up ℤ)).obj (dE.koszul.obj M)) ≫
        DerivedCategory.Q.map (tensorMap E Ω h p ℓ r dE dΩ m M) ≫ bΩ.kappa.hom.app M := by
  let P := dE.koszul.obj M
  let V := dΩ.koszul.obj M
  let R := coefficientRestriction E Ω h
  have ht := derived_transpose E Ω h s
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
    ((HomotopyCategory.quotient _ (.up ℤ)).obj V)
    ((HomotopyCategory.quotient _ (.up ℤ)).map (m.koszul.app M))
  have hfactor : R.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj V) =
      R.mapDerivedCategoryFactors.hom.app V := by
    rw [R.mapDerivedCategoryFactorsh_hom_app]
    simp only [DerivedCategory.quotientCompQhIso,
      HomologicalComplexUpToQuasiIso.quotientCompQhIso,
      Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_hom,
      Quotient.lift.isLift_inv]
    erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.id_comp, Category.comp_id]
  have hfactorInv : R.mapDerivedCategoryFactorsh.inv.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj V) =
      R.mapDerivedCategoryFactors.inv.app V := by
    apply (cancel_mono (R.mapDerivedCategoryFactors.hom.app V)).1
    rw [← hfactor]
    rw [Iso.inv_hom_id_app, hfactor, Iso.inv_hom_id_app]
    rfl
  have ht' : (s.adjunction.homEquiv _ _).symm
      (DerivedCategory.Q.map (m.koszul.app M) ≫ R.mapDerivedCategoryFactors.inv.app V) =
      s.comparison.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map (tensorMap E Ω h p ℓ r dE dΩ m M) := by
    convert ht using 1
    · congr 1
      rw [hfactorInv]
      rfl
    · congr 1
      rw [Adjunction.homEquiv_counit,
        Adjunction.mapHomotopyCategory_counit_app_quotient]
      rfl
  rw [mate, ← Adjunction.homEquiv_naturality_left_symm, hsquare M]
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right_symm]
  erw [ht']
  exact Category.assoc _ _ _

/-- Invertibility and the explicit representative of the actual adjunct, for every
admissible representation and every profinite test space. The localized chain map
is preceded by the canonical derived-tensor comparison, including the quotient/Qh
transport. Its invertibility asserts that this Koszul representative computes derived
tensor. Multiplication is stated on every balanced tensor generator, in every subset
coordinate, and includes the scalar unit z=1.
Source: the conclusion and its more precise clause
(blueprint: lem-sfb-tame-inertia-scalar-mate-isomorphism). -/
def Computes (s : DerivedTensor E Ω h)
    (bE : Comparison E p ℓ r E dE) (bΩ : Comparison E p ℓ r Ω dΩ) : Prop :=
  ∀ M : Inputs E p ℓ r,
    IsIso (mate E Ω h p ℓ r dE dΩ m s M) ∧
    IsIso (tensorMap E Ω h p ℓ r dE dΩ m M) ∧
    IsIso (s.comparison.app ((HomotopyCategory.quotient _ (.up ℤ)).obj
      (dE.koszul.obj M))) ∧
    (s.functor.map (bE.kappa.hom.app M) ≫ mate E Ω h p ℓ r dE dΩ m s M =
      s.functor.map ((DerivedCategory.quotientCompQhIso _).hom.app (dE.koszul.obj M)) ≫
      s.comparison.app ((HomotopyCategory.quotient _ (.up ℤ)).obj (dE.koszul.obj M)) ≫
      DerivedCategory.Qh.map
        (((tensor E Ω h).mapHomotopyCategoryFactors (.up ℤ)).hom.app (dE.koszul.obj M)) ≫
      (DerivedCategory.quotientCompQhIso _).inv.app
        (((tensor E Ω h).mapHomologicalComplex (.up ℤ)).obj (dE.koszul.obj M)) ≫
      DerivedCategory.Q.map (tensorMap E Ω h p ℓ r dE dΩ m M) ≫ bΩ.kappa.hom.app M) ∧
    (∀ (a : ℤ) (S : Profinite.{u})
      (z : (InternalAbelianSheafModule.sectionRings
        (coherentTopology Profinite.{u}) (ring Ω).X).obj (op S))
      (x : CondensedAction.sectionModule (ring E) ((dE.koszul.obj M).X a) S)
      (I : Indices r a) (t : S),
      (dΩ.coordinates M a S
        (((((tensorMap E Ω h p ℓ r dE dΩ m M).f a).hom.hom.app (op S)).hom)
          (tensorGenerator E Ω h ((dE.koszul.obj M).X a) S z x)) I).down t =
      z.down t • extension E Ω (fixed E p ℓ r M) ((dE.coordinates M a S x I).down t))

end Profinite.TameInertiaScalarMate

/-- The unit-normalized derived scalar mate on all-continuous tame-inertia invariants
is invertible and is represented by scalar multiplication on the finite Koszul complex.
The normalized realizations and scalar derived pair are conclusions, so no extra
hypothesis on M, the field inclusion, or its flatness is assumed. The index r is any
natural number, and `Inputs` includes representations with zero fixed submodule.

Source: main-20261015, direct-image stability, paragraph (3), finite-coordinate
scalar-mate calculation (blueprint: lem-sfb-tame-inertia-scalar-mate-isomorphism).

Proof:
1. For N=M^H use the finite averaging projector and an E-basis of N. The specified
finite-dimensional product topology identifies F tensor_E N with F^d. All continuous
sections therefore identify N_F with C_F^d, compatibly with restriction and scalars.
Each Koszul term is finite free, indexed by pairs (I,j), including the empty basis.
2. Apply the recorded internal/sectionwise module equivalence. Tensoring with a finite
free sheaf is a finite direct sum, by the inverse maps x tensor (a_j) to (a_j x)
and (x_j) to sum x_j tensor e_j. Thus its terms are flat. The complex vanishes outside
[0,r], so Stacks 06YQ makes it K-flat. The normalized derived scalar adjunction of
lem-pur-sheaf-ring-derived-coefficient-adjunction transports to these internal modules;
its ordinary tensor is the existing `Mod.extendScalars` coequalizer by adjoint uniqueness.
Its canonical comparison is invertible on this flat-term K-flat representative.
3. The ordinary tensor adjunct of the coefficient inclusion sends z tensor (x_I) to
(z x_I). In basis coordinates its inverse sends (y_{I,j}) to sum y_{I,j} tensor e_{I,j}.
Balancing proves both inverse identities. The differential matrices have E entries,
so multiplication commutes with the identical alternating deletion differential.
This proves the chain map is invertible and gives the displayed section formula.
4. Apply the normalized Koszul comparison (its auxiliary characteristic-p field can
be F_p). Its coefficient square identifies the actual invariant coefficient map with
the termwise inclusion x to 1 tensor x. The scalar adjunction's unit normalization
identifies the adjunct of this inclusion with the class of the map in step 3,
preceded by the canonical derived-tensor computation comparison.
5. Naturality of the Hom bijection gives T(kappa_E) followed by sigma equal to that
comparison followed by Q(t) and kappa_Omega. All these comparison maps are invertible,
so sigma is invertible. The equality retains the actual unit. For r=0 there is one
term and ordinary scalar multiplication; for N=0 all terms are zero. No completion
or restriction to locally constant sections is used.
-/
theorem Profinite.TameInertiaScalarMate.scalar_mate_isomorphism
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (_distinct : p ≠ ℓ)
    (Ω : Type u) [NormedField Ω] [NormedAlgebra ℚ_[ℓ] Ω]
    [IsAlgClosure ℚ_[ℓ] Ω] (E : IntermediateField ℚ_[ℓ] Ω)
    [FiniteDimensional ℚ_[ℓ] E] (r : ℕ) :
    ∃ d : Profinite.TameInertiaKoszul.Result E p ℓ r Ω continuous_subtype_val,
      letI := d.abelianE
      letI := d.abelianΩ
      letI := d.contextE
      letI := d.contextΩ
      letI := d.restriction
      letI := d.restrictionUniversal
      ∃ s : Profinite.TameInertiaScalarMate.DerivedTensor E Ω continuous_subtype_val,
        Profinite.TameInertiaScalarMate.Computes E Ω continuous_subtype_val p ℓ r
          d.modelE d.modelΩ d.maps s d.comparisonE d.comparisonΩ := by
  classical
  obtain ⟨d⟩ := Profinite.TameInertiaKoszul.continuous_koszul p ℓ _distinct
    (ZMod p) Ω E r
  let := d.abelianE
  let := d.abelianΩ
  let := d.contextE
  let := d.contextΩ
  let := d.restriction
  let := d.restrictionUniversal
  obtain ⟨s, hs⟩ := Profinite.TameInertiaScalarMate.derived_tensor_computation
    E Ω continuous_subtype_val p ℓ r d.modelE
  refine ⟨d, s, ?_⟩
  intro M
  let := hs M
  let := Profinite.TameInertiaScalarMate.scalar_tensor_computation
    E Ω continuous_subtype_val p ℓ r d.modelE d.modelΩ d.maps M
  have he := Profinite.TameInertiaScalarMate.mate_equation
    E Ω continuous_subtype_val p ℓ r d.modelE d.modelΩ d.maps s
    d.comparisonE d.comparisonΩ d.coefficientSquare M
  have : IsIso (s.functor.map (d.comparisonE.kappa.hom.app M) ≫
      Profinite.TameInertiaScalarMate.mate E Ω continuous_subtype_val p ℓ r
        d.modelE d.modelΩ d.maps s M) := by
    rw [he]
    infer_instance
  have := IsIso.of_isIso_comp_left (s.functor.map (d.comparisonE.kappa.hom.app M))
    (Profinite.TameInertiaScalarMate.mate E Ω continuous_subtype_val p ℓ r
      d.modelE d.modelΩ d.maps s M)
  refine ⟨inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · simp only [DerivedCategory.quotientCompQhIso,
      HomologicalComplexUpToQuasiIso.quotientCompQhIso,
      Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_hom,
      Quotient.lift.isLift_inv]
    erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.id_comp, Category.id_comp]
    exact he
  · exact Profinite.TameInertiaScalarMate.tensorMap_generator
      E Ω continuous_subtype_val p ℓ r d.modelE d.modelΩ d.maps M

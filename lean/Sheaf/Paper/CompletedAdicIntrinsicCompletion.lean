/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q39
-/
module

public import Sheaf.Paper.CompletedAdicCoefficientDatum
public import Sheaf.Paper.IntrinsicKoszulCompletion
public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import WeilConjectures.AlgebraicGeometry.KoszulDifferential
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
/-! # Intrinsic Koszul completion over the completed coefficient sheaf

Source: blueprint, sec-proper-base-change/sk-thm-properbasechange,
node def-weil-pbc-intrinsic-completion; Stacks Tag 099M
(blueprint: def-weil-pbc-intrinsic-completion).

Koszul complexes are obtained by scalar extension of the recorded exterior-algebra
construction along the residue-normalized map from the constant ring to A_T. All tensor
products, products and mapping fibres below are in modules over A_T.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe t

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme

variable {A : Type t} [CommRing A]

/-- The scalar map to the completed ring is uniquely fixed by all its residue sections.
Source: blueprint, def-weil-pbc-intrinsic-completion, the action of the generators
(blueprint: def-weil-pbc-intrinsic-completion).
Proof: for each positive quotient use the residue homomorphism followed by the constant
sections of its continuous-functions presheaf and sheafification. These maps commute with
quotient transitions. The limit property gives a unique map of ring sheaves, and it is
commutative because both rings are commutative. Maps out of a constant sheaf are fixed by
their constant presheaf sections, so the displayed equation characterizes it uniquely. -/
theorem completedAdicScalar_exists (T : Scheme.{t}) (d : AdicCoefficientDatum A) :
    ∃! α : adicConstantRing T A ⟶ completedAdicCommRing T d,
      ∀ (n : ℕ) (U : T.ProEtᵒᵖ) (a : ULift.{t + 1} A),
        (completedAdicProjection T d n).hom.app U
          (((sheafCompose (ProEt.topology T)
            (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map α).hom.app U
            ((koszulConstantUnit T A).app U a)) =
        (ProEtale.finiteCoefficientScalarMap T (completedAdicQuotient d n)).app U
          (ULift.up (Ideal.Quotient.mk (d.ideal ^ (n + 1)) a.down)) := by
  let J := ProEt.topology T
  let F := (Functor.const T.ProEtᵒᵖ).obj (RingCat.of (ULift.{t + 1} A))
  let D := completedAdicRingSystem T d
  let E := sheafToPresheaf J RingCat.{t + 1}
  let q (n : ℕ) : ULift.{t + 1} A →+* completedAdicQuotient d n :=
    RingHom.ulift (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
  let σ (n : ℕ) : F ⟶ (completedAdicFiniteRing T d n).obj :=
    (Functor.const T.ProEtᵒᵖ).map (RingCat.ofHom (q n)) ≫
      ProEtale.finiteCoefficientScalarMap T (completedAdicQuotient d n)
  have hσ (n : ℕ) : σ (n + 1) ≫ (completedAdicFiniteStep T d n).hom = σ n := by
    ext U a
    have hs := congrArg
      (fun k ↦ (k.app U).hom
        ((ProEtale.finiteCoefficientConstants T
          (completedAdicQuotient d (n + 1))).app U (q (n + 1) a)))
      (toSheafify_naturality J (completedAdicFinitePresheafStep T d n))
    have hc : (completedAdicFinitePresheafStep T d n).app U
        ((ProEtale.finiteCoefficientConstants T
          (completedAdicQuotient d (n + 1))).app U (q (n + 1) a)) =
      (ProEtale.finiteCoefficientConstants T
        (completedAdicQuotient d n)).app U (q n a) := by
      apply ContinuousMap.ext
      intro x
      rfl
    simp only [NatTrans.comp_app, RingCat.comp_apply] at hs
    rw [hc] at hs
    exact hs.symm
  let c : Cone (D ⋙ E) :=
    { pt := F
      π := NatTrans.ofOpSequence σ (fun n ↦ by
        dsimp only [Functor.const_obj_map, Functor.comp_map, D, E,
          completedAdicRingSystem]
        rw [Functor.ofOpSequence_map_homOfLE_succ]
        change 𝟙 F ≫ σ n = σ (n + 1) ≫ (completedAdicFiniteStep T d n).hom
        simpa only [Category.id_comp] using (hσ n).symm) }
  let L := isLimitOfPreserves E (limit.isLimit D)
  let β : F ⟶ (completedAdicRing T d).obj := L.lift c
  let F' := (Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{t + 1} A))
  let β' : F' ⟶ (completedAdicCommRing T d).obj :=
    { app := fun U ↦
        letI := completedAdicCommRingStructure T d U
        CommRingCat.ofHom (β.app U).hom
      naturality := fun U V f ↦ (forget₂ CommRingCat RingCat).map_injective
        (β.naturality f) }
  let α : adicConstantRing T A ⟶ completedAdicCommRing T d :=
    ((sheafificationAdjunction J CommRingCat.{t + 1}).homEquiv F'
      (completedAdicCommRing T d)).symm β'
  have hα : toSheafify J F' ≫ α.hom = β' :=
    ((sheafificationAdjunction J CommRingCat.{t + 1}).homEquiv F'
      (completedAdicCommRing T d)).apply_symm_apply β'
  have hnorm (n : ℕ) (U : T.ProEtᵒᵖ) (a : ULift.{t + 1} A) :
      (completedAdicProjection T d n).hom.app U
        (((sheafCompose J (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map α).hom.app U
          ((koszulConstantUnit T A).app U a)) =
        (ProEtale.finiteCoefficientScalarMap T (completedAdicQuotient d n)).app U
          (q n a) := by
    have ha := congrArg (fun k : F' ⟶ (completedAdicCommRing T d).obj ↦
      (k.app U).hom a) hα
    change (α.hom.app U).hom ((toSheafify J F').app U a) = (β.app U).hom a at ha
    change (completedAdicProjection T d n).hom.app U
      ((α.hom.app U).hom ((toSheafify J F').app U a)) = _
    rw [ha]
    exact congrArg (fun k : F ⟶ (completedAdicFiniteRing T d n).obj ↦
      (k.app U).hom a) (L.fac c (op n))
  refine ⟨α, hnorm, ?_⟩
  intro ψ hψ
  have htest : toSheafify J F' ≫ ψ.hom = β' := by
    apply ((Functor.whiskeringRight T.ProEtᵒᵖ CommRingCat RingCat).obj
      (forget₂ CommRingCat RingCat)).map_injective
    change Functor.whiskerRight (toSheafify J F' ≫ ψ.hom)
      (forget₂ CommRingCat RingCat) = β
    apply L.hom_ext
    intro j
    rw [L.fac c j]
    ext U a
    exact hψ j.unop U a
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ (completedAdicCommRing T d).property
  exact htest.trans hα.symm

/-- The actual scalar map, with its unique residue normalization.
Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: def-weil-pbc-intrinsic-completion). -/
def completedAdicScalar (T : Scheme.{t}) (d : AdicCoefficientDatum A) :
    adicConstantRing T A ⟶ completedAdicCommRing T d :=
  (completedAdicScalar_exists T d).exists.choose

set_option linter.defProp false in
/-- The scalar-extension witness with its object and morphism tensor formulas.
Source: blueprint def-weil-pbc-intrinsic-completion; Stacks Tag 06YY
(blueprint: def-weil-pbc-intrinsic-completion). -/
def completedAdicScalarExtensionData (T : Scheme.{t}) (d : AdicCoefficientDatum A) :=
  completedAdicChangeData T (completedAdicScalar T d)

/-- Ordinary scalar extension of constant A-module sheaves to A_T-module sheaves.
Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: def-weil-pbc-intrinsic-completion). -/
def completedAdicScalarExtension (T : Scheme.{t}) (d : AdicCoefficientDatum A) :
    SheafOfModules.{t + 1} (adicModuleRing T A) ⥤ CompletedAdicModules T d :=
  completedAdicChange T (completedAdicScalar T d)

/-- Scalar extension is additive, from the normalized change-of-rings witness.
Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: def-weil-pbc-intrinsic-completion). -/
instance completedAdicScalarExtension_additive (T : Scheme.{t}) (d : AdicCoefficientDatum A) :
    (completedAdicScalarExtension T d).Additive :=
  (completedAdicScalarExtensionData T d).choose_spec.choose_spec.choose_spec.choose

/-- The sheafified tensor generator in scalar extension. The equality transport is the
object formula of the scalar-extension witness, not a freely chosen identification.
Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: def-weil-pbc-intrinsic-completion). -/
def completedAdicScalarTensor (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (M : SheafOfModules.{t + 1} (adicModuleRing T A)) (U : T.ProEtᵒᵖ)
    (s : (completedAdicCommRing T d).obj.obj U) (x : M.val.obj U) :
    ((completedAdicScalarExtension T d).obj M).val.obj U :=
  (eqToHom ((completedAdicScalarExtensionData T d).choose_spec.choose M).symm).val.app U
    ((toSheafify (ProEt.topology T)
      (SheafOfModules.changeOfRingsPresheaf (completedAdicScalar T d) M).presheaf).app U
        (s ⊗ₜ[(adicConstantRing T A).obj.obj U,
          ((completedAdicScalar T d).hom.app U).hom] x))

/-- The Koszul complex of a_1^(m+1),...,a_r^(m+1) over A_T, in degrees [-r,0].
It is the recorded constant exterior complex followed by actual extension of scalars.
Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: def-weil-pbc-intrinsic-completion). -/
def completedAdicKoszul (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (m : ℕ) : CochainComplex (CompletedAdicModules T d) ℤ :=
  ((completedAdicScalarExtension T d).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (koszulPowerSheaf T A r a m)

/-- The inverse Koszul transition: multiplication by a_j in degree -1 of each factor,
identity in degree zero. Extension of scalars preserves the recorded exterior map.
Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: def-weil-pbc-intrinsic-completion). -/
def completedAdicKoszulStep (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (m : ℕ) :
    completedAdicKoszul T d r a (m + 1) ⟶ completedAdicKoszul T d r a m :=
  letI := koszulConstantFunctor_preservesZero T A
  ((completedAdicScalarExtension T d).mapHomologicalComplex (ComplexShape.up ℤ)).map
    (((koszulConstantFunctor T A).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (koszulPowerTransition A r a m))

/-- The degree-zero unit is determined by the tensor of the two scalar units.
Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: def-weil-pbc-intrinsic-completion).
Proof: the displayed section is compatible with restrictions since both its factors are.
The unit-module/global-section equivalence gives the unique module map with that value on
one. In degree zero the constant Koszul unit identifies the rank-one module with degree
zero, and extension of scalars preserves this identification. -/
theorem completedAdicKoszulUnitZero_exists (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (m : ℕ) :
    ∃! u : SheafOfModules.unit (completedAdicRing T d) ⟶ (completedAdicKoszul T d r a m).X 0,
      ∀ U : T.ProEtᵒᵖ, u.val.app U (1 : (completedAdicRing T d).obj.obj U) =
        completedAdicScalarTensor T d _ U 1
          ((koszulSheafUnitZero T A r a m).val.app U
            (1 : (adicModuleRing T A).obj.obj U)) := by
  sorry

/-- The specified degree-zero inclusion A_T[0] to its Koszul complex.
Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: def-weil-pbc-intrinsic-completion). -/
def completedAdicKoszulUnitZero (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (m : ℕ) :
    SheafOfModules.unit (completedAdicRing T d) ⟶ (completedAdicKoszul T d r a m).X 0 :=
  (completedAdicKoszulUnitZero_exists T d r a m).exists.choose

/-- The total tensor C tensor Q_(m+1) over the completed ring.
Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: def-weil-pbc-intrinsic-completion). -/
def completedAdicKoszulTensor (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (C : CochainComplex (CompletedAdicModules T d) ℤ) (m : ℕ) :=
  letI := SheafOfModules.monoidalCategory (completedAdicCommRing T d)
  letI : (curriedTensor (CompletedAdicModules T d)).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
      (completedAdicCommRing T d)
  letI : ∀ M : CompletedAdicModules T d,
      ((curriedTensor (CompletedAdicModules T d)).obj M).PreservesZeroMorphisms :=
    fun M ↦ SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
      (completedAdicCommRing T d) M
  CochainComplex.mapBifunctor C (completedAdicKoszul T d r a m) (curriedTensor _)

/-- The tensor transition 1_C tensor q_(m+2,m+1).
Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: def-weil-pbc-intrinsic-completion). -/
def completedAdicKoszulTensorStep (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (C : CochainComplex (CompletedAdicModules T d) ℤ) (m : ℕ) :
    completedAdicKoszulTensor T d r a C (m + 1) ⟶ completedAdicKoszulTensor T d r a C m :=
  letI := SheafOfModules.monoidalCategory (completedAdicCommRing T d)
  letI : (curriedTensor (CompletedAdicModules T d)).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
      (completedAdicCommRing T d)
  letI : ∀ M : CompletedAdicModules T d,
      ((curriedTensor (CompletedAdicModules T d)).obj M).PreservesZeroMorphisms :=
    fun M ↦ SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
      (completedAdicCommRing T d) M
  HomologicalComplex.mapBifunctorMap (𝟙 C) (completedAdicKoszulStep T d r a m)
    (curriedTensor _) (ComplexShape.up ℤ)

/-- In degree p the unit sends c to c tensor 1 in the (p,0) total summand.
Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: def-weil-pbc-intrinsic-completion). -/
def completedAdicKoszulTensorUnitF (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (C : CochainComplex (CompletedAdicModules T d) ℤ) (m : ℕ) (p : ℤ) :
    C.X p ⟶ (completedAdicKoszulTensor T d r a C m).X p :=
  letI := SheafOfModules.monoidalCategory (completedAdicCommRing T d)
  letI : (curriedTensor (CompletedAdicModules T d)).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
      (completedAdicCommRing T d)
  letI : ∀ M : CompletedAdicModules T d,
      ((curriedTensor (CompletedAdicModules T d)).obj M).PreservesZeroMorphisms :=
    fun M ↦ SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
      (completedAdicCommRing T d) M
  (ρ_ (C.X p)).inv ≫ (C.X p ◁ completedAdicKoszulUnitZero T d r a m) ≫
    HomologicalComplex.ιMapBifunctor C (completedAdicKoszul T d r a m) (curriedTensor _)
      (ComplexShape.up ℤ) p 0 p (add_zero p)

/-- The tensor units are chain maps.
Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: def-weil-pbc-intrinsic-completion).
Proof: the differential of the Koszul degree-zero unit is zero, since the complex has no
positive degrees. The total differential on c tensor 1 is therefore dc tensor 1; naturality
of the right unit isomorphism gives the displayed chain-map identity. -/
theorem completedAdicKoszulTensorUnitF_comm (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (C : CochainComplex (CompletedAdicModules T d) ℤ)
    (m : ℕ) (p q : ℤ) (_hpq : (ComplexShape.up ℤ).Rel p q) :
    completedAdicKoszulTensorUnitF T d r a C m p ≫
        (completedAdicKoszulTensor T d r a C m).d p q =
      C.d p q ≫ completedAdicKoszulTensorUnitF T d r a C m q := by
  sorry

/-- The actual chain map c ↦ c tensor 1 to each Koszul tensor complex.
Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: def-weil-pbc-intrinsic-completion). -/
def completedAdicKoszulTensorUnit (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (C : CochainComplex (CompletedAdicModules T d) ℤ) (m : ℕ) :
    C ⟶ completedAdicKoszulTensor T d r a C m where
  f := completedAdicKoszulTensorUnitF T d r a C m
  comm' := completedAdicKoszulTensorUnitF_comm T d r a C m

/-- The termwise product B(C) of the positive-power Koszul tensor complexes.
Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: def-weil-pbc-intrinsic-completion). -/
def completedAdicKoszulProduct (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (C : CochainComplex (CompletedAdicModules T d) ℤ) :=
  ∏ᶜ (completedAdicKoszulTensor T d r a C)

/-- The chain map 1-s with coordinates z_m - t_m(z_(m+1)).
Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: def-weil-pbc-intrinsic-completion). -/
def completedAdicKoszulOneSubShift (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (C : CochainComplex (CompletedAdicModules T d) ℤ) :
    completedAdicKoszulProduct T d r a C ⟶ completedAdicKoszulProduct T d r a C :=
  𝟙 _ - Pi.lift (fun m ↦ Pi.π (completedAdicKoszulTensor T d r a C) (m + 1) ≫
    completedAdicKoszulTensorStep T d r a C m)

/-- The mapping fibre with degree i terms B^i and B^(i-1). Taking the cone of -(1-s)
and shifting by -1 gives exactly the differential (dx,(1-s)x-dy), under the canonical
index isomorphisms of the shift. Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: def-weil-pbc-intrinsic-completion). -/
def completedAdicKoszulFibre (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (C : CochainComplex (CompletedAdicModules T d) ℤ) :
    CochainComplex (CompletedAdicModules T d) ℤ :=
  (CochainComplex.mappingCone (-completedAdicKoszulOneSubShift T d r a C))⟦(-1 : ℤ)⟧

/-- The compatible tensor units form the map u_C to B(C).
Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: def-weil-pbc-intrinsic-completion). -/
def completedAdicKoszulProductUnit (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (C : CochainComplex (CompletedAdicModules T d) ℤ) :
    C ⟶ completedAdicKoszulProduct T d r a C :=
  Pi.lift (completedAdicKoszulTensorUnit T d r a C)

/-- The completion unit c ↦ (u_C(c),0) commutes with the fibre differential.
Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: def-weil-pbc-intrinsic-completion).
Proof: the transition on each degree-zero Koszul unit is identity, so (1-s)u_C=0.
The first coordinate of the fibre differential is d_B u_C=u_C d_C and the second
coordinate is zero. Thus inclusion in the first summand is a chain map. -/
theorem completedAdicKoszulUnitF_comm (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (C : CochainComplex (CompletedAdicModules T d) ℤ)
    (p q : ℤ) (_hpq : (ComplexShape.up ℤ).Rel p q) :
    ((completedAdicKoszulProductUnit T d r a C).f p ≫
      HomologicalComplex.homotopyCofiber.inlX (-completedAdicKoszulOneSubShift T d r a C)
        p (p + (-1)) (by change p + (-1) + 1 = p; omega)) ≫
        (completedAdicKoszulFibre T d r a C).d p q =
      C.d p q ≫ (completedAdicKoszulProductUnit T d r a C).f q ≫
        HomologicalComplex.homotopyCofiber.inlX (-completedAdicKoszulOneSubShift T d r a C)
          q (q + (-1)) (by change q + (-1) + 1 = q; omega) := by
  sorry

/-- The specified chain-level completion unit into the explicit mapping fibre.
Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: def-weil-pbc-intrinsic-completion). -/
def completedAdicKoszulUnitComplex (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (C : CochainComplex (CompletedAdicModules T d) ℤ) :
    C ⟶ completedAdicKoszulFibre T d r a C where
  f p := (completedAdicKoszulProductUnit T d r a C).f p ≫
    HomologicalComplex.homotopyCofiber.inlX (-completedAdicKoszulOneSubShift T d r a C)
      p (p + (-1)) (by change p + (-1) + 1 = p; omega)
  comm' := completedAdicKoszulUnitF_comm T d r a C

/-- The Koszul completion of a derived object, using the localization's representative.
No K-flatness or boundedness restriction on that representative is needed: the finite free
Koszul factors preserve quasi-isomorphisms, and exact products compute derived products.
Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: def-weil-pbc-intrinsic-completion). -/
def completedAdicIntrinsicCompletion (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (K : DerivedCategory (CompletedAdicModules T d)) :
    DerivedCategory (CompletedAdicModules T d) :=
  DerivedCategory.Q.obj
    (completedAdicKoszulFibre T d r a (DerivedCategory.Q.objPreimage K))

/-- The image of c ↦ (u_C(c),0), transported along the localization representative iso.
Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: def-weil-pbc-intrinsic-completion). -/
def completedAdicIntrinsicUnit (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (K : DerivedCategory (CompletedAdicModules T d)) :
    K ⟶ completedAdicIntrinsicCompletion T d r a K :=
  (DerivedCategory.Q.objObjPreimageIso K).inv ≫
    DerivedCategory.Q.map
      (completedAdicKoszulUnitComplex T d r a (DerivedCategory.Q.objPreimage K))

/-- Derived I-completeness is invertibility of the specified Koszul completion map.
The generator equation is supplied when this predicate is used for the ideal of d.
Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: def-weil-pbc-intrinsic-completion). -/
def IsCompletedAdicDerivedComplete (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (_ha : Ideal.span (Set.range a) = d.ideal)
    (K : DerivedCategory (CompletedAdicModules T d)) : Prop :=
  IsIso (completedAdicIntrinsicUnit T d r a K)

/-- The explicit completion and its unit are independent of the complex representative.
Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: def-weil-pbc-intrinsic-completion).
Proof: the Koszul factors are bounded finite free complexes, so total tensor with them
preserves quasi-isomorphisms. Exact countable products on the pro-etale site
(lem-weil-proetale-countable-products-exact) preserve their levelwise quasi-isomorphisms;
the resulting maps of mapping fibres are quasi-isomorphisms by the cone triangle.
The tensor units commute with all these maps. Localization therefore gives the asserted
unit-compatible isomorphism for any representative and its identification with K. -/
theorem completedAdicIntrinsicCompletion_comparison (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (K : DerivedCategory (CompletedAdicModules T d))
    (C : CochainComplex (CompletedAdicModules T d) ℤ) (e : DerivedCategory.Q.obj C ≅ K) :
    ∃ j : DerivedCategory.Q.obj (completedAdicKoszulFibre T d r a C) ≅
        completedAdicIntrinsicCompletion T d r a K,
      DerivedCategory.Q.map (completedAdicKoszulUnitComplex T d r a C) ≫ j.hom =
        e.hom ≫ completedAdicIntrinsicUnit T d r a K := by
  sorry

end AlgebraicGeometry.Scheme

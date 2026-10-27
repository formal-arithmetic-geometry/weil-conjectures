/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q108
-/
module

public import Sheaf.Paper.NormalGenericLisseCocycle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.GaloisAction

import Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import Sheaf.AlgebraicGeometry.CoefficientSectionsLocalization

/-! # Generic scalar comparison for all-continuous lisse coefficients

Source: Bhatt--Scholze, Lemma 7.4.7, pp. 70--71; the agent tensor/descent
calculation for arbitrary nonarchimedean normed fields, with their full norm topology.
(blueprint: lem-sfb-generic-lisse-scalar-comparison).

The fibre and its Galois maps are the published actual generic sections. Scalar
multiplication is the published constant action; only its laws are postponed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.ProEtale
namespace GenericLisseScalar

variable {A B : Type u} [NormedField A] [NormedField B]

/-- Extension preserves lisseness, including rank zero.
Source: Bhatt--Scholze 7.4.7, DAG steps 1--2
(blueprint: lem-sfb-generic-lisse-scalar-comparison).
Proof: inverse image preserves the tensor coequalizer and the coefficient comparison
identifies its two arrows (det-pe-topos-functoriality-inverse-image,
lem-sfb-finite-upper-star-tensor, sk-def-sfb-pullback-from-point-comp).
On each trivializing slice, lem-sfb-ringed-site-free-matrix-scalar-extension identifies
extension of r copies of the regular module with r copies, also for r=0.
The same cover therefore witnesses IsLisseCoefficientModule. -/
theorem extension_lisse (X : Scheme.{u}) (φ : A →+* B) (hφ : Continuous φ)
    (L : NormContinuousLisse A X) :
    IsLisseCoefficientModule (normContinuousRing B).X
      ((normContinuousExtension X φ hφ).obj L.obj) := by
  sorry

/-- The restriction of the actual internal scalar-extension functor to lisse modules.
Source: Bhatt--Scholze 7.4.7, DAG steps 1--2
(blueprint: lem-sfb-generic-lisse-scalar-comparison). -/
def extension (X : Scheme.{u}) (φ : A →+* B) (hφ : Continuous φ) :
    NormContinuousLisse A X ⥤ NormContinuousLisse B X :=
  { obj := fun L ↦ ⟨(normContinuousExtension X φ hφ).obj L.obj,
      extension_lisse X φ hφ L⟩
    map := fun f ↦ ObjectProperty.homMk ((normContinuousExtension X φ hφ).map f.hom)
    map_id := fun L ↦ congrArg ObjectProperty.homMk
      ((normContinuousExtension X φ hφ).map_id L.obj)
    map_comp := fun f g ↦ congrArg ObjectProperty.homMk
      ((normContinuousExtension X φ hφ).map_comp f.hom g.hom) }

/-- Pullback on underlying abelian sheaves, allowing different coefficients.
Source: Bhatt--Scholze 7.4.7 (blueprint: lem-sfb-generic-lisse-scalar-comparison). -/
def pullUnderlying
    {Λ Γ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Γ] [IsCommMonObj Γ]
    {T X : Scheme.{u}} (f : T ⟶ X)
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Γ X))
    (t : L.X ⟶ M.X) :
    ((CondensedRing.upperStar Λ f).obj L).X ⟶
      ((CondensedRing.upperStar Γ f).obj M).X :=
  (CondensedRing.upperStarObjXIso Λ f L).hom ≫
    (upperStar Ab.{u + 1} f).map t ≫
    (CondensedRing.upperStarObjXIso Γ f M).inv

/-- Ordinary extension unit on abelian sheaves.
Source: Bhatt--Scholze 7.4.7
(blueprint: lem-sfb-generic-lisse-scalar-comparison). -/
def baseUnit (X : Scheme.{u}) (φ : A →+* B) (hφ : Continuous φ)
    (L : NormContinuousLisse A X) :
    L.obj.X ⟶ ((normContinuousExtension X φ hφ).obj L.obj).X :=
  Mod.extendUnitHom (normContinuousCoefficientMap X φ hφ) L.obj

/-- The specialized unit.
Source: Bhatt--Scholze 7.4.7 (blueprint: lem-sfb-generic-lisse-scalar-comparison). -/
abbrev chartUnit {T X : Scheme.{u}} (f : T ⟶ X) (φ : A →+* B) (hφ : Continuous φ)
    (L : NormContinuousLisse A X) :=
  pullUnderlying f L.obj ((normContinuousExtension X φ hφ).obj L.obj)
    (baseUnit X φ hφ L)


section Charts

variable {Λ Γ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Γ] [IsCommMonObj Γ]
    (a : Λ ⟶ Γ) [IsMonHom a]

/-- A chart after scalar extension is normalized on every original basis inclusion.
Source: Bhatt--Scholze 7.4.7, DAG step 2
(blueprint: lem-sfb-generic-lisse-scalar-comparison). -/
def IsExtendedCoefficientChart {T X : Scheme.{u}} (f : T ⟶ X)
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) (r : ℕ)
    (eA : (CondensedRing.upperStar Λ f).obj L ≅
      Mod.finiteFree (condensedRingObj Λ T) r)
    (eB : (CondensedRing.upperStar Γ f).obj
        ((Mod.extendScalars (coefficientMap a X)).obj L) ≅
      Mod.finiteFree (condensedRingObj Γ T) r) : Prop :=
  ∀ j : Fin r,
    (biproduct.ι (fun _ : Fin r ↦
      Mod.regular (condensedRingObj Λ T)) j).hom ≫
        eA.inv.hom ≫ pullUnderlying f L ((Mod.extendScalars (coefficientMap a X)).obj L)
          (Mod.extendUnitHom (coefficientMap a X) L) ≫ eB.hom.hom =
      coefficientMap a T ≫
        (biproduct.ι (fun _ : Fin r ↦
          Mod.regular (condensedRingObj Γ T)) j).hom

/-- Every chart retains its precise rank, and every transition or morphism entry is
carried by the coefficient map. The entry square states entrywise postcomposition
without choosing a second realization of coefficient sections.
Source: Bhatt--Scholze 7.4.7, DAG steps 1--2 and 4
(blueprint: lem-sfb-generic-lisse-scalar-comparison).
Proof: pullback preserves the defining tensor coequalizer. Its free comparison sends
s tensor (a_j) to (s φ(a_j)), with inverse the sum of s_j tensor e_j. The unit therefore
satisfies IsExtendedChart. Naturality of this unit with a morphism, precomposed with
the j-th inclusion and postcomposed with the i-th projection, gives the displayed
entry square. On overlaps apply this to the identity of L in its two bases, obtaining
the transition formula. The coefficient map is postcomposition by φ on all continuous
sections. The empty biproduct gives r=0 and empty matrix dimensions. -/
def ChartAssertions {T X : Scheme.{u}} (f : T ⟶ X) : Prop :=
    (∀ (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) (r : ℕ)
      (eA : (CondensedRing.upperStar Λ f).obj L ≅
        Mod.finiteFree (condensedRingObj Λ T) r),
      ∃ eB : (CondensedRing.upperStar Γ f).obj
          ((Mod.extendScalars (coefficientMap a X)).obj L) ≅
        Mod.finiteFree (condensedRingObj Γ T) r,
          IsExtendedCoefficientChart a f L r eA eB) ∧
    ∀ (L M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
      (t : L ⟶ M) (r s : ℕ)
      (eA : (CondensedRing.upperStar Λ f).obj L ≅
        Mod.finiteFree (condensedRingObj Λ T) r)
      (dA : (CondensedRing.upperStar Λ f).obj M ≅
        Mod.finiteFree (condensedRingObj Λ T) s)
      (eB : (CondensedRing.upperStar Γ f).obj
          ((Mod.extendScalars (coefficientMap a X)).obj L) ≅
        Mod.finiteFree (condensedRingObj Γ T) r)
      (dB : (CondensedRing.upperStar Γ f).obj
          ((Mod.extendScalars (coefficientMap a X)).obj M) ≅
        Mod.finiteFree (condensedRingObj Γ T) s),
      IsExtendedCoefficientChart a f L r eA eB → IsExtendedCoefficientChart a f M s dA dB →
      ∀ (i : Fin s) (j : Fin r),
        (biproduct.ι (fun _ : Fin r ↦
          Mod.regular (condensedRingObj Λ T)) j).hom ≫
          eA.inv.hom ≫ ((CondensedRing.upperStar Λ f).map t).hom ≫
          dA.hom.hom ≫ (biproduct.π (fun _ : Fin s ↦
            Mod.regular (condensedRingObj Λ T)) i).hom ≫
          coefficientMap a T =
        coefficientMap a T ≫
          (biproduct.ι (fun _ : Fin r ↦
            Mod.regular (condensedRingObj Γ T)) j).hom ≫
          eB.inv.hom ≫ ((CondensedRing.upperStar Γ f).map
            ((Mod.extendScalars (coefficientMap a X)).map t)).hom ≫ dB.hom.hom ≫
          (biproduct.π (fun _ : Fin s ↦
            Mod.regular (condensedRingObj Γ T)) i).hom

end Charts

/-- Local chart compatibility for the prescribed continuous coefficient map.
Source: Bhatt--Scholze 7.4.7, DAG steps 1--2 and 4
(blueprint: lem-sfb-generic-lisse-scalar-comparison).
Proof: the tensor coequalizer commutes with inverse image. On finite free modules,
its map is the direct sum of the coefficient homomorphism, including the empty sum.
Naturality of its unit gives the entry square for every rectangular morphism and,
on overlaps, the transition matrices. -/
theorem charts {T X : Scheme.{u}} (f : T ⟶ X) (φ : A →+* B) (hφ : Continuous φ) :
    @ChartAssertions (normContinuousRing A).X (normContinuousRing B).X _ _ _ _
      (Profinite.continuousMapRingObjMapOfUniverse φ hφ)
      (Profinite.isMonHom_continuousMapRingObjMapOfUniverse φ hφ) T X f := by
  sorry


/-- Evaluation of a morphism of abelian sheaves on a small-site object.
Source: the section map in Bhatt--Scholze 7.4.7
(blueprint: lem-sfb-generic-lisse-scalar-comparison). -/
def evalHom {T : Scheme.{u}} (U : T.ProEt)
    {F G : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}} (t : F ⟶ G) :
    F.obj.obj (op U) →+ G.obj.obj (op U) :=
  (t.hom.app (op U)).hom

/-- Evaluate the canonical module pullback of an arrow.
Source: Bhatt--Scholze 7.4.7, functoriality on sections
(blueprint: lem-sfb-generic-lisse-scalar-comparison). -/
def pullMapSections {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] {T Y : Scheme.{u}} (f : T ⟶ Y) (U : T.ProEt)
    {L M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)}
    (t : L ⟶ M) :=
  evalHom U ((CondensedRing.upperStar Λ f).map t).hom

/-- Evaluation of the scalar-extension unit after pullback, before coefficient specialization.
Source: Bhatt--Scholze 7.4.7, DAG steps 1 and 3
(blueprint: lem-sfb-generic-lisse-scalar-comparison). -/
def coefficientUnitArrow
    {Λ Γ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Γ] [IsCommMonObj Γ]
    {T Y : Scheme.{u}} (a : condensedRingObj Λ Y ⟶ condensedRingObj Γ Y)
    [IsMonHom a] (f : T ⟶ Y) (U : T.ProEt)
    (L : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    Arrow AddCommGrpCat.{u + 1} :=
  Arrow.mk ((pullUnderlying f L ((Mod.extendScalars a).obj L)
    (Mod.extendUnitHom a L)).hom.app (op U))

variable (X : Scheme.{u}) [IsIntegral X] (Ω : Type u) [Field Ω]
  [Algebra X.functionField Ω] [IsSepClosure X.functionField Ω]

/-- Constant scalar multiplication on the actual generic sections, with no chosen basis.
Source: Bhatt--Scholze 7.4.7, DAG step 3
(blueprint: lem-sfb-generic-lisse-scalar-comparison). -/
def scalar (L : NormContinuousLisse A X) (a : A)
    (v : NormalGenericLisse.geometricSections X A Ω L) :
    NormalGenericLisse.geometricSections X A Ω L :=
  (normContinuousScalar (Spec (.of X.functionField)) a
    (NormalGenericLisse.genericModule X A L)).hom.app
      (op (FieldSeparableCech.closureObject X.functionField Ω)) v

/-- The constant action satisfies precisely the module laws on actual sections.
Source: Bhatt--Scholze 7.4.7, DAG step 3
(blueprint: lem-sfb-generic-lisse-scalar-comparison).
Proof: the pointwise continuous constants define a ring homomorphism into the internal
coefficient ring. Apply the unit, associativity and distributivity equations for its
module action, then evaluate on the separable-closure object. This uses only the module
axioms, not local freeness or any scalar comparison theorem. -/
theorem scalar_laws (L : NormContinuousLisse A X) :
    (∀ v, scalar X Ω L 1 v = v) ∧
    (∀ a b v, scalar X Ω L (a * b) v = scalar X Ω L a (scalar X Ω L b v)) ∧
    (∀ a, scalar X Ω L a 0 = 0) ∧
    (∀ a v z, scalar X Ω L a (v + z) = scalar X Ω L a v + scalar X Ω L a z) ∧
    (∀ a b v, scalar X Ω L (a + b) v = scalar X Ω L a v + scalar X Ω L b v) ∧
    (∀ v, scalar X Ω L 0 v = 0) := by
  sorry

/-- The actual section fibre as an A-module. Its scalar data are explicit; the named
scalar_laws theorem supplies only proofs.
Source: Bhatt--Scholze 7.4.7, DAG step 3
(blueprint: lem-sfb-generic-lisse-scalar-comparison). -/
instance fiberModule (L : NormContinuousLisse A X) :
    Module A (NormalGenericLisse.geometricSections X A Ω L) where
  smul := scalar X Ω L
  one_smul := (scalar_laws X Ω L).1
  mul_smul := (scalar_laws X Ω L).2.1
  smul_zero := (scalar_laws X Ω L).2.2.1
  smul_add := (scalar_laws X Ω L).2.2.2.1
  add_smul := (scalar_laws X Ω L).2.2.2.2.1
  zero_smul := (scalar_laws X Ω L).2.2.2.2.2

/-- The map of actual generic sections induced by a sheaf morphism.
Source: Bhatt--Scholze 7.4.7, DAG step 4
(blueprint: lem-sfb-generic-lisse-scalar-comparison). -/
def map {L M : NormContinuousLisse A X} (f : L ⟶ M) :
    NormalGenericLisse.geometricSections X A Ω L →+
      NormalGenericLisse.geometricSections X A Ω M :=
  pullMapSections (NormalGenericLisse.genericMap X)
    (FieldSeparableCech.closureObject X.functionField Ω) f.hom

/-- Restriction along Spec(g), with the c(gh)=c(g)c(h) convention of the field Cech node.
Source: Bhatt--Scholze Example 4.1.10, DAG step 5
(blueprint: lem-sfb-generic-lisse-scalar-comparison). -/
def action (L : NormContinuousLisse A X) (g : Ω ≃ₐ[X.functionField] Ω) :
    NormalGenericLisse.geometricSections X A Ω L →+
      NormalGenericLisse.geometricSections X A Ω L :=
  ((NormalGenericLisse.genericModule X A L).X.obj.map
    (NormalGenericLisse.automorphism X Ω g).op).hom

/-- The evaluated internal extension unit as a bundled arrow, before identifying its
endpoints with the generic sections of the lisse-subcategory lift.
Source: Bhatt--Scholze 7.4.7, DAG steps 1 and 3
(blueprint: lem-sfb-generic-lisse-scalar-comparison). -/
def unitArrow (φ : A →+* B) (hφ : Continuous φ) (L : NormContinuousLisse A X) :
    Arrow AddCommGrpCat.{u + 1} :=
  coefficientUnitArrow (Λ := (normContinuousRing A).X) (Γ := (normContinuousRing B).X)
    (normContinuousCoefficientMap X φ hφ) (NormalGenericLisse.genericMap X)
    (FieldSeparableCech.closureObject X.functionField Ω) L.obj

/-- The source of the evaluated unit is the actual original generic section object.
Source: Bhatt--Scholze 7.4.7, DAG steps 1 and 3
(blueprint: lem-sfb-generic-lisse-scalar-comparison).
Proof: the source of pullUnderlying is the canonical generic module pullback;
evaluating on the separable-closure object is precisely geometricSections. -/
theorem unitSource_eq (φ : A →+* B) (hφ : Continuous φ) (L : NormContinuousLisse A X) :
    (unitArrow X Ω φ hφ L).left = NormalGenericLisse.geometricSections X A Ω L := by
  sorry

/-- Forgetting the lisse property leaves precisely the same extended section object.
Source: Bhatt--Scholze 7.4.7, DAG steps 1 and 3
(blueprint: lem-sfb-generic-lisse-scalar-comparison).
Proof: unfold the lisse-subcategory lift, whose object is the ordinary extension
with its lisseness proof attached. Forgetting this proof returns the same module;
applying the same generic pullback and evaluation gives the displayed equality. -/
theorem unitTarget_eq (φ : A →+* B) (hφ : Continuous φ) (L : NormContinuousLisse A X) :
    (unitArrow X Ω φ hφ L).right =
      NormalGenericLisse.geometricSections X B Ω ((extension X φ hφ).obj L) := by
  sorry

/-- The scalar-extension unit on the actual generic fibre. The equality transports
identify the endpoints of its actual evaluated internal arrow.
Source: Bhatt--Scholze 7.4.7, DAG steps 1 and 3
(blueprint: lem-sfb-generic-lisse-scalar-comparison). -/
def unit (φ : A →+* B) (hφ : Continuous φ) (L : NormContinuousLisse A X) :
    NormalGenericLisse.geometricSections X A Ω L →+
      NormalGenericLisse.geometricSections X B Ω ((extension X φ hφ).obj L) :=
  (eqToHom (unitSource_eq X Ω φ hφ L).symm ≫ (unitArrow X Ω φ hφ L).hom ≫
    eqToHom (unitTarget_eq X Ω φ hφ L)).hom

/-- The generic geometric finite-etale fibre functor. The existing equivalence with FLC
sheaves identifies its automorphism group with the etale fundamental group of the node.
Source: Stacks 0BND; Bhatt--Scholze 7.4.10, DAG step 6
(blueprint: lem-sfb-generic-lisse-scalar-comparison). -/
def etaleFiber : X.FiniteEtale ⥤ FintypeCat.{u} := by
  letI : IsSepClosed Ω := IsSepClosure.sep_closed X.functionField
  exact Scheme.FiniteEtale.fiber
    (Scheme.FiniteEtale.pointOfAlgebra Ω (NormalGenericLisse.genericMap X))

/-- The induced Galois map, defined by precomposition with Spec of the field automorphism.
This is the existing generic Galois-to-fibre-automorphism construction, not an arbitrary map.
Source: Stacks 0BQM; Bhatt--Scholze 7.4.10, DAG step 6
(blueprint: lem-sfb-generic-lisse-scalar-comparison). -/
def quotient : (Ω ≃ₐ[X.functionField] Ω) →* Aut (etaleFiber X Ω) := by
  letI : IsSepClosed Ω := IsSepClosure.sep_closed X.functionField
  exact Scheme.FiniteEtale.galoisToAut (NormalGenericLisse.genericMap X)

/-- The full natural generic comparison, normalized on pure tensors and including every
rectangular matrix, Galois action, and simultaneous quotient/basepoint transport.
Source: Bhatt--Scholze 7.4.7, pp. 70--71, agent extension; DAG steps 1--6
(blueprint: lem-sfb-generic-lisse-scalar-comparison).
Proof: inverse image preserves the tensor coequalizer (step 1). On local free charts
ordinary extension preserves all ranks and sends every entry by φ (step 2).
Over Spec Ω the field Cech coordinates trivialize L and identify sections with A^n.
The coefficient-section normalization identifies constants with A and B. The unit map
then gives b tensor (a_j) ↦ (b φ(a_j)); its inverse is the finite sum of b_j tensor e_j
(step 3). Pure tensors prove naturality on every morphism (step 4). The same entrywise
calculation on C(G_k,A) sends c(g) to φ(c(g)), and the vertex convention gives
c(gh)=c(g)c(h), so the comparison is G_k-equivariant (step 5). Given a surjective
quotient q through which both actions factor, lift an element and use that identity;
precompose by the inverse of the one fixed basepoint isomorphism (step 6). Empty
bases give the zero comparison and every empty rectangular matrix. No finite-valued
or finite-subextension restriction is imposed on continuous coefficients. -/
theorem comparison [IsLocallyNoetherian X]
    (_hnormal : ∀ x : X,
      IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
    [Algebra A B] (_hA : IsNonarchimedean (norm : A → ℝ))
    (_hB : IsNonarchimedean (norm : B → ℝ)) (hφ : Continuous (algebraMap A B)) :
    ∃ e : ∀ L : NormContinuousLisse A X,
        (B ⊗[A] NormalGenericLisse.geometricSections X A Ω L) ≃ₗ[B]
          NormalGenericLisse.geometricSections X B Ω
            ((extension X (algebraMap A B) hφ).obj L),
      (∀ (L : NormContinuousLisse A X) (b : B)
        (v : NormalGenericLisse.geometricSections X A Ω L),
        e L (b ⊗ₜ[A] v) =
          scalar X Ω ((extension X (algebraMap A B) hφ).obj L) b
            (unit X Ω (algebraMap A B) hφ L v)) ∧
      (∀ (L M : NormContinuousLisse A X) (f : L ⟶ M) (b : B)
        (v : NormalGenericLisse.geometricSections X A Ω L),
        e M (b ⊗ₜ[A] map X Ω f v) =
          map X Ω ((extension X (algebraMap A B) hφ).map f) (e L (b ⊗ₜ[A] v))) ∧
      (∀ (L : NormContinuousLisse A X) (g : Ω ≃ₐ[X.functionField] Ω) (b : B)
        (v : NormalGenericLisse.geometricSections X A Ω L),
        e L (b ⊗ₜ[A] action X Ω L g v) =
          action X Ω ((extension X (algebraMap A B) hφ).obj L) g
            (e L (b ⊗ₜ[A] v))) ∧
      (∀ (L M : NormContinuousLisse A X) (f : L ⟶ M) (n m : ℕ)
        (c : Module.Basis (Fin n) A (NormalGenericLisse.geometricSections X A Ω L))
        (d : Module.Basis (Fin m) A (NormalGenericLisse.geometricSections X A Ω M))
        (i : Fin m) (j : Fin n),
        ((d.baseChange B).map (e M)).repr
          (map X Ω ((extension X (algebraMap A B) hφ).map f)
            (((c.baseChange B).map (e L)) j)) i =
          algebraMap A B (d.repr (map X Ω f (c j)) i)) ∧
      (∀ (L : NormContinuousLisse A X) (n : ℕ)
        (c : Module.Basis (Fin n) A (NormalGenericLisse.geometricSections X A Ω L))
        (g : Ω ≃ₐ[X.functionField] Ω) (i j : Fin n),
        ((c.baseChange B).map (e L)).repr
          (action X Ω ((extension X (algebraMap A B) hφ).obj L) g
            (((c.baseChange B).map (e L)) j)) i =
          algebraMap A B (c.repr (action X Ω L g (c j)) i)) ∧
      ∀ (_hqc : CompactSpace X) (_hq : Function.Surjective (quotient X Ω))
        (Ωx : Type u) [Field Ωx] [IsAlgClosed Ωx] (x : Spec (.of Ωx) ⟶ X)
        (a : Aut (etaleFiber X Ω) ≃ₜ* Aut (Scheme.flcFiber x))
        (L : NormContinuousLisse A X)
        (ρA : Aut (etaleFiber X Ω) → NormalGenericLisse.geometricSections X A Ω L →
          NormalGenericLisse.geometricSections X A Ω L)
        (ρB : Aut (etaleFiber X Ω) → NormalGenericLisse.geometricSections X B Ω
            ((extension X (algebraMap A B) hφ).obj L) →
          NormalGenericLisse.geometricSections X B Ω
            ((extension X (algebraMap A B) hφ).obj L)),
        (∀ g v, ρA (quotient X Ω g) v = action X Ω L g v) →
        (∀ g v, ρB (quotient X Ω g) v =
          action X Ω ((extension X (algebraMap A B) hφ).obj L) g v) →
        (∀ (γ : Aut (etaleFiber X Ω)) (b : B) (v : NormalGenericLisse.geometricSections X A Ω L),
          e L (b ⊗ₜ[A] ρA γ v) = ρB γ (e L (b ⊗ₜ[A] v))) ∧
        ∀ (δ : Aut (Scheme.flcFiber x)) (b : B) (v : NormalGenericLisse.geometricSections X A Ω L),
          e L (b ⊗ₜ[A] ρA (a.symm δ) v) = ρB (a.symm δ) (e L (b ⊗ₜ[A] v)) := by
  sorry

end GenericLisseScalar
end AlgebraicGeometry.ProEtale

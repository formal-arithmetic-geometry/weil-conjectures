/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q58
-/
module

public import Sheaf.AlgebraicGeometry.AffineRelativeDualizingComparison
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.RingTheory.RingPseudoCoherent
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
import Sheaf.Algebra.Homology.BoundedAboveProjectiveModel
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.Algebra.Homology.FlatOpcyclesTorCriterion
import Sheaf.Paper.AffineProjectiveComplexDerivedHom
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Homology.HomotopyCategory.KProjective

/-! # Relative flat Hom-complex models under arbitrary base change

Source: Stacks Project, Tag 0E1U, lemma-compute-RHom-relatively-perfect.
(blueprint: lem-sfb-relative-rhom-flat-base-change-model).

The statement includes the finite direct-sum description, normalized chain isomorphisms,
the additive degree-zero comparison, and its compatibility with all coefficient maps.
The helper declarations only name existing constructions or package this node's conclusions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped TensorProduct DirectSum

namespace CochainComplex

/-- The canonical inclusion S → S tensor_R T. This names the existing tensor inclusion.
Source: Stacks Project, Tag 0E1U, lemma-compute-RHom-relatively-perfect.
(blueprint: lem-sfb-relative-rhom-flat-base-change-model). -/
def relativeRHomScalar {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (T : CommAlgCat.{u} R) : S →+* S ⊗[R] T :=
  (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T).toRingHom

/-- The canonical coefficient transition id_S tensor v on the base-changed algebra.
Source: Stacks Project, Tag 0E1U, lemma-compute-RHom-relatively-perfect.
(blueprint: lem-sfb-relative-rhom-flat-base-change-model). -/
def relativeRHomRingMap {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {T U : CommAlgCat.{u} R} (v : T ⟶ U) : S ⊗[R] T →+* S ⊗[R] U :=
  (Algebra.TensorProduct.map (AlgHom.id R S) v.hom).toRingHom

/-- Termwise ordinary tensor with T, retaining the S tensor_R T action.
The existing scalar-extension convention is (S tensor_R T) tensor_S C, canonically
C tensor_R T by (s tensor t) tensor x ↦ sx tensor t. No replacement complex is used.
Source: Stacks Project, Tag 0E1U, lemma-compute-RHom-relatively-perfect.
(blueprint: lem-sfb-relative-rhom-flat-base-change-model). -/
def relativeRHomTensor {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (T : CommAlgCat.{u} R) :
    CochainComplex (ModuleCat.{u} S) ℤ ⥤ CochainComplex (ModuleCat.{u} (S ⊗[R] T)) ℤ :=
  (ModuleCat.extendScalars (relativeRHomScalar (S := S) T)).mapHomologicalComplex (.up ℤ)

/-- The recorded K-flat derived extension along S → S tensor_R T.
This uses relativeDualizingDerivedExtension, without choosing another derived functor.
Source: Stacks Project, Tag 0E1U, lemma-compute-RHom-relatively-perfect.
(blueprint: lem-sfb-relative-rhom-flat-base-change-model). -/
def relativeRHomDerived {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (T : CommAlgCat.{u} R) :
    DerivedCategory (ModuleCat.{u} S) ⥤ DerivedCategory (ModuleCat.{u} (S ⊗[R] T)) :=
  AlgebraicGeometry.relativeDualizingDerivedExtension (relativeRHomScalar (S := S) T)

open scoped ChangeOfRings in
/-- The pure tensor sx tensor t in the existing left scalar-extension convention.
It is represented by (s tensor t) tensor x, so balancing is built into the tensor product.
Source: Stacks Project, Tag 0E1U, lemma-compute-RHom-relatively-perfect.
(blueprint: lem-sfb-relative-rhom-flat-base-change-model). -/
def relativeRHomPure {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (T : CommAlgCat.{u} R) (C : CochainComplex (ModuleCat.{u} S) ℤ)
    (n : ℤ) (s : S) (t : T) (x : C.X n) : ((relativeRHomTensor (S := S) T).obj C).X n :=
  (s ⊗ₜ[R] t) ⊗ₜ[S, relativeRHomScalar (S := S) T] x

/-- Termwise exact restriction along the canonical coefficient transition.
Source: Stacks Project, Tag 0E1U, lemma-compute-RHom-relatively-perfect.
(blueprint: lem-sfb-relative-rhom-flat-base-change-model). -/
def relativeRHomRes {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {T U : CommAlgCat.{u} R} (v : T ⟶ U) :
    CochainComplex (ModuleCat.{u} (S ⊗[R] U)) ℤ ⥤
      CochainComplex (ModuleCat.{u} (S ⊗[R] T)) ℤ :=
  (ModuleCat.restrictScalars (relativeRHomRingMap (S := S) v)).mapHomologicalComplex (.up ℤ)

/-- The canonical derived-to-ordinary comparison on the chosen complex.
It is the recorded K-flat counit, transported through the homotopy quotient factorization.
Source: Stacks Project, Tag 0E1U, lemma-compute-RHom-relatively-perfect.
(blueprint: lem-sfb-relative-rhom-flat-base-change-model). -/
def relativeRHomCounit {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (T : CommAlgCat.{u} R) (C : CochainComplex (ModuleCat.{u} S) ℤ) :
    (relativeRHomDerived (S := S) T).obj (DerivedCategory.Q.obj C) ⟶
      DerivedCategory.Q.obj ((relativeRHomTensor (S := S) T).obj C) :=
  (relativeRHomDerived (S := S) T).map ((DerivedCategory.quotientCompQhIso _).app C).inv ≫
    (AlgebraicGeometry.relativeDualizingExtensionCounit (relativeRHomScalar (S := S) T)).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj C) ≫
    DerivedCategory.Qh.map
      (((ModuleCat.extendScalars (relativeRHomScalar (S := S) T)).mapHomotopyCategoryFactors
        (.up ℤ)).app C).hom ≫
    ((DerivedCategory.quotientCompQhIso _).app ((relativeRHomTensor (S := S) T).obj C)).hom

set_option maxHeartbeats 600000 in
-- Shared derived categories require a larger elaboration budget.
/-- The conclusions for any allowed pair of representatives, with their normalized maps.
finiteSum is fixed by its coordinate projections. homIso is fixed on every pure tensor.
The representative isomorphisms are pinned by the actual derived-to-ordinary counit.
homologyIso sends a cycle representing a chain map to its localized derived morphism.
These are conclusion data whose existence is asserted by the theorem, not hypotheses
or choices used to manufacture a derived Hom object.
Source: Stacks Project, Tag 0E1U, lemma-compute-RHom-relatively-perfect.
(blueprint: lem-sfb-relative-rhom-flat-base-change-model). -/
structure RelativeRHomFlatBaseChangeComparisons
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (K L : DerivedCategory (ModuleCat.{u} S))
    (P F : CochainComplex (ModuleCat.{u} S) ℤ)
    (eP : DerivedCategory.Q.obj P ≅ K) (eF : DerivedCategory.Q.obj F ≅ L) where
  finiteSum : ∀ n : ℤ, (moduleHomComplex P F).X n ≃ₗ[S]
    ⨁ p : ℤ, (P.X p →ₗ[S] F.X (p + n))
  finiteSum_projection : ∀ (n p : ℤ) (z : (moduleHomComplex P F).X n),
    DirectSum.component S ℤ (fun p ↦ P.X p →ₗ[S] F.X (p + n)) p (finiteSum n z) =
      (z.v p (p + n) rfl).hom
  boundedBelow : ∃ c : ℤ, ∀ n : ℤ, n < c → IsZero ((moduleHomComplex P F).X n)
  flat : ∀ n : ℤ, Module.Flat R
    ((ModuleCat.restrictScalars (algebraMap R S)).obj ((moduleHomComplex P F).X n))
  represents : DerivedCategory.Q.obj (moduleHomComplex P F) ≅
    (ordinaryModuleDerivedInternalHom S).obj (op K, L)
  sourceIso : ∀ T : CommAlgCat.{u} R,
    DerivedCategory.Q.obj ((relativeRHomTensor (S := S) T).obj P) ≅ 
      (relativeRHomDerived (S := S) T).obj K
  targetIso : ∀ T : CommAlgCat.{u} R,
    DerivedCategory.Q.obj ((relativeRHomTensor (S := S) T).obj F) ≅ 
      (relativeRHomDerived (S := S) T).obj L
  source_normalized : ∀ T : CommAlgCat.{u} R,
    relativeRHomCounit (S := S) T P ≫ (sourceIso T).hom = (relativeRHomDerived (S := S) T).map
      eP.hom
  target_normalized : ∀ T : CommAlgCat.{u} R,
    relativeRHomCounit (S := S) T F ≫ (targetIso T).hom = (relativeRHomDerived (S := S) T).map
      eF.hom
  homIso : ∀ T : CommAlgCat.{u} R,
    (relativeRHomTensor (S := S) T).obj (moduleHomComplex P F) ≅
      moduleHomComplex ((relativeRHomTensor (S := S) T).obj P) (
        (relativeRHomTensor (S := S) T).obj F)
  homIso_pure : ∀ (T : CommAlgCat.{u} R) (n p : ℤ)
    (h : (moduleHomComplex P F).X n) (x : P.X p) (s s' : S) (t t' : T),
    (((homIso T).hom.f n (relativeRHomPure (S := S) T (moduleHomComplex P F) n s t h)).v
      p (p + n) rfl) (relativeRHomPure (S := S) T P p s' t' x) =
      relativeRHomPure (S := S) T F (p + n) (s * s') (t * t') ((h.v p (p + n) rfl) x)
  targetRepresents : ∀ T : CommAlgCat.{u} R,
    DerivedCategory.Q.obj
      (moduleHomComplex ((relativeRHomTensor (S := S) T).obj P) (
        (relativeRHomTensor (S := S) T).obj F)) ≅
      (ordinaryModuleDerivedInternalHom (S ⊗[R] T)).obj
        (op ((relativeRHomDerived (S := S) T).obj K), (relativeRHomDerived (S := S) T).obj L)
  homologyIso : ∀ T : CommAlgCat.{u} R,
    ((relativeRHomTensor (S := S) T).obj (moduleHomComplex P F)).homology 0 ≃+
      ((relativeRHomDerived (S := S) T).obj K ⟶ (relativeRHomDerived (S := S) T).obj L)
  homology_normalized : ∀ (T : CommAlgCat.{u} R)
    (f : (relativeRHomTensor (S := S) T).obj P ⟶ (relativeRHomTensor (S := S) T).obj F)
    (z : ((relativeRHomTensor (S := S) T).obj (moduleHomComplex P F)).cycles 0),
    (homIso T).hom.f 0
      (((relativeRHomTensor (S := S) T).obj (moduleHomComplex P F)).iCycles 0 z) =
        HomComplex.Cochain.ofHom f →
    homologyIso T (((relativeRHomTensor (S := S) T).obj (moduleHomComplex P F)).homologyπ 0 z) =
      (sourceIso T).inv ≫ DerivedCategory.Q.map f ≫ (targetIso T).hom


/-- The derived comparison induced by the specified chain isomorphism.
Source: Stacks Project, Tag 0E1U, lemma-compute-RHom-relatively-perfect.
(blueprint: lem-sfb-relative-rhom-flat-base-change-model). -/
def relativeRHomBaseChangedIso
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {K L : DerivedCategory (ModuleCat.{u} S)}
    {P F : CochainComplex (ModuleCat.{u} S) ℤ}
    {eP : DerivedCategory.Q.obj P ≅ K} {eF : DerivedCategory.Q.obj F ≅ L}
    (c : RelativeRHomFlatBaseChangeComparisons (R := R) K L P F eP eF)
    (T : CommAlgCat.{u} R) :
    DerivedCategory.Q.obj ((relativeRHomTensor T).obj (moduleHomComplex P F)) ≅
      (ordinaryModuleDerivedInternalHom (S ⊗[R] T)).obj
        (op ((relativeRHomDerived T).obj K), (relativeRHomDerived T).obj L) :=
  DerivedCategory.Q.mapIso (c.homIso T) ≪≫ c.targetRepresents T

/-- The exact derived restriction along id_S tensor v, using mapDerivedCategory.
Source: Stacks Project, Tag 0E1U, lemma-compute-RHom-relatively-perfect.
(blueprint: lem-sfb-relative-rhom-flat-base-change-model). -/
def relativeRHomDerivedRes {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {T U : CommAlgCat.{u} R} (v : T ⟶ U) :
    DerivedCategory (ModuleCat.{u} (S ⊗[R] U)) ⥤
      DerivedCategory (ModuleCat.{u} (S ⊗[R] T)) :=
  (ModuleCat.restrictScalars (relativeRHomRingMap (S := S) v)).mapDerivedCategory

set_option maxHeartbeats 600000 in
-- Shared derived categories require a larger elaboration budget.
/-- Canonical coefficient maps and their compatibility with derived scalar extension.
The universal-arrow fields say precisely that the normalized units exhibit extension
from S tensor_R T to S tensor_R U. The final square is the claimed H⁰ compatibility:
the universal property uniquely determines the extended morphism. Identity and composition
use heterogeneous equality only to avoid unfolding the equal restricted scalar structures;
the underlying module elements and their equalities are the usual ones.
Source: Stacks Project, Tag 0E1U, lemma-compute-RHom-relatively-perfect.
(blueprint: lem-sfb-relative-rhom-flat-base-change-model). -/
structure RelativeRHomFlatBaseChangeTransitions
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {K L : DerivedCategory (ModuleCat.{u} S)}
    {P F : CochainComplex (ModuleCat.{u} S) ℤ}
    {eP : DerivedCategory.Q.obj P ≅ K} {eF : DerivedCategory.Q.obj F ≅ L}
    (c : RelativeRHomFlatBaseChangeComparisons (R := R) K L P F eP eF) where
  change : ∀ {T U : CommAlgCat.{u} R} (v : T ⟶ U)
    (C : CochainComplex (ModuleCat.{u} S) ℤ),
    (relativeRHomTensor (S := S) T).obj C ⟶ (relativeRHomRes (S := S) v).obj
      ((relativeRHomTensor (S := S) U).obj C)
  change_pure : ∀ {T U : CommAlgCat.{u} R} (v : T ⟶ U)
    (C : CochainComplex (ModuleCat.{u} S) ℤ) (n : ℤ) (s : S) (t : T) (x : C.X n),
    (change v C).f n (relativeRHomPure (S := S) T C n s t x) = relativeRHomPure (S := S) U C n s
      (v t) x
  change_identity : ∀ (T : CommAlgCat.{u} R)
    (C : CochainComplex (ModuleCat.{u} S) ℤ) (n : ℤ)
    (x : ((relativeRHomTensor (S := S) T).obj C).X n),
    HEq ((change (𝟙 T) C).f n x) x
  change_composition : ∀ {T U V : CommAlgCat.{u} R} (v : T ⟶ U) (w : U ⟶ V)
    (C : CochainComplex (ModuleCat.{u} S) ℤ) (n : ℤ)
    (x : ((relativeRHomTensor (S := S) T).obj C).X n)
    (y : ((relativeRHomTensor (S := S) U).obj C).X n),
    HEq y ((change v C).f n x) →
      HEq ((change w C).f n y) ((change (v ≫ w) C).f n x)
  sourceUnit : ∀ {T U : CommAlgCat.{u} R} (v : T ⟶ U),
    (relativeRHomDerived (S := S) T).obj K ⟶
      (relativeRHomDerivedRes (S := S) v).obj
        ((relativeRHomDerived (S := S) U).obj K)
  targetUnit : ∀ {T U : CommAlgCat.{u} R} (v : T ⟶ U),
    (relativeRHomDerived (S := S) T).obj L ⟶
      (relativeRHomDerivedRes (S := S) v).obj
        ((relativeRHomDerived (S := S) U).obj L)

  sourceUnit_universal : ∀ {T U : CommAlgCat.{u} R} (v : T ⟶ U),
    ∀ N : DerivedCategory (ModuleCat.{u} (S ⊗[R] U)),
      Function.Bijective fun g : (relativeRHomDerived (S := S) U).obj K ⟶ N ↦
        sourceUnit v ≫ (relativeRHomDerivedRes (S := S) v).map g
  targetUnit_universal : ∀ {T U : CommAlgCat.{u} R} (v : T ⟶ U),
    ∀ N : DerivedCategory (ModuleCat.{u} (S ⊗[R] U)),
      Function.Bijective fun g : (relativeRHomDerived (S := S) U).obj L ⟶ N ↦
        targetUnit v ≫ (relativeRHomDerivedRes (S := S) v).map g
  sourceUnit_normalized : ∀ {T U : CommAlgCat.{u} R} (v : T ⟶ U),
    (c.sourceIso T).hom ≫ sourceUnit v = DerivedCategory.Q.map (change v P) ≫
      ((ModuleCat.restrictScalars (relativeRHomRingMap (S := S)
        v)).mapDerivedCategoryFactors).inv.app
        ((relativeRHomTensor (S := S) U).obj P) ≫
      (relativeRHomDerivedRes (S := S) v).map (c.sourceIso U).hom
  targetUnit_normalized : ∀ {T U : CommAlgCat.{u} R} (v : T ⟶ U),
    (c.targetIso T).hom ≫ targetUnit v = DerivedCategory.Q.map (change v F) ≫
      ((ModuleCat.restrictScalars (relativeRHomRingMap (S := S)
        v)).mapDerivedCategoryFactors).inv.app
        ((relativeRHomTensor (S := S) U).obj F) ≫
      (relativeRHomDerivedRes (S := S) v).map (c.targetIso U).hom
  transition : ∀ {T U : CommAlgCat.{u} R} (v : T ⟶ U)
    (z : ((relativeRHomTensor (S := S) T).obj (moduleHomComplex P F)).cycles 0)
    (z' : ((relativeRHomTensor (S := S) U).obj (moduleHomComplex P F)).cycles 0),
    ((relativeRHomTensor (S := S) U).obj (moduleHomComplex P F)).iCycles 0 z' =
      (change v (moduleHomComplex P F)).f 0
        (((relativeRHomTensor (S := S) T).obj (moduleHomComplex P F)).iCycles 0 z) →
    sourceUnit v ≫ (relativeRHomDerivedRes (S := S) v).map
      (c.homologyIso U (((relativeRHomTensor (S := S) U).obj (moduleHomComplex P F)).homologyπ 0
        z')) =
    c.homologyIso T (((relativeRHomTensor (S := S) T).obj (moduleHomComplex P F)).homologyπ 0 z) ≫
      targetUnit v

/-- Exactly the allowed pair P,F: bounded-above finite free P representing K,
and bounded relatively flat F representing L. This predicate packages the hypotheses
on a pair; it contains no construction and no additional finiteness condition on F.
Source: Stacks Project, Tag 0E1U, lemma-compute-RHom-relatively-perfect.
(blueprint: lem-sfb-relative-rhom-flat-base-change-model). -/
def RelativeRHomFlatModelPair
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (K L : DerivedCategory (ModuleCat.{u} S))
    (P F : CochainComplex (ModuleCat.{u} S) ℤ) : Prop :=
  (∃ m : ℤ, ∀ p : ℤ, m < p → IsZero (P.X p)) ∧
  (∀ p : ℤ, Module.Free S (P.X p) ∧ Module.Finite S (P.X p)) ∧
  Nonempty (DerivedCategory.Q.obj P ≅ K) ∧
  (∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q → IsZero (F.X q)) ∧
  (∀ q : ℤ, Module.Flat R
    ((ModuleCat.restrictScalars (algebraMap R S)).obj (F.X q))) ∧
  Nonempty (DerivedCategory.Q.obj F ≅ L)

set_option maxHeartbeats 400000 in
-- Elaborate the canonical tensor structures in the relative amplitude hypothesis.
/-- Flat Hom-complex models and all their arbitrary-base-change comparisons.

Proof:
1. Choose P by pseudo-coherence. Taking N=R bounds L's cohomology. Use
   lem-weil-pbc-bounded-above-projective-model to represent L by a projective Q zero
   above b. Projective modules are flat (lem-weil-pbc-projective-module-flat), and
   flatness is transitive (lem-pc-module-flat-transitive). Bounded-above flat Q is
   K-flat (lem-pc-module-bounded-flat-kflat). Universal tensor vanishing in degree a-1
   makes its a-th opcycles flat (lem-pc-module-flat-opcycles-tor-criterion).
   Truncate Q below a using those opcycles. The quotient Q → F is a quasi-isomorphism
   and F has the required bounded flat terms. No finite generation of Q is used.
2. For any such P,F choose upper bound m of P and bounds c,d of F. In degree n only
   c-n ≤ p ≤ min(m,d-n) contribute to moduleHomComplex, so its product is exactly
   the finite direct sum specified by finiteSum_projection, zero for n<c-m.
   Each summand is a finite power of F^(p+n), using a finite basis of P^p, hence
   R-flat by lem-weil-pbc-finite-product-flat-modules. The bounded-above projective
   Hom computation (lem-sc-affine-projective-complex-derived-hom) identifies its
   localization with the recorded ordinary derived internal Hom.
3. Both P and F are bounded-above R-flat and therefore R-K-flat. Apply
   lem-sfb-flat-algebra-derived-module-tensor-exchange to a free R-resolution V → T[0].
   Its augmentation tensored with either complex is a quasi-isomorphism, since its
   cone is tensor with the acyclic cone of V → T[0]. Thus the actual derived counits
   are invertible and fix sourceIso and targetIso, including all representative maps.
4. On a finite free term the Hom comparison is the coordinate tensor isomorphism.
   Tensor commutes with the finite sums of step 2. The prescribed evaluation formula
   gives the degree maps and commutes with d_F h - (-1)^n h d_P. Its target computes
   derived Hom over S tensor_R T by the same bounded-above projective Hom lemma.
5. Degree-zero cycles are chain maps, and boundaries are null homotopies. Use
   lem-sc-bounded-above-projective-kprojective and
   lem-coef-kprojective-derived-hom-bijection to identify their additive quotient
   with derived morphisms. This is homology_normalized, with the chosen source and
   target isomorphisms explicitly inserted.
6. For v:T → U the terms of F_T are T-flat by lem-weil-pbc-flat-module-base-change;
   those of P_T are T-flat by projectivity and flat transitivity. Repeat step 3 over T.
   The resulting normalized units have the derived scalar-extension universal property.
   On a pure cochain both coefficient change and scalar extension evaluate to
   h(p) tensor v(t)u. Tensor sends homotopies to homotopies, so this equality gives
   the stated square on H⁰. On pure tensors identity fixes h tensor t and composition
   sends it to h tensor w(v(t)); generation by pure tensors proves both coherence
   fields. The balancing maps are the canonical iterated-tensor identifications.
Source: Stacks Project, Tag 0E1U, lemma-compute-RHom-relatively-perfect.
(blueprint: lem-sfb-relative-rhom-flat-base-change-model). -/
theorem relativeRHom_flat_baseChange_model
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (hflat : RingHom.Flat (algebraMap R S))
    (K L : DerivedCategory (ModuleCat.{u} S)) (hK : DerivedCategory.IsPseudoCoherent K)
    (a b : ℤ) (hab : a ≤ b)
    (hL : ∀ (N : ModuleCat.{u} R) (j : ℤ), j < a ∨ b < j →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) j).obj
        (((ModuleCat.restrictScalars (algebraMap R S)).mapDerivedCategory.obj L) ⊗
          (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N))) :
    (∃ P F : CochainComplex (ModuleCat.{u} S) ℤ, RelativeRHomFlatModelPair (R := R) K L P F) ∧
    ∀ (P F : CochainComplex (ModuleCat.{u} S) ℤ), RelativeRHomFlatModelPair (R := R) K L P F →
      ∀ (eP : DerivedCategory.Q.obj P ≅ K) (eF : DerivedCategory.Q.obj F ≅ L),
        ∃ c : RelativeRHomFlatBaseChangeComparisons (R := R) K L P F eP eF,
          Nonempty (RelativeRHomFlatBaseChangeTransitions c) := by
  sorry

end CochainComplex

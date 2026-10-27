/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q59
-/
module

public import Sheaf.Paper.NormContinuousMonodromyData
public import Sheaf.Paper.FieldSeparableCechCoordinates
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.Topology.Connected.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Sheaf.Topology.ContinuousMapCondensedRing
public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.Paper.ContinuousRingUniverseRealization
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

import Sheaf.AlgebraicGeometry.NormalGenericContinuousSections
import Sheaf.AlgebraicGeometry.NormalTopologicallyNoetherianComponents
import Sheaf.CategoryTheory.Sites.GrothendieckTopos

/-! # Normal generic restriction and lisse Galois cocycles

Source: Bhatt--Scholze, Lemmas 7.4.7 and 7.4.10, pp. 70--71, and the explicit
normed-coefficient matrix/descent argument in the DAG. The normed-field assertion is
an agent extension of that framework, not a quotation of the local-field theorem.
(blueprint: lem-sfb-normal-generic-lisse-cocycle).

The fibre is evaluation on the separable-closure object of the generic small site.
Equivalently these are global sections after restriction to that object's slice site.
The section normalization fixes both the functor on arrows and its Galois action.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale
namespace NormalGenericLisse

variable (X : Scheme.{u}) [IsIntegral X]

/-- The actual generic-point morphism, with the function field defined by its stalk.
Source: Bhatt--Scholze 7.4.10, DAG proof step 1.
(blueprint: lem-sfb-normal-generic-lisse-cocycle). -/
abbrev genericMap : Spec (.of X.functionField) ⟶ X :=
  X.fromSpecStalk (genericPoint X)

variable (A : Type u) [NormedField A]

/-- Restriction is the recorded inverse image on internal coefficient modules.
Source: Bhatt--Scholze 7.4.7, DAG proof step 4.
(blueprint: lem-sfb-normal-generic-lisse-cocycle). -/
abbrev genericModule (L : NormContinuousLisse A X) :=
  (CondensedRing.upperStar (normContinuousRing A).X (genericMap X)).obj L.obj

variable (Ω : Type u) [Field Ω] [Algebra X.functionField Ω] [IsSepClosure X.functionField Ω]

/-- Actual sections over Spec Ω, viewed as an object of the generic small pro-etale site.
Evaluation on this object is Gamma of the restriction to its slice, so this is V_A(L).
Source: Bhatt--Scholze 7.4.7 and Example 4.1.10, DAG proof step 5.
(blueprint: lem-sfb-normal-generic-lisse-cocycle). -/
abbrev geometricSections (L : NormContinuousLisse A X) : AddCommGrpCat.{u + 1} :=
  (genericModule X A L).X.obj.obj
    (op (FieldSeparableCech.closureObject X.functionField Ω))

/-- Spec of a k-automorphism lies over Spec k.
Source: the separable Cech coordinates, DAG proof step 6.
(blueprint: lem-sfb-normal-generic-lisse-cocycle).
Proof: the algebra automorphism fixes the image of k. Apply the contravariant Spec
functor to g composed with the algebra map, which is that same algebra map. -/
theorem automorphism_over (g : Ω ≃ₐ[X.functionField] Ω) :
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) =
        Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) := by
  sorry

/-- The canonical site endomorphism induced by a field automorphism.
Source: Bhatt--Scholze Example 4.1.10, DAG proof step 6.
(blueprint: lem-sfb-normal-generic-lisse-cocycle). -/
def automorphism (g : Ω ≃ₐ[X.functionField] Ω) :
    FieldSeparableCech.closureObject X.functionField Ω ⟶
      FieldSeparableCech.closureObject X.functionField Ω :=
  MorphismProperty.Over.homMk (Spec.map (CommRingCat.ofHom g.toRingHom))
    (automorphism_over X Ω g)

/-- Full faithfulness and reflection for the actual generic restriction, with constant
scalar multiplication specified using the existing internal-module scalar operation.
Source: Bhatt--Scholze 7.4.10, DAG proof step 4.
(blueprint: lem-sfb-normal-generic-lisse-cocycle). -/
def RestrictionAssertions : Prop :=
  (∀ L : NormContinuousLisse A X,
    IsLisseCoefficientModule (normContinuousRing A).X (genericModule X A L)) ∧
  (∀ L M : NormContinuousLisse A X,
    Function.Bijective (fun f : L ⟶ M ↦
      (CondensedRing.upperStar (normContinuousRing A).X (genericMap X)).map f.hom)) ∧
  (∀ (L M : NormContinuousLisse A X) (f : L ⟶ M),
    IsIso ((CondensedRing.upperStar (normContinuousRing A).X (genericMap X)).map f.hom) →
      IsIso f) ∧
  ∀ (L M : NormContinuousLisse A X) (f : L ⟶ M) (a : A), ∃ t : L ⟶ M,
    t.hom.hom = f.hom.hom ≫ normContinuousScalar X a M.obj ∧
      ((CondensedRing.upperStar (normContinuousRing A).X (genericMap X)).map t.hom).hom =
        ((CondensedRing.upperStar (normContinuousRing A).X (genericMap X)).map f.hom).hom ≫
          normContinuousScalar (Spec (.of X.functionField)) a (genericModule X A M)

set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- The functor and its identification with actual section fibres.
Source: Bhatt--Scholze 7.4.7, DAG proof steps 5--8.
(blueprint: lem-sfb-normal-generic-lisse-cocycle). -/
structure FiberFunctor where
  functor : NormContinuousLisse A X ⥤
    NormContinuousRepresentations A (Ω ≃ₐ[X.functionField] Ω)
  sections (L : NormContinuousLisse A X) :
    (functor.obj L).obj.V ≃+ geometricSections X A Ω L

/-- Full faithfulness and the equations fixing scalars, arrows and Galois action by the
actual restricted sheaf. These specify canonical data, not arbitrary actions or maps.
Source: Bhatt--Scholze 7.4.7 and Example 4.1.10, DAG proof steps 5--8.
(blueprint: lem-sfb-normal-generic-lisse-cocycle). -/
def FiberFunctor.IsNormalized (F : FiberFunctor X A Ω) : Prop :=
  Nonempty F.functor.FullyFaithful ∧ F.functor.Additive ∧
  (∀ (L : NormContinuousLisse A X) (a : A) (v : (F.functor.obj L).obj.V),
    F.sections L (a • v) =
      (normContinuousScalar (Spec (.of X.functionField)) a (genericModule X A L)).hom.app
        (op (FieldSeparableCech.closureObject X.functionField Ω)) (F.sections L v)) ∧
  (∀ (L : NormContinuousLisse A X) (g : Ω ≃ₐ[X.functionField] Ω)
      (v : (F.functor.obj L).obj.V),
    F.sections L ((F.functor.obj L).obj.ρ g v) =
      (genericModule X A L).X.obj.map (automorphism X Ω g).op (F.sections L v)) ∧
  (∀ (L M : NormContinuousLisse A X) (f : L ⟶ M)
      (v : (F.functor.obj L).obj.V),
    F.sections M ((F.functor.map f).hom.hom v) =
      (((CondensedRing.upperStar (normContinuousRing A).X (genericMap X)).map f.hom).hom.hom.app
        (op (FieldSeparableCech.closureObject X.functionField Ω))) (F.sections L v)) ∧
  ∀ (L M : NormContinuousLisse A X) (f : L ⟶ M) (a : A), ∃ t : L ⟶ M,
    t.hom.hom = f.hom.hom ≫ normContinuousScalar X a M.obj ∧
      F.functor.map t = a • F.functor.map f

/-- The common rank is the dimension of the normalized section fibre; every nonempty
trivializing object has this rank, with no requirement of positive rank.
Source: Bhatt--Scholze 7.4.10, DAG proof step 5.
(blueprint: lem-sfb-normal-generic-lisse-cocycle). -/
def RankAssertions (F : FiberFunctor X A Ω) : Prop :=
  ∀ L : NormContinuousLisse A X, ∃ n : ℕ,
    Nonempty (Module.Basis (Fin n) A (F.functor.obj L).obj.V) ∧
    Module.finrank A (F.functor.obj L).obj.V = n ∧
    ∀ (U : X.ProEt), Nonempty U.left → ∀ r : ℕ,
      Nonempty ((CondensedRing.upperStar (normContinuousRing A).X U.hom).obj L.obj ≅
        Mod.finiteFree (coefficientRing U.left (normContinuousRing A)).X r) → r = n

/-- All rectangular constant matrices, including empty dimensions, descend precisely when
they intertwine the Galois matrices. The morphism and its matrix are unique.
Source: Bhatt--Scholze 7.4.7, DAG proof step 7.
(blueprint: lem-sfb-normal-generic-lisse-cocycle). -/
def HomAssertions (F : FiberFunctor X A Ω) : Prop :=
  ∀ (L M : NormContinuousLisse A X) (n m : ℕ)
    (b : Module.Basis (Fin n) A (F.functor.obj L).obj.V)
    (d : Module.Basis (Fin m) A (F.functor.obj M).obj.V)
    (T : Matrix (Fin m) (Fin n) A),
    (∃! f : L ⟶ M, LinearMap.toMatrix b d (F.functor.map f).hom.hom = T) ↔
      ∀ g : Ω ≃ₐ[X.functionField] Ω,
        T * LinearMap.toMatrix b b ((F.functor.obj L).obj.ρ g) =
          LinearMap.toMatrix d d ((F.functor.obj M).obj.ρ g) * T

/-- Sections of the actual norm-continuous pulled-back ring on a Cech object.
Source: Hemo--Richarz--Scholbach Example 3.1, DAG proof steps 2 and 6.
(blueprint: lem-sfb-normal-generic-lisse-cocycle). -/
abbrev coefficientSections (q : ℕ) : CommRingCat.{u + 1} :=
  (InternalAbelianSheafModule.sectionRings
    (Scheme.ProEt.topology (Spec (.of X.functionField)))
    (condensedRingObj (normContinuousRing A).X (Spec (.of X.functionField)))).obj
      (op (FieldSeparableCech.object X.functionField Ω q))

/-- Sectionwise scalar action is the action of the recorded internal/sectionwise module
functor, on precisely the original abelian sections.
Source: Hemo--Richarz--Scholbach Example 3.1, DAG proof steps 2 and 6.
(blueprint: lem-sfb-normal-generic-lisse-cocycle). -/
def sectionAction (L : NormContinuousLisse A X) (q : ℕ)
    (a : coefficientSections X A Ω q)
    (v : (genericModule X A L).X.obj.obj
      (op (FieldSeparableCech.object X.functionField Ω q))) :
    (genericModule X A L).X.obj.obj
      (op (FieldSeparableCech.object X.functionField Ω q)) :=
  let N := ((InternalAbelianSheafModule.sectionModuleFunctor
    (Scheme.ProEt.topology (Spec (.of X.functionField)))
    (condensedRingObj (normContinuousRing A).X (Spec (.of X.functionField)))).obj
      (genericModule X A L)).val.obj (op (FieldSeparableCech.object X.functionField Ω q))
  @SMul.smul _ N (ModuleCat.isModule N).toSMul a v

/-- The two vertex restrictions of a basis are related by the actual descent matrix.
The scalar entries are sections of the actual coefficient ring, obtained through theta.
Source: Bhatt--Scholze Example 4.1.10, DAG proof steps 6--7.
(blueprint: lem-sfb-normal-generic-lisse-cocycle). -/
def HasDescentMatrix (F : FiberFunctor X A Ω) (L : NormContinuousLisse A X) (n : ℕ)
    (b : Module.Basis (Fin n) A (F.functor.obj L).obj.V)
    (θ : coefficientSections X A Ω 1 ≃+*
      C((Ω ≃ₐ[X.functionField] Ω), A))
    (c : (Matrix (Fin n) (Fin n) C((Ω ≃ₐ[X.functionField] Ω), A))ˣ) : Prop :=
  ∀ i : Fin n,
    (genericModule X A L).X.obj.map
        (WidePullback.π
          (fun _ : Fin 2 ↦ (FieldSeparableCech.closureArrow X.functionField Ω).hom) 1).op
        (F.sections L (b i)) =
      ∑ j : Fin n, sectionAction X A Ω L 1 (θ.symm (c.val j i))
        ((genericModule X A L).X.obj.map
          (WidePullback.π
            (fun _ : Fin 2 ↦ (FieldSeparableCech.closureArrow X.functionField Ω).hom) 0).op
          (F.sections L (b j)))

/-- Canonical continuous Cech coordinates, normalized at every Galois point, and the
invertible descent matrix in every finite basis. The homomorphism law has order g h.
Source: Bhatt--Scholze Example 4.1.10, DAG proof step 6.
(blueprint: lem-sfb-normal-generic-lisse-cocycle). -/
def CocycleAssertions (F : FiberFunctor X A Ω) : Prop :=
  ∀ (e : ∀ q : ℕ, (FieldSeparableCech.object X.functionField Ω q).left ≅
    ((profiniteToProEtOf (Spec (.of Ω))).obj
      (FieldSeparableCech.power X.functionField Ω q)).left),
    FieldSeparableCech.AreCoordinates X.functionField Ω e →
    ∃ θ : coefficientSections X A Ω 1 ≃+*
        C((Ω ≃ₐ[X.functionField] Ω), A),
      (∀ (a : coefficientSections X A Ω 1)
        (g : Ω ≃ₐ[X.functionField] Ω),
        θ a g =
          ((ContinuousRingUniverse.comparison (Spec (.of X.functionField)) A).hom.app
            (op (FieldSeparableCech.object X.functionField Ω 1)) a).down
            ((FieldSeparableCech.testPoint X.functionField Ω 1 (fun _ ↦ g) ≫ (e 1).inv).base
              (IsLocalRing.closedPoint Ω))) ∧
      ∀ (L : NormContinuousLisse A X) (n : ℕ)
        (b : Module.Basis (Fin n) A (F.functor.obj L).obj.V),
        ∃ (c : (Matrix (Fin n) (Fin n) C((Ω ≃ₐ[X.functionField] Ω), A))ˣ)
          (σ : (Ω ≃ₐ[X.functionField] Ω) →* (Matrix (Fin n) (Fin n) A)ˣ),
          HasDescentMatrix X A Ω F L n b θ c ∧
          Continuous (fun g ↦ (σ g).val) ∧
          ∀ (g : Ω ≃ₐ[X.functionField] Ω) (i j : Fin n),
            (c.val i j) g = (σ g).val i j ∧
            (σ g).val i j =
              LinearMap.toMatrix b b ((F.functor.obj L).obj.ρ g) i j

/-- Basis replacement conjugates the cocycle, and changes rectangular arrow coordinates
by the corresponding left and right transition matrices.
Source: Bhatt--Scholze 7.4.7, DAG proof step 8.
(blueprint: lem-sfb-normal-generic-lisse-cocycle). -/
def BasisChangeAssertions (F : FiberFunctor X A Ω) : Prop :=
  (∀ (L : NormContinuousLisse A X) (n : ℕ)
    (b b' : Module.Basis (Fin n) A (F.functor.obj L).obj.V)
    (g : Ω ≃ₐ[X.functionField] Ω),
    LinearMap.toMatrix b' b' ((F.functor.obj L).obj.ρ g) =
      LinearMap.toMatrix b b' LinearMap.id *
        LinearMap.toMatrix b b ((F.functor.obj L).obj.ρ g) *
          LinearMap.toMatrix b' b LinearMap.id) ∧
  ∀ (L M : NormContinuousLisse A X) (n m : ℕ)
    (b b' : Module.Basis (Fin n) A (F.functor.obj L).obj.V)
    (d d' : Module.Basis (Fin m) A (F.functor.obj M).obj.V) (f : L ⟶ M),
    LinearMap.toMatrix b' d' (F.functor.map f).hom.hom =
      LinearMap.toMatrix d d' LinearMap.id *
        LinearMap.toMatrix b d (F.functor.map f).hom.hom *
          LinearMap.toMatrix b' b LinearMap.id

/-- Regular-module and direct-sum normalizations. The sum is identified using its actual
projection arrows, so its action is the block sum in concatenated coordinates.
Source: Bhatt--Scholze 7.4.7, DAG proof step 8.
(blueprint: lem-sfb-normal-generic-lisse-cocycle). -/
def UnitSumAssertions (F : FiberFunctor X A Ω) : Prop :=
  (∃ h : IsLisseCoefficientModule (normContinuousRing A).X
      (Mod.regular (coefficientRing X (normContinuousRing A)).X),
    Nonempty ((F.functor.obj ⟨_, h⟩).obj ≅
      Rep.trivial A (Ω ≃ₐ[X.functionField] Ω) (ULift.{u + 1} A))) ∧
  ∀ L M : NormContinuousLisse A X,
    ∃ h : IsLisseCoefficientModule (normContinuousRing A).X (L.obj ⊞ M.obj),
      ∃ E : (F.functor.obj ⟨_, h⟩).obj.V ≃ₗ[A]
          ((F.functor.obj L).obj.V × (F.functor.obj M).obj.V),
        (∀ v : (F.functor.obj ⟨_, h⟩).obj.V,
          E v =
            ((F.functor.map
                (ObjectProperty.homMk (biprod.fst : L.obj ⊞ M.obj ⟶ L.obj) :
                  (⟨_, h⟩ : NormContinuousLisse A X) ⟶ L)).hom.hom v,
             (F.functor.map
                (ObjectProperty.homMk (biprod.snd : L.obj ⊞ M.obj ⟶ M.obj) :
                  (⟨_, h⟩ : NormContinuousLisse A X) ⟶ M)).hom.hom v)) ∧
        ∀ (g : Ω ≃ₐ[X.functionField] Ω) (v : (F.functor.obj ⟨_, h⟩).obj.V),
          E ((F.functor.obj ⟨_, h⟩).obj.ρ g v) =
            ((F.functor.obj L).obj.ρ g (E v).1, (F.functor.obj M).obj.ρ g (E v).2)

/-- The complete generic-restriction assertion after the integrality conclusion is known.
The separable closure and normed coefficient field are arbitrary in the scheme universe;
no completeness, nontrivial valuation or coefficient algebraic closure is assumed.
Source: Bhatt--Scholze 7.4.7--7.4.10, DAG proof steps 2--8.
(blueprint: lem-sfb-normal-generic-lisse-cocycle). -/
def Assertions : Prop :=
  (∀ (U : X.ProEt), IsAffine U.left → Nonempty U.left →
    Nonempty (pullback (C := Scheme.{u}) U.hom (genericMap X))) ∧
  ∀ (A : Type u) [NormedField A] [IsUltrametricDist A],
    RestrictionAssertions X A ∧
    TotallyDisconnectedSpace A ∧
    (∀ (a b : A), a ≠ b → ∀ r : ℝ, 0 < r → r < dist a b →
      IsClopen (Metric.ball a r) ∧ a ∈ Metric.ball a r ∧ b ∉ Metric.ball a r) ∧
    IsIso (ContinuousRingUniverse.comparison X A) ∧
    ∀ (Ω : Type u) [Field Ω] [Algebra X.functionField Ω] [IsSepClosure X.functionField Ω],
      ∃ F : FiberFunctor X A Ω,
        F.IsNormalized ∧ RankAssertions X A Ω F ∧ CocycleAssertions X A Ω F ∧
          HomAssertions X A Ω F ∧ BasisChangeAssertions X A Ω F ∧ UnitSumAssertions X A Ω F

end NormalGenericLisse

/-- Generic restriction is fully faithful for lisse normed coefficient modules on a
nonempty connected normal Noetherian scheme, and its section fibres give the normalized
continuous Galois cocycles and all the asserted matrix, rank and sum compatibilities.
Source: Bhatt--Scholze 7.4.7 and 7.4.10, pp. 70--71; the agent normed-field extension.
(blueprint: lem-sfb-normal-generic-lisse-cocycle).

Proof: (1) Noetherian topology and the normal-component decomposition give finitely many
clopen integral components. Nonempty connectedness leaves one, so X is integral.
(2) Ultrametric balls are clopen and separate distinct points. Thus A is totally
disconnected, and the normalized continuous coefficient realization applies.
(3) normal_generic_continuous_sections extends coefficient functions uniquely from
U_eta to every affine pro-etale U. A nonempty U has distinct constants 0 and 1;
its generic fibre cannot be empty, since its function ring would then be a singleton.
(4) Choose common affine local free bases for L and M. Extend the generic matrix
entries uniquely. Compare on affine refinements of overlaps by injectivity, then
use sheaf gluing to obtain a unique global module map. Entrywise extension is
A-linear. Extend an inverse to see that generic restriction reflects isomorphisms.
(5) FieldSeparableCech.module_coordinates trivializes L over the separable closure.
Its sections are A^n. Every nonempty trivializing object has nonempty generic fibre;
after faithfully flat extension to the closure it remains nonempty. Evaluating inverse
rectangular trivialization matrices at a point forces its rank to equal n.
(6) Compare the two pulled-back bases on the double overlap. The free-module matrix
calculation gives an invertible section matrix. FieldSeparableCech.section_coordinates
identifies its entries with C(G_k,A), with c(gh)=c(g)c(h). Evaluation gives a continuous
homomorphism into GL_n(A), whose action is restriction along Spec of g.
(7) A constant rectangular matrix descends iff T c_L=c_M T. Necessity is restriction
naturality; sufficiency is the sheaf equalizer/gluing axiom along Spec Ω -> Spec k.
Evaluation gives the intertwining equations, and step (4) returns to X.
(8) Changing basis by P conjugates by P inverse on the left; arrow matrices change by
Q inverse on the left and P on the right. Sections and restriction supply the functor
and its linearity. The unit basis has cocycle 1. Direct sums concatenate bases and give
block sums. Empty bases and rectangular matrices with an empty dimension give the
unique zero maps, so rank zero is included throughout. -/
theorem normal_generic_lisse_cocycle (X : Scheme.{u}) [ConnectedSpace X] [IsNoetherian X]
    (hnormal : ∀ x : X,
      IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)) :
    IsIntegral X ∧ ∀ hX : IsIntegral X, @NormalGenericLisse.Assertions.{u} X hX := by
  sorry

end AlgebraicGeometry.ProEtale

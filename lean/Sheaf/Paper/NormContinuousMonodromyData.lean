/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.Topology.ContinuousMapCondensedRingMap
public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import Sheaf.AlgebraicGeometry.FundamentalGroup.FLCFiber
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-! # Data for monodromy with full continuous norm-topology coefficients

Source: Bhatt--Scholze, Section 7.4, Lemmas 7.4.7 and 7.4.10, and the norm-topology
strengthening in the proof of lem-sfb-normal-continuous-algcl-monodromy.
(blueprint: def-sfb-norm-continuous-monodromy-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- The recorded all-continuous condensed ring, with its recorded multiplication.
Source: Bhatt--Scholze 7.4.7, norm-topology coefficient strengthening
(blueprint: def-sfb-norm-continuous-monodromy-data). -/
def normContinuousRing (K : Type u) [NormedField K] :
    Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
  { X := Profinite.continuousMapRingObjOfUniverse.{u, u} K
    mon := Profinite.continuousMapRingObjOfUniverseMonObj K }

/-- Commutativity uses the recorded pointwise ring structure, not another multiplication.
Source: Bhatt--Scholze 7.4.7, commutative field coefficients
(blueprint: def-sfb-norm-continuous-monodromy-data). -/
instance normContinuousRing_comm (K : Type u) [NormedField K] :
    IsCommMonObj (normContinuousRing K).X :=
  Profinite.isCommMonObj_continuousMapRingObjOfUniverse K

/-- The full subcategory of the recorded internal module category on lisse objects.
Source: Bhatt--Scholze 7.4.7, Loc_X(K)
(blueprint: def-sfb-norm-continuous-monodromy-data). -/
abbrev NormContinuousLisse (K : Type u) [NormedField K] (X : Scheme.{u}) :=
  ObjectProperty.FullSubcategory (IsLisseCoefficientModule (normContinuousRing K).X (X := X))

/-- Finite-dimensional representations with continuous matrix entries in a finite basis.
The empty basis is permitted. Arrows are all equivariant linear maps, inherited from Rep.
Source: Bhatt--Scholze 7.4.7, Rep_cont(K), with the specified norm topology
(blueprint: def-sfb-norm-continuous-monodromy-data). -/
abbrev NormContinuousRepresentations (K : Type u) [NormedField K]
    (G : Type v) [Group G] [TopologicalSpace G] :=
  ObjectProperty.FullSubcategory (fun V : Rep.{u + 1} K G ↦
    ∃ (n : ℕ) (b : Module.Basis (Fin n) K V.V),
      ∀ i j : Fin n, Continuous (fun g : G ↦ b.repr (V.ρ g (b j)) i))

/-- Postcomposition by a continuous field inclusion, then the specified p_X^*.
Source: Bhatt--Scholze 7.4.7, coefficient comparison
(blueprint: def-sfb-norm-continuous-monodromy-data). -/
def normContinuousCoefficientMap {E K : Type u} [NormedField E] [NormedField K]
    (X : Scheme.{u}) (f : E →+* K) (hf : Continuous f) :
    (coefficientRing X (normContinuousRing E)).X ⟶
      (coefficientRing X (normContinuousRing K)).X :=
  (upperStarFromPoint X).map (Profinite.continuousMapRingObjMapOfUniverse f hf)

/-- The postcomposition map is a ring-object map for the specified structures.
Source: Bhatt--Scholze 7.4.7, coefficient comparison
(blueprint: def-sfb-norm-continuous-monodromy-data). -/
instance normContinuousCoefficientMap_mon {E K : Type u} [NormedField E] [NormedField K]
    (X : Scheme.{u}) (f : E →+* K) (hf : Continuous f) :
    IsMonHom (normContinuousCoefficientMap X f hf) :=
  letI := Profinite.continuousMapRingObjOfUniverseMonObj E
  letI := Profinite.continuousMapRingObjOfUniverseMonObj K
  letI := Profinite.isMonHom_continuousMapRingObjMapOfUniverse f hf
  inferInstanceAs (IsMonHom ((upperStarFromPoint X).map
    (Profinite.continuousMapRingObjMapOfUniverse f hf)))

/-- Commutativity after the specified pullback from the point.
Source: Bhatt--Scholze 7.4.7, field coefficients
(blueprint: def-sfb-norm-continuous-monodromy-data). -/
instance normContinuousCoefficient_comm (K : Type u) [NormedField K] (X : Scheme.{u}) :
    IsCommMonObj (coefficientRing X (normContinuousRing K)).X :=
  inferInstanceAs (IsCommMonObj (condensedRingObj (normContinuousRing K).X X))

/-- Ordinary internal extension along the canonical postcomposition coefficient map.
Source: Bhatt--Scholze 7.4.7, coefficient comparison
(blueprint: def-sfb-norm-continuous-monodromy-data). -/
abbrev normContinuousExtension {E K : Type u} [NormedField E] [NormedField K]
    (X : Scheme.{u}) (f : E →+* K) (hf : Continuous f) :=
  Mod.extendScalars (normContinuousCoefficientMap X f hf)

/-- Multiplication by a constant on the all-continuous condensed coefficient sheaf.
Source: Bhatt--Scholze 7.4.7, K-linearity
(blueprint: def-sfb-norm-continuous-monodromy-data). -/
def normContinuousMultiply {K : Type u} [NormedField K] (a : K) :
    (normContinuousRing K).X ⟶ (normContinuousRing K).X :=
  ⟨{ app := fun S ↦ AddCommGrpCat.ofHom
      { toFun := fun f ↦ ULift.up (ContinuousMap.const S.unop a * f.down)
        map_zero' := congrArg ULift.up (mul_zero _)
        map_add' := fun f g ↦ congrArg ULift.up (mul_add _ f.down g.down) }
     naturality := fun _ _ _ ↦ rfl }⟩

/-- The constant scalar a in R_{K,X}, as a morphism out of the tensor unit.
Source: Bhatt--Scholze 7.4.7, K-linearity
(blueprint: def-sfb-norm-continuous-monodromy-data). -/
def normContinuousConstant {K : Type u} [NormedField K] (X : Scheme.{u}) (a : K) :
    𝟙_ (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ⟶
      (coefficientRing X (normContinuousRing K)).X :=
  Functor.LaxMonoidal.ε (upperStarFromPoint X) ≫
    (upperStarFromPoint X).map
      (MonObj.one (X := (normContinuousRing K).X) ≫ normContinuousMultiply a)

/-- The underlying abelian-sheaf endomorphism given by the constant scalar a.
Source: Bhatt--Scholze 7.4.7, K-linearity
(blueprint: def-sfb-norm-continuous-monodromy-data). -/
def normContinuousScalar {K : Type u} [NormedField K] (X : Scheme.{u}) (a : K)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (coefficientRing X (normContinuousRing K)).X) : M.X ⟶ M.X :=
  (λ_ M.X).inv ≫ (normContinuousConstant X a ▷ M.X) ≫
    ModObj.smul (M := (coefficientRing X (normContinuousRing K)).X) (X := M.X)

/-- A K-linear monodromy equivalence, including its regular-module normalization.
Linearity is expressed on underlying sheaf morphisms using actual constant scalars.
Equivalence and additivity preserve finite direct sums, including the empty sum.
Source: Bhatt--Scholze 7.4.7 and 7.4.10, norm-topology strengthening
(blueprint: def-sfb-norm-continuous-monodromy-data). -/
structure NormContinuousMonodromy (K : Type u) [NormedField K] (X : Scheme.{u})
    (G : Type v) [Group G] [TopologicalSpace G] where
  equivalence : NormContinuousLisse K X ≌ NormContinuousRepresentations K G
  additive : equivalence.inverse.Additive
  linear : ∀ (V W : NormContinuousRepresentations K G) (f : V ⟶ W) (a : K),
    (equivalence.inverse.map (a • f)).hom.hom =
      (equivalence.inverse.map f).hom.hom ≫
        normContinuousScalar X a (equivalence.inverse.obj W).obj
  regular : ∃ h : IsLisseCoefficientModule (normContinuousRing K).X
      (Mod.regular (coefficientRing X (normContinuousRing K)).X),
    Nonempty ((equivalence.functor.obj ⟨_, h⟩).obj ≅
      Rep.trivial K G (ULift.{u + 1} K))

/-- Scalar compatibility data: a restriction of the actual ordinary internal extension,
with a natural vector-space isomorphism intertwining the scalar-extended action.
Its naturality and action equations are tested on pure tensors, which span the tensor.
Source: Bhatt--Scholze 7.4.7, norm-topology scalar comparison
(blueprint: def-sfb-norm-continuous-monodromy-data). -/
structure NormContinuousScalarComparison {E K : Type u} [NormedField E] [NormedField K]
    [Algebra E K] (X : Scheme.{u}) (G : Type v) [Group G] [TopologicalSpace G]
    (hf : Continuous (algebraMap E K))
    (eE : NormContinuousMonodromy E X G) (eK : NormContinuousMonodromy K X G) where
  extension : NormContinuousLisse E X ⥤ NormContinuousLisse K X
  extensionIso : extension ⋙ ObjectProperty.ι _ ≅
    ObjectProperty.ι _ ⋙ normContinuousExtension X (algebraMap E K) hf
  comparison : ∀ L : NormContinuousLisse E X,
    (K ⊗[E] (eE.equivalence.functor.obj L).obj.V) ≃ₗ[K]
      (eK.equivalence.functor.obj (extension.obj L)).obj.V
  equivariant : ∀ (L : NormContinuousLisse E X) (g : G) (a : K)
      (v : (eE.equivalence.functor.obj L).obj.V),
    comparison L (a ⊗ₜ[E] ((eE.equivalence.functor.obj L).obj.ρ g v)) =
      (eK.equivalence.functor.obj (extension.obj L)).obj.ρ g
        (comparison L (a ⊗ₜ[E] v))
  naturality : ∀ (L M : NormContinuousLisse E X) (f : L ⟶ M) (a : K)
      (v : (eE.equivalence.functor.obj L).obj.V),
    comparison M (a ⊗ₜ[E] (eE.equivalence.functor.map f).hom.hom v) =
      (eK.equivalence.functor.map (extension.map f)).hom.hom
        (comparison L (a ⊗ₜ[E] v))

end AlgebraicGeometry.ProEtale

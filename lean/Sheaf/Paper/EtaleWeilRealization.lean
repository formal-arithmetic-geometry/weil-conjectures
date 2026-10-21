/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P6
-/
module

public import Sheaf.Paper.EtaleWeilRepresentationData
public import Sheaf.Paper.EtaleWeilFiberHom

/-! # The normalized etale Weil realization functor

Source: Weil II (1.1.10)-(1.1.12). Objects and arrows are the recorded
fundamental representation and the actual etale stalk maps.
(blueprint: new-p6-etale-weil-realization)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
open FiniteEtale

variable (l : ℕ) [Fact l.Prime] (Q : Type (u + 1)) [Field Q]
  [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
  {Y : Scheme.{u}} [IsNoetherian Y] [Y.IsSeparated]
  [∀ x : Y, Invertible (l : Y.residueField x)]
  (h : Y ≅ Y) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (t : Spec (.of Ω) ⟶ Y) {G : Type v} [Group G]
  (d : Monodromy.DegreeDatum G) (D : EtaleWeilDegreeData h t G d)

variable [ConnectedSpace Y]

/-- The Hom equivalence is fixed uniquely by its underlying stalk map.
Source: Weil II (1.1.12) (blueprint: new-p6-etale-weil-realization). -/
def etaleWeilHomEquiv (F H : EtaleLisseWeilSheaf l Q h) :
    (F ⟶ H) ≃ (etaleFundamentalRep l Q h t d D F).IntertwiningMap
      (etaleFundamentalRep l Q h t d D H) :=
  (etaleWeilFiberHom l Q h t d D F H).choose

private theorem homEquiv_map {F H : EtaleLisseWeilSheaf l Q h} (a : F ⟶ H) :
    (etaleWeilHomEquiv l Q h t d D F H a).toLinearMap =
      (etaleAlgebraicFiberMap l Q t
        ((Endofunctor.IsoAlgebra.forget
          (lisseAlgebraicAutomorphismPullback h l Q)).map a)).hom :=
  (etaleWeilFiberHom l Q h t d D F H).choose_spec a

omit [ConnectedSpace Y] in
private theorem fiberMap_id (F : LisseAlgebraicSheaf l Y Q) :
    etaleAlgebraicFiberMap l Q t (𝟙 F) = 𝟙 _ := by
  simp [etaleAlgebraicFiberMap]

omit [ConnectedSpace Y] in
private theorem fiberMap_comp {F H K : LisseAlgebraicSheaf l Y Q}
    (a : F ⟶ H) (b : H ⟶ K) :
    etaleAlgebraicFiberMap l Q t (a ≫ b) =
      etaleAlgebraicFiberMap l Q t a ≫ etaleAlgebraicFiberMap l Q t b := by
  simp [etaleAlgebraicFiberMap, Category.assoc]

/-- The forward realization uses the actual fibres, without a coordinate replacement.
The representation belongs to the l-adic subcategory by its geometric restriction.
Source: Weil II (1.1.10)-(1.1.12) (blueprint: new-p6-etale-weil-realization). -/
def etaleWeilRealization :
    EtaleLisseWeilSheaf l Q h ⥤ etaleLisseWeilRepresentations l Q h t d D where
  obj F := ⟨Rep.of (etaleFundamentalRep l Q h t d D F),
    etaleFundamentalRep_isLAdic l Q h t d D F⟩
  map {F H} a := ObjectProperty.homMk
    (Rep.ofHom (etaleWeilHomEquiv l Q h t d D F H a))
  map_id F := by
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    change (etaleWeilHomEquiv l Q h t d D F F (𝟙 F)).toLinearMap = LinearMap.id
    exact (homEquiv_map l Q h t d D (𝟙 F)).trans
      (congrArg ModuleCat.Hom.hom (fiberMap_id l Q t F.carrier))
  map_comp {F H K} a b := by
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    change (etaleWeilHomEquiv l Q h t d D F K (a ≫ b)).toLinearMap =
      (etaleWeilHomEquiv l Q h t d D H K b).toLinearMap.comp
        (etaleWeilHomEquiv l Q h t d D F H a).toLinearMap
    calc
      _ = (etaleAlgebraicFiberMap l Q t
          ((Endofunctor.IsoAlgebra.forget
            (lisseAlgebraicAutomorphismPullback h l Q)).map (a ≫ b))).hom :=
        homEquiv_map l Q h t d D (a ≫ b)
      _ = (etaleAlgebraicFiberMap l Q t b.hom.f).hom.comp
          (etaleAlgebraicFiberMap l Q t a.hom.f).hom :=
        congrArg ModuleCat.Hom.hom (fiberMap_comp l Q t a.hom.f b.hom.f)
      _ = _ := congrArg₂ LinearMap.comp
        (homEquiv_map l Q h t d D b).symm (homEquiv_map l Q h t d D a).symm

/-- On arrows, realization is exactly the prescribed etale stalk map.
Source: Weil II (1.1.12) (blueprint: new-p6-etale-weil-realization). -/
theorem etaleWeilRealization_map {F H : EtaleLisseWeilSheaf l Q h} (a : F ⟶ H) :
    ((etaleWeilRealization l Q h t d D).map a).hom.hom.toLinearMap =
      (etaleAlgebraicFiberMap l Q t
        ((Endofunctor.IsoAlgebra.forget
          (lisseAlgebraicAutomorphismPullback h l Q)).map a)).hom :=
  homEquiv_map l Q h t d D a

/-- Full faithfulness is the Hom dictionary, with no essential-surjectivity assertion.
Source: Weil II (1.1.12) (blueprint: new-p6-etale-weil-realization). -/
def etaleWeilRealization_fullyFaithful :
    (etaleWeilRealization l Q h t d D).FullyFaithful where
  preimage {F H} a := (etaleWeilHomEquiv l Q h t d D F H).symm a.hom.hom
  map_preimage a := by
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    exact (etaleWeilHomEquiv l Q h t d D _ _).apply_symm_apply _
  preimage_map a := (etaleWeilHomEquiv l Q h t d D _ _).symm_apply_apply a

end AlgebraicGeometry.Scheme

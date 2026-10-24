/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Additivity
public import WeilConjectures.TraceFormula.FrobeniusLocalTerm
public import WeilConjectures.TraceFormula.GraphPieces
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleTriangulated

/-!

# The open–closed triangle and the closed piece at a fixed point

Let `x` be a rational point of `X` with open complement `j : U = X ∖ {x} ⟶ X`.

* The open–closed triangle `j_! Lj^* K ⟶ K ⟶ Ri_* Li^* K ⟶` of an open immersion `j` and a closed
  immersion `i` onto its complement is distinguished in the triangulated category `Dᵇc(X)` itself
  (`ProEtale.CondensedRing.exists_distTriang_openImmersionLowerShriek_lowerStar`), with the
  extension by zero `j_!`; in particular for `i = x`, `j = X ∖ {x}`
  (`ProEtale.CondensedRing.exists_distTriang_pointCompl_rationalPoint`).
* For a map `v : Lh^* K ⟶ K` and `x` fixed by `h`, the closed piece coefficient
  `u^Z = [x, x]_! v_x` is compatible with `v` along the unit `η : K ⟶ Rx_* Lx^* K`:
  `u^Z ∘ Lh^* η = η ∘ v` (blueprint `prop-trf-trace-class-additivity`, proof of item 2,
  step (b); `ProEtale.CondensedRing.Correspondence.upperStar_map_unit_comp_graphClosedPieceCoeff`),
  and likewise for the closed piece of a Weil object
  (`ProEtale.CondensedRing.WeilBoundedConstructible.upperStar_map_unit_comp_closedPieceCoeff`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-! ### The open–closed triangle in `Dᵇc(X)` -/

section Triangle

variable {X U Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  (j : U ⟶ X) [IsOpenImmersion j.left] (i : Z ⟶ X) [IsClosedImmersion i.left]

/-- **The open–closed localization triangle in `Dᵇc(X)`**: for an open immersion `j : U ⟶ X` and
a closed immersion `i : Z ⟶ X` onto its complement, the counit `j_! Lj^* K ⟶ K` of the extension
by zero and the unit `K ⟶ Ri_* Li^* K` of `Li^* ⊣ Ri_*` extend to a distinguished triangle of the
triangulated category `Dᵇc(X)`. The distinguished triangles of the full subcategory are those whose
image in the ambient derived category is distinguished, so this is
`exists_distTriang_openImmersionLowerShriek_openClosed`. -/
theorem exists_distTriang_openImmersionLowerShriek_lowerStar
    (hcompl : IsCompl (Set.range j.left.base) (Set.range i.left.base))
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ∃ δ, Triangle.mk
        ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j).counit.app K)
        ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ i).unit.app K) δ ∈
      distTriang (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) := by
  obtain ⟨δ, hδ⟩ := exists_distTriang_openImmersionLowerShriek_openClosed j i hcompl K
  obtain ⟨δ₀, rfl⟩ := WeilBoundedConstructible.exists_eq_map_comp_commShiftIso
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).fullyFaithfulι
    δ
  exact ⟨δ₀, hδ⟩

/-- **The open–closed triangle of a rational point**: with `j : X ∖ {x} ⟶ X` the open complement
of a rational point `x`, the triangle `j_! Lj^* K ⟶ K ⟶ Rx_* Lx^* K ⟶` is distinguished in
`Dᵇc(X)`. -/
theorem exists_distTriang_pointComplι_rationalPoint (x : RationalPoint X)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ∃ δ, Triangle.mk
        ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ
          (pointComplι x)).counit.app K)
        ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ x).unit.app K) δ ∈
      distTriang (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :=
  exists_distTriang_openImmersionLowerShriek_lowerStar (pointComplι x) x
    (isCompl_range_pointComplι x) K

end Triangle

/-! ### The closed piece and the unit -/

variable {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

/-- Transport of `Ly^* a` along an equality `y = x` of morphisms. -/
lemma boundedConstructibleUpperStar_map_comp_eqToHom {P : Over (Spec (.of k))}
    [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom] {y x : P ⟶ X}
    (e : y = x) {A B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (a : A ⟶ B) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ y).map a ≫
        eqToHom (by rw [e]) =
      eqToHom (by rw [e]) ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).map a := by
  subst e
  simp

namespace Correspondence

variable (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) {h : X ⟶ X}
  (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).obj K ⟶ K)
  {x : RationalPoint X} (hx : x ≫ h = x)

/-- The proper pushforward diagram `(x, x)` from the point correspondence `(s, 𝟙, 𝟙)` of an
arbitrary endomorphism `w` of the stalk `Lx^* K` to the graph `(𝟙, h)`, for `x` fixed by `h`.
For `w = v_x` it is `graphClosedPieceDiagram`. -/
noncomputable abbrev pointPushforwardDiagram
    (w : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K ⟶
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K) :
    (ofEnd _ w).ProperPushforwardDiagram X where
  f := x
  D := X
  b₁ := 𝟙 X
  b₂ := h
  g := x
  w₁ := by
    rw [Category.comp_id]
    exact (Category.id_comp x).symm
  w₂ := by
    rw [hx]
    exact (Category.id_comp x).symm

set_option backward.isDefEq.respectTransparency true in
/-- The stalk computation behind `upperStar_map_unit_comp_pushforwardCoeffUnit`: the composite
```
Lx^* Lh^* K --Lx^* Lh^* η--> Lx^* Lh^* Rx_* Lx^* K ≅ L(𝟙)^* Lx^* Rx_* Lx^* K --ε--> L(𝟙)^* Lx^* K
  ≅ Lx^* K --v_x--> Lx^* K
```
is `Lx^* v`, by the triangle identity of `Lx^* ⊣ Rx_*`. -/
lemma upperStar_map_unit_comp_comp_graphStalkMap :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).map
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).map
          ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ x).unit.app K)) ≫
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ x h).inv.app
        (pointClosedPiece K x) ≫
      eqToHom (by rw [hx, Category.id_comp]) ≫
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 (point k)) x).hom.app
        (pointClosedPiece K x) ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 (point k))).map
        ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ x).counit.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K)) ≫
      (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ (point k)).hom.app _ ≫
      graphStalkMap K h v x hx =
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).map v := by
  have h₁ := (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ x h).inv.naturality
    ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ x).unit.app K)
  have h₂ := (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ (point k)).hom.naturality
    ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ x).counit.app
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K))
  have h₃ := boundedConstructibleUpperStarComp_id_left_app (Profinite.padicAlgClRingObj ℓ) ℓ x
    (pointClosedPiece K x)
  have h₄ := boundedConstructibleUpperStar_map_comp_eqToHom hx
    ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ x).unit.app K)
  have h₅ := (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ x).left_triangle_components K
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at h₁ h₂
  dsimp only [Functor.id_obj]
  rw [graphStalkMap, reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, eqToHom_trans_assoc,
    reassoc_of% h₄, reassoc_of% h₅, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, Iso.inv_hom_id_app_assoc]

set_option backward.isDefEq.respectTransparency true in
/-- The ordinary half `γ` of the coefficient pushforward along `(x, x)`:
`Lh^* K^Z --η--> Rx_* Lx^* Lh^* K^Z ≅ Rx_* L(𝟙)^* Lx^* K^Z --ε--> Rx_* L(𝟙)^* Lx^* K`. -/
lemma pushforwardCoeffUnit_pointPushforwardDiagram
    (w : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K ⟶
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K) :
    (pointPushforwardDiagram K hx w).pushforwardCoeffUnit =
      (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ x).unit.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).obj
            (pointClosedPiece K x)) ≫
        (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ x).map
          ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ x h).inv.app
              (pointClosedPiece K x) ≫
            eqToHom (by rw [hx, Category.id_comp]) ≫
            (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 (point k))
              x).hom.app (pointClosedPiece K x) ≫
            (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 (point k))).map
              ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ x).counit.app
                ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K))) :=
  by
  dsimp only [ProperPushforwardDiagram.pushforwardCoeffUnit, pointPushforwardDiagram, ofEnd,
    ProperPushforwardDiagram.coeff]
  rfl

set_option backward.isDefEq.respectTransparency true in
/-- The exceptional half `δ` of the coefficient pushforward along `(x, x)` is the identity, up to
`R(𝟙)^! ≅ 𝟭`. -/
lemma pushforwardCoeffCounit_pointPushforwardDiagram
    (w : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K ⟶
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K) :
    (pointPushforwardDiagram K hx w).pushforwardCoeffCounit =
      (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ x).map
          ((boundedConstructibleUpperShriekId ℓ (point k)).hom.app
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K)) ≫
        (boundedConstructibleUpperShriekId ℓ X).inv.app (pointClosedPiece K x) := sorry

set_option backward.isDefEq.respectTransparency true in
/-- The ordinary half `γ` of the coefficient pushforward along `(x, x)` of the stalk map `v_x`,
followed by `v_x`, is adjoint to `Lx^* v`: precomposed with `Lh^* η`, it is `η ∘ v`. -/
lemma upperStar_map_unit_comp_pushforwardCoeffUnit :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).map
        ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ x).unit.app K) ≫
      (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ x).unit.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).obj
            (pointClosedPiece K x)) ≫
        (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ x).map
          ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ x h).inv.app
              (pointClosedPiece K x) ≫
            eqToHom (by rw [hx, Category.id_comp]) ≫
            (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 (point k))
              x).hom.app (pointClosedPiece K x) ≫
            (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 (point k))).map
              ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ x).counit.app
                ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K))) ≫
      (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ x).map
        ((boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ (point k)).hom.app _ ≫
          graphStalkMap K h v x hx) =
      v ≫ (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ x).unit.app K := by sorry

set_option backward.isDefEq.respectTransparency true in
/-- The coefficient pushforward along `(x, x)` of the stalk map `v_x` is compatible with `v`
along the unit `η : K ⟶ Rx_* Lx^* K`. -/
lemma upperStar_map_unit_comp_pushforwardCoeff_pointPushforwardDiagram
    (w : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K ⟶
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K)
    (hw : w = graphStalkMap K h v x hx) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).map
        ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ x).unit.app K) ≫
      (pointPushforwardDiagram K hx w).pushforwardCoeff =
      v ≫ (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ x).unit.app K ≫
        (boundedConstructibleUpperShriekId ℓ X).inv.app _ := by sorry

/-- **The closed piece coefficient is compatible with the unit** (blueprint
`prop-trf-trace-class-additivity`, proof of item 2, step (b)): for `x` fixed by `h`, the closed
piece coefficient `u^Z = [x, x]_! v_x` satisfies `u^Z ∘ Lh^* η = η ∘ v` for the unit
`η : K ⟶ Rx_* Lx^* K`, up to `R(𝟙)^! ≅ 𝟭`. -/
theorem upperStar_map_unit_comp_graphClosedPieceCoeff :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).map
        ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ x).unit.app K) ≫
      graphClosedPieceCoeff K v hx =
      v ≫ (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ x).unit.app K ≫
        (boundedConstructibleUpperShriekId ℓ X).inv.app _ :=
  upperStar_map_unit_comp_pushforwardCoeff_pointPushforwardDiagram K v hx _ rfl

end Correspondence

namespace WeilBoundedConstructible

variable {Φ : X ⟶ X}

/-- **The closed piece coefficient of a Weil object is compatible with the unit** (blueprint
`prop-trf-trace-class-additivity`, proof of item 2, step (b)): for `x` fixed by `Φ_m`, the closed
piece coefficient `u^Z = [x, x]_! F_{x,m}` satisfies `u^Z ∘ LΦ_m^* η = η ∘ φ_m` for the unit
`η : K ⟶ Rx_* Lx^* K`, up to `R(𝟙)^! ≅ 𝟭`. -/
theorem upperStar_map_unit_comp_closedPieceCoeff (K : WeilBoundedConstructible ℓ Φ) (m : ℕ)
    (x : RationalPoint X) (hx : x ≫ frobeniusIterate Φ m = x) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (frobeniusIterate Φ m)).map
        ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ x).unit.app K.carrier) ≫
      K.closedPieceCoeff m x hx =
      (K.iterateStr m).hom ≫
        (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ x).unit.app K.carrier ≫
        (boundedConstructibleUpperShriekId ℓ X).inv.app _ :=
  Correspondence.upperStar_map_unit_comp_pushforwardCoeff_pointPushforwardDiagram K.carrier
    (K.iterateStr m).hom hx _ (stalkFrobenius_eq_graphStalkMap K m x hx)

end WeilBoundedConstructible

end AlgebraicGeometry.ProEtale.CondensedRing

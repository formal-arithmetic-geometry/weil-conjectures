/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Jacobson.Ring
public import WeilConjectures.TraceFormula.PointTrace
public import WeilConjectures.TraceFormula.Specialization.PointsSupport

/-!

# Complexes supported at finitely many closed points

Let `V` be a separated scheme of finite type over a separably closed field `k` and `S` a finite
set of closed points of `V`. A bounded constructible `ℚ̄_ℓ`-complex `C` on `V` whose restriction to
`V ∖ S` vanishes, and whose global sections `RΓ(V, C)` vanish, is zero
(`ProEtale.CondensedRing.isZero_of_isZero_upperStar_finsetComplOpens`, blueprint
`det-nearby-kunneth-finite-support`).

The closed points need not be rational: `k` need not be perfect. This generalises
`WeilConjectures.TraceFormula.Specialization.PointsSupport` (rational points). The residue field
`κ(z)` of a closed point is finite, hence purely inseparable, over `k`, so it is separably closed
(`ProEtale.CondensedRing.isSepClosed_of_locallyOfFiniteType`). Every bounded constructible complex
on `Spec κ(z)` is then a finite direct sum of shifts of the unit, and `RΓ(Spec κ(z), -)` detects
vanishing (`ProEtale.CondensedRing.isZero_of_isZero_lowerStar_toPoint_of_isSepClosed`): a summand
`𝟙⟦d⟧ = La^* 𝟙⟦d⟧ ⟶ E` is adjoint to a morphism into `Ra_* E = 0`. The open–closed triangle at a
closed point then splits as for rational points, and one concludes by induction on `S`.

-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Residue fields of closed points -/

section ResidueField

variable {k : Type u} [Field k] (K : Type u) [Field K]

/-- A field of finite type over a separably closed field `k` (through a morphism
`Spec K ⟶ Spec k` locally of finite type) is separably closed: it is finite, hence purely
inseparable, over `k`. -/
lemma isSepClosed_of_locallyOfFiniteType [IsSepClosed k] (g : Spec (.of K) ⟶ Spec (.of k))
    [LocallyOfFiniteType g] : IsSepClosed K := by
  let f : CommRingCat.of k ⟶ CommRingCat.of K := Spec.preimage g
  have hf : f.hom.FiniteType := by
    have : LocallyOfFiniteType (Spec.map f) := by
      rw [Spec.map_preimage]
      infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  letI := f.hom.toAlgebra
  have : Algebra.FiniteType k K := hf
  have := finite_of_finite_type_of_isJacobsonRing k K
  exact Algebra.IsAlgebraic.isSepClosed (F := k) (E := K)

/-- A field receiving a morphism from `k` has the characteristic of `k`. -/
lemma ringChar_eq_of_spec (g : Spec (.of K) ⟶ Spec (.of k)) : ringChar K = ringChar k := by
  letI := (Spec.preimage g).hom.toAlgebra
  exact (Algebra.ringChar_eq k K).symm

end ResidueField

/-! ### Closed points as schemes over `k` -/

section ClosedPoint

variable {k : Type u} [Field k] {V : Over (Spec (.of k))}

/-- The closed point `Spec κ(z)` of `V`, as a scheme over `k`. -/
noncomputable abbrev closedPointOver (z : V.left) : Over (Spec (.of k)) :=
  Over.mk (V.left.fromSpecResidueField z ≫ V.hom)

/-- The inclusion `Spec κ(z) ⟶ V` of a point. -/
noncomputable abbrev closedPointι (z : V.left) : closedPointOver z ⟶ V :=
  Over.homMk (V.left.fromSpecResidueField z)

lemma range_closedPointι (z : V.left) : Set.range (closedPointι z).left.base = {z} :=
  Scheme.range_fromSpecResidueField z

lemma isClosedImmersion_closedPointι {z : V.left} (hz : IsClosed {z}) :
    IsClosedImmersion (closedPointι z).left :=
  isClosed_singleton_iff_isClosedImmersion.1 hz

lemma locallyOfFiniteType_closedPointOver [LocallyOfFiniteType V.hom] {z : V.left}
    (hz : IsClosed {z}) : LocallyOfFiniteType (closedPointOver z).hom := by
  have : IsClosedImmersion (V.left.fromSpecResidueField z) :=
    isClosed_singleton_iff_isClosedImmersion.1 hz
  exact inferInstanceAs (LocallyOfFiniteType (V.left.fromSpecResidueField z ≫ V.hom))

lemma quasiCompact_closedPointOver [QuasiCompact V.hom] {z : V.left}
    (hz : IsClosed {z}) : QuasiCompact (closedPointOver z).hom := by
  have : IsClosedImmersion (V.left.fromSpecResidueField z) :=
    isClosed_singleton_iff_isClosedImmersion.1 hz
  exact inferInstanceAs (QuasiCompact (V.left.fromSpecResidueField z ≫ V.hom))

lemma isSeparated_closedPointOver [IsSeparated V.hom] {z : V.left}
    (hz : IsClosed {z}) : IsSeparated (closedPointOver z).hom := by
  have : IsClosedImmersion (V.left.fromSpecResidueField z) :=
    isClosed_singleton_iff_isClosedImmersion.1 hz
  exact inferInstanceAs (IsSeparated (V.left.fromSpecResidueField z ≫ V.hom))

end ClosedPoint

/-! ### Global sections on a separably closed point -/

section Point

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- **Global sections detect vanishing on a separably closed point**: let `P` be a `k`-scheme
of finite type whose underlying scheme is `Spec K` for a separably closed field `K`. A bounded
constructible complex `E` on `P` with `RΓ(P, E) = 0` vanishes. Indeed `E` is a finite direct sum of
shifts `𝟙⟦d⟧` of the unit, and every morphism `𝟙⟦d⟧ = La^* 𝟙⟦d⟧ ⟶ E` is adjoint to a morphism
`𝟙⟦d⟧ ⟶ Ra_* E = 0`. -/
theorem isZero_of_isZero_lowerStar_toPoint_of_isSepClosed {P : Over (Spec (.of k))}
    [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
    (K : Type u) [Field K] [IsSepClosed K] [Fact (ringChar K).Prime] [Fact (ringChar K ≠ ℓ)]
    (hP : P.left = Spec (.of K)) (E : Dᵇc(P.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hE : IsZero ((boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (toPoint P)).obj E)) : IsZero E := by
  obtain ⟨P, f, rfl⟩ : ∃ (P' : Scheme.{u}) (f : P' ⟶ Spec (.of k)), P = Over.mk f :=
    ⟨P.left, P.hom, rfl⟩
  dsimp only [Over.mk_left] at hP
  subst hP
  let Dc := (nonempty_shiftDecomposition_point ℓ K E).some
  set adj := boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
    (toPoint (Over.mk f))
  have hincl : ∀ j, Dc.incl j = 0 := fun j ↦ by
    let e : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (toPoint (Over.mk f))).obj ((shiftFunctor _ (Dc.deg j)).obj (𝟙_ _)) ≅
        (shiftFunctor _ (Dc.deg j)).obj (𝟙_ _) :=
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (toPoint (Over.mk f))).commShiftIso (Dc.deg j)).app _ ≪≫
        (shiftFunctor _ (Dc.deg j)).mapIso (Functor.Monoidal.εIso _).symm
    have h0 : adj.homEquiv _ _ (e.hom ≫ Dc.incl j) = 0 := hE.eq_of_tgt _ _
    have h1 : e.hom ≫ Dc.incl j = 0 := by
      rw [← (adj.homEquiv _ _).symm_apply_apply (e.hom ≫ Dc.incl j), h0,
        Adjunction.homEquiv_counit, Functor.map_zero, zero_comp]
    simpa using h1
  refine (IsZero.iff_id_eq_zero E).2 ?_
  rw [← Dc.total]
  exact Finset.sum_eq_zero fun j _ ↦ by rw [hincl j, comp_zero]

end Point

/-! ### Open–closed vanishing at a closed point -/

section Vanishing

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]

/-- **Open–closed detection of vanishing**: if `x : P ⟶ V` is a closed immersion and
`g : Y ⟶ V` a quasi-compact morphism with complementary range, then a complex `E` with
`Lx^* E = 0` and `Lg^* E = 0` vanishes. -/
theorem isZero_of_isCompl_range_of_isClosedImmersion {V : Over (Spec (.of k))}
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    {P : Over (Spec (.of k))} [LocallyOfFiniteType P.hom] [QuasiCompact P.hom]
    [IsSeparated P.hom] (x : P ⟶ V) [IsClosedImmersion x.left]
    {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y.hom] (g : Y ⟶ V) [QuasiCompact g.left]
    (hcompl : IsCompl (Set.range x.left.base) (Set.range g.left.base))
    (E : Dᵇc(V.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hxE : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj E))
    (hgE : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).obj E)) :
    IsZero E := by
  have hiso := isIso_of_isIso_boundedConstructibleUpperStar_map_of_isCompl _ ℓ x g hcompl
    (0 : E ⟶ E) ⟨⟨hgE.to_ _, hgE.eq_of_src _ _, hgE.eq_of_src _ _⟩⟩
    ⟨⟨hxE.to_ _, hxE.eq_of_src _ _, hxE.eq_of_src _ _⟩⟩
  refine (IsZero.iff_id_eq_zero _).2 ?_
  rw [← IsIso.hom_inv_id (0 : E ⟶ E), zero_comp]

omit [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] in
/-- The factorization through an open `W` of a closed immersion with range in `W` is a closed
immersion. -/
lemma isClosedImmersion_opensOverLift (W : X.left.Opens) {P : Over (Spec (.of k))}
    (x : P ⟶ X) [IsClosedImmersion x.left] (hx : Set.range x.left.base ⊆ W) :
    IsClosedImmersion (opensOverLift W x hx).left := by
  have h : (opensOverLift W x hx).left ≫ W.ι = x.left :=
    congrArg CommaMorphism.left (opensOverLift_ι W x hx)
  have : IsPreimmersion ((opensOverLift W x hx).left ≫ W.ι) := by
    rw [h]
    infer_instance
  have : IsPreimmersion (opensOverLift W x hx).left := IsPreimmersion.of_comp _ W.ι
  refine IsClosedImmersion.of_isPreimmersion _ ?_
  have hr : Set.range (opensOverLift W x hx).left.base =
      W.ι.base ⁻¹' Set.range x.left.base := by
    rw [← h, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    exact (W.ι.isOpenEmbedding.injective.preimage_image _).symm
  rw [hr]
  exact x.left.isClosedEmbedding.isClosed_range.preimage W.ι.base.hom.continuous

/-- **Open–closed detection of vanishing on an open neighbourhood of a closed point**: let
`x : P ⟶ X` be a closed immersion with range in the open `W'` and `g : Y ⟶ X` a morphism whose
range is the complement of the range of `x` in `W'`. If `Lx^* E = 0` and `Lg^* E = 0`, then `E`
vanishes on `W'`. -/
theorem isZero_upperStar_opensOverι_of_isCompl_of_isClosedImmersion (W' : X.left.Opens)
    {P : Over (Spec (.of k))} [LocallyOfFiniteType P.hom] [QuasiCompact P.hom]
    [IsSeparated P.hom] (x : P ⟶ X) [IsClosedImmersion x.left]
    (hx : Set.range x.left.base ⊆ W') {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom]
    [QuasiCompact Y.hom] [IsSeparated Y.hom] (g : Y ⟶ X) (hg : Set.range g.left.base ⊆ W')
    (hxg : Disjoint (Set.range x.left.base) (Set.range g.left.base))
    (hW' : (W' : Set X.left) ⊆ Set.range x.left.base ∪ Set.range g.left.base)
    (E : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hxE : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj E))
    (hgE : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).obj E)) :
    IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (opensOverι W')).obj E) := by
  have := isClosedImmersion_opensOverLift W' x hx
  set xV := opensOverLift W' x hx
  obtain ⟨gV, rfl⟩ : ∃ gV : Y ⟶ opensOver W', gV ≫ opensOverι W' = g :=
    ⟨_, opensOverLift_ι W' g hg⟩
  have : QuasiCompact (gV.left ≫ (opensOver W').hom) := by
    rw [Over.w gV]
    infer_instance
  have : QuasiCompact gV.left := QuasiCompact.of_comp gV.left (opensOver W').hom
  have hxV : xV ≫ opensOverι W' = x := opensOverLift_ι W' x hx
  refine isZero_of_isCompl_range_of_isClosedImmersion ℓ xV gV ?_ _
    (isZero_upperStar_obj_upperStar_obj _ ℓ _ _ E (hxV ▸ hxE))
    (isZero_upperStar_obj_upperStar_obj _ ℓ _ _ E hgE)
  refine Set.isCompl_range_of_injective W'.ι.isOpenEmbedding.injective
    (range_comp_left_base xV (opensOverι W')) (range_comp_left_base gV (opensOverι W'))
    (by rwa [hxV]) ?_
  rw [Scheme.Opens.range_ι, hxV]
  exact hW'

/-- **Hom vanishing at a closed immersion**: if `D` vanishes on an open neighbourhood `V` of the
range of a proper `x = xV ≫ jV`, then every morphism `Rx_* E ⟶ D` vanishes. -/
lemma eq_zero_of_lowerStar_of_isProper {V P : Over (Spec (.of k))} [LocallyOfFiniteType V.hom]
    [QuasiCompact V.hom] [IsSeparated V.hom] [LocallyOfFiniteType P.hom] [QuasiCompact P.hom]
    [IsSeparated P.hom] (xV : P ⟶ V) (jV : V ⟶ X) [IsOpenImmersion jV.left] {x : P ⟶ X}
    [IsProper x.left] (hx : xV ≫ jV = x) (E : Dᵇc(P.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (D : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hD : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ jV).obj D))
    (φ : (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj E ⟶ D) :
    φ = 0 := by
  subst hx
  have hZ : IsZero ((boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ
      (xV ≫ jV)).obj D) :=
    ((boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ xV).map_isZero
      (hD.of_iso ((boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ jV).app D))).of_iso
      ((boundedConstructibleUpperShriekComp_padicAlgCl ℓ xV jV).app D)
  set adj := boundedConstructibleUpperShriekAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
    (xV ≫ jV)
  set e := (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (xV ≫ jV)).app E
  have h : e.hom ≫ φ = 0 := by
    rw [← (adj.homEquiv _ _).symm_apply_apply (e.hom ≫ φ), hZ.eq_of_tgt (adj.homEquiv _ _ _) 0,
      Adjunction.homEquiv_counit, Functor.map_zero, zero_comp]
  exact (cancel_epi e.hom).1 (h.trans comp_zero.symm)

/-- If `Rx_* Lx^* C` is a retract of `C` through the unit, `RΓ(X, C) = 0`, and global sections on
`P` detect vanishing, then `Lx^* C = 0`: `RΓ(P, Lx^* C) = RΓ(X, Rx_* Lx^* C)` is a retract of
`RΓ(X, C) = 0`. -/
lemma isZero_upperStar_of_retract_of_conservative {P : Over (Spec (.of k))}
    [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom] (x : P ⟶ X)
    (hcons : ∀ E : Dᵇc(P.left)⟦Profinite.padicAlgClRingObj ℓ⟧,
      IsZero ((boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (toPoint P)).obj E) → IsZero E)
    (C : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hΓ : IsZero ((boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (toPoint X)).obj C))
    (s : (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj C) ⟶ C)
    (hs : s ≫ (boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
      x).unit.app C = 𝟙 _) :
    IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj C) := by
  have hP : IsZero ((boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (toPoint X)).obj ((boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj C))) := by
    refine (IsZero.iff_id_eq_zero _).2 ?_
    rw [← CategoryTheory.Functor.map_id, ← hs, Functor.map_comp,
      hΓ.eq_of_tgt ((boundedConstructibleLowerStar _ ℓ (toPoint X)).map s) 0, zero_comp]
  have hxa : x ≫ toPoint X = toPoint P := by
    ext1
    simp
  exact hcons _ (hP.of_iso (eqToIso (by rw [hxa]) ≪≫
    ((boundedConstructibleLowerStarComp _ ℓ x (toPoint X)).app _).symm))

end Vanishing

end AlgebraicGeometry.ProEtale.CondensedRing

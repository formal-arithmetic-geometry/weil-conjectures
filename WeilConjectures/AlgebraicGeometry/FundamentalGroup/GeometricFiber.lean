/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction
public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius

/-!
# The geometric fundamental group maps into the geometric part of the Weil group

Let `p : C₀ ⟶ Spec K` be a scheme over a field, `C = C₀ ×_K K̄` its geometric fibre with
projection `π : C ⟶ C₀` and structure morphism `a : C ⟶ Spec K̄`, and `t` a `K̄`-rational point
of `C`, i.e. `t ≫ a = 𝟙`. Such a point exists as soon as `C₀` is nonempty, quasi-compact and
locally of finite type (`AlgebraicGeometry.Scheme.Hom.exists_comp_eq_id_of_isAlgClosed`).

The base change to `C` of a constant cover `C₀ ×_K Spec A` is totally split: every point of its
geometric fibre at `t` lies on a section
(`AlgebraicGeometry.Scheme.FiniteEtale.exists_section_pullback_constantCover`). Hence the
fundamental group `π₁(C, t)` acts trivially on these fibres, and its image in `π₁(C₀, s)`
under the map induced by `π` and a path lies in the geometric part `{g | (g, 0) ∈ W(C₀, s)}` of
the Weil group (`AlgebraicGeometry.Scheme.FiniteEtale.mem_weilGroup_fundamentalGroupMap`).

## Main statements

- `AlgebraicGeometry.Scheme.Hom.exists_comp_eq_id_of_isAlgClosed`: a nonempty quasi-compact
  scheme locally of finite type over an algebraically closed field has a rational point.
- `AlgebraicGeometry.Scheme.FiniteEtale.smul_eq_self_of_section`: the fundamental group fixes
  the points of the geometric fibre which lie on a section.
- `AlgebraicGeometry.Scheme.FiniteEtale.mem_weilGroup_fundamentalGroupMap`: the image of
  `π₁(C, t)` acts trivially on the geometric fibres of the constant covers.
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry

/-- A nonempty quasi-compact scheme locally of finite type over an algebraically closed field `k`
has a `k`-rational point: the residue field at a closed point is finite over `k`, hence equal
to `k`. -/
lemma Scheme.Hom.exists_comp_eq_id_of_isAlgClosed {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    [Nonempty X] : ∃ σ : Spec (.of k) ⟶ X, σ ≫ f = 𝟙 _ := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨x, -, hx⟩ := (isClosed_univ (X := X)).exists_closed_singleton Set.univ_nonempty
  have : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  let g := X.fromSpecResidueField x ≫ f
  have : IsFinite g := isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.2 inferInstance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective g
  have hfin : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]
    infer_instance
  let := φ.hom.toAlgebra
  have : Module.Finite k (X.residueField x) := hfin
  have hbij : Function.Bijective φ.hom :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := X.residueField x)
  let e : k ≃+* X.residueField x := RingEquiv.ofBijective φ.hom hbij
  refine ⟨Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ X.fromSpecResidueField x, ?_⟩
  rw [Category.assoc]
  change _ ≫ g = _
  rw [← hφ, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext a
  exact e.symm_apply_apply a

namespace Scheme.FiniteEtale

section Section

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)
  (G : Type*) [Group G] [∀ P, MulAction G ((fiber s).obj P)] [IsNaturalSMul (fiber s) G]

/-- The fundamental group fixes the points of a geometric fibre which lie on a section: such a
point is the image of the unique point of the geometric fibre of `Y` itself. -/
lemma smul_eq_self_of_section (P : Y.FiniteEtale) (σ : Y ⟶ P.obj.left)
    (hσ : σ ≫ P.obj.hom = 𝟙 Y) (y : (fiber s).obj P) (hy : y.left = s ≫ σ) (g : G) :
    g • y = y := by
  let T : Y.FiniteEtale := ⟨MorphismProperty.Over.mk ⊤ (𝟙 Y) inferInstance,
    inferInstanceAs (IsFinite (𝟙 Y))⟩
  let S : T ⟶ P := ObjectProperty.homMk (MorphismProperty.Over.homMk σ hσ)
  let x₀ : (fiber s).obj T := Over.homMk s (Category.comp_id s)
  have hx₀ : g • x₀ = x₀ := fiber_ext s <| by
    rw [← Category.comp_id (g • x₀).left, ← Category.comp_id x₀.left]
    exact (fiber_left_comp s (g • x₀)).trans (fiber_left_comp s x₀).symm
  have hy' : y = (fiber s).map S x₀ := fiber_ext s hy
  rw [hy', ← IsNaturalSMul.naturality g S x₀, hx₀]

end Section

section GeometricFiber

variable {K : Type u} [Field K] {C : Scheme.{u}} (p : C ⟶ Spec (.of K))

/-- The base change to the geometric fibre `C = C₀ ×_K K̄` of a constant cover `C₀ ×_K Spec A` is
totally split: a point of its geometric fibre at a `K̄`-rational point `t` of `C` lies on the
section `C ⟶ (C₀ ×_K Spec A) ×_{C₀} C` given by the projection `π` and the morphism
`C ⟶ Spec K̄ ⟶ Spec A` induced by the corresponding `K`-algebra map `A → K̄`. -/
lemma exists_section_pullback_constantCover (A : FiniteEtaleAlgebra K)
    {t : Spec (.of (AlgebraicClosure K)) ⟶ p.geometricFiber}
    (ht : t ≫ p.geometricFiberToAlgebraicClosure = 𝟙 _)
    (y : (fiber t).obj ((pullback p.geometricFiberProj).obj (constantCover p A))) :
    ∃ σ : p.geometricFiber ⟶ ((pullback p.geometricFiberProj).obj (constantCover p A)).obj.left,
      σ ≫ ((pullback p.geometricFiberProj).obj (constantCover p A)).obj.hom = 𝟙 _ ∧
        y.left = t ≫ σ := by
  have hc : Limits.pullback.fst (pullback.fst p A.specHom) p.geometricFiberProj ≫
      pullback.fst p A.specHom =
        Limits.pullback.snd (pullback.fst p A.specHom) p.geometricFiberProj ≫
          p.geometricFiberProj :=
    Limits.pullback.condition
  have hy : y.left ≫ Limits.pullback.snd (pullback.fst p A.specHom) p.geometricFiberProj = t :=
    fiber_left_comp t y
  have h₁ : y.left ≫ Limits.pullback.fst (pullback.fst p A.specHom) p.geometricFiberProj ≫
      pullback.fst p A.specHom = t ≫ p.geometricFiberProj := by
    rw [hc, ← Category.assoc, hy]
  let u : Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of A.1) :=
    y.left ≫ Limits.pullback.fst (pullback.fst p A.specHom) p.geometricFiberProj ≫
      Limits.pullback.snd p A.specHom
  have hu : u ≫ A.specHom = (Scheme.specAlgebraicClosure K).hom := by
    simp only [u, Category.assoc, ← Limits.pullback.condition]
    rw [← Category.assoc (Limits.pullback.fst _ _) (pullback.fst p A.specHom) p,
      ← Category.assoc y.left, h₁, Category.assoc, Scheme.Hom.geometricFiber_condition,
      ← Category.assoc, ht]
    exact Category.id_comp _
  let σ₀ : p.geometricFiber ⟶ Limits.pullback p A.specHom :=
    Limits.pullback.lift p.geometricFiberProj (p.geometricFiberToAlgebraicClosure ≫ u) (by
      rw [Scheme.Hom.geometricFiber_condition, Category.assoc, hu])
  have hσ₀ : σ₀ ≫ Limits.pullback.fst p A.specHom = 𝟙 _ ≫ p.geometricFiberProj := by
    simp [σ₀]
  refine ⟨Limits.pullback.lift σ₀ (𝟙 _) hσ₀, Limits.pullback.lift_snd _ _ _, ?_⟩
  have key : t ≫ Limits.pullback.lift σ₀ (𝟙 _) hσ₀ = y.left := by
    apply Limits.pullback.hom_ext
    · change (t ≫ _) ≫ Limits.pullback.fst (pullback.fst p A.specHom) p.geometricFiberProj =
        y.left ≫ Limits.pullback.fst (pullback.fst p A.specHom) p.geometricFiberProj
      rw [Category.assoc, Limits.pullback.lift_fst]
      apply Limits.pullback.hom_ext
      · rw [Category.assoc, Category.assoc, h₁, Limits.pullback.lift_fst]
      · rw [Category.assoc, Category.assoc, Limits.pullback.lift_snd, ← Category.assoc t, ht,
          Category.id_comp]
    · change (t ≫ _) ≫ Limits.pullback.snd (pullback.fst p A.specHom) p.geometricFiberProj =
        y.left ≫ Limits.pullback.snd (pullback.fst p A.specHom) p.geometricFiberProj
      rw [Category.assoc, Limits.pullback.lift_snd, Category.comp_id, hy]
  exact key.symm

variable {t : Spec (.of (AlgebraicClosure K)) ⟶ p.geometricFiber}
  (ht : t ≫ p.geometricFiberToAlgebraicClosure = 𝟙 _)
  (G' : Type*) [Group G'] [∀ P, MulAction G' ((fiber t).obj P)] [IsNaturalSMul (fiber t) G']

include ht in
/-- The fundamental group of the geometric fibre acts trivially on the geometric fibres of the
base changes of the constant covers. -/
lemma smul_eq_self_pullback_constantCover (A : FiniteEtaleAlgebra K)
    (y : (fiber t).obj ((pullback p.geometricFiberProj).obj (constantCover p A))) (g : G') :
    g • y = y := by
  obtain ⟨σ, hσ, hy⟩ := exists_section_pullback_constantCover p A ht y
  exact smul_eq_self_of_section t G' _ σ hσ y hy g

variable [Finite K] [ConnectedSpace C] {s : Spec (.of (AlgebraicClosure K)) ⟶ C}
  (τ : pullback p.geometricFiberProj ⋙ fiber t ≅ fiber s)
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G]

include ht in
/-- The image of the fundamental group of the geometric fibre in `π₁(C₀, s)` acts trivially on
the geometric fibres of the constant covers: it lies in the geometric part of the Weil group. -/
lemma mem_weilGroup_fundamentalGroupMap (G' : Type u) [Group G']
    [∀ P, MulAction G' ((fiber t).obj P)] [IsNaturalSMul (fiber t) G'] (g : G') :
    (fundamentalGroupMap τ G' G g, (1 : Multiplicative ℤ)) ∈ weilGroup p s G := by
  refine (mem_weilGroup_iff p s G).2 fun A y ↦ ?_
  obtain ⟨y', rfl⟩ : ∃ y', τ.hom.app _ y' = y :=
    ⟨τ.inv.app _ y, ConcreteCategory.congr_hom (τ.inv_hom_id_app _) y⟩
  rw [fundamentalGroupMap_smul, smul_eq_self_pullback_constantCover p ht G' A y' g]
  rfl

end GeometricFiber

end Scheme.FiniteEtale

end AlgebraicGeometry

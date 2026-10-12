/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Artinian
public import WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing
public import WeilConjectures.ConstructibleSheaf.Monoidal
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf

/-!
# The eight curve assertions in dimension zero

Let `k` be an algebraically closed field and `Z` a curve over `k` of dimension at most zero, that
is a finite discrete `k`-scheme of finite type. Every abelian étale sheaf on `Z` has vanishing
cohomology in positive degrees (each point of `Z` has an algebraically closed residue field),
and `H⁰` of a sheaf with finite stalks is finite, since a global section is determined by its
germs at the finitely many points. Together with the field extension invariance in dimension
zero (`AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_topologicalKrullDim_le_zero`) this
proves the eight curve assertions on `Z` for coefficients in a finite ring.

## Main statements

- `AlgebraicGeometry.Scheme.isZero_sheaf_of_isEmpty`: an étale sheaf on the empty scheme is
  zero.
- `AlgebraicGeometry.IsCurve.finite_and_discreteTopology_of_topologicalKrullDim_le_zero`: a curve
  of dimension at most zero is finite and discrete.
- `AlgebraicGeometry.Scheme.subsingleton_H_of_finite_of_discreteTopology`: vanishing of the
  cohomology in positive degrees.
- `AlgebraicGeometry.Scheme.finite_H_zero_of_finite`: finiteness of `H⁰`.
- `AlgebraicGeometry.IsCurve.Assertions.of_topologicalKrullDim_le_zero`: the eight assertions in
  dimension zero.
-/

@[expose] public section

universe u

open CategoryTheory Limits Abelian ZeroObject

namespace AlgebraicGeometry

open Etale

/-- An étale sheaf of abelian groups on the empty scheme is zero: the empty family of geometric
points is conservative. -/
lemma Scheme.isZero_sheaf_of_isEmpty {X : Scheme.{u}} [IsEmpty X]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) : IsZero G := by
  have : IsIso (0 : G ⟶ 0) := Scheme.isIso_of_isIso_sheafFiber_map _ fun s ↦ isEmptyElim s
  exact (isZero_zero _).of_iso (asIso (0 : G ⟶ 0))

/-- A curve over a field of dimension at most zero has finitely many points, and its topology is
discrete: it is locally noetherian of dimension zero, hence locally artinian, and quasi-compact. -/
lemma IsCurve.finite_and_discreteTopology_of_topologicalKrullDim_le_zero {k : Type u} [Field k]
    {Z : Scheme.{u}} (g : Z ⟶ Spec (.of k)) [IsCurve g] (hZ : topologicalKrullDim Z ≤ 0) :
    Finite Z ∧ DiscreteTopology Z := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian g
  have := IsLocallyArtinian.of_topologicalKrullDim_le_zero hZ
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace g
  exact ⟨finite_of_compact_of_discrete, inferInstance⟩

/-- **Vanishing of the cohomology of a finite discrete scheme** of finite type over an
algebraically closed field `k`: every abelian étale sheaf `G` has `Hⁿ(Z, G) = 0` for `n ≥ 1`,
the points of `Z` being closed with algebraically closed residue fields.
(blueprint: `lem-weil-pbc-zero-dimensional-cohomology`, positive degrees) -/
theorem Scheme.subsingleton_H_of_finite_of_discreteTopology {k : Type u} [Field k]
    [IsAlgClosed k] {Z : Scheme.{u}} (g : Z ⟶ Spec (.of k)) [LocallyOfFiniteType g] [Finite Z]
    [DiscreteTopology Z] (G : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) :
    Subsingleton (Sheaf.H G (n + 1)) := by
  have : IsEmpty (⊥ : Z.Opens).toScheme := ⟨fun x ↦ x.2⟩
  refine Etale.subsingleton_H_of_isZero_upperStar ⊥ (Set.toFinite _)
    (fun x _ ↦ isClosed_discrete _) (fun x _ ↦ ?_) G (Scheme.isZero_sheaf_of_isEmpty _) n
  have := Scheme.isAlgClosed_residueField_of_isClosed g x (isClosed_discrete _)
  infer_instance

/-- **`H⁰` of a sheaf with finite stalks on a finite scheme is finite.** A global section of an
abelian étale sheaf `G` on a scheme `Z` with finitely many points is determined by its germs at
the geometric points `Z.algClosurePoint z`, i.e. `H⁰(Z, G) = Hom(ℤ, G)` injects into the finite
product `∏_z Hom(ℤ, G_z)`. -/
theorem Scheme.finite_H_zero_of_finite {Z : Scheme.{u}} [Finite Z]
    (G : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : ∀ z : Z,
      Finite ((Z.uliftPointSmallEtale z).sheafFiber (A := AddCommGrpCat.{u + 1}).obj G)) :
    Finite (Sheaf.H G 0) := by
  have : LocallySmall.{u + 1} Z.Etale := locallySmall_max.{u + 1, u}
  let I := (constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  let ψ : (I ⟶ G) → ∀ z : Z,
      ULift.{u + 1} ℤ →+ (Z.uliftPointSmallEtale z).sheafFiber (A := AddCommGrpCat.{u + 1}).obj G :=
    fun φ z ↦ (((Z.uliftPointSmallEtale z).sheafFiberConstantSheafIso
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv ≫ (Z.uliftPointSmallEtale z).sheafFiber.map φ).hom
  have hψ : Function.Injective ψ := by
    intro φ φ' h
    refine ((isConservativeFamilyOfPoints_ulift_pointSmallEtale Z).jointlyFaithful
      AddCommGrpCat.{u + 1}).map_injective ?_
    rintro ⟨-, ⟨z⟩⟩
    have := congrArg AddCommGrpCat.ofHom (congrFun h z)
    simp only [ψ, AddCommGrpCat.ofHom_hom] at this
    simpa only [Iso.cancel_iso_inv_left] using this
  have (z : Z) : Finite (ULift.{u + 1} ℤ →+
      (Z.uliftPointSmallEtale z).sheafFiber (A := AddCommGrpCat.{u + 1}).obj G) := by
    have := hG z
    refine Finite.of_injective (fun χ ↦ χ ⟨1⟩) fun χ χ' h ↦ ?_
    refine AddMonoidHom.ext fun ⟨n⟩ ↦ ?_
    have h₁ : (⟨n⟩ : ULift.{u + 1} ℤ) = n • (⟨1⟩ : ULift.{u + 1} ℤ) := by ext; simp
    rw [h₁, map_zsmul, map_zsmul]
    exact congrArg (n • ·) h
  have : Finite (I ⟶ G) := Finite.of_injective ψ hψ
  exact Finite.of_equiv _ Ext.addEquiv₀.toEquiv.symm

namespace IsCurve

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Over a finite coefficient ring every étale sheaf of modules is torsion: its stalks are
killed by the characteristic of `Λ`. -/
lemma isTorsionSheaf_of_finite [Finite Λ] {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) : Scheme.IsTorsionSheaf F where
  isTorsion_sheafFiber Ω _ _ s x := by
    have hn : ringChar Λ ≠ 0 := CharP.char_ne_zero_of_finite Λ (ringChar Λ)
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨ringChar Λ, Nat.pos_of_ne_zero hn, ?_⟩
    rw [← Nat.cast_smul_eq_nsmul Λ, ringChar.Nat.cast_ringChar, zero_smul]

/-- **The eight curve assertions in dimension zero.** Let `k` be algebraically closed, `Z` a
curve over `k` of dimension at most zero and `G` an étale sheaf of modules over a finite ring
`Λ` on `Z`. Then `C(Z, G)` holds: the cohomology of `G` vanishes in positive degrees, also on
the opens of `Z`; `H⁰(Z, G)` is finite when `G` is constructible; and the field extension
invariance is `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_topologicalKrullDim_le_zero`.
(blueprint: `lem-weil-pbc-curve-dense-open-localization`, the assertions on the
zero-dimensional complement) -/
theorem Assertions.of_topologicalKrullDim_le_zero [Finite Λ] {k : Type u} [Field k]
    [IsAlgClosed k] {Z : Scheme.{u}} (g : Z ⟶ Spec (.of k)) [IsCurve g]
    (hZ : topologicalKrullDim Z ≤ 0) (G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Assertions Λ g G := by
  obtain ⟨hfin, hdisc⟩ := finite_and_discreteTopology_of_topologicalKrullDim_le_zero g hZ
  have hvan (n : ℕ) := Scheme.subsingleton_H_of_finite_of_discreteTopology g
    ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G) n
  have hvan' (q : ℕ) (hq : 0 < q) : Subsingleton (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G) q) := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hq
    simpa using hvan n
  have hfin₀ [Scheme.IsConstructibleSheaf G] (q : ℕ) : Finite (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G) q) := by
    rcases q with _ | n
    · refine Scheme.finite_H_zero_of_finite _ fun z ↦ ?_
      have : LocallySmall.{u + 1} Z.Etale := locallySmall_max.{u + 1, u}
      have hG := (Scheme.IsConstructibleSheaf.isFiniteSheaf
        (inferInstance : Scheme.IsConstructibleSheaf G)).isFinitelyGenerated_sheafFiber _
          (Z.algClosurePoint z)
      rw [ModuleCat.isFinitelyGenerated_iff] at hG
      have : Finite ((Scheme.pointSmallEtale (Z.algClosurePoint z)).sheafFiber
        (A := ModuleCat.{u + 1} Λ).obj G) :=
        Module.finite_of_finite Λ
      let e₁ := ((Z.uliftPointSmallEtale z).sheafFiberCompIso
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).app G
      let e₂ : (Z.uliftPointSmallEtale z).sheafFiber (A := ModuleCat.{u + 1} Λ).obj G ≅
          (Scheme.pointSmallEtale (Z.algClosurePoint z)).sheafFiber
            (A := ModuleCat.{u + 1} Λ).obj G :=
        ((Scheme.pointSmallEtale (Z.algClosurePoint z)).uliftSheafFiberIso _).app G
      exact Finite.of_equiv _ (e₁ ≪≫ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapIso
        e₂).addCommGroupIsoToAddEquiv.toEquiv.symm
    · have := hvan n
      exact Finite.of_subsingleton
  have := isTorsionSheaf_of_finite Λ G
  refine ⟨fun q hq ↦ hvan' q (by omega), fun q hq ↦ hvan' q (by omega),
    fun p _ _ _ q hq ↦ hvan' q (by omega), fun q ↦ hfin₀ q, fun q ↦ hfin₀ q,
    fun k' _ _ X' ι f' ι' h q ↦
      bijective_cohomologyMap_of_topologicalKrullDim_le_zero Λ g hZ h G q,
    fun k' _ _ X' ι f' ι' h q ↦
      bijective_cohomologyMap_of_topologicalKrullDim_le_zero Λ g hZ h G q, fun {W} a _ ↦ ?_⟩
  have : Finite W := Finite.of_injective _ a.isOpenEmbedding.injective
  have : DiscreteTopology W := a.isOpenEmbedding.isEmbedding.discreteTopology
  have := Scheme.subsingleton_H_of_finite_of_discreteTopology (a ≫ g)
    ((a)^*[AddCommGrpCat.{u + 1}].obj
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G)) 1
  exact fun _ ↦ ⟨0, Subsingleton.elim _ _⟩

end IsCurve

end AlgebraicGeometry

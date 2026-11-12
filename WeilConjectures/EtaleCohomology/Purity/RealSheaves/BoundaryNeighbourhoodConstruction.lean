/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Endomorphism
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.InertiaNeighbourhood
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryNeighbourhoodData
public import WeilConjectures.WeilSheaf.BoundaryStrictHenselization

/-!
# Construction of strictly henselian neighbourhoods of boundary points

Let `j : U₀ ⟶ C₀` be a nonempty open of a smooth geometrically connected curve over a finite
field `k₀`, `z` a boundary point with closed point `x`, `W` the chosen affine chart at `z` with
ring `R = Γ(C₀, W)`, `B` the integral closure of `R` in the separable closure `Ω` of `k(C)` and
`Q` a maximal ideal of `B` over `z`. The ring `A = B_Q^{I_Q}` of inertia invariants gives a
strictly henselian neighbourhood of the boundary point
(`AlgebraicGeometry.WeilGroup.BoundaryNeighbourhood`, blueprint
`lem-wf-boundary-stalk-invariants`), provided `Q` is *compatible* with the geometric point
`x̄ = geometricFiberPointOfFinitePoint x`: the reduction modulo `Q` of the embedding
`ι : k̄ ↪ Ω` of the geometric generic point (`AlgebraicGeometry.WeilGroup.genericEmb`) induces on
`κ(x)` the embedding `κ(x) ↪ k̄` of `x̄`
(`AlgebraicGeometry.WeilGroup.nonempty_boundaryNeighbourhood_of_compatible`). The Frobenius lift
is given by an element `σ_F` of the decomposition group of `Q` acting on `ι(k̄)` as the
`deg x`-th power of the geometric Frobenius.

* `Spec A ⟶ C̄` is given by `Spec A ⟶ Spec R ⟶ C₀` and `ι(k̄) ⊆ A`;
* the lift of `x̄` is `Spec` of the residue map `A ⟶ κ(A) ≅ k̄`;
* the punctured part is `Spec Ω^{I_Q}` (`AlgebraicGeometry.exists_iso_pullback_geometricFiberMap`);
* the Frobenius lift is `Spec σ_F|_A`.
-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing
open scoped Pointwise

namespace AlgebraicGeometry.WeilGroup

open Scheme Scheme.FiniteEtale ProEtale

variable {K : Type u} [Field K] [Finite K] {C U : Scheme.{u}} [C.Over (Spec (.of K))]
  [U.Over (Spec (.of K))] [IsCurve (C ↘ Spec (.of K))] [GeometricallyConnected (C ↘ Spec (.of K))]
  [ConnectedSpace C] [Smooth (C ↘ Spec (.of K))] [IsIntegral C]
  (j : U ⟶ C) [IsOpenImmersion j] [Nonempty U] [j.IsOver (Spec (.of K))]

local notation "Ω" => SeparableClosure (Scheme.functionField C)

set_option hygiene false in
local notation "j̄" => Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of K)))

omit [Finite K] [IsCurve (C ↘ Spec (.of K))] [GeometricallyConnected (C ↘ Spec (.of K))]
  [ConnectedSpace C] [Smooth (C ↘ Spec (.of K))] in
/-- The structure map `k₀ ⟶ Ω` of the generic geometric point factors through the sections over
an affine open. -/
lemma genericStructHom_eq {W : C.Opens} (hW : IsAffineOpen W) [Nonempty W]
    [IsDedekindDomain Γ(C, W)] :
    genericStructHom (U ↘ Spec (.of K)) j =
      (algebraMap Γ(C, W) Ω).comp (sectionsStructHom (k₀ := K) hW) := by
  obtain ⟨Q, hQ⟩ := Ideal.exists_maximal (integralClosure Γ(C, W) Ω)
  have hfp : hW.fromSpec ≫ (C ↘ Spec (.of K)) =
      Spec.map (CommRingCat.ofHom (sectionsStructHom (k₀ := K) hW)) := by
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have h1 : genericBasePoint j ≫ (U ↘ Spec (.of K)) = Spec.map (CommRingCat.ofHom
      ((algebraMap Γ(C, W) Ω).comp (sectionsStructHom (k₀ := K) hW))) := by
    rw [← comp_over j (Spec (.of K)), ← Category.assoc, pointOfAlgebra_comp_eq_specAtPrime j hW Q,
      specAtPrime, Category.assoc, Category.assoc, hfp, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    rw [IsScalarTower.algebraMap_apply Γ(C, W) (integralClosure Γ(C, W) Ω)
      (Localization.AtPrime Q), Ideal.atPrimeToField_algebraMap]
    rfl
  have h2 := spec_genericStructHom (U ↘ Spec (.of K)) j
  rw [h1] at h2
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h2)

omit [IsCurve (C ↘ Spec (.of K))] [GeometricallyConnected (C ↘ Spec (.of K))]
  [ConnectedSpace C] [Smooth (C ↘ Spec (.of K))] [IsIntegral C] in
/-- A ring endomorphism `σ` of `A` fixing the image of `R` and acting on `ε : k̄ ⟶ A` as `Frⁿ`
lifts the `n`-th power of the geometric Galois Frobenius along a morphism `h : Spec A ⟶ C̄`
given by `Spec A ⟶ Spec R ⟶ C` and `Spec ε`. -/
lemma specMap_comp_eq_comp_geometricGaloisFrobenius_pow {A R : CommRingCat.{u}}
    (g : Spec R ⟶ C) (alg : R ⟶ A) (σ : A ⟶ A) (hσalg : alg ≫ σ = alg)
    (ε : CommRingCat.of (AlgebraicClosure K) ⟶ A) (n : ℕ)
    (hσε : Spec.map σ ≫ Spec.map ε = Spec.map ε ≫ (specGeometricFrobenius K ^ n).asIso.hom)
    (h : Spec A ⟶ (C ↘ Spec (.of K)).geometricFiber)
    (hhproj : h ≫ (C ↘ Spec (.of K)).geometricFiberProj = Spec.map alg ≫ g)
    (hhalg : h ≫ (C ↘ Spec (.of K)).geometricFiberToAlgebraicClosure = Spec.map ε) :
    Spec.map σ ≫ h = h ≫ ((C ↘ Spec (.of K)).geometricGaloisFrobenius ^ n).asIso.hom := by
  apply Scheme.Hom.geometricFiber_hom_ext
  · rw [Category.assoc, Category.assoc,
      Scheme.Hom.geometricGaloisFrobenius_pow_hom_comp_geometricFiberProj, hhproj,
      ← Category.assoc, ← Spec.map_comp, hσalg]
  · rw [Category.assoc, Category.assoc,
      Scheme.Hom.geometricGaloisFrobenius_pow_hom_comp_geometricFiberToAlgebraicClosure,
      hhalg, hσε, ← Category.assoc, hhalg]

/-- An endomorphism preserving the section and nonunits descends to the residue map. -/
lemma residueMap_equivariant_of_section {A L : Type*} [CommRing A] [CommRing L]
    (ε : L →+* A) (r : A →+* L) (σ : A →+* A) (Φ : L →+* L)
    (hrε : r.comp ε = RingHom.id L) (hr : ∀ a, r a = 0 ↔ ¬ IsUnit a)
    (hσ : ∀ a, IsUnit (σ a) → IsUnit a) (hσε : ∀ y, σ (ε y) = ε (Φ y))
    (a : A) : r (σ a) = Φ (r a) := by
  have h0 : r (a - ε (r a)) = 0 := by
    rw [r.map_sub, RingHom.congr_fun hrε, sub_self]
  have h1 : r (σ (a - ε (r a))) = 0 :=
    (hr _).2 fun hu ↦ (hr _).1 h0 (hσ _ hu)
  rw [σ.map_sub, r.map_sub, sub_eq_zero] at h1
  exact h1.trans ((congrArg r (hσε (r a))).trans (RingHom.congr_fun hrε _))

omit [IsCurve (C ↘ Spec (.of K))] [GeometricallyConnected (C ↘ Spec (.of K))]
  [ConnectedSpace C] [Smooth (C ↘ Spec (.of K))] [IsIntegral C] in
/-- Ring-level equivariance gives the three spectrum identities of a Frobenius lift. -/
lemma exists_specMap_frobeniusLift {A R E : Type u} [CommRing A] [CommRing R] [CommRing E]
    (g : Spec (.of R) ⟶ C) (alg : R →+* A) (σ : A →+* A)
    (hσalg : ∀ a, σ (alg a) = alg a)
    (ε : AlgebraicClosure K →+* A) (r : A →+* AlgebraicClosure K)
    (γ : A →+* E) (τ : E →+* E) (Φ : AlgebraicClosure K →+* AlgebraicClosure K) (n : ℕ)
    (hΦ : (specGeometricFrobenius K ^ n).asIso.hom = Spec.map (CommRingCat.ofHom Φ))
    (hσε : ∀ y, σ (ε y) = ε (Φ y)) (hrσ : ∀ a, r (σ a) = Φ (r a))
    (hγσ : ∀ a, γ (σ a) = τ (γ a))
    (h : Spec (.of A) ⟶ (C ↘ Spec (.of K)).geometricFiber)
    (hhproj : h ≫ (C ↘ Spec (.of K)).geometricFiberProj =
      Spec.map (CommRingCat.ofHom alg) ≫ g)
    (hhalg : h ≫ (C ↘ Spec (.of K)).geometricFiberToAlgebraicClosure =
      Spec.map (CommRingCat.ofHom ε)) :
    ∃ α : Spec (.of A) ⟶ Spec (.of A),
      α ≫ h = h ≫ ((C ↘ Spec (.of K)).geometricGaloisFrobenius ^ n).asIso.hom ∧
      (specGeometricFrobenius K ^ n).asIso.hom ≫ Spec.map (CommRingCat.ofHom r) =
        Spec.map (CommRingCat.ofHom r) ≫ α ∧
      Spec.map (CommRingCat.ofHom τ) ≫ Spec.map (CommRingCat.ofHom γ) =
        Spec.map (CommRingCat.ofHom γ) ≫ α := by
  have hσalg' : CommRingCat.ofHom alg ≫ CommRingCat.ofHom σ = CommRingCat.ofHom alg :=
    CommRingCat.hom_ext (RingHom.ext hσalg)
  have hσε' : CommRingCat.ofHom ε ≫ CommRingCat.ofHom σ =
      CommRingCat.ofHom Φ ≫ CommRingCat.ofHom ε :=
    CommRingCat.hom_ext (RingHom.ext hσε)
  have hrσ' : CommRingCat.ofHom r ≫ CommRingCat.ofHom Φ =
      CommRingCat.ofHom σ ≫ CommRingCat.ofHom r :=
    CommRingCat.hom_ext (RingHom.ext fun a ↦ (hrσ a).symm)
  have hγσ' : CommRingCat.ofHom γ ≫ CommRingCat.ofHom τ =
      CommRingCat.ofHom σ ≫ CommRingCat.ofHom γ :=
    CommRingCat.hom_ext (RingHom.ext fun a ↦ (hγσ a).symm)
  refine ⟨Spec.map (CommRingCat.ofHom σ), ?_, ?_, ?_⟩
  · exact specMap_comp_eq_comp_geometricGaloisFrobenius_pow g _ _ hσalg' _ n (by
      rw [hΦ, ← Spec.map_comp, ← Spec.map_comp, hσε']) h hhproj hhalg
  · rw [hΦ, ← Spec.map_comp, ← Spec.map_comp, hrσ']
  · rw [← Spec.map_comp, ← Spec.map_comp, hγσ']

-- Select the standard actions directly, avoiding searches through unrelated actions.
noncomputable local instance boundaryIdealMulSemiringActionConstruction {W : C.Opens} [Nonempty W]
    [Algebra Γ(C, W) Ω] [IsScalarTower Γ(C, W) C.functionField Ω] :
    MulSemiringAction Gal(Ω/C.functionField) (integralClosure Γ(C, W) Ω) := by
  let : SMulCommClass Gal(Ω/C.functionField) Γ(C, W) Ω :=
    AlgEquiv.smulCommClass_of_isScalarTower Γ(C, W) C.functionField Ω
  infer_instance

noncomputable local instance boundaryIdealMulActionConstruction {W : C.Opens} [Nonempty W]
    [Algebra Γ(C, W) Ω] [IsScalarTower Γ(C, W) C.functionField Ω] :
    MulAction Gal(Ω/C.functionField) (Ideal (integralClosure Γ(C, W) Ω)) :=
  Ideal.pointwiseDistribMulAction.toMulAction

omit [IsCurve (C ↘ Spec (.of K))] [GeometricallyConnected (C ↘ Spec (.of K))] [ConnectedSpace C]
  [Smooth (C ↘ Spec (.of K))] in
/-- **The Frobenius lift on `Spec B_Q^{I_Q}`.** Let `σ_F` be an element of the decomposition
group of `Q` acting on the image of an embedding `ε₀ : k̄ ↪ Ω`, contained in `B_Q^{I_Q}` through
`ε`, as the `n`-th power of the geometric Frobenius, and `h : Spec B_Q^{I_Q} ⟶ C̄` given by
`Spec B_Q^{I_Q} ⟶ C` and `Spec ε`. Then `α = Spec σ_F|_{B_Q^{I_Q}}` lifts the `n`-th power of the
geometric Galois Frobenius of `C̄`, compatibly with `Spec r` and the generic point. -/
theorem exists_frobeniusLift_inertiaInvariants {W : C.Opens} (hW : IsAffineOpen W) [Nonempty W]
    (Q : Ideal (integralClosure Γ(C, W) Ω)) [Q.IsMaximal]
    {σF : Gal(Ω/C.functionField)} (hσF : σF ∈ MulAction.stabilizer Gal(Ω/C.functionField) Q)
    (ε₀ : AlgebraicClosure K →+* Ω)
    (ε : AlgebraicClosure K →+* Ideal.inertiaInvariants C.functionField Q)
    (r : Ideal.inertiaInvariants C.functionField Q →+* AlgebraicClosure K)
    (hrε : r.comp ε = RingHom.id _) (hr : ∀ a, r a = 0 ↔ ¬ IsUnit a)
    (hε : ∀ y, Ideal.inertiaInvariantsToField _ Q (ε y) = ε₀ y) (n : ℕ)
    (hσFk : ∀ y, σF (ε₀ y) = ε₀ (letI := Fintype.ofFinite K
       (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K) ^ n) y))
    (h : Spec (.of (Ideal.inertiaInvariants C.functionField Q)) ⟶
      (C ↘ Spec (.of K)).geometricFiber)
    (hhproj : h ≫ (C ↘ Spec (.of K)).geometricFiberProj = specInertiaInvariantsTo hW Q)
    (hhalg : h ≫ (C ↘ Spec (.of K)).geometricFiberToAlgebraicClosure =
      Spec.map (CommRingCat.ofHom ε)) :
    ∃ α : Spec (.of (Ideal.inertiaInvariants C.functionField Q)) ⟶
        Spec (.of (Ideal.inertiaInvariants C.functionField Q)),
      α ≫ h = h ≫ ((C ↘ Spec (.of K)).geometricGaloisFrobenius ^ n).asIso.hom ∧
      (specGeometricFrobenius K ^ n).asIso.hom ≫ Spec.map (CommRingCat.ofHom r) =
        Spec.map (CommRingCat.ofHom r) ≫ α ∧
      Spec.map (CommRingCat.ofHom (σF : Ω →+* Ω)) ≫ Spec.map (CommRingCat.ofHom
        (Ideal.inertiaInvariantsToField C.functionField Q).toRingHom) =
        Spec.map (CommRingCat.ofHom
          (Ideal.inertiaInvariantsToField C.functionField Q).toRingHom) ≫ α := by
  let _ := Fintype.ofFinite K
  let Φ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K :=
    FiniteField.geometricFrobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K) ^ n
  have hσε (y : AlgebraicClosure K) :
      Ideal.inertiaInvariantsMap C.functionField Q hσF (ε y) = ε (Φ y) :=
    Ideal.injective_inertiaInvariantsToField _ Q (by
      rw [Ideal.inertiaInvariantsToField_inertiaInvariantsMap, hε, hε, hσFk])
  have hrσ : ∀ a : Ideal.inertiaInvariants C.functionField Q,
      r (Ideal.inertiaInvariantsMap C.functionField Q hσF a) = Φ (r a) :=
    residueMap_equivariant_of_section ε r
      (Ideal.inertiaInvariantsMap C.functionField Q hσF) Φ.toRingEquiv.toRingHom
      hrε hr (fun _ ↦ Ideal.isUnit_of_isUnit_inertiaInvariantsMap hσF) hσε
  exact exists_specMap_frobeniusLift hW.fromSpec
    (algebraMap Γ(C, W) (Ideal.inertiaInvariants C.functionField Q))
    (Ideal.inertiaInvariantsMap C.functionField Q hσF)
    (Ideal.inertiaInvariantsMap_algebraMap hσF) ε r
    (Ideal.inertiaInvariantsToField C.functionField Q).toRingHom (σF : Ω →+* Ω)
    Φ.toRingEquiv.toRingHom n (specGeometricFrobenius_pow_hom K n) hσε hrσ
    (Ideal.inertiaInvariantsToField_inertiaInvariantsMap hσF) h hhproj hhalg

omit [IsCurve (C ↘ Spec (.of K))] [GeometricallyConnected (C ↘ Spec (.of K))]
  [ConnectedSpace C] [Smooth (C ↘ Spec (.of K))] [IsIntegral C] in
/-- A section of the residue map identifies the lifted geometric point by its projections. -/
lemma specMap_eq_geometricFiberPoint_of_projections {A : Type u} [CommRing A]
    (ε : AlgebraicClosure K →+* A) (r : A →+* AlgebraicClosure K)
    (hrε : r.comp ε = RingHom.id _) (x : C.finitePoints)
    (h : Spec (.of A) ⟶ (C ↘ Spec (.of K)).geometricFiber)
    (hproj : Spec.map (CommRingCat.ofHom r) ≫ h ≫
        (C ↘ Spec (.of K)).geometricFiberProj =
      (C ↘ Spec (.of K)).geometricFiberPointOfFinitePoint x ≫
        (C ↘ Spec (.of K)).geometricFiberProj)
    (hhalg : h ≫ (C ↘ Spec (.of K)).geometricFiberToAlgebraicClosure =
      Spec.map (CommRingCat.ofHom ε)) :
    Spec.map (CommRingCat.ofHom r) ≫ h =
      𝟙 _ ≫ (C ↘ Spec (.of K)).geometricFiberPointOfFinitePoint x := by
  rw [Category.id_comp]
  apply Scheme.Hom.geometricFiber_hom_ext
  · exact (Category.assoc _ _ _).trans hproj
  · rw [Category.assoc, hhalg, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hrε,
      Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricFiberToAlgebraicClosure,
      CommRingCat.ofHom_id, Spec.map_id]

omit [IsCurve (C ↘ Spec (.of K))] [GeometricallyConnected (C ↘ Spec (.of K))]
  [ConnectedSpace C] [Smooth (C ↘ Spec (.of K))] in
/-- The map on the punctured neighbourhood is the geometric generic point. -/
lemma genericGeomPoint_eq_of_projections {W : C.Opens} (hW : IsAffineOpen W) [Nonempty W]
    {A : Type u} [CommRing A] (alg : Γ(C, W) →+* A)
    (ε : AlgebraicClosure K →+* A) (γ : A →+* Ω)
    (hγalg : γ.comp alg = algebraMap Γ(C, W) Ω)
    (hγε : γ.comp ε = genericEmb (U ↘ Spec (.of K)) j)
    (h : Spec (.of A) ⟶ (C ↘ Spec (.of K)).geometricFiber)
    (hhproj : h ≫ (C ↘ Spec (.of K)).geometricFiberProj =
      Spec.map (CommRingCat.ofHom alg) ≫ hW.fromSpec)
    (hhalg : h ≫ (C ↘ Spec (.of K)).geometricFiberToAlgebraicClosure =
      Spec.map (CommRingCat.ofHom ε))
    {T : Scheme.{u}} (s : Spec (.of Ω) ⟶ T) (e : T ⟶ pullback h j̄)
    (hfst : s ≫ e ≫ pullback.fst h j̄ = Spec.map (CommRingCat.ofHom γ)) :
    s ≫ (e ≫ pullback.snd h j̄) = genericGeomPoint (U ↘ Spec (.of K)) j := by
  have hgen : genericBasePoint j ≫ j =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(C, W) Ω)) ≫ hW.fromSpec := by
    rw [Category.assoc, genericPointLift_comp, hW.fromSpecFunctionField_eq, ← Category.assoc,
      ← Spec.map_comp]
    congr 2
    ext a
    exact (IsScalarTower.algebraMap_apply Γ(C, W) C.functionField Ω a).symm
  apply Scheme.Hom.geometricFiber_hom_ext
  · rw [genericGeomPoint_geometricFiberProj, ← cancel_mono j, hgen]
    rw [Category.assoc, Category.assoc, Category.assoc,
      ← Scheme.Hom.geometricFiberMap_comp_geometricFiberProj j (comp_over j _)]
    rw [← pullback.condition_assoc, hhproj, reassoc_of% hfst, ← Spec.map_comp_assoc,
      ← CommRingCat.ofHom_comp, hγalg]
  · rw [genericGeomPoint_geometricFiberToAlgebraicClosure]
    rw [Category.assoc, Category.assoc,
      ← Scheme.Hom.geometricFiberMap_comp_geometricFiberToAlgebraicClosure j (comp_over j _),
      ← pullback.condition_assoc, hhalg, reassoc_of% hfst, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, hγε]

omit [GeometricallyConnected (C ↘ Spec (.of K))] in
/-- Assemble a boundary neighbourhood from a residue map and a punctured spectrum. -/
lemma nonempty_boundaryNeighbourhood_of_spectrum_data
    (I : Subgroup Gal(Ω/C.functionField)) (σF : Gal(Ω/C.functionField)) (x : C.finitePoints)
    {A : Type u} [CommRing A] [IsStrictlyHenselianLocalRing A]
    (r : A →+* AlgebraicClosure K) (hr : ∀ a, r a = 0 ↔ ¬ IsUnit a)
    (γ : A →+* Ω) (h : Spec (.of A) ⟶ (C ↘ Spec (.of K)).geometricFiber) [WeaklyEtale h]
    (hw : Spec.map (CommRingCat.ofHom r) ≫ h =
      𝟙 _ ≫ (C ↘ Spec (.of K)).geometricFiberPointOfFinitePoint x)
    (L : IntermediateField C.functionField Ω) [Algebra.IsSeparable L Ω] [Normal L Ω]
    (e' : Spec (.of L) ≅ pullback h j̄)
    (hspec : specFieldMap L Ω ≫ (e'.hom ≫ pullback.snd h j̄) =
      genericGeomPoint (U ↘ Spec (.of K)) j)
    (hfst : specFieldMap L Ω ≫ e'.hom ≫ pullback.fst h j̄ =
      Spec.map (CommRingCat.ofHom γ))
    (hmem : ∀ σ : Gal(Ω/C.functionField), σ ∈ I ↔
      ∀ b : L, σ (algebraMap L Ω b) = algebraMap L Ω b)
    (α : Spec (.of A) ⟶ Spec (.of A))
    (hα : α ≫ h = h ≫ ((C ↘ Spec (.of K)).geometricGaloisFrobenius ^
      (C ↘ Spec (.of K)).degreeOver x.1).asIso.hom)
    (hcα : (specGeometricFrobenius K ^ (C ↘ Spec (.of K)).degreeOver x.1).asIso.hom ≫
      Spec.map (CommRingCat.ofHom r) = Spec.map (CommRingCat.ofHom r) ≫ α)
    (hεα : Spec.map (CommRingCat.ofHom (σF : Ω →+* Ω)) ≫ Spec.map (CommRingCat.ofHom γ) =
      Spec.map (CommRingCat.ofHom γ) ≫ α) :
    Nonempty (BoundaryNeighbourhood (K := K) j I σF x) := by
  let t : ProEt.mk (𝟙 (Spec (.of (AlgebraicClosure K)))) ⟶
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤
        ((C ↘ Spec (.of K)).geometricFiberPointOfFinitePoint x)).obj (ProEt.mk h) :=
    MorphismProperty.Over.homMk (pullback.lift (Spec.map (CommRingCat.ofHom r)) (𝟙 _) hw)
      (pullback.lift_snd _ _ _)
  have htl : t.left ≫ pullback.fst h ((C ↘ Spec (.of K)).geometricFiberPointOfFinitePoint x) =
      Spec.map (CommRingCat.ofHom r) := pullback.lift_fst _ _ _
  let k := e'.hom ≫ pullback.snd h j̄
  let e : ProEt.mk k ≅ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ j̄).obj (ProEt.mk h) :=
    MorphismProperty.Over.isoMk e' rfl
  refine ⟨{
    A := A
    h := h
    t := t
    ht := by rw [htl]; exact specMap_closedPoint_of_forall_eq_zero_iff r hr
    K' := L
    exists_algebraMap_eq := fun a ↦ ⟨algebraMap C.functionField L a,
      (IsScalarTower.algebraMap_apply C.functionField L Ω a).symm⟩
    k := k
    e := e
    specFieldMap_comp := hspec
    mem_iff := hmem
    α := α
    hα := hα
    hcα := by rw [htl]; exact hcα
    hεα := by
      change Spec.map _ ≫ (specFieldMap L Ω ≫ e'.hom ≫ pullback.fst h j̄) =
        (specFieldMap L Ω ≫ e'.hom ≫ pullback.fst h j̄) ≫ α
      rw [hfst]
      exact hεα }⟩

omit [GeometricallyConnected (C ↘ Spec (.of K))] in
/-- **A strictly henselian neighbourhood of a boundary point from a compatible point.** Let `c`
be an affine chart at the boundary point `z` with closed point `x`, `Q` a maximal ideal over `z`
of the integral closure of `Γ(C, W)` in `Ω`, compatible with `x̄` and the geometric generic
point: `ι(ι_x(ā)) ≡ a mod Q` for `a ∈ Γ(C, W)`, where `ι : k̄ ↪ Ω` is `genericEmb` and
`ι_x : κ(x) ↪ k̄` the embedding of `x̄`. Let `σ_F` be an element of the decomposition group of
`Q` acting on `ι(k̄)` as the `deg x`-th power of the geometric Frobenius. Then the inertia
invariants `B_Q^{I_Q}` give a strictly henselian neighbourhood of the boundary point for the
inertia group of `Q` and `σ_F`. (blueprint `lem-wf-boundary-stalk-invariants`) -/
theorem nonempty_boundaryNeighbourhood_of_compatible {z : C} (hz : z ∉ Set.range j.base)
    (c : BoundaryChart (C ↘ Spec (.of K)) j z) (x : C.finitePoints) (hx : x.1 = z)
    (Q : Ideal (integralClosure Γ(C, c.W) Ω)) [Q.IsMaximal] [Q.LiesOver c.ideal]
    (hQ : ∀ a : Γ(C, c.W), ∃ b ∈ Q, (b : Ω) =
      genericEmb (U ↘ Spec (.of K)) j ((C ↘ Spec (.of K)).geometricFiberPointEmb x
        (sectionsResidue x (hx ▸ c.mem) a)) - algebraMap Γ(C, c.W) Ω a)
    (σF : Gal(Ω/C.functionField)) (hσF : σF ∈ MulAction.stabilizer Gal(Ω/C.functionField) Q)
    (hσFk : ∀ y, σF (genericEmb (U ↘ Spec (.of K)) j y) = genericEmb (U ↘ Spec (.of K)) j
      (letI := Fintype.ofFinite K
       (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K) ^
        (C ↘ Spec (.of K)).degreeOver x.1) y)) :
    Nonempty (BoundaryNeighbourhood (K := K) j (Q.inertia Gal(Ω/C.functionField)) σF x) := by
  subst hx
  let _ := Fintype.ofFinite K
  have hW := c.isAffineOpen
  have hxW : x.1 ∈ c.W := c.mem
  have : IsDedekindDomain Γ(C, c.W) := isDedekindDomain_of_isAffineOpen (C ↘ Spec (.of K)) hW
  have := isStrictlyHenselianLocalRing_inertiaInvariants_of_isAffineOpen hW Q
  -- the embedding of `k̄` and the residue map
  have hε₀ : (genericEmb (U ↘ Spec (.of K)) j).comp (algebraMap K (AlgebraicClosure K)) =
      (algebraMap Γ(C, c.W) Ω).comp (sectionsStructHom (k₀ := K) hW) := by
    rw [genericEmb_comp_algebraMap, genericStructHom_eq j hW]
  obtain ⟨ε, r, hrε, hr, hε, hφ⟩ := exists_algebraicClosure_inertiaInvariants hW Q x hxW _ hε₀
  have hgAp : specInertiaInvariantsTo hW Q ≫ (C ↘ Spec (.of K)) =
      Spec.map (CommRingCat.ofHom ε) ≫ (Scheme.specAlgebraicClosure K).hom := by
    have hfp : hW.fromSpec ≫ (C ↘ Spec (.of K)) =
        Spec.map (CommRingCat.ofHom (sectionsStructHom (k₀ := K) hW)) := by
      rw [CommRingCat.ofHom_hom, Spec.map_preimage]
    simp only [specInertiaInvariantsTo, Category.assoc, hfp, Scheme.specAlgebraicClosure,
      Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]
  -- the neighbourhood `h`
  obtain ⟨h, hhW, hhproj, hhalg⟩ : ∃ h : Spec (.of (Ideal.inertiaInvariants C.functionField Q)) ⟶
      (C ↘ Spec (.of K)).geometricFiber, WeaklyEtale h ∧
      h ≫ (C ↘ Spec (.of K)).geometricFiberProj = specInertiaInvariantsTo hW Q ∧
      h ≫ (C ↘ Spec (.of K)).geometricFiberToAlgebraicClosure =
        Spec.map (CommRingCat.ofHom ε) :=
    ⟨_, weaklyEtale_specInertiaInvariantsToGeometricFiber hW Q x hxW ε hgAp,
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  -- the lift of `x̄`
  have hpt := specMap_comp_specInertiaInvariantsTo_of_compatible hW Q x hxW _ ε r hrε hr hε _ hQ
  have hw := specMap_eq_geometricFiberPoint_of_projections ε r hrε x h (by
    rw [hhproj, hpt, Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricFiberProj]) hhalg
  -- the punctured neighbourhood
  obtain ⟨e', he'⟩ := exists_iso_pullback_geometricFiberMap hW Q x hxW j c.ϖ (c.opensRange_inf hz)
    c.ϖ_mem (c.ϖ_ne_zero hz) h hhproj
  have hfst : specFieldMap (IntermediateField.fixedField (Q.inertia Gal(Ω/C.functionField))) Ω ≫
      e'.hom ≫ pullback.fst h j̄ = Spec.map (CommRingCat.ofHom
        (Ideal.inertiaInvariantsToField C.functionField Q).toRingHom) := by
    rw [he', ← Spec.map_comp]
    rfl
  have hspec := genericGeomPoint_eq_of_projections j hW
    (algebraMap Γ(C, c.W) (Ideal.inertiaInvariants C.functionField Q)) ε
    (Ideal.inertiaInvariantsToField C.functionField Q).toRingHom
    (Ideal.inertiaInvariantsToField C.functionField Q).comp_algebraMap
    (RingHom.ext hε) h hhproj hhalg _ e'.hom hfst
  -- the Galois group of `Ω / K'` is the inertia group
  have hmem (σ : Gal(Ω/C.functionField)) : σ ∈ Q.inertia Gal(Ω/C.functionField) ↔
      ∀ b : IntermediateField.fixedField (Q.inertia Gal(Ω/C.functionField)),
        σ (algebraMap _ Ω b) = algebraMap _ Ω b := by
    refine ⟨fun hσ b ↦ (IntermediateField.mem_fixedField_iff _ _).1 b.2 σ hσ, fun hσ ↦ ?_⟩
    rw [← Ideal.fixingSubgroup_fixedField_inertia Q (K := C.functionField)]
    exact (IntermediateField.mem_fixingSubgroup_iff _ σ).2 fun y hy ↦ hσ ⟨y, hy⟩
  -- the Frobenius lift
  obtain ⟨α, hα, hcα, hεα⟩ := exists_frobeniusLift_inertiaInvariants hW Q hσF _ ε r hrε hr hε _
    hσFk h hhproj hhalg
  exact nonempty_boundaryNeighbourhood_of_spectrum_data j _ σF x r hr
    (Ideal.inertiaInvariantsToField C.functionField Q).toRingHom h hw
    (IntermediateField.fixedField (Q.inertia Gal(Ω/C.functionField))) e' hspec hfst hmem
    α hα hcα hεα

end AlgebraicGeometry.WeilGroup

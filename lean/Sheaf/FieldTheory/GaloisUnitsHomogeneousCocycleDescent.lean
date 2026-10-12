/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker S1
-/
module

public import Sheaf.FieldTheory.GaloisUnitsTwoCocycles
public import Sheaf.FieldTheory.GaloisUnitsCohomology
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Tactic.Abel
/-!
# Homogeneous Galois unit cocycles and their coboundary quotient

Source: Stacks Project, Section 0DVG, inhomogeneous differential, and Mathlib's
`TopRep.homogeneousCochains` and concrete `TopModuleCat` kernels and cokernels.
(blueprint: lem-sc-galois-units-homogeneous-cocycle-equivalence)
(blueprint: lem-sc-galois-units-homogeneous-cocycle-descent)
-/

@[expose] public section

universe u r v

namespace Field
open CategoryTheory TopRep
noncomputable section
set_option backward.isDefEq.respectTransparency false

section Cochains

variable {R : Type r} [CommRing R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] (A : TopRep.{v} R G)

private abbrev HC₂ : TopModuleCat.{v} R := ((resolution' A).X 2).invariants

private def coordinates (f : HC₂ A) : C(G × G, A) := by
  change ((resolution' A).X 2).ρ.invariants at f
  exact ⟨fun p ↦ f.val 1 p.1 (p.1 * p.2), by fun_prop⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] in
private lemma rho_mul (g h : G) (m : A) : A.ρ g (A.ρ h m) = A.ρ (g * h) m :=
  (congrArg (fun t ↦ t m) (A.ρ.toMonoidHom.map_mul g h)).symm

omit [LocallyCompactSpace G] in
private lemma equivariant (f : HC₂ A) (g a b c : G) :
    A.ρ g (f.val a b c) = f.val (g * a) (g * b) (g * c) := by
  have h := DFunLike.congr_fun (DFunLike.congr_fun (DFunLike.congr_fun
    ((ContRepresentation.mem_invariants _).mp f.property g) (g * a)) (g * b)) (g * c)
  simpa using h

private def reconstruct (hc : Continuous (fun p : G × A ↦ A.ρ p.1 p.2))
    (c : C(G × G, A)) : HC₂ A := by
  let F : C((G × G) × G, A) :=
    ⟨fun p ↦ A.ρ p.1.1 (c (p.1.1⁻¹ * p.1.2, p.1.2⁻¹ * p.2)),
      hc.comp (continuous_fst.fst.prodMk (c.continuous.comp (by fun_prop)))⟩
  refine ⟨F.curry.curry, ?_⟩
  apply (ContRepresentation.mem_invariants _).mpr
  intro g
  ext a b d
  change A.ρ g (A.ρ (g⁻¹ * a)
      (c ((g⁻¹ * a)⁻¹ * (g⁻¹ * b), (g⁻¹ * b)⁻¹ * (g⁻¹ * d)))) =
    A.ρ a (c (a⁻¹ * b, b⁻¹ * d))
  simp only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
  rw [rho_mul, mul_inv_cancel_left]

private lemma coordinates_reconstruct
    (hc : Continuous (fun p : G × A ↦ A.ρ p.1 p.2)) (c : C(G × G, A)) :
    coordinates A (reconstruct A hc c) = c := by
  ext p
  change A.ρ 1 (c (1⁻¹ * p.1, p.1⁻¹ * (p.1 * p.2))) = c p
  simp

private lemma reconstruct_coordinates
    (hc : Continuous (fun p : G × A ↦ A.ρ p.1 p.2)) (f : HC₂ A) :
    reconstruct A hc (coordinates A f) = f := by
  apply Subtype.ext
  ext a b c
  change A.ρ a (f.val 1 (a⁻¹ * b) ((a⁻¹ * b) * (b⁻¹ * c))) = f.val a b c
  rw [equivariant]
  simp [mul_assoc]

omit [LocallyCompactSpace G] in
private lemma differential₂ (f : HC₂ A) (a b c d : G) :
    (((homogeneousCochains A).d 2 3).hom f).val a b c d =
      f.val b c d - (f.val a c d - (f.val a b d - f.val a b c)) := by
  rw [homogeneousCochains.d_apply]
  rfl

private lemma kernel_coordinates (f : HC₂ A)
    (hf : ((homogeneousCochains A).d 2 3).hom f = 0) :
    ∀ g h i, A.ρ g (coordinates A f (h, i)) - coordinates A f (g * h, i) +
      coordinates A f (g, h * i) - coordinates A f (g, h) = 0 := by
  intro g h i
  have hz := DFunLike.congr_fun (DFunLike.congr_fun (DFunLike.congr_fun
    (DFunLike.congr_fun (congrArg Subtype.val hf) 1) g) (g * h)) (g * (h * i))
  rw [differential₂] at hz
  change f.val g (g * h) (g * (h * i)) -
      (f.val 1 (g * h) (g * (h * i)) -
        (f.val 1 g (g * (h * i)) - f.val 1 g (g * h))) = 0 at hz
  have he := equivariant A f g 1 h (h * i)
  simp only [mul_one] at he
  change A.ρ g (f.val 1 h (h * i)) - f.val 1 (g * h) ((g * h) * i) +
    f.val 1 g (g * (h * i)) - f.val 1 g (g * h) = 0
  rw [he, mul_assoc]
  abel_nf at hz ⊢
  exact hz

omit [LocallyCompactSpace G] in
private lemma reconstruct_kernel
    (hc : Continuous (fun p : G × A ↦ A.ρ p.1 p.2)) (c : C(G × G, A))
    (h : ∀ g h i, A.ρ g (c (h, i)) - c (g * h, i) + c (g, h * i) - c (g, h) = 0) :
    ((homogeneousCochains A).d 2 3).hom (reconstruct A hc c) = 0 := by
  apply Subtype.ext
  ext a b d e
  rw [differential₂]
  change A.ρ b (c (b⁻¹ * d, d⁻¹ * e)) -
    (A.ρ a (c (a⁻¹ * d, d⁻¹ * e)) -
      (A.ρ a (c (a⁻¹ * b, b⁻¹ * e)) - A.ρ a (c (a⁻¹ * b, b⁻¹ * d)))) = 0
  have hh := congrArg (A.ρ a) (h (a⁻¹ * b) (b⁻¹ * d) (d⁻¹ * e))
  simp only [map_sub, map_add, map_zero, rho_mul, mul_assoc,
    mul_inv_cancel_left] at hh
  abel_nf at hh ⊢
  exact hh

private def kernelEquiv (hc : Continuous (fun p : G × A ↦ A.ρ p.1 p.2)) :
    ((homogeneousCochains A).d 2 3).hom.ker ≃
      {c : C(G × G, A) // ∀ g h i,
        A.ρ g (c (h, i)) - c (g * h, i) + c (g, h * i) - c (g, h) = 0} where
  toFun f := ⟨coordinates A f.val, kernel_coordinates A f.val f.property⟩
  invFun c := ⟨reconstruct A hc c.val, reconstruct_kernel A hc c.val c.property⟩
  left_inv f := Subtype.ext (reconstruct_coordinates A hc f.val)
  right_inv c := Subtype.ext (coordinates_reconstruct A hc c.val)

private abbrev HC₁ : TopModuleCat.{v} R := ((resolution' A).X 1).invariants

private def coordinates₁ (f : HC₁ A) : C(G, A) := by
  change ((resolution' A).X 1).ρ.invariants at f
  exact ⟨fun g ↦ f.val 1 g, by fun_prop⟩

omit [LocallyCompactSpace G] in
private lemma equivariant₁ (f : HC₁ A) (g a b : G) :
    A.ρ g (f.val a b) = f.val (g * a) (g * b) := by
  have h := DFunLike.congr_fun (DFunLike.congr_fun
    ((ContRepresentation.mem_invariants _).mp f.property g) (g * a)) (g * b)
  simpa using h

private def reconstruct₁ (hc : Continuous (fun p : G × A ↦ A.ρ p.1 p.2))
    (c : C(G, A)) : HC₁ A := by
  let F : C(G × G, A) :=
    ⟨fun p ↦ A.ρ p.1 (c (p.1⁻¹ * p.2)),
      hc.comp (continuous_fst.prodMk (c.continuous.comp (by fun_prop)))⟩
  refine ⟨F.curry, ?_⟩
  apply (ContRepresentation.mem_invariants _).mpr
  intro g
  ext a b
  change A.ρ g (A.ρ (g⁻¹ * a) (c ((g⁻¹ * a)⁻¹ * (g⁻¹ * b)))) =
    A.ρ a (c (a⁻¹ * b))
  simp only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
  rw [rho_mul, mul_inv_cancel_left]

omit [LocallyCompactSpace G] in
private lemma differential₁ (f : HC₁ A) (a b c : G) :
    (((homogeneousCochains A).d 1 2).hom f).val a b c =
      f.val b c - (f.val a c - f.val a b) := by
  rw [homogeneousCochains.d_apply]
  rfl

private lemma coordinates_differential₁ (f : HC₁ A) (g h : G) :
    coordinates A (((homogeneousCochains A).d 1 2).hom f) (g, h) =
      A.ρ g (coordinates₁ A f h) - coordinates₁ A f (g * h) + coordinates₁ A f g := by
  change (((homogeneousCochains A).d 1 2).hom f).val 1 g (g * h) = _
  rw [differential₁]
  have he := equivariant₁ A f g 1 h
  simp only [mul_one] at he
  change f.val g (g * h) - (f.val 1 (g * h) - f.val 1 g) =
    A.ρ g (f.val 1 h) - f.val 1 (g * h) + f.val 1 g
  rw [he]
  abel

omit [LocallyCompactSpace G] in
private lemma coordinates₁_reconstruct₁
    (hc : Continuous (fun p : G × A ↦ A.ρ p.1 p.2)) (c : C(G, A)) :
    coordinates₁ A (reconstruct₁ A hc c) = c := by
  ext g
  change A.ρ 1 (c (1⁻¹ * g)) = c g
  simp

private noncomputable def concreteData : (homogeneousCochains A).sc' 1 2 3 |>.LeftHomologyData := by
  let S := (homogeneousCochains A).sc' 1 2 3
  exact ⟨_, _, _, _, _, TopModuleCat.isLimitKer S.g, by simp, TopModuleCat.isColimitCoker _⟩

private lemma coordinates_injective (hc : Continuous (fun p : G × A ↦ A.ρ p.1 p.2)) :
    Function.Injective (coordinates A) :=
  (show Function.LeftInverse (reconstruct A hc) (coordinates A) from
    reconstruct_coordinates A hc).injective

private lemma boundary_coordinates (hc : Continuous (fun p : G × A ↦ A.ρ p.1 p.2))
    (x y : ((homogeneousCochains A).d 2 3).hom.ker) :
    (concreteData A).f'.hom.range.quotientRel x y ↔
      ∃ b : C(G, A), ∀ g h, coordinates A y.val (g, h) =
        coordinates A x.val (g, h) + (A.ρ g (b h) - b (g * h) + b g) := by
  rw [Submodule.quotientRel_def, ← Submodule.neg_mem_iff, neg_sub]
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨coordinates₁ A B, ?_⟩
    intro g h
    have he := congrArg (fun z ↦ coordinates A z (g, h)) (congrArg Subtype.val hB)
    change coordinates A (((homogeneousCochains A).d 1 2).hom B) (g, h) =
      coordinates A y.val (g, h) - coordinates A x.val (g, h) at he
    rw [coordinates_differential₁] at he
    exact (eq_sub_iff_add_eq.mp he).symm.trans (add_comm _ _)
  · rintro ⟨b, hb⟩
    refine ⟨reconstruct₁ A hc b, ?_⟩
    apply Subtype.ext
    apply coordinates_injective A hc
    ext p
    change coordinates A (((homogeneousCochains A).d 1 2).hom
      (reconstruct₁ A hc b)) p = coordinates A y.val p - coordinates A x.val p
    rcases p with ⟨g, h⟩
    rw [coordinates_differential₁, coordinates₁_reconstruct₁, hb g h]
    abel

end Cochains

variable (K : Type u) [Field K]

private theorem action_continuous : Continuous (fun p :
    Gal(SeparableClosure K/K) × (galoisUnitsTopRep K) ↦
    (galoisUnitsTopRep K).ρ p.1 p.2) := by
  have : DiscreteTopology (galoisUnitsTopRep K) := ⟨rfl⟩
  rw [continuous_prod_of_discrete_right]
  intro x
  rw [continuous_discrete_rng]
  intro y
  change Additive ((SeparableClosure K)ˣ) at x y
  let : TopologicalSpace (SeparableClosure K) := ⊥
  have : DiscreteTopology (SeparableClosure K) := ⟨rfl⟩
  have : ContinuousSMul Gal(SeparableClosure K/K) (SeparableClosure K) :=
    continuousSMul_iff_stabilizer_isOpen.mpr stabilizer_isOpen_of_isIntegral
  have h : Continuous (fun g : Gal(SeparableClosure K/K) ↦
      g • ((x.toMul : (SeparableClosure K)ˣ) : SeparableClosure K)) :=
    continuous_id.smul continuous_const
  convert h.isOpen_preimage {((y.toMul : (SeparableClosure K)ˣ) : SeparableClosure K)}
    (isOpen_discrete _) using 1
  ext g
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  change Additive.ofMul (g • x.toMul) = y ↔
    g ((x.toMul : (SeparableClosure K)ˣ) : SeparableClosure K) =
      ((y.toMul : (SeparableClosure K)ˣ) : SeparableClosure K)
  exact ⟨fun h ↦ congrArg (fun z : Additive ((SeparableClosure K)ˣ) ↦
      (z.toMul : SeparableClosure K)) h,
    fun h ↦ congrArg Additive.ofMul (Units.ext h)⟩

private def explicitCocycleEquiv :
    {c : C(Gal(SeparableClosure K/K) × Gal(SeparableClosure K/K), galoisUnitsTopRep K) //
      ∀ g h i, (galoisUnitsTopRep K).ρ g (c (h, i)) - c (g * h, i) + c (g, h * i) - c (g, h) = 0} ≃
        GaloisUnitsTwoCocycle K :=
    { toFun := fun c ↦ ⟨c.val, c.val.continuous, c.property⟩
      invFun := fun c ↦ ⟨⟨c.val, c.property.1⟩, c.property.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

noncomputable abbrev GaloisUnitsHomogeneousCocycles (K : Type u) [Field K] : Type u :=
  ContinuousCohomology.cocycles (galoisUnitsTopRep K) 2

/-- The explicit change of variables identifies homogeneous degree-two cocycles with
inhomogeneous continuous cocycles.
Proof: evaluate at `(1,g,gh)` and use `f(g₀,g₁,g₂) = g₀ • c(g₀⁻¹g₁,g₁⁻¹g₂)` for the inverse.
The cocycle identity and continuity follow by direct substitution.
(blueprint: lem-sc-galois-units-homogeneous-cocycle-equivalence) -/
theorem nonempty_equiv_galoisUnitsHomogeneousCocycles_twoCocycle
    (K : Type u) [Field K] :
    Nonempty (GaloisUnitsHomogeneousCocycles K ≃ GaloisUnitsTwoCocycle K) := by
  let A := galoisUnitsTopRep K
  let e : ContinuousCohomology.cocycles A 2 ≅
      TopModuleCat.of ℤ ((homogeneousCochains A).d 2 3).hom.ker :=
    Limits.KernelFork.mapIsoOfIsLimit
      ((homogeneousCochains A).cyclesIsKernel 2 3 (by simp))
      (TopModuleCat.isLimitKer _) (Iso.refl _)
  exact ⟨(((forget (TopModuleCat ℤ)).mapIso e).toEquiv).trans
    ((kernelEquiv A (action_continuous K)).trans (explicitCocycleEquiv K))⟩

/-- A cochain equivalence descends through homology to the coboundary quotient.
Proof: homology is algebraic kernel modulo image; the formulas carry the degree-one
 differential to the displayed coboundary, so quotient induction gives inverse maps.
(blueprint: lem-sc-galois-units-homogeneous-cocycle-descent) -/
theorem nonempty_equiv_galoisUnitsH2_twoCocycleClasses_of_cocycle_equiv
    (K : Type u) [Field K]
    (h : Nonempty (GaloisUnitsHomogeneousCocycles K ≃ GaloisUnitsTwoCocycle K)) :
    Nonempty (GaloisUnitsH2 K ≃ GaloisUnitsTwoCocycleClasses K) := by
  rcases h with ⟨_⟩
  let A := galoisUnitsTopRep K
  let D := concreteData A
  let eH : continuousCohomology 2 A ≅ D.H :=
    (homogeneousCochains A).homologyIsoSc' 1 2 3 (by simp) (by simp) ≪≫ D.homologyIso
  let e := (kernelEquiv A (action_continuous K)).trans (explicitCocycleEquiv K)
  let eQ : (((homogeneousCochains A).d 2 3).hom.ker ⧸ D.f'.hom.range) ≃
      GaloisUnitsTwoCocycleClasses K :=
    Quotient.congr e (by
      intro x y
      change D.f'.hom.range.quotientRel x y ↔
        galoisUnitsTwoCocycleRel K (e x) (e y)
      rw [boundary_coordinates A (action_continuous K)]
      constructor
      · rintro ⟨b, hb⟩
        exact ⟨b, b.continuous, hb⟩
      · rintro ⟨b, hb, hrel⟩
        exact ⟨⟨b, hb⟩, hrel⟩)
  exact ⟨(((forget (TopModuleCat ℤ)).mapIso eH).toEquiv).trans eQ⟩
end

end Field

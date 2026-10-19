/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U4
-/
module

public import Sheaf.AlgebraicGeometry.Morphisms.FiniteEtaleAdicSectionsTransfer
public import Sheaf.RingTheory.Depth
import Sheaf.AlgebraicGeometry.Morphisms.DepthTwoPunctureGlobalSections
import Sheaf.AlgebraicGeometry.Morphisms.PrincipalThickeningLocalDivision
import Sheaf.AlgebraicGeometry.PrincipalSectionStableAnnihilator

/-! # Eventual vanishing of scalar restriction kernels on principal punctures

Source: Stacks Project, Tags 0H3E, 0BLD, 0BK0 and 0AVY.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem bounded_local_division_gluing
    (X : Scheme.{u}) (g a : Γ(X, ⊤)) (c n : ℕ)
    (hkill : ∀ (V : X.Opens) (k : ℕ) (s : Γ(X, V)),
      (X.presheaf.map (homOfLE le_top).op g) ^ k * s = 0 →
      (X.presheaf.map (homOfLE le_top).op g) ^ c * s = 0)
    (hlocal : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧ ∃ b : Γ(X, V),
      X.presheaf.map (homOfLE le_top).op a =
        (X.presheaf.map (homOfLE le_top).op g) ^ (n + c + 1) * b) :
    ∃ b : Γ(X, ⊤), a = g ^ (n + 1) * b := by
  classical
  choose V hx b hb using hlocal
  let s (x : X) : Γ(X, V x) :=
    (X.presheaf.map (homOfLE le_top).op g) ^ c * b x
  have hcover : (⊤ : X.Opens) ≤ iSup V := by
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
  have hres (U V : X.Opens) (h : U ≤ V) (t : Γ(X, ⊤)) :
      X.presheaf.map (homOfLE h).op
        (X.presheaf.map (homOfLE le_top).op t) =
      X.presheaf.map (homOfLE le_top).op t := by
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  have hcpt : TopCat.Presheaf.IsCompatible X.presheaf V s := by
    intro x y
    let U := V x ⊓ V y
    let gx : Γ(X, U) := X.presheaf.map (homOfLE le_top).op g
    let bx : Γ(X, U) := X.presheaf.map (homOfLE inf_le_left).op (b x)
    let by' : Γ(X, U) := X.presheaf.map (homOfLE inf_le_right).op (b y)
    have he : gx ^ (n + c + 1) * bx = gx ^ (n + c + 1) * by' := by
      have hhx := congrArg (X.presheaf.map (homOfLE
        (inf_le_left : U ≤ V x)).op) (hb x)
      have hhy := congrArg (X.presheaf.map (homOfLE
        (inf_le_right : U ≤ V y)).op) (hb y)
      simp only [map_mul, map_pow, hres] at hhx hhy
      exact hhx.symm.trans hhy
    have hz : gx ^ c * (bx - by') = 0 :=
      hkill U (n + c + 1) (bx - by') (by rw [mul_sub, he, sub_self])
    have hs : gx ^ c * bx = gx ^ c * by' := by
      rwa [mul_sub, sub_eq_zero] at hz
    change X.presheaf.map (homOfLE (inf_le_left : U ≤ V x)).op (s x) =
      X.presheaf.map (homOfLE (inf_le_right : U ≤ V y)).op (s y)
    simpa only [s, map_mul, map_pow, hres] using hs
  obtain ⟨t, ht, _⟩ := (TopCat.Sheaf.existsUnique_gluing'
    ⟨X.presheaf, X.IsSheaf⟩ V ⊤ (fun _ ↦ homOfLE le_top) hcover s hcpt)
  refine ⟨t, ?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨X.presheaf, X.IsSheaf⟩ V ⊤
    (fun _ ↦ homOfLE le_top) hcover
  intro x
  rw [map_mul, map_pow, ht]
  dsimp only [s]
  rw [← mul_assoc, ← pow_add]
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb x

/-- A scalar vanishing on a sufficiently deep punctured thickening lies in a
prescribed power of the principal ideal.

Source: Stacks Project, Tag 0H3E (the pro-isomorphism preceding the displayed
diagram), and Tags 0BLD, 0BK0 and 0AVY.
(blueprint: lem-sbc-punctured-principal-restriction-kernel)

Proof: Set F = O_W and I = (g) = ker(R to R/(g)). Depth three gives
Gamma(W,F)=R by canonical restriction and H^1(W,F)=0, using 0AVY and 0BK0.
Choose c with Ann(g^j)=Ann(g^c) for j at least c. Form E_j=[F --g^j--> F]
in degrees -1 and 0, with transition multiplication by g in degree -1.
The natural map E_j to F/g^j F has cone F[g^j][2]. The error-system
transition across c indices is zero, because g^c annihilates its stabilized
sheaf. This is the pro-isomorphism of 0H3E. Apply derived global sections
and degree-zero cohomology; pro-zero systems remain pro-zero under these
operations, and the kernel of the induced comparison is pro-zero.
Since H^1(W,F)=0, the cone cohomology in degree zero is R/g^j R, with its
usual quotient transitions. Hence for each n there is m at least n such
that the kernel of R/I^(m+1) to Gamma(W,F/g^(m+1)F) maps to zero in
R/I^(n+1). The pullback description of openThickening and the canonical
GammaSpecIso identify its scalar comparison with the displayed formula.
Apply this kernel assertion to the class of a-b when their restricted
images agree. Its class at level n is zero exactly when a-b belongs to
I^(n+1). This does not assert injectivity at any individual level.
The zero and nilpotent principal generators are included: stabilization
still holds, and the scalar comparison is eventually ordinary Hartogs. -/
theorem punctured_principal_restriction_kernel
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (g : R) (hg : g ∈ IsLocalRing.maximalIdeal R)
    (hdepth : (3 : ℕ∞) ≤ IsLocalRing.depth (R := R) R)
    (W : (Spec (.of R)).Opens)
    (hW : ∀ x : Spec (.of R), x ∈ W ↔ x ≠ IsLocalRing.closedPoint R) :
    let f := Ideal.Quotient.mk (Ideal.span {g})
    let I := RingHom.ker f
    ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ ∀ a b : R,
      ((ΓSpecIso (.of R)).inv ≫
        (FiniteEtale.Adic.openThickeningMap f W m ≫ W.ι).appTop) a =
      ((ΓSpecIso (.of R)).inv ≫
        (FiniteEtale.Adic.openThickeningMap f W m ≫ W.ι).appTop) b →
      a - b ∈ I ^ (n + 1) := by
  classical
  have _ := hg
  dsimp only
  let f := Ideal.Quotient.mk (Ideal.span {g})
  let I := RingHom.ker f
  let ρ : CommRingCat.of R ⟶ Γ(W.toScheme, ⊤) :=
    (ΓSpecIso (.of R)).inv ≫ W.ι.appTop
  have htwo : (2 : ℕ∞) ≤ IsLocalRing.depth (R := R) R :=
    le_trans (by decide) hdepth
  have hρ : Function.Bijective ρ :=
    (depth_two_puncture_globalSections_bijective R htwo W hW).comp
      (ConcreteCategory.bijective_of_isIso (ΓSpecIso (.of R)).inv)
  have : CompactSpace W := isCompact_iff_compactSpace.mp
    (TopologicalSpace.NoetherianSpace.isCompact (W : Set (Spec (.of R))))
  have : IsNoetherian W.toScheme := IsNoetherian.mk
  obtain ⟨c, hc⟩ := exists_principal_section_stable_annihilator W.toScheme (ρ g)
  intro n
  refine ⟨n + c, Nat.le_add_right n c, ?_⟩
  intro a b hab
  let t := ρ (a - b)
  have hz : (FiniteEtale.Adic.openThickeningMap f W (n + c)).appTop t = 0 := by
    have he : (FiniteEtale.Adic.openThickeningMap f W (n + c)).appTop (ρ a) =
        (FiniteEtale.Adic.openThickeningMap f W (n + c)).appTop (ρ b) := by
      simpa only [ρ, f, Scheme.Hom.comp_appTop, ← Category.assoc,
        ConcreteCategory.comp_apply]
        using hab
    change (FiniteEtale.Adic.openThickeningMap f W (n + c)).appTop (ρ (a - b)) = 0
    rw [map_sub, map_sub, he, sub_self]
  obtain ⟨s, hs⟩ := bounded_local_division_gluing W.toScheme (ρ g) t c n hc
    (principal_thickening_local_division R g W (n + c) t hz)
  obtain ⟨r, hr⟩ := hρ.surjective s
  have he : a - b = g ^ (n + 1) * r := by
    apply hρ.injective
    rw [map_mul, map_pow, hr]
    exact hs
  rw [he]
  apply Ideal.mul_mem_right
  apply Ideal.pow_mem_pow
  rw [Ideal.mk_ker]
  exact Ideal.subset_span (Set.mem_singleton g)

end AlgebraicGeometry.Scheme

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRings
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.RingTheory.RingPseudoCoherent
import WeilConjectures.RingTheory.PseudoCoherentInverseRingReconstructionModels

/-!
# Pseudo-coherent reconstruction over a tower of nilpotent quotients

Let `A = lim A_n` be the limit of a tower of rings with surjective transitions and nilpotent
kernels, and `E = R lim E_n` for a compatible tower of objects `E_n ∈ D(A_n)` with `E_1`
pseudo-coherent. Then `E` is pseudo-coherent, represented by the limit of compatible finite-free
models of the `E_n`, and the comparison maps `E ⊗^L_A A_n → E_n` are isomorphisms.

## Implementation details

By nilpotent invariance every `E_n` is pseudo-coherent. Marked free-complex lifting across each
nilpotent quotient builds a strictly compatible tower of finite-free complexes `P_n`, all zero
above one cutoff `b`, with degreewise surjective transitions `u_n` representing the given
transitions. Bases lift through the `u_n` (a lift of a basis modulo a nilpotent ideal is a basis,
by inverting `gf` and `fg` with geometric sums), so the termwise limit `P` is finite free with
`P ⊗_A A_n ≅ P_n`. The surjective module-complex tower lemma identifies `Q(P)` with the derived
limit, and comparing Roos triangles via TR3 gives a projection-respecting isomorphism
`Q(P) ≅ E` (no canonical choice is asserted). Finally, finite free bounded-above complexes are
K-flat and projective, so derived change of rings is computed by the ordinary tensor complex and
the derived comparison is represented by the chain isomorphism `P ⊗_A A_n → P_n`.

## References

* [Stacks, Tag 0CQF]
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- Reconstruction of a compatible pseudo-coherent tower, including its finite-free models.
The index `0` denotes the paper's index `1`. The ring-limit universal property in `hlim`
is the compatible-tuple construction, invariant under its unique ring isomorphism.
The left adjoints `L` and `M` of derived restriction of scalars denote derived tensor.
The normalization `hχ` specifies the canonical composition of restrictions. The maps
`η` and the equation for `γ` identify ordinary and derived tensor on the free model,
so the last equality identifies the actual projection-induced comparison maps. -/
theorem isPseudoCoherent_inverse_ring_reconstruction
    (R : ℕ → Type u) [∀ n, CommRing (R n)]
    (φ : ∀ n, R (n + 1) →+* R n)
    (hsurj : ∀ n, Function.Surjective (φ n))
    (hnil : ∀ n, IsNilpotent (RingHom.ker (φ n)))
    (A : Type u) [CommRing A] (q : ∀ n, A →+* R n)
    (hq : ∀ n, q n = (φ n).comp (q (n + 1)))
    (hlim : ∀ x : ∀ n, R n, (∀ n, φ n (x (n + 1)) = x n) →
      ∃! a : A, ∀ n, q n a = x n)
    [HasDerivedCategory.{w} (ModuleCat.{max u v} A)]
    [∀ n, HasDerivedCategory.{w} (ModuleCat.{max u v} (R n))]
    (L : ∀ n, DerivedCategory (ModuleCat.{max u v} (R (n + 1))) ⥤
      DerivedCategory (ModuleCat.{max u v} (R n)))
    (adjφ : ∀ n, L n ⊣ (ModuleCat.restrictScalars (φ n)).mapDerivedCategory)
    (M : ∀ n, DerivedCategory (ModuleCat.{max u v} A) ⥤
      DerivedCategory (ModuleCat.{max u v} (R n)))
    (adjq : ∀ n, M n ⊣ (ModuleCat.restrictScalars (q n)).mapDerivedCategory)
    (χ : ∀ n, (ModuleCat.restrictScalars (q n)).mapDerivedCategory ≅
      (ModuleCat.restrictScalars (φ n)).mapDerivedCategory ⋙
        (ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategory)
    (hχ : ∀ n (C : CochainComplex (ModuleCat.{max u v} (R n)) ℤ),
      (χ n).hom.app (Q.obj C) ≫
        (ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategory.map
          ((ModuleCat.restrictScalars (φ n)).mapDerivedCategoryFactors.hom.app C) ≫
        (ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.restrictScalars (φ n)).mapHomologicalComplex (.up ℤ)).obj C) =
      (ModuleCat.restrictScalars (q n)).mapDerivedCategoryFactors.hom.app C ≫
        Q.map ((NatIso.mapHomologicalComplex
          (ModuleCat.restrictScalarsComp' (q (n + 1)) (φ n) (q n) (hq n))
          (.up ℤ)).hom.app C))
    (Eₙ : ∀ n, DerivedCategory (ModuleCat.{max u v} (R n)))
    (t : ∀ n, Eₙ (n + 1) ⟶
      (ModuleCat.restrictScalars (φ n)).mapDerivedCategory.obj (Eₙ n))
    (hred : ∀ n, IsIso (((adjφ n).homEquiv (Eₙ (n + 1)) (Eₙ n)).symm (t n)))
    (hpc : IsPseudoCoherent (Eₙ 0))
    [HasProduct (fun n ↦ (ModuleCat.restrictScalars (q n)).mapDerivedCategory.obj (Eₙ n))]
    (E : DerivedCategory (ModuleCat.{max u v} A))
    (pE : E ⟶ ∏ᶜ fun n ↦
      (ModuleCat.restrictScalars (q n)).mapDerivedCategory.obj (Eₙ n))
    (δ : (∏ᶜ fun n ↦ (ModuleCat.restrictScalars (q n)).mapDerivedCategory.obj (Eₙ n)) ⟶
      E⟦(1 : ℤ)⟧)
    (hE : IsDerivedLimitTriangle
      (fun n ↦ (ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategory.map (t n) ≫
        (χ n).inv.app (Eₙ n)) E pE δ) :
    IsPseudoCoherent E ∧
    (∀ n, IsIso (((adjq n).homEquiv E (Eₙ n)).symm (pE ≫ Pi.π _ n))) ∧
    ∃ (Pₙ : ∀ n, CochainComplex (ModuleCat.{max u v} (R n)) ℤ)
      (b : ℤ) (βₙ : ∀ n, Q.obj (Pₙ n) ≅ Eₙ n)
      (uₙ : ∀ n, Pₙ (n + 1) ⟶
        ((ModuleCat.restrictScalars (φ n)).mapHomologicalComplex (.up ℤ)).obj (Pₙ n))
      (θₙ : ∀ n, ((ModuleCat.extendScalars (φ n)).mapHomologicalComplex (.up ℤ)).obj
        (Pₙ (n + 1)) ≅ Pₙ n)
      (P : CochainComplex (ModuleCat.{max u v} A) ℤ) (β : Q.obj P ≅ E)
      (p : ∀ n, P ⟶
        ((ModuleCat.restrictScalars (q n)).mapHomologicalComplex (.up ℤ)).obj (Pₙ n))
      (θ : ∀ n, ((ModuleCat.extendScalars (q n)).mapHomologicalComplex (.up ℤ)).obj P ≅ Pₙ n)
      (η : ∀ n, P ⟶ ((ModuleCat.restrictScalars (q n)).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.extendScalars (q n)).mapHomologicalComplex (.up ℤ)).obj P))
      (γ : ∀ n, (M n).obj (Q.obj P) ≅
        Q.obj (((ModuleCat.extendScalars (q n)).mapHomologicalComplex (.up ℤ)).obj P)),
      (∀ n, (Pₙ n).IsStrictlyLE b) ∧
      (∀ n i, Module.Free (R n) ((Pₙ n).X i) ∧ Module.Finite (R n) ((Pₙ n).X i)) ∧
      (∀ n i, Function.Surjective ((uₙ n).f i)) ∧
      (∀ n i, ((ModuleCat.extendRestrictScalarsAdj (φ n)).homEquiv
        ((Pₙ (n + 1)).X i) ((Pₙ n).X i) ((θₙ n).hom.f i)) = (uₙ n).f i) ∧
      (∀ n, Q.map (uₙ n) = (βₙ (n + 1)).hom ≫ t n ≫
        (ModuleCat.restrictScalars (φ n)).mapDerivedCategory.map (βₙ n).inv ≫
        (ModuleCat.restrictScalars (φ n)).mapDerivedCategoryFactors.hom.app (Pₙ n)) ∧
      P.IsStrictlyLE b ∧
      (∀ i, Module.Free A (P.X i) ∧ Module.Finite A (P.X i)) ∧
      (∀ n i (y : P.X i), (uₙ n).f i ((p (n + 1)).f i y) = (p n).f i y) ∧
      (∀ i (x : ∀ n, (Pₙ n).X i), (∀ n, (uₙ n).f i (x (n + 1)) = x n) →
        ∃! y : P.X i, ∀ n, (p n).f i y = x n) ∧
      (∀ n, Q.map (p n) ≫
        (ModuleCat.restrictScalars (q n)).mapDerivedCategoryFactors.inv.app (Pₙ n) ≫
        (ModuleCat.restrictScalars (q n)).mapDerivedCategory.map (βₙ n).hom =
        β.hom ≫ pE ≫ Pi.π _ n) ∧
      (∀ n i, ((ModuleCat.extendRestrictScalarsAdj (q n)).homEquiv
        (P.X i) ((Pₙ n).X i) ((θ n).hom.f i)) = (p n).f i) ∧
      (∀ n i, (η n).f i = (ModuleCat.extendRestrictScalarsAdj (q n)).unit.app (P.X i)) ∧
      (∀ n, (adjq n).unit.app (Q.obj P) ≫
        (ModuleCat.restrictScalars (q n)).mapDerivedCategory.map (γ n).hom ≫
        (ModuleCat.restrictScalars (q n)).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.extendScalars (q n)).mapHomologicalComplex (.up ℤ)).obj P) =
        Q.map (η n)) ∧
      (∀ n, (γ n).hom ≫ Q.map (θ n).hom ≫ (βₙ n).hom =
        (M n).map β.hom ≫ ((adjq n).homEquiv E (Eₙ n)).symm (pE ≫ Pi.π _ n)) := by
  have hm := reconstruction_models (R := R) (φ := φ) (hsurj := hsurj) (hnil := hnil)
    (A := A) (q := q) (hq := hq) (hlim := hlim) (L := L) (adjφ := adjφ) (M := M)
    (adjq := adjq) (χ := χ) (hχ := hχ) (Eₙ := Eₙ) (t := t) (hred := hred)
    (hpc := hpc) (E := E) (pE := pE) (δ := δ) (hE := hE)
  obtain ⟨Pₙ, b, βₙ, uₙ, θₙ, P, β, p, θ, η, γ, hdata⟩ := hm
  rcases hdata with ⟨hboundₙ, hfreeₙ, hsurjₙ, hθₙ, huₙ, hPbound, hPfree,
    hproj, hlimP, hcomparison, hθ, hη, hγ, hfinal⟩
  have hpcE : IsPseudoCoherent E := ⟨P, b, hPbound, hPfree, ⟨β⟩⟩
  have hIso (n : ℕ) : IsIso (((adjq n).homEquiv E (Eₙ n)).symm (pE ≫ Pi.π _ n)) := by
    let f := ((adjq n).homEquiv E (Eₙ n)).symm (pE ≫ Pi.π _ n)
    have hi : IsIso ((M n).map β.hom ≫ f) := by
      rw [← hfinal n]
      infer_instance
    set_option linter.style.haveILetI false in
      letI : IsIso ((M n).map β.hom ≫ f) := hi
    exact IsIso.of_isIso_comp_left ((M n).map β.hom) f
  exact ⟨hpcE, hIso, ⟨Pₙ, b, βₙ, uₙ, θₙ, P, β, p, θ, η, γ,
    ⟨hboundₙ, hfreeₙ, hsurjₙ, hθₙ, huₙ, hPbound, hPfree, hproj, hlimP,
      hcomparison, hθ, hη, hγ, hfinal⟩⟩⟩

end DerivedCategory

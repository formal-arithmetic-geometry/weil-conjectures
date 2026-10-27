/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
public import WeilConjectures.AlgebraicGeometry.ProjTildeFunctorial
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.ProjStandardOpenProperties
import Sheaf.Algebra.Module.GradedLocalizationExact
import WeilConjectures.AlgebraicGeometry.Modules.BasisExactness

/-!
# Exactness of associated graded-module sheaves on Proj

Source: Stacks Project, Constructions, Lemma 01M7, final assertion
(blueprint: lem-sfb-proj-graded-sheafification-exact).

For general graded modules, `def-weil-pbc-proj-twisting-sheaf` (1) refers to the
associated sheaves of `gradedModuleSheaf_exists`. Their chart identifications are
written below as additive embeddings with prescribed range, scalar compatibility,
and restriction formulas, as in `tilde_functorial`. The sheaf arrows are specified
by that theorem's fraction formula. No new associated sheaf construction is made.
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace LocalizedModule HomogeneousLocalization

namespace AlgebraicGeometry.Proj

/-- An exact sequence of integer-graded modules over any nonnegatively graded
commutative ring induces a short exact sequence of associated module sheaves on Proj.
Source: Stacks Project, Constructions, Lemma 01M7, final assertion.
(blueprint: lem-sfb-proj-graded-sheafification-exact)

Proof:
1. By `lem-weil-pbc-proj-standard-open-inclusion`, positive homogeneous standard opens
   form a basis. The chart descriptions of `def-weil-pbc-proj-twisting-sheaf` (1),
   supplied by `gradedModuleSheaf_exists`, identify the sections with degree-zero
   fractions. By `lem-sc-p1-proj-tilde-functorial`, the induced maps on these charts
   send y/f^m to phi(y)/f^m and psi(y)/f^m respectively.
2. Extend the ring grading to the integers by zero in negative degrees. It is an
   internal grading of the same ring and acts on the given module gradings: negative
   scalars are zero and the nonnegative scalar rule is hsmul. Fix a positive homogeneous
   f. Apply `lem-sc-graded-localization-exact` to the exact triples 0 → M 0 → M 1,
   M 0 → M 1 → M 2, and M 1 → M 2 → 0. All maps preserve degree. Its degree-zero
   clause gives injectivity of the first chart map, exactness in the middle and
   surjectivity of the second, since localizing the zero module gives zero.
3. Apply `lem-sc-p1-module-basis-exactness` to this basis and these sheaf maps. The
   chart exactness of step 2 gives zero composite, a monic first map, an epic second
   map and exactness of their short complex. These are precisely ShortComplex.ShortExact.
   The argument also applies to empty Proj and empty standard opens. It uses no
   generation in degree one, Noetherian property, or field assumption.
-/
theorem graded_sheafification_shortExact
    {S : Type u} [CommRing S] (𝒜 : ℕ → AddSubgroup S) [GradedRing 𝒜]
    (M : Fin 3 → Type u) [∀ j, AddCommGroup (M j)] [∀ j, Module S (M j)]
    (𝓜 : ∀ j, ℤ → AddSubgroup (M j))
    (h𝓜 : ∀ j, DirectSum.IsInternal (𝓜 j))
    (hsmul : ∀ (j : Fin 3) (n : ℕ) (z : ℤ) (a : S) (y : M j),
      a ∈ 𝒜 n → y ∈ 𝓜 j z → a • y ∈ 𝓜 j (n + z))
    (F : Fin 3 → (Proj 𝒜).Modules)
    (alpha : ∀ (j : Fin 3) (f : S) (d : ℕ), 0 < d → f ∈ 𝒜 d →
      (F j).val.obj (op (basicOpen 𝒜 f)) →+ LocalizedModule.Away f (M j))
    (halpha : ∀ (j : Fin 3) (f : S) (d : ℕ) (hd : 0 < d) (hf : f ∈ 𝒜 d),
      Function.Injective (alpha j f d hd hf) ∧
      Set.range (alpha j f d hd hf) = degreeZeroFractions
        (fun n : ℕ ↦ (𝒜 n : Set S)) (fun n : ℕ ↦ (𝓜 j n : Set (M j)))
        (Submonoid.powers f))
    (hscalar : ∀ (j : Fin 3) (f : S) (d : ℕ) (hd : 0 < d) (hf : f ∈ 𝒜 d)
      (r : HomogeneousLocalization.Away 𝒜 f) (s : (F j).val.obj (op (basicOpen 𝒜 f))),
      alpha j f d hd hf (awayToSection 𝒜 f r • s) =
        algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f) r •
          alpha j f d hd hf s)
    (hres : ∀ (j : Fin 3) (f g : S) (d b : ℕ) (hd : 0 < d) (hb : 0 < b)
      (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 b) (inc : basicOpen 𝒜 g ≤ basicOpen 𝒜 f)
      (e k : ℕ) (a : S), 0 < e → a ∈ 𝒜 k → g ^ e = a * f →
      ∀ (m : ℕ) (y : M j) (s : (F j).val.obj (op (basicOpen 𝒜 f))),
      alpha j f d hd hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
      alpha j g b hb hg ((F j).val.map (homOfLE inc).op s) =
        mk (a ^ m • y) (⟨g ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g))
    (phi : M 0 →ₗ[S] M 1) (psi : M 1 →ₗ[S] M 2)
    (hphi : ∀ (z : ℤ) (y : M 0), y ∈ 𝓜 0 z → phi y ∈ 𝓜 1 z)
    (hpsi : ∀ (z : ℤ) (y : M 1), y ∈ 𝓜 1 z → psi y ∈ 𝓜 2 z)
    (hinj : Function.Injective phi) (hexact : Function.Exact phi psi)
    (hsurj : Function.Surjective psi)
    (i : F 0 ⟶ F 1) (q : F 1 ⟶ F 2)
    (hi : ∀ (f : S) (d : ℕ) (hd : 0 < d) (hf : f ∈ 𝒜 d) (m : ℕ) (y : M 0)
      (s : (F 0).val.obj (op (basicOpen 𝒜 f))),
      alpha 0 f d hd hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
      alpha 1 f d hd hf (i.val.app (op (basicOpen 𝒜 f)) s) =
        mk (phi y) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f))
    (hq : ∀ (f : S) (d : ℕ) (hd : 0 < d) (hf : f ∈ 𝒜 d) (m : ℕ) (y : M 1)
      (s : (F 1).val.obj (op (basicOpen 𝒜 f))),
      alpha 1 f d hd hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
      alpha 2 f d hd hf (q.val.app (op (basicOpen 𝒜 f)) s) =
        mk (psi y) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f)) :
    ∃ h : i ≫ q = 0, (ShortComplex.mk i q h).ShortExact := by
  sorry

end AlgebraicGeometry.Proj

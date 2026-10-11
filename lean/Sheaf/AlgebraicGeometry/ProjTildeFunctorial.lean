/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.AlgebraicGeometry.ProjGradedModuleSheafExists

/-!
# Functoriality of associated module sheaves on Proj

Source: Stacks Project, Constructions, Lemma 01M7, final paragraph, and the construction
before Definition 01M6 (blueprint: lem-sc-p1-proj-tilde-functorial).

The three graded modules are indexed by `Fin 3`. Chart and stalk identifications are
written as injective additive maps into the ordinary localizations with prescribed image.
These are precisely the inclusions composed with the equivalences supplied by
`gradedModuleSheaf_exists`; no new associated sheaf is chosen or defined here.
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace LocalizedModule HomogeneousLocalization

namespace AlgebraicGeometry.Proj

/-- A degree-preserving linear map has a unique associated sheaf map, with the indicated
fraction formulas on charts and stalks. These maps preserve composition and identities.
Source: Stacks, Constructions, Lemma 01M7 and the construction before Definition 01M6.
(blueprint: lem-sc-p1-proj-tilde-functorial)

Proof:
1. On every positive homogeneous standard open, send `y/f^m` to `phi(y)/f^m`.
   Localization makes this well defined, additive and linear over the degree-zero ring,
   as in `lem-weil-pbc-graded-module-away-restriction`.
2. For an inclusion with `g^e = a*f`, restriction sends `y/f^m` to `a^m*y/g^(e*m)`.
   Linearity of `phi` gives compatibility with restriction. The same fraction calculation
   gives the identity and composition formulas.
3. The standard opens form a basis by `lem-weil-pbc-proj-standard-open-inclusion`.
   Apply `lem-weil-pbc-sheaf-of-modules-from-basis` to extend these compatible maps
   uniquely to the sheaves of `lem-weil-pbc-proj-graded-module-sheaf-exists`.
   Uniqueness on the basis gives the global identity and composition laws.
4. By clause (c) of `lem-weil-pbc-proj-graded-module-sheaf-exists`, stalks are the
   equal-degree fractions outside the homogeneous prime. The chart formula gives
   the asserted formula for germs. A denominator of degree zero is handled by multiplying
   numerator and denominator by a positive homogeneous element outside that prime.
-/
theorem tilde_functorial
    {S : Type u} [CommRing S] (𝒜 : ℕ → AddSubgroup S) [GradedRing 𝒜]
    (M : Fin 3 → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module S (M i)]
    (𝓜 : ∀ i, ℤ → AddSubgroup (M i))
    (h𝓜 : ∀ i, DirectSum.IsInternal (𝓜 i))
    (hsmul : ∀ (i : Fin 3) (n : ℕ) (z : ℤ) (a : S) (y : M i),
      a ∈ 𝒜 n → y ∈ 𝓜 i z → a • y ∈ 𝓜 i (n + z))
    (F : Fin 3 → (Proj 𝒜).Modules)
    (alpha : ∀ (i : Fin 3) (f : S), ∀ (d : ℕ), 0 < d → f ∈ 𝒜 d →
      (F i).val.obj (op (basicOpen 𝒜 f)) →+ LocalizedModule.Away f (M i))
    (halpha : ∀ (i : Fin 3) (f : S) (d : ℕ) (hd : 0 < d) (hf : f ∈ 𝒜 d),
      Function.Injective (alpha i f d hd hf) ∧
      Set.range (alpha i f d hd hf) = degreeZeroFractions
        (fun n : ℕ ↦ (𝒜 n : Set S)) (fun n : ℕ ↦ (𝓜 i n : Set (M i)))
        (Submonoid.powers f))
    (hscalar : ∀ (i : Fin 3) (f : S) (d : ℕ) (hd : 0 < d) (hf : f ∈ 𝒜 d)
      (r : HomogeneousLocalization.Away 𝒜 f) (s : (F i).val.obj (op (basicOpen 𝒜 f))),
      alpha i f d hd hf (awayToSection 𝒜 f r • s) =
        algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f) r •
          alpha i f d hd hf s)
    (hres : ∀ (i : Fin 3) (f g : S) (d b : ℕ) (hd : 0 < d) (hb : 0 < b)
      (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 b) (inc : basicOpen 𝒜 g ≤ basicOpen 𝒜 f)
      (e k : ℕ) (a : S), 0 < e → a ∈ 𝒜 k → g ^ e = a * f →
      ∀ (m : ℕ) (y : M i) (s : (F i).val.obj (op (basicOpen 𝒜 f))),
      alpha i f d hd hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
      alpha i g b hb hg ((F i).val.map (homOfLE inc).op s) =
        mk (a ^ m • y) (⟨g ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g))
    (mu : ∀ (i : Fin 3) (x : Proj 𝒜),
      (RingedSpace.moduleStalkFunctor (Proj 𝒜).toRingedSpace x).obj (F i) →+
        LocalizedModule x.asHomogeneousIdeal.toIdeal.primeCompl (M i))
    (hmu : ∀ (i : Fin 3) (x : Proj 𝒜), Function.Injective (mu i x) ∧
      Set.range (mu i x) = degreeZeroFractions
        (fun n : ℕ ↦ (𝒜 n : Set S)) (fun n : ℕ ↦ (𝓜 i n : Set (M i)))
        x.asHomogeneousIdeal.toIdeal.primeCompl)
    (hgerm : ∀ (i : Fin 3) (x : Proj 𝒜) (f : S) (d : ℕ) (hd : 0 < d)
      (hf : f ∈ 𝒜 d) (hx : x ∈ basicOpen 𝒜 f) (m : ℕ) (y : M i)
      (s : (F i).val.obj (op (basicOpen 𝒜 f)))
      (t : x.asHomogeneousIdeal.toIdeal.primeCompl),
      alpha i f d hd hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
      (t : S) = f ^ m →
      mu i x (TopCat.Presheaf.germ (F i).val.presheaf (basicOpen 𝒜 f) x hx s) = mk y t) :
    ∃ lift : ∀ (i j : Fin 3) (phi : M i →ₗ[S] M j),
      (∀ (z : ℤ) (y : M i), y ∈ 𝓜 i z → phi y ∈ 𝓜 j z) → (F i ⟶ F j),
      (∀ (i j : Fin 3) (phi : M i →ₗ[S] M j)
        (hphi : ∀ (z : ℤ) (y : M i), y ∈ 𝓜 i z → phi y ∈ 𝓜 j z)
        (chi : F i ⟶ F j),
        (∀ (f : S) (d : ℕ) (hd : 0 < d) (hf : f ∈ 𝒜 d) (m : ℕ) (y : M i)
          (s : (F i).val.obj (op (basicOpen 𝒜 f))),
          alpha i f d hd hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
          alpha j f d hd hf (chi.val.app (op (basicOpen 𝒜 f)) s) =
            mk (phi y) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f)) ↔
          chi = lift i j phi hphi) ∧
      (∀ (i j k : Fin 3) (phi : M i →ₗ[S] M j) (psi : M j →ₗ[S] M k)
        (hphi : ∀ (z : ℤ) (y : M i), y ∈ 𝓜 i z → phi y ∈ 𝓜 j z)
        (hpsi : ∀ (z : ℤ) (y : M j), y ∈ 𝓜 j z → psi y ∈ 𝓜 k z),
        lift i k (psi.comp phi) (fun z y hy ↦ hpsi z (phi y) (hphi z y hy)) =
          lift i j phi hphi ≫ lift j k psi hpsi) ∧
      (∀ i : Fin 3, lift i i (LinearMap.id : M i →ₗ[S] M i) (fun _ _ hy ↦ hy) = 𝟙 (F i)) ∧
      (∀ (i j : Fin 3) (phi : M i →ₗ[S] M j)
        (hphi : ∀ (z : ℤ) (y : M i), y ∈ 𝓜 i z → phi y ∈ 𝓜 j z)
        (x : Proj 𝒜) (d : ℕ) (h : x.asHomogeneousIdeal.toIdeal.primeCompl)
        (y : M i), (h : S) ∈ 𝒜 d → y ∈ 𝓜 i d →
        ∀ s : (RingedSpace.moduleStalkFunctor (Proj 𝒜).toRingedSpace x).obj (F i),
        mu i x s = mk y h →
        mu j x ((RingedSpace.moduleStalkFunctor (Proj 𝒜).toRingedSpace x).map
          (lift i j phi hphi) s) = mk (phi y) h) := by
  sorry

end AlgebraicGeometry.Proj

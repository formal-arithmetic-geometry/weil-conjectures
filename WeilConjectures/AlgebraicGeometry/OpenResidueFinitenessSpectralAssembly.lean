/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SmoothPurity.Supporting.ExcellentRing
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.AlgebraicGeometry.FiniteCoverSpectralObjectAssembly
public import WeilConjectures.AlgebraicGeometry.ConstructibleSpectralAbutmentObject
public import WeilConjectures.AlgebraicGeometry.PlusDerivedConstructibleComparison

/-! # Assembly of the finite-open-cover spectral witness -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- Assemble the finite-cover spectral witness from its principal-intersection terms.

Source: ILO, Exposé XIII, Theorem 1.1.1(i), Proposition 2.3.4 and Remark 2.3.5.
The principal-page data supplies the initial page; the ordered Cech construction supplies the
spectral sequence and its finite abutment filtration.
This theorem stops before restriction descent.

Proof: apply `finite_open_cover_direct_image_spectral_sequence`
(lem-per-finite-open-cover-direct-image-spectral-sequence) to `V = U ×_X S → S` and the ordered
cover `W`: it gives a first-quadrant spectral sequence with
`E₁^{p,r} = ⊕_{a : Fin (p+1) ↪o Fin m} R^r((⋂ W (a k)) → S)_*(G|)` abutting, through a finite
filtration, to `R^{p+r}(V → S)_*(G|_V)`, the `q`-th homology of the displayed derived image.
Each summand is constructible by `hTerms`, a finite direct sum is constructible
(thm-constructible-serre), and `E₁^{p,r} = 0` for `p ≥ m`.  The Serre page induction and the
finite `E∞` filtration (`constructible_spectral_abutment`,
lem-per-qe-open-residue-constructible-spectral-abutment; its declaration must first be placed
below this module, since the item module imports this one) give constructibility of the
abutment in degree `q ≥ 0`.  If `m = 0`, `iSup W = ⊤` forces `V` to be empty and all terms vanish.
(blueprint: lem-per-qe-open-residue-spectral-assembly)
-/
theorem open_residue_constructible_spectral_witness
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type (u + 1)) [Field k] [Finite k] [CharP k ℓ]
    {X U : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (hXdim : ∃ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (hXqe : ∀ V : X.Opens, IsAffineOpen V → IsQuasiExcellent (Γ(X, V)))
    (hℓ : IsUnit (ℓ : Γ(X, ⊤)))
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (I : Type u) [Fintype I] (Ucov : I → X.Opens)
    (hAff : ∀ i, IsAffineOpen (Ucov i))
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} k))
    (hG : Scheme.IsConstructibleEtaleModuleSheaf G)
    (q : ℤ) (hq : 0 ≤ q) (i : I)
    (hTerms : ∃ (m : ℕ) (W : Fin m → (Limits.pullback j (Ucov i).ι).Opens),
      iSup W = ⊤ ∧
        ∀ (p r : ℕ) (a : Fin (p + 1) ↪o Fin m),
          Scheme.IsConstructibleEtaleModuleSheaf
            ((finiteCoverHigherImage k (Limits.pullback.snd j (Ucov i).ι)
              (finiteCoverIntersection W a) r).obj
              ((upperStar (ModuleCat.{u + 1} k)
                (Limits.pullback.fst j (Ucov i).ι)).obj G))) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf (Ucov i).toScheme.smallEtaleTopology (ModuleCat.{u + 1} k)) q).obj
        ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} k)
          (Limits.pullback.snd j (Ucov i).ι)).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((upperStar (ModuleCat.{u + 1} k)
              (Limits.pullback.fst j (Ucov i).ι)).obj G)))) := by
  obtain ⟨m, W, hW, hterms⟩ := hTerms
  let M := ((upperStar (ModuleCat.{u + 1} k)
    (Limits.pullback.fst j (Ucov i).ι)).obj G)
  have hterms' : ∀ (p r : ℕ) (a : Fin (p + 1) ↪o Fin m),
      Scheme.IsConstructibleSheaf
        ((finiteCoverHigherImage k (Limits.pullback.snd j (Ucov i).ι)
          (finiteCoverIntersection W a) r).obj M) := by
    intro p r a
    exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1
      (hterms p r a)
  obtain ⟨E, hpage, hab⟩ := finite_cover_spectral_object_assembly
    (k := k) (f := Limits.pullback.snd j (Ucov i).ι) m W hW M hterms'
  have hH := constructible_spectral_abutment_object E _ hpage hab q.toNat
  have hplus := constructible_plus_homology_of_rightDerived
    (Limits.pullback.snd j (Ucov i).ι) M q hq hH
  exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 hplus

end AlgebraicGeometry.Etale

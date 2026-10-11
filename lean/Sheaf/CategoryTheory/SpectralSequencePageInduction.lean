import Mathlib.Algebra.Homology.SpectralSequence.Basic
import Sheaf.CategoryTheory.ExactCoupleConvergence

/-!
# Page induction for morphisms of spectral sequences

Source: blueprint `lem-sp-page-induction` (blueprint: lem-sp-page-induction).

Spectral sequences are Mathlib's `SpectralSequence` (node `def-sp-spectral-sequence`) on
bidegrees `ℤ × ℤ`, starting at page `2`. The limiting page is formed as in
`def-sp-convergence` (`CategoryTheory.BigradedExactCouple.CycleBoundaryTower`,
`LimitSubobjects`, `pageInfinity`), with the recursion applied to the pages and differentials
of the spectral sequence: cycles `Z r p q` and boundaries `B r p q` are subobjects of
`E_2^{p,q}`, `Z 2 = ⊤`, `B 2 = ⊥`, the projection `π 2` is the inclusion, `Z (r+1)` and
`B (r+1)` are the images in `E_2` of the inverse images of `ker d_r` and `im d_r` under
`π r : Z_r → E_r`, and `π (r+1)` is the lift of `π r` to the cycles of `E_r` followed by the
homology projection and the structure isomorphism `H(E_r) ≅ E_{r+1}`. `E_∞ = Z_∞/B_∞` is the
cokernel of `Z_∞ ∩ B_∞ ⊆ Z_∞` (which is `B_∞ ⊆ Z_∞`), for a greatest lower bound `Z_∞` of the
`Z_r` and a least upper bound `B_∞` of the `B_r`, when these exist.
-/

universe u v

namespace CategoryTheory

open Limits

/-- Page induction (blueprint: lem-sp-page-induction). If a morphism `φ : E ⟶ E'` of
spectral sequences is an isomorphism on `E_2` in every bidegree, then it is an isomorphism on
every page `E_r`, `2 ≤ r`; and if the limiting cycles and boundaries of `E` and `E'` exist,
`φ_2` restricts to `u : Z_∞ → Z'_∞` and induces an isomorphism `ψ : E_∞ ≅ E'_∞`.

Proof: (1) By `def-sp-spectral-sequence`, each `φ_r` is a chain map and `φ_{r+1}` is the map
induced on homology under the identifications `H(E_r) ≅ E_{r+1}`. (2) `φ_2` is an isomorphism;
if `φ_r` is one, its commutation with `d_r` identifies kernels and images of the differentials,
so it induces an isomorphism on homology, and `φ_{r+1}` is an isomorphism; induct on `r`.
(3) By induction on `r`, the isomorphism `φ_2` maps `Z_r` onto `Z'_r` and `B_r` onto `B'_r`
and the induced map on `Z_r/B_r` is `φ_r`: for `r = 2` this is clear, and in the step
`φ_r` maps `ker d_r`, `im d_r` onto `ker d'_r`, `im d'_r`, so `φ_2` maps their inverse images
`Z_{r+1}`, `B_{r+1}` onto `Z'_{r+1}`, `B'_{r+1}`, inducing `φ_{r+1}` by (1). An isomorphism
carries greatest lower bounds and least upper bounds of subobjects to those of the images, so
`φ_2(Z_∞) = Z'_∞`, `φ_2(B_∞) = B'_∞`, and `φ_2` induces `E_∞ = Z_∞/B_∞ ≅ Z'_∞/B'_∞ = E'_∞`. -/
theorem spectralSequence_page_induction
    {C : Type u} [Category.{v} C] [Abelian C]
    {c : ℤ → ComplexShape (ℤ × ℤ)}
    (E E' : SpectralSequence C c 2) (φ : E ⟶ E')
    (h₂ : ∀ (p q : ℤ), IsIso ((φ.hom 2 le_rfl).f ⟨p, q⟩))
    -- the cycle/boundary recursion of `def-sp-convergence` for `E`
    (Z B : ∀ (_ : ℤ) (p q : ℤ), Subobject ((E.page 2 le_rfl).X ⟨p, q⟩))
    (π : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ), (Z r p q : C) ⟶ (E.page r hr).X ⟨p, q⟩)
    (hZ₂ : ∀ p q : ℤ, Z 2 p q = ⊤) (hB₂ : ∀ p q : ℤ, B 2 p q = ⊥)
    (hπ₂ : ∀ p q : ℤ, π 2 le_rfl p q = (Z 2 p q).arrow)
    (hZ : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ), Z (r + 1) p q =
      (Subobject.«exists» (Z r p q).arrow).obj
        ((Subobject.pullback (π r hr p q)).obj (kernelSubobject ((E.page r hr).dFrom ⟨p, q⟩))))
    (hB : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ), B (r + 1) p q =
      (Subobject.«exists» (Z r p q).arrow).obj
        ((Subobject.pullback (π r hr p q)).obj (imageSubobject ((E.page r hr).dTo ⟨p, q⟩))))
    (ι : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ), (Z (r + 1) p q : C) ⟶ (Z r p q : C))
    (hι : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ),
      ι r hr p q ≫ (Z r p q).arrow = (Z (r + 1) p q).arrow)
    (κ : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ), (Z (r + 1) p q : C) ⟶ (E.page r hr).cycles ⟨p, q⟩)
    (hκ : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ),
      κ r hr p q ≫ (E.page r hr).iCycles ⟨p, q⟩ = ι r hr p q ≫ π r hr p q)
    (hπ : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ), π (r + 1) (by omega) p q =
      κ r hr p q ≫ (E.page r hr).homologyπ ⟨p, q⟩ ≫ (E.iso r (r + 1) ⟨p, q⟩ rfl hr).hom)
    -- the same recursion for `E'`
    (Z' B' : ∀ (_ : ℤ) (p q : ℤ), Subobject ((E'.page 2 le_rfl).X ⟨p, q⟩))
    (π' : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ), (Z' r p q : C) ⟶ (E'.page r hr).X ⟨p, q⟩)
    (hZ₂' : ∀ p q : ℤ, Z' 2 p q = ⊤) (hB₂' : ∀ p q : ℤ, B' 2 p q = ⊥)
    (hπ₂' : ∀ p q : ℤ, π' 2 le_rfl p q = (Z' 2 p q).arrow)
    (hZ' : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ), Z' (r + 1) p q =
      (Subobject.«exists» (Z' r p q).arrow).obj
        ((Subobject.pullback (π' r hr p q)).obj (kernelSubobject ((E'.page r hr).dFrom ⟨p, q⟩))))
    (hB' : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ), B' (r + 1) p q =
      (Subobject.«exists» (Z' r p q).arrow).obj
        ((Subobject.pullback (π' r hr p q)).obj (imageSubobject ((E'.page r hr).dTo ⟨p, q⟩))))
    (ι' : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ), (Z' (r + 1) p q : C) ⟶ (Z' r p q : C))
    (hι' : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ),
      ι' r hr p q ≫ (Z' r p q).arrow = (Z' (r + 1) p q).arrow)
    (κ' : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ), (Z' (r + 1) p q : C) ⟶ (E'.page r hr).cycles ⟨p, q⟩)
    (hκ' : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ),
      κ' r hr p q ≫ (E'.page r hr).iCycles ⟨p, q⟩ = ι' r hr p q ≫ π' r hr p q)
    (hπ' : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ), π' (r + 1) (by omega) p q =
      κ' r hr p q ≫ (E'.page r hr).homologyπ ⟨p, q⟩ ≫ (E'.iso r (r + 1) ⟨p, q⟩ rfl hr).hom)
    -- existence of the limiting cycles and boundaries of `E` and `E'`
    (Zinf Binf : ∀ p q : ℤ, Subobject ((E.page 2 le_rfl).X ⟨p, q⟩))
    (hZinf : ∀ p q : ℤ, IsGLB {S | ∃ r : ℤ, 2 ≤ r ∧ S = Z r p q} (Zinf p q))
    (hBinf : ∀ p q : ℤ, IsLUB {S | ∃ r : ℤ, 2 ≤ r ∧ S = B r p q} (Binf p q))
    (Zinf' Binf' : ∀ p q : ℤ, Subobject ((E'.page 2 le_rfl).X ⟨p, q⟩))
    (hZinf' : ∀ p q : ℤ, IsGLB {S | ∃ r : ℤ, 2 ≤ r ∧ S = Z' r p q} (Zinf' p q))
    (hBinf' : ∀ p q : ℤ, IsLUB {S | ∃ r : ℤ, 2 ≤ r ∧ S = B' r p q} (Binf' p q)) :
    (∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ), IsIso ((φ.hom r hr).f ⟨p, q⟩)) ∧
      ∀ p q : ℤ, ∃ (u : (Zinf p q : C) ⟶ (Zinf' p q : C))
        (ψ : cokernel ((Subobject.pullback (Zinf p q).arrow).obj (Binf p q)).arrow ⟶
          cokernel ((Subobject.pullback (Zinf' p q).arrow).obj (Binf' p q)).arrow),
        u ≫ (Zinf' p q).arrow = (Zinf p q).arrow ≫ (φ.hom 2 le_rfl).f ⟨p, q⟩ ∧
        cokernel.π _ ≫ ψ = u ≫ cokernel.π _ ∧ IsIso ψ := by
  sorry

end CategoryTheory

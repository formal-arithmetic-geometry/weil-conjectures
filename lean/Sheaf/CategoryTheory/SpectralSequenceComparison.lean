/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Sheaf.CategoryTheory.Filtration
public import Sheaf.CategoryTheory.FiniteFiltrationInduction

/-!
# Uniformly bounded spectral-sequence comparison

Source: Stacks Project, Etale Cohomology, Lemma 0EZM, finite-term comparison in its proof
(blueprint: lem-weil-pbc-complex-spectral-sequence-comparison).

The spectral sequences are Mathlib's `SpectralSequence` (node `def-sp-spectral-sequence`)
starting at page `1`, with the node's indexing: `E_r^{p,q}` is `(E.page r).X ⟨p, q⟩` and
`d_r : E_r^{p,q} → E_r^{p-r+1,q+r}`, i.e. the complex shape `ComplexShape.up' ⟨1 - r, r⟩`.
Morphisms of spectral sequences are morphisms in Mathlib's category of spectral sequences.
-/

@[expose] public section

universe u

namespace CategoryTheory

open Limits

/-- The finite-term comparison of uniformly bounded spectral sequences.

The index set is the directed set `I`; the transition morphisms `u_{i'i}` of spectral sequences
are the functor `E`, the compatible morphisms `v_i : E_i → E'` are `v` with `hv`. The abutments
`A_i^n` are `A n` (transition maps `a_{i'i}^n = (A n).map`, filtered by `a`), with
filtrations `F n i`; the target abutment `B n` carries `G n`; `b n i` are filtered
homomorphisms with `b_{i'}^n a_{i'i}^n = b_i^n` (`hb`). `N p q` is the page at which, by
(iii), all pages have stabilized in bidegree `(p, q)` (`hstable`, `hstable'`: the differentials
into and out of `(p, q)` vanish from page `N p q` on), so `E_∞^{p,q}` is displayed as
`E_{N p q}^{p,q}`; `conv`, `conv'` are the convergence isomorphisms
`E_∞^{p,q} ≅ gr^q A^{p+q}`, commuting with the morphisms induced by `u`, `v` and by `a`, `b`
on graded pieces (`hconv`, `hconv'`). (i) is `hpage`, (ii) is `hvanish`, `hvanish'`, (iv) is
`hfil`, `hfil'`.

Proof: filtered-colimit exactness in abelian groups identifies the colimit of each page's
kernels and images with the kernel and image of the colimit differential, so induction on pages
propagates the page-one isomorphism to every page. The vanishing region (ii) gives the
stabilization page `max (p + 1) (q - a) + 1` independent of `i`, and the compatible convergence
isomorphisms identify `colim_i gr^q A_i^{p+q}` with `gr^q A^{p+q}`. Finally, descending
induction through the finite filtration range `a ≤ q ≤ n` uses the short exact sequences of
successive filtration steps and the five lemma, starting above `n` where the steps vanish and
ending at `a` where the filtration is the whole abutment.
(blueprint: lem-weil-pbc-complex-spectral-sequence-comparison) -/
theorem complex_spectral_sequence_comparison
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (E : I ⥤ SpectralSequence AddCommGrpCat.{u}
      (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1)
    (E' : SpectralSequence AddCommGrpCat.{u}
      (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1)
    (v : ∀ i : I, E.obj i ⟶ E')
    (hv : ∀ {i j : I} (f : i ⟶ j), E.map f ≫ v j = v i)
    (A : ℤ → I ⥤ AddCommGrpCat.{u})
    (F : ∀ (n : ℤ) (i : I), DecreasingFiltration ((A n).obj i))
    (B : ℤ → AddCommGrpCat.{u}) (G : ∀ n : ℤ, DecreasingFiltration (B n))
    (a : ∀ (n : ℤ) {i j : I} (_ : i ⟶ j),
      (⟨(A n).obj i, F n i⟩ : FilteredObject AddCommGrpCat.{u}) ⟶ ⟨(A n).obj j, F n j⟩)
    (ha : ∀ (n : ℤ) {i j : I} (f : i ⟶ j), (a n f).hom = (A n).map f)
    (b : ∀ (n : ℤ) (i : I),
      (⟨(A n).obj i, F n i⟩ : FilteredObject AddCommGrpCat.{u}) ⟶ ⟨B n, G n⟩)
    (hb : ∀ (n : ℤ) {i j : I} (f : i ⟶ j), (A n).map f ≫ (b n j).hom = (b n i).hom)
    (a₀ : ℤ)
    (N : ℤ → ℤ → ℤ) (hN : ∀ p q : ℤ, 1 ≤ N p q)
    (hstable : ∀ (i : I) (p q r : ℤ) (hr : N p q ≤ r),
      ((E.obj i).page r ((hN p q).trans hr)).d ⟨p, q⟩ ⟨p + (1 - r), q + r⟩ = 0 ∧
      ((E.obj i).page r ((hN p q).trans hr)).d ⟨p - (1 - r), q - r⟩ ⟨p, q⟩ = 0)
    (hstable' : ∀ (p q r : ℤ) (hr : N p q ≤ r),
      (E'.page r ((hN p q).trans hr)).d ⟨p, q⟩ ⟨p + (1 - r), q + r⟩ = 0 ∧
      (E'.page r ((hN p q).trans hr)).d ⟨p - (1 - r), q - r⟩ ⟨p, q⟩ = 0)
    (conv : ∀ (i : I) (p q : ℤ),
      ((E.obj i).page (N p q) (hN p q)).X ⟨p, q⟩ ≅ (F (p + q) i).gradedPiece q)
    (conv' : ∀ p q : ℤ, (E'.page (N p q) (hN p q)).X ⟨p, q⟩ ≅ (G (p + q)).gradedPiece q)
    (hconv : ∀ {i j : I} (f : i ⟶ j) (p q : ℤ),
      ((E.map f).hom (N p q) (hN p q)).f ⟨p, q⟩ ≫ (conv j p q).hom =
        (conv i p q).hom ≫ FilteredObject.gradedMap (a (p + q) f) q)
    (hconv' : ∀ (i : I) (p q : ℤ),
      ((v i).hom (N p q) (hN p q)).f ⟨p, q⟩ ≫ (conv' p q).hom =
        (conv i p q).hom ≫ FilteredObject.gradedMap (b (p + q) i) q)
    (hpage : ∀ (p q : ℤ)
      (φ : colimit (E ⋙ SpectralSequence.pageFunctor AddCommGrpCat.{u}
        (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1 1 ⋙
        HomologicalComplex.eval _ _ ⟨p, q⟩) ⟶ (E'.page 1).X ⟨p, q⟩),
      (∀ i : I, colimit.ι _ i ≫ φ = ((v i).hom 1).f ⟨p, q⟩) → IsIso φ)
    (hvanish : ∀ (i : I) (p q : ℤ), p < 0 ∨ q < a₀ →
      IsZero (((E.obj i).page 1).X ⟨p, q⟩))
    (hvanish' : ∀ p q : ℤ, p < 0 ∨ q < a₀ → IsZero ((E'.page 1).X ⟨p, q⟩))
    (hfil : ∀ (n : ℤ) (i : I) (q : ℤ),
      (q ≤ a₀ → (F n i).step q = ⊤) ∧ (n < q → (F n i).step q = ⊥))
    (hfil' : ∀ n q : ℤ, (q ≤ a₀ → (G n).step q = ⊤) ∧ (n < q → (G n).step q = ⊥)) :
    ∀ (n : ℤ) (φ : colimit (A n) ⟶ B n),
      (∀ i : I, colimit.ι (A n) i ≫ φ = (b n i).hom) → IsIso φ := by
  sorry

end CategoryTheory

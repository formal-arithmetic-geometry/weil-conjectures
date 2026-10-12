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
import Sheaf.CategoryTheory.SpectralSequenceFinitePageComparison
import Sheaf.CategoryTheory.FiniteFilteredColimitComparison

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

-- The explicit convergence pages make the stabilization and vanishing assumptions redundant
-- in this proof. Keep the original signature, including all its hypothesis names.
set_option linter.unusedVariables false in
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

Proof: apply finite-page comparison to the page `N p q`. Construct its comparison
cocone from `v` and `hv`. Composing its colimit descent with `conv' p q` gives an
isomorphism to the target graded piece. The two convergence compatibility equations
show that `conv i p q` identifies the page diagram with the source graded diagram,
and that this isomorphism is induced by `b` on graded pieces. For fixed `n`, take
`p = n - q` for each `q` and cancel `n - q + q = n`. The finite filtered-colimit
comparison, with common lower bound `a₀` and upper bound `n`, then gives the claim.
No additional stabilization argument is needed: the displayed finite pages and their
convergence isomorphisms are already hypotheses of this statement.
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
  have graded : ∀ p q : ℤ, ∃ (Q : I ⥤ AddCommGrpCat.{u})
      (e : ∀ i : I, Q.obj i ≅ (F (p + q) i).gradedPiece q),
      (∀ {i j : I} (f : i ⟶ j),
        Q.map f ≫ (e j).hom = (e i).hom ≫
          FilteredObject.gradedMap (a (p + q) f) q) ∧
      ∃ ψ : colimit Q ⟶ (G (p + q)).gradedPiece q,
        (∀ i : I, colimit.ι Q i ≫ ψ = (e i).hom ≫
          FilteredObject.gradedMap (b (p + q) i) q) ∧ IsIso ψ := by
    intro p q
    let Q := E ⋙ SpectralSequence.pageFunctor AddCommGrpCat.{u}
      (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1 (N p q) (hN p q) ⋙
      HomologicalComplex.eval _ _ ⟨p, q⟩
    let c : Cocone Q :=
      { pt := (E'.page (N p q) (hN p q)).X ⟨p, q⟩
        ι :=
          { app := fun i ↦ ((v i).hom (N p q) (hN p q)).f ⟨p, q⟩
            naturality := by
              intro i j f
              have h := congrArg
                (fun w ↦ (w.hom (N p q) (hN p q)).f ⟨p, q⟩) (hv f)
              simpa [Q] using h } }
    let θ : colimit Q ⟶ c.pt := colimit.desc Q c
    have hθ : ∀ i : I, colimit.ι Q i ≫ θ =
        ((v i).hom (N p q) (hN p q)).f ⟨p, q⟩ := by
      intro i
      exact colimit.ι_desc c i
    have : IsIso θ := spectral_sequence_finite_page_comparison
      E E' v hv hpage (N p q) (hN p q) p q θ hθ
    refine ⟨Q, fun i ↦ conv i p q, ?_, θ ≫ (conv' p q).hom, ?_, ?_⟩
    · intro i j f
      exact hconv f p q
    · intro i
      rw [← Category.assoc, hθ]
      exact hconv' i p q
    · infer_instance
  intro n φ hφ
  apply finite_filtered_colimit_comparison (A n) (F n) (B n) (G n)
    (a n) (ha n) (b n) (hb n) a₀ n (hfil n) (hfil' n) _ φ hφ
  intro q
  have H := graded (n - q) q
  have hn : n - q + q = n := by omega
  rw [hn] at H
  exact H

end CategoryTheory

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.HypercoverDescent
public import WeilConjectures.AlgebraicGeometry.Sites.QcqsHypercoverRefinement

/-!
# Finite hypercover descent

Let `X = lim Dᵢ` be a cofiltered limit of quasi-compact quasi-separated schemes with affine
transition maps. This file collects the statement of blueprint
`lemma-weil-pbc-finite-hypercover-descent` in one theorem
(`AlgebraicGeometry.TruncatedDescent.exists_and_exists_hom_and_exists_eq_and_isHypercover`):
truncated semi-simplicial objects of the small étale site of `X` with qcqs terms, morphisms into
base changes and equalities of morphisms descend to a finite stage, and every étale hypercover of
`X` is refined by a qcqs hypercover whose `N`-skeleton is the base change of an `N`-truncated
object over some `Dₖ` whose coskeletal extension is a hypercover at all late enough stages.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {I : Type u} [SmallCategory I] [IsCofiltered I] {D : I ⥤ Scheme.{u}} {c : Cone D}
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]

open SemiSimplicialObject

/-- **Finite hypercover descent** (blueprint `lemma-weil-pbc-finite-hypercover-descent`). Let
`X = lim Dᵢ` be a cofiltered limit of quasi-compact quasi-separated schemes with affine
transition maps.
1. (*objects*) the truncation in degrees `≤ N` of a semi-simplicial object of the small étale
   site of `X` with qcqs terms is the base change of an `N`-truncated one at some stage `Dₖ`;
2. (*morphisms*) a morphism into a base change from `Dₖ` descends to a later stage;
3. (*equalities*) morphisms which agree over `X` agree at a later stage;
4. (*hypercovers*) every étale hypercover `U` of `X` is refined by a qcqs hypercover
   `V ⟶ U` (`Scheme.exists_isQcqsHypercover_hom`), and for every `N` the `N`-skeleton of `V` is
   the base change of an `N`-truncated object `T` over some `Dₖ` (`toCosk` is an isomorphism in
   degrees `≤ N`), and at every late enough stage the coskeletal extension of `T` is a
   hypercover. -/
theorem TruncatedDescent.exists_and_exists_hom_and_exists_eq_and_isHypercover (hc : IsLimit c) :
    (∀ (U : SemiSimplicialObject c.pt.Etale), (∀ n, Scheme.Etale.qcqs _ (U.obj n)) →
      ∀ N : ℕ, ∃ k : I, Nonempty (TruncatedDescent c U N k)) ∧
    (∀ {U : SemiSimplicialObject c.pt.Etale} {N : ℕ} {k : I} (d : TruncatedDescent c U N k)
      (W : SemiSimplicialObject (D.obj k).Etale) (f : U ⟶ W.baseChange (c.π.app k)),
      ∃ (k' : I) (g : k' ⟶ k), Nonempty ((d.baseChange g).Hom (W.baseChange (D.map g))
        (Etale.baseChangeLift (c.π.app k) f (c.π.app k') (D.map g) (c.w g)))) ∧
    (∀ {U : SemiSimplicialObject c.pt.Etale} {N : ℕ} {k : I} (d : TruncatedDescent c U N k)
      (W : SemiSimplicialObject (D.obj k).Etale)
      (a b : ∀ (n : ℕ) (h : n ≤ N), d.T.obj n h ⟶ W.obj n),
      (∀ (n : ℕ) (h : n ≤ N), d.m n h ≫ (a n h).left = d.m n h ≫ (b n h).left) →
      ∃ (k' : I) (g : k' ⟶ k), ∀ (n : ℕ) (h : n ≤ N),
        (MorphismProperty.Over.pullback @Etale ⊤ (D.map g)).map (a n h) =
          (MorphismProperty.Over.pullback @Etale ⊤ (D.map g)).map (b n h)) ∧
    (∀ U : SemiSimplicialObject c.pt.Etale, U.IsHypercover c.pt.smallEtaleTopology → ∀ N : ℕ,
      ∃ (V : SemiSimplicialObject c.pt.Etale) (_ : Scheme.IsQcqsHypercover V) (_ : V ⟶ U)
        (k : I) (d : TruncatedDescent c V N k), (∀ (n : ℕ), n ≤ N → IsIso (d.toCosk.app n)) ∧
        ∃ (k₀ : I) (f₀ : k₀ ⟶ k), ∀ (k' : I) (g : k' ⟶ k₀),
          (d.baseChange (g ≫ f₀)).T.cosk.IsHypercover (D.obj k').smallEtaleTopology) :=
  ⟨fun U hU N ↦ exists_truncatedDescent hc U hU N,
    fun d W f ↦ d.exists_hom hc W f,
    fun d W a b hab ↦ d.exists_eq hc W a b hab,
    fun U hU N ↦ by
      have := Scheme.compactSpace_of_isLimit D c hc
      have := quasiSeparatedSpace_pt hc
      obtain ⟨V, hV, ⟨f⟩⟩ := Scheme.exists_isQcqsHypercover_hom hU
      obtain ⟨k, ⟨d⟩⟩ := exists_truncatedDescent hc V
        (fun n ↦ ⟨hV.compactSpace n, hV.quasiSeparatedSpace n⟩) N
      exact ⟨V, hV, f, k, d, fun n hn ↦ d.isIso_toCosk_app n hn,
        d.exists_isHypercover hc hV.isHypercover⟩⟩

/-- **The truncation of a hypercover is the base change of the descended truncation**: for a
descent datum `d` of the `N`-truncation of `U` at the stage `Dₖ`, the terms of `U.truncate N` are
the base changes to the limit `X` of the terms of the descended `N`-truncated object `d.T`. -/
noncomputable def TruncatedDescent.truncateIso {U : SemiSimplicialObject c.pt.Etale} {N : ℕ}
    {k : I} (d : TruncatedDescent c U N k) (n : ℕ) (h : n ≤ N) :
    (U.truncate N).obj n h ≅
      (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app k)).obj (d.T.obj n h) :=
  have := d.isIso_toCosk_app n h
  asIso (d.toCosk.app n) ≪≫
    (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app k)).mapIso (d.T.coskIso n h)

end AlgebraicGeometry

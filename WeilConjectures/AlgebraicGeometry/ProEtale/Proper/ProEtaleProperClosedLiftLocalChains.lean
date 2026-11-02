/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClosedLiftChain.ProEtaleClosedLiftChainCalculus
public import WeilConjectures.AlgebraicGeometry.ProEtale.Proper.ProEtaleProperClosedFibreConnectedness
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover

/-! # Local arrow chains through the proper closed fibre

Source: Step 3 of `lem-sp-proetale-proper-closed-overlap-chains`.
(blueprint: lem-sp-proetale-proper-closed-lift-local-chains).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

namespace ClosedLiftChain

variable {X Z : Scheme.{u}} {z : Z ⟶ X} {P : X.ProEt}

/-- Restrict a factorization through a closed-lift test along an arrow into its source. -/
def Vertex.restrict {V V' : X.ProEt} {f : V ⟶ P} (h : V' ⟶ V) (v : Vertex z f) :
    Vertex z (h ≫ f) :=
  ⟨v.index, h ≫ v.arrow, by rw [Category.assoc, v.comm]⟩

/-- Edges restrict along arrows into their common source. -/
theorem Edge.restrict {V V' : X.ProEt} {f : V ⟶ P} (h : V' ⟶ V) {v w : Vertex z f}
    (e : Edge v w) : Edge (v.restrict h) (w.restrict h) := by
  obtain ⟨U, hU, a, b, c, hab, hac, hbc⟩ := e
  exact ⟨U, hU, h ≫ a, b, c, by simp [Vertex.restrict, hab],
    by simp [Vertex.restrict, hac], hbc⟩

/-- Finite chains restrict along arrows into their common source. -/
theorem reflTransGen_edge_restrict {V V' : X.ProEt} {f : V ⟶ P} (h : V' ⟶ V)
    {v w : Vertex z f} (H : Relation.ReflTransGen Edge v w) :
    Relation.ReflTransGen Edge (v.restrict h) (w.restrict h) :=
  Relation.ReflTransGen.lift (Vertex.restrict h) (fun _ _ e ↦ Edge.restrict h e) _ _ H

/-- Transport a chain along equalities of the underlying arrows. -/
theorem reflTransGen_edge_congr {V : X.ProEt} {f f' : V ⟶ P} (hf : f = f')
    {i j : ClosedLiftArrowIndex z P} {x x' : V ⟶ i.val.1} {y y' : V ⟶ j.val.1}
    {hx : x ≫ i.val.2 = f} {hy : y ≫ j.val.2 = f}
    {hx' : x' ≫ i.val.2 = f'} {hy' : y' ≫ j.val.2 = f'} (hxx : x = x') (hyy : y = y')
    (H : Relation.ReflTransGen Edge (⟨i, x, hx⟩ : Vertex z f) ⟨j, y, hy⟩) :
    Relation.ReflTransGen Edge (⟨i, x', hx'⟩ : Vertex z f') ⟨j, y', hy'⟩ := by
  subst hf hxx hyy
  exact H

/-- A map of closed-lift tests over `P`, compatible with the two factorizations,
gives an edge. -/
theorem Edge.of_hom {V : X.ProEt} {f : V ⟶ P} {v w : Vertex z f}
    (g : v.index.val.1 ⟶ w.index.val.1) (hg : g ≫ w.index.val.2 = v.index.val.2)
    (hvw : v.arrow ≫ g = w.arrow) : Edge v w :=
  ⟨v.index.val.1, v.index.property, v.arrow, 𝟙 _, g, by simp, hvw, by simp [hg]⟩

/-- A map of closed-lift tests over `P` in the opposite direction also gives an edge. -/
theorem Edge.of_hom' {V : X.ProEt} {f : V ⟶ P} {v w : Vertex z f}
    (g : w.index.val.1 ⟶ v.index.val.1) (hg : g ≫ v.index.val.2 = w.index.val.2)
    (hwv : w.arrow ≫ g = v.arrow) : Edge v w :=
  ⟨w.index.val.1, w.index.property, w.arrow, g, 𝟙 _, hwv, by simp, by simp [hg]⟩

/-- The two factorizations of an arrow into an overlap `t ×_P s` of closed-lift tests
are joined by a finite chain of edges. -/
def OverlapChain (t s : ClosedLiftArrowIndex z P) {V : X.ProEt}
    (g : V ⟶ pullback t.val.2 s.val.2) : Prop :=
  Relation.ReflTransGen Edge
    (⟨t, g ≫ pullback.fst t.val.2 s.val.2, by simp only [Category.assoc]⟩ :
      Vertex z (g ≫ pullback.fst t.val.2 s.val.2 ≫ t.val.2))
    ⟨s, g ≫ pullback.snd t.val.2 s.val.2, by
      simp only [Category.assoc, pullback.condition]⟩

/-- Overlap chains restrict along arrows into their source. -/
theorem OverlapChain.comp {t s : ClosedLiftArrowIndex z P} {V V' : X.ProEt}
    {g : V ⟶ pullback t.val.2 s.val.2} (h : V' ⟶ V) (H : OverlapChain t s g) :
    OverlapChain t s (h ≫ g) :=
  reflTransGen_edge_congr (by simp only [Category.assoc])
    (by simp only [Category.assoc])
    (by simp only [Category.assoc]) (reflTransGen_edge_restrict h H)

/-- If overlap chains exist on a Zariski neighbourhood of every point of every affine
weakly contractible object over the overlap, then they exist on a covering family of the
overlap.

Proof: cover the overlap by affine weakly contractible objects
(`ProEt.exists_affine_weaklyContractible_covering_family`). Cover each of them by the given
Zariski neighbourhoods of all of its points; this is a Zariski, hence pro-étale, covering.
Compose the two coverings. -/
theorem exists_cover_overlapChain_of_forall_nhds (t s : ClosedLiftArrowIndex z P)
    (hloc : ∀ (V : X.ProEt) [IsAffine V.left],
      (∀ (F G : Sheaf (ProEt.topology X) (Type (u + 1))) (e : F ⟶ G),
        Epi e → Function.Surjective (e.hom.app (op V))) →
      ∀ (g : V ⟶ pullback t.val.2 s.val.2) (x : V.left),
        ∃ O : V.left.Opens, x ∈ O ∧
          OverlapChain t s (ProEt.ofOpenImmersionHom V O.ι ≫ g)) :
    ∃ (κ : Type (u + 1)) (V : κ → X.ProEt) (a : ∀ j, V j ⟶ pullback t.val.2 s.val.2),
      Presieve.ofArrows V a ∈ ProEt.precoverage X _ ∧ ∀ j, OverlapChain t s (a j) := by
  obtain ⟨I, V, f, hcov, haff, hw⟩ :=
    ProEt.exists_affine_weaklyContractible_covering_family X (pullback t.val.2 s.val.2)
  have hloc' (i : I) (x : (V i).left) := @hloc (V i) (haff i) (hw i) (f i) x
  choose O hxO hO using hloc'
  refine ⟨Σ i : I, (V i).left, fun q ↦ ProEt.ofOpenImmersion (V q.1) (O q.1 q.2).ι,
    fun q ↦ ProEt.ofOpenImmersionHom (V q.1) (O q.1 q.2).ι ≫ f q.1, ?_, fun q ↦ hO q.1 q.2⟩
  refine Precoverage.comp_mem_coverings f hcov
    (fun i x ↦ ProEt.ofOpenImmersionHom (V i) (O i x).ι) fun i ↦ ?_
  rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
  exact zariskiPrecoverage_le_proetalePrecoverage _
    ((Scheme.ofArrows_mem_precoverage_iff _).mpr
      ⟨fun x ↦ ⟨x, show x ∈ Set.range (O i x).ι by rw [Opens.range_ι]; exact hxO i x⟩,
        fun x ↦ inferInstanceAs (IsOpenImmersion (O i x).ι)⟩)

end ClosedLiftChain

/-- Local form of `proper_closed_lift_local_chains`: over an affine weakly contractible
object `V` of the pro-étale site mapping to the overlap of two closed-lift tests, the two
factorizations are joined by a finite chain on a Zariski neighbourhood of every point.

This is the geometric core of Step 3 of `lem-sp-proetale-proper-closed-overlap-chains`.
It is a consequence of `proper_closed_lift_local_chains` (pull a covering family back
to `V` and split it on a clopen partition by `ProEt.exists_clopen_partition`).

Proof sketch. Fix `x`, with images `u` in the test `U = t.val.1`, `u'` in `U' = s.val.1`
and `y` in `P`. Closed-lift tests are henselian along their closed fibre (the argument of
`proper_test_closed_fibre_connectedness`), and their local rings at closed points are
strictly henselian. Hence `u` and `u'` determine geometric specializations of `y` into
the closed fibre of `P`, and every edge preserves the class of such a specialization
modulo specialization inside the closed fibre. The two classes agree: by Stein
connectedness over the strictly henselian local ring of `W` at the closed point below
`y`, the closed fibre of the normalization of the closure of `y` in every finite separable
extension of its residue field is connected. The Zariski connectedness `hconnected` of
the closure of `y` itself does not suffice for this step: one point of the closed fibre
can carry several branches of that closure, and a chain of Zariski neighbourhoods does
not keep track of the branch. Along a chain of branch-adjacent points choose affine
neighbourhoods, refine them by henselizations of affine weakly contractible covers
(these are closed-lift tests), and lift the arrows from `V` through the resulting finite
diagram. The covers of `V` needed for these lifts split on a clopen neighbourhood of `x`
because `V` is weakly contractible. -/
theorem proper_closed_lift_local_chains_nhds
    {B D E : Scheme.{u}} (p : B ⟶ D) (i : E ⟶ D)
    [IsProper p] [IsOpenImmersion i] [QuasiCompact i]
    (W : D.ProEt) [IsAffine W.left]
    (hW : ∀ (F G : Sheaf (ProEt.topology D) (Type (u + 1))) (e : F ⟶ G),
      Epi e → Function.Surjective (e.hom.app (op W)))
    (hconnected :
      let z := (pullback.fst p i).closedComplement
      let P := (proEtaleBaseChange p).obj W
      ∀ C : Set P.left, IsClosed C → IsIrreducible C →
        IsConnected (C ∩ P.hom ⁻¹' Set.range z)) :
    let z := (pullback.fst p i).closedComplement
    let P := (proEtaleBaseChange p).obj W
    ∀ (t s : ClosedLiftArrowIndex z P) (V : B.ProEt) [IsAffine V.left],
      (∀ (F G : Sheaf (ProEt.topology B) (Type (u + 1))) (e : F ⟶ G),
        Epi e → Function.Surjective (e.hom.app (op V))) →
      ∀ (g : V ⟶ pullback t.val.2 s.val.2) (x : V.left),
        ∃ O : V.left.Opens, x ∈ O ∧
          ClosedLiftChain.OverlapChain t s (ProEt.ofOpenImmersionHom V O.ι ≫ g) := by
  sorry

/-- Two arrows from closed-lift tests into the proper pullback are locally joined
by a finite chain whose edges extend together to a closed-lift test. This assertion
is about site objects and their arrows, independently of the coefficient ring.

Source: Step 3 of `lem-sp-proetale-proper-closed-overlap-chains`.
(blueprint: lem-sp-proetale-proper-closed-lift-local-chains).

Proof: cover the overlap by affine weakly contractible objects. On each of them,
`proper_closed_lift_local_chains_nhds` gives chains on a Zariski neighbourhood of every
point. These neighbourhoods form Zariski covers; composing them with the first cover
gives the covering family (`ClosedLiftChain.exists_cover_overlapChain_of_forall_nhds`).
No cover of the original overlap by ClosedLiftTests is asserted. Empty overlaps use the
empty covering family and need no endpoint choices. -/
theorem proper_closed_lift_local_chains
    {B D E : Scheme.{u}} (p : B ⟶ D) (i : E ⟶ D)
    [IsProper p] [IsOpenImmersion i] [QuasiCompact i]
    (W : D.ProEt) [IsAffine W.left]
    (hW : ∀ (F G : Sheaf (ProEt.topology D) (Type (u + 1))) (e : F ⟶ G),
      Epi e → Function.Surjective (e.hom.app (op W)))
    (hconnected :
      let z := (pullback.fst p i).closedComplement
      let P := (proEtaleBaseChange p).obj W
      ∀ C : Set P.left, IsClosed C → IsIrreducible C →
        IsConnected (C ∩ P.hom ⁻¹' Set.range z)) :
    let z := (pullback.fst p i).closedComplement
    let P := (proEtaleBaseChange p).obj W
    ∀ t s : ClosedLiftArrowIndex z P,
      ∃ (κ : Type (u + 1)) (V : κ → B.ProEt)
        (a : ∀ j, V j ⟶ pullback t.val.2 s.val.2),
        Presieve.ofArrows V a ∈ ProEt.precoverage B _ ∧
        ∀ j, Relation.ReflTransGen ClosedLiftChain.Edge
          (⟨t, a j ≫ pullback.fst t.val.2 s.val.2, by
            simp only [Category.assoc]⟩ :
            ClosedLiftChain.Vertex z (a j ≫ pullback.fst t.val.2 s.val.2 ≫ t.val.2))
          ⟨s, a j ≫ pullback.snd t.val.2 s.val.2, by
            simp only [Category.assoc, pullback.condition]⟩ := by
  intro z P t s
  exact ClosedLiftChain.exists_cover_overlapChain_of_forall_nhds t s
    fun V _ hV g x ↦ proper_closed_lift_local_chains_nhds p i W hW hconnected t s V hV g x

end AlgebraicGeometry.Scheme

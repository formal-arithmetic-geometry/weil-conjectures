/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.AlgebraicGeometry.OpenCoverTensorPullbackComparison
public import Sheaf.AlgebraicGeometry.LocalOverlapTransitions
public import Sheaf.AlgebraicGeometry.LocalMapPairCompatibility
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Sheaf.AlgebraicGeometry.FinitePresentationTestMapZeroEventually
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent

/-! # Eventual compatibility for one pair of local maps

Source: Stacks Project, Tag 01ZR (3), first proof by Zariski gluing.
(blueprint: lem-pc-fp-local-map-pair-eventually). -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

attribute [local irreducible] Scheme.Modules.tensorPullback
  Scheme.Modules.openCoverTensorPullbackComparison

/-- One pair of recovered local maps satisfies the overlap equation at every
sufficiently late stage. No finiteness assumption on the cover is required.
Source: Stacks Project, Tag 01ZR (3), first proof by Zariski gluing.
(blueprint: lem-pc-fp-local-map-pair-eventually).

Proof: Let W be the fibre product of the two affine cover members over X_k.
Quasi-separatedness makes W quasi-compact. On W subtract the two composites
in the descent-morphism compatibility square. The source and target are ordinary
pullbacks of F and G, hence finitely presented and quasi-coherent. On the inverse
limit, conjugation by the canonical restriction comparisons identifies this
square with the compatibility square for the restrictions of δ. That square
commutes by functoriality. Thus the defect has zero limit pullback. Apply
finitePresentation_test_map_zero_eventually to W and this defect. At any later
stage the defect still vanishes, because pullback preserves zero. Every test
scheme mapping to the two later cover members maps to W and factors through
its base change at the vanishing stage. Pull back the zero equation along this
factorization and conjugate by the ordinary pullback composition comparisons
and tensor restriction comparisons. Naturality gives exactly the equation below.
Empty overlaps have a unique map, zero modules cause no exception, and the pair
may have equal indices. The proof does not require a finite cover or a common
bound for multiple pairs. -/
theorem finitePresentation_local_map_pair_eventually
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [QuasiSeparated f]
    (k : I) (hik : i ≤ k)
    (F G : (pullback f (Spec.map (R.map (homOfLE hik)))).Modules)
    (hF : F.IsFinitePresentation) (hFq : F.IsQuasicoherent)
    (hG : G.IsFinitePresentation) (hGq : G.IsQuasicoherent)
    (U₀ : (pullback f (Spec.map (R.map (homOfLE hik)))).OpenCover.{u})
    (a b : U₀.I₀) [IsAffine (U₀.X a)] [IsAffine (U₀.X b)]
    (δ : (Scheme.Modules.tensorPullback (overlapLimitMap R c f hik)).obj F ⟶
      (Scheme.Modules.tensorPullback (overlapLimitMap R c f hik)).obj G)
    (r₀ : ∀ x, (Scheme.Modules.pullback (U₀.f x)).obj F ⟶
      (Scheme.Modules.pullback (U₀.f x)).obj G)
    (hr : ∀ x,
      let p := overlapLimitMap R c f hik
      let e := Scheme.Modules.openCoverTensorPullbackComparison p U₀ x
      e.inv.app F ≫ (Scheme.Modules.pullback (U₀.pullbackHom p x)).map (r₀ x) ≫
        e.hom.app G = (Scheme.Modules.pullback ((U₀.pullback₁ p).f x)).map δ) :
    ∃ (l : I) (hkl : k ≤ l), ∀ (m : I) (hkm : k ≤ m), l ≤ m →
      let q := baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE hik))))
        (T' := Over.mk (Spec.map (R.map (homOfLE (hik.trans hkm)))))
        (Over.homMk (Spec.map (R.map (homOfLE hkm)))
          (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
      let U := U₀.pullback₁ q
      let Q := modulesPseudofunctor.toDescentData U.f
      let C := Scheme.Modules.tensorPullback q
      let r : ∀ x, (Q.obj (C.obj F)).obj x ⟶ (Q.obj (C.obj G)).obj x := fun x ↦
        let e := Scheme.Modules.openCoverTensorPullbackComparison q U₀ x
        e.inv.app F ≫ (Scheme.Modules.pullback (U₀.pullbackHom q x)).map (r₀ x) ≫
          e.hom.app G
      Pseudofunctor.DescentData.PairCompatibility r a b := by sorry

end AlgebraicGeometry

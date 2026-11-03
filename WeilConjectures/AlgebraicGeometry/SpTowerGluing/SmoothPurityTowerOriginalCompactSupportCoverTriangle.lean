/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerOriginalCoverMaps

/- Source anchor for this transported binary-gluing step:
`det-sp-tower-gluing`, Gluing and Uniformity, in the current blueprint at
`part-duality-trace-formula/sec-smooth-purity/sec-sp-grp-ladic-summary/`
`sec-towers-and-integral-coefficients/sk-prop-sp-tower-geometric/`
`sk-prop-sp-tower-geometric-gluing.proof.md`.
-/

/-! # Compact-support image of the canonical binary cover triangle

Source: latest smooth-purity blueprint, Local pairs, Gluing and Uniformity.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerGluing

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

/-- The canonical signed cover triangle after compact support, in the original
coefficient-tower category.
Source: latest smooth-purity blueprint, Gluing, compact-support open-cover triangle
(blueprint: lem-sp-tower-original-compact-support-cover-triangle).

Proof. Uniform cohomological bounds for H imply boundedness below in the ordinary
derived tower category: exact level evaluations detect zero ordinary tower modules
on cohomology. Transport H through the section-preserving realization to a bounded-
below sequence-site complex. Use ordinarySequence and its proved kernel
identification. The sum of the open counits is epic, checked on the two covering
opens using their adjunction sections and then by exact level evaluation. Applying
this degreewise gives the short exact sequence of complexes. Its derived triangle
is distinguished. Exact open extension and derived proper direct image preserve it
on bounded-below complexes. Transport this triangle through the target realization. The source
realization unit and counit identify its three vertices with the displayed objects.
The comparison for the second vertex is the canonical finite-biproduct comparison
of the additive compact-support functor. For the first arrow, transpose the defining
nestedCounit through the transported open adjunctions; the realization counits and
spActualRestrictionComp give exactly originalOpenAlpha. The second arrow is the sum
of the transported open counits. Isomorphic distinguished triangles are distinguished,
so retain its transported boundary. This assertion uses neither a target counit K
nor a representing pair; the same sheaf-local argument includes empty and repeated opens. -/
theorem tower_original_compact_support_cover_triangle
    (k : Type u) [Field k]
    (X Y : Over (Spec (CommRingCat.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) (c : Compactification f.left)
    (U V : X.left.Opens) (_cover : U ⊔ V = ⊤)
    (H : SpTowerCalculus.C l E b q X.left) :
    letI := (q.abelian Y.left).hasDerived
    let wU := Limits.pullback.fst U.ι V.ι
    let wV := Limits.pullback.snd U.ι V.ι
    let jW := wU ≫ U.ι
    ∃ delta : (SpTowerCalculus.F l E b o q c).obj H.obj ⟶
        ((SpTowerCalculus.F l E b o q c).obj
          ((SpTowerCalculus.openExtension l E b o q jW).obj
            ((SpTowerCalculus.etalePullback l E b o q jW).obj H.obj)))⟦(1 : ℤ)⟧,
      Triangle.mk
        (biprod.lift
          ((SpTowerCalculus.F l E b o q c).map
            (originalOpenAlpha l E b o q wU U.ι jW rfl H.obj))
          (-((SpTowerCalculus.F l E b o q c).map
            (originalOpenAlpha l E b o q wV V.ι jW
              Limits.pullback.condition.symm H.obj))))
        (biprod.desc
          ((SpTowerCalculus.F l E b o q c).map
            ((towerOpenAdjunction l E b o q U.ι).counit.app H.obj))
          ((SpTowerCalculus.F l E b o q c).map
            ((towerOpenAdjunction l E b o q V.ι).counit.app H.obj))) delta ∈
          distTriang (spDerivedCoefficientTowers l E Y.left (q.abelian Y.left)) := by sorry

end AlgebraicGeometry.ProEtale.SpTowerGluing

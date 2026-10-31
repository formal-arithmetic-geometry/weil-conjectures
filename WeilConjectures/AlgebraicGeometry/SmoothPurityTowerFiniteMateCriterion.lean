/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerMateEvaluationReduction

/-! # Finite mates and normalization of the source

Source: latest blueprint, tower exceptional base change, proof (2).
(blueprint: stage3-sp-finite-mates-normalized-source).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme WeilConjectures Opposite
namespace AlgebraicGeometry.ProEtale.SpExceptionalBaseChange
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

/-- The finite invertibility and source-normalization inputs, without asserting a tower
mate isomorphism or any integral reconstruction.
Source: latest blueprint tower exceptional base change, proof (2).

Proof: at level n use b.ideals n to identify the ell-power coefficient ring with
its cofinal uniformizer-power quotient. Transport the fixed finite coefficient
comparison and its adjunction, preserving the actual unit and counit. The gluing
realization compares the given finite right adjoints with these fixed exceptional
functors. Uniqueness of counit transposes identifies finiteMate with the canonical
smooth exceptional base-change map under those comparisons. The finite smooth
base-change theorem makes it invertible, and full inclusions reflect invertibility.
For normalization, obtain strict Tate towers from the chart gluing data. Apply tower
gamma for f, transported along c.comm, to see that a.right preserves normalized
inputs. Pullback commutes with quotient derived tensor: the canonical scalar/pullback
comparison and input reduction identify every output reduction with a composite of
isomorphisms. This follows from the given Geometry.pullTransitionFormula and the
section-normalized coordinates, and remains valid for nonflat quotient maps.
Equal indices are the scalar unitor, and the argument includes zero objects, empty
schemes and relative dimension zero.
(blueprint: stage3-sp-finite-mates-normalized-source). -/
theorem finite_mates_and_source_normalized
    (k : FiniteFieldDatum.{u}) (_hne : l ≠ k.p)
    (X Y X' Y' : Over (Spec (CommRingCat.of k.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
    [IsSeparated Y'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
    (f : X ⟶ Y) (v : Y' ⟶ Y) (u' : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback u'.left f'.left f.left v.left)
    (d : ℕ) [SmoothOfRelativeDimension d f.left] (c : Compactification f.left)
    (a : SpTowerMate.Data l E b o q sq c)
    (hfinite : ∀ (n : ℕ)
      (K : spFiniteConstructibleTorCategory Y.left (SpTowerShriek.R l E n)),
      IsIso ((SpTowerMate.finiteExchange l E b (sq := sq) (c := c) n).app
        ((a.levels.right n).obj K).obj)) :
    (∀ (n : ℕ) (K : spFiniteConstructibleTorCategory Y.left (SpTowerShriek.R l E n)),
      IsIso (SpTowerMate.finiteMate l E b o q a n K (hfinite n K))) ∧
    ∀ K : SpTowerCalculus.C l E b q Y.left,
      IsSpNormalizedTower l E Y.left (q.abelian Y.left) K.obj →
        IsSpNormalizedTower l E X'.left (q.abelian X'.left)
          (((SpTowerMate.U l E b o q a).obj (a.right.obj K)).obj) := by sorry

end AlgebraicGeometry.ProEtale.SpExceptionalBaseChange

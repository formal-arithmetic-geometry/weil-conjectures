/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientAdjoints.FiniteCoefficientAdjointData
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientAdjoints.EtaleFiniteStageMateClosed
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientAdjoints.EtaleFiniteStageMateLocality

/-! # Invertibility of the ordinary etale finite-stage exceptional mate

Source: the ordinary etale argument of lem-pur-finite-coefficient-adjoint-comparisons,
steps 8--12, and current blueprint reduction-exceptional, Locality and Charts.
(blueprint: lem-pur-etale-finite-stage-mate-invertible).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
attribute [local instance 20000] CommRing.toRing Field.toCommRing DFunLike.toCoeFun
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
namespace AlgebraicGeometry.FiniteCoefficientAdjoints

end AlgebraicGeometry.FiniteCoefficientAdjoints

namespace AlgebraicGeometry.FiniteCoefficientAdjoints

/-- The canonical counit transpose for ordinary etale exceptional inverse image is
invertible on a constructible finite-Tor input, for one actual stage arrow.

Source: parent lem-pur-finite-coefficient-adjoint-comparisons, steps 8--12;
current blueprint reduction-exceptional, Locality and Charts.
(blueprint: lem-pur-etale-finite-stage-mate-invertible).

Proof: stage_ramification identifies both coefficient rings with positive DVR
quotients. On affine-space projections the normalized trace comparison is
etaleAffineProjectionCoefficientMate. For a closed immersion use the complementary
quasi-compact open. Represent the input by a degreewise-injective K-injective complex
and resolve the target coefficient module by an A-flat K-flat complex. Tensor the
injective support sequence after restriction to A. Its middle comparison is identity;
its open comparison is the finite-constant projection isomorphism. Relative finite
torsion cohomological dimension for finite-type maps over k supplies its bound;
no bound on the absolute cohomological dimension of k is used. The resulting
map of distinguished support triangles has invertible first component by two out of
three. Hom from a supported complex to the open direct image is zero in every shift;
the exact Hom sequence therefore identifies this component uniquely with the
counit transpose displayed here. Closed direct image and restriction of scalars
reflect isomorphisms. Factor the morphism on finite affine charts into a closed
immersion followed by an affine-space projection. Adjoint locality, compact-support
composition and mate pasting identify restriction of the displayed mate with the
composite of the two invertible cases. Geometric stalks detect its invertibility.
The inverse compact-support map is comparisonInverse: proper coefficient change
and open tensor balancing prove that its isomorphism branch is used on every input.
Identity arrows, equal levels, empty schemes, quotient maps and ramified embeddings
are covered; no flatness of the coefficient arrow is required. -/
theorem etale_finite_stage_mate_invertible
    (k : Type u) [Field k] (p l : ℕ) [CharP k p] (hk : Finite k ∨ IsAlgClosed k)
    (hp : 0 < p)
    [Fact l.Prime] (hlp : l ≠ p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    {s t : Stage l E} (a : Arrow s t) (c : Compactification f)
    (L : Etale.DerivedCategoryModule s.ring Y)
    (hL : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} s.ring) Y L) :
    letI := finiteTypeNoetherian k X
    letI := finiteTypeNoetherian k Y
    letI := (finiteTypeMorphismProperties k f).1
    letI := (finiteTypeMorphismProperties k f).2.1
    letI := (finiteTypeMorphismProperties k f).2.2
    IsIso ((etaleAdjunction t.ring c).homEquiv _ _
      (Etale.ExceptionalCoefficients.comparisonInverse a.ringMap c
          ((etaleUpper s.ring c).obj L) ≫
        (Etale.scalarExtension a.ringMap Y).map
          ((etaleAdjunction s.ring c).counit.app L))) := by
  let := finiteTypeNoetherian k X
  let := finiteTypeNoetherian k Y
  let := (finiteTypeMorphismProperties k f).1
  let := (finiteTypeMorphismProperties k f).2.1
  let := (finiteTypeMorphismProperties k f).2.2
  exact etale_finite_stage_mate_locality k p l hk hp hlp E a
    (fun g ↦ etale_finite_stage_mate_closed k p l hp hlp E g a) f c L hL

end AlgebraicGeometry.FiniteCoefficientAdjoints

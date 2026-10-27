module

public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Geometrically.Integral

import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
import Sheaf.AlgebraicGeometry.SplitSolvableTorsorDefinitions
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Affine-space trivialization over a split reductive quotient

Source: Brion, On Linearization of Line Bundles (2015), Lemma 2.3, proof, p.118,
and Remark 2.2(v), p.117. The structural and scalar-extension clauses are made explicit.
(blueprint: lem-sfb-split-reductive-affine-space-quotient)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A smooth connected affine algebraic group over an algebraically closed field is,
as a scheme over that field, an affine-space product over a split reductive quotient.
The product is in `Over (Spec (.of k))`, so its underlying scheme is the fibre product.
The last equation identifies the scalar-extended affine coordinate with the pullback of
that of the original isomorphism; together with the first-projection equation this
specifies the scalar extension of the same isomorphism, rather than a new trivialization.

Source: Brion, On Linearization of Line Bundles (2015), Lemma 2.3, proof, p.118,
and Remark 2.2(v), p.117; Milne, Algebraic Groups (2017), Sections 6.45--6.46,
Corollary 16.24 and Proposition 16.55(b), Corollary 16.56.
(blueprint: lem-sfb-split-reductive-affine-space-quotient)

Proof plan, following the seven steps of the DAG node:
1. Choose the unipotent radical U by lem-sfb-unipotent-radical-existence. The identity
   section makes G geometrically connected by
   lem-sbc-connected-rational-point-geometrically-connected. Apply
   lem-sfb-affine-normal-quotient-geometry to construct q : G → H = G/U, with H smooth,
   affine, geometrically connected and of finite type, and its right U-torsor comparison.
2. A smooth connected normal unipotent subgroup V of H has inverse image P in G.
   The quotient geometry gives the exact sequence with kernel U and quotient V.
   By lem-sfb-smooth-unipotent-extension, P is unipotent. Maximality of U gives P = U
   and hence V = 1. Thus H is reductive. Choose a split maximal torus using the
   existence clause of lem-sfb-reductive-borel-pair-structure.
3. The field k is perfect. Apply lem-sfb-perfect-unipotent-additive-series to U.
   Its tails are split series in def-sfb-split-solvable-right-torsors.
4. Construct U_j ≅ affine space by reverse induction on this additive series.
   The terminal term is the trivial group, hence affine zero-space. For each step,
   the quotient is the affine line. Apply lem-sfb-split-unipotent-affine-torsor-section
   over that affine base. Its section and the torsor comparison give
   U_j ≅ affine line × U_(j+1). Adjoin the coordinate to obtain U ≅ affine n-space.
5. Apply the same torsor-section lemma to G → H. If s is a section, the map
   (h,u) ↦ s(h)u is an isomorphism H × U → G. Its inverse, followed on the second
   factor by the affine-space isomorphism of U, gives a. Its first projection is q.
6. The quotient H is connected as a surjective image of G. Its identity section
   makes it geometrically connected by the rational-point lemma. Apply
   lem-trf-smooth-connected-fibre-normal-integrality to obtain integrality after
   every extension. Iterated fibre products give geometric integrality of H_L.
   Smoothness is preserved by lem-pc-proper-base-change(2). Tensoring an affine
   coordinate ring and its finite list of generators proves affineness and finite type.
7. Pull back a and its inverse to every L/k. Pullback preserves the inverse and
   projection equations; the polynomial-algebra base-change identity identifies
   the second factor with affine n-space over L. The displayed affine-coordinate
   equation records this identification. For G = 1 take H = 1 and n = 0.
-/
theorem exists_split_reductive_affine_space_quotient
    {k : Type u} [Field k] [IsAlgClosed k]
    (G : Grp (Over (Spec (.of k))))
    [Smooth G.X.hom] [ConnectedSpace G.X.left]
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom] :
    ∃ (H : Grp (Over (Spec (.of k)))) (q : G ⟶ H) (n : ℕ)
      (a : G.X ≅ H.X ⨯
        (AffineSpace (ULift.{u} (Fin n)) (Spec (.of k))).asOver (Spec (.of k))),
      ReductiveTorusCentralizer.IsReductive H ∧
      (∃ (T : Grp (Over (Spec (.of k)))) (i : T ⟶ H) (r : ℕ),
        ReductiveTorusCentralizer.IsMaximalTorus i ∧
        Nonempty (T ≅ MultiplicativeType.splitTorus k r)) ∧
      a.hom ≫ prod.fst = q.hom.hom ∧
      ∀ (L : Type u) [Field L] [Algebra k L],
        Smooth ((MultiplicativeType.baseChange (K := L)).obj H).X.hom ∧
        IsAffine ((MultiplicativeType.baseChange (K := L)).obj H).X.left ∧
        GeometricallyIntegral ((MultiplicativeType.baseChange (K := L)).obj H).X.hom ∧
        LocallyOfFiniteType ((MultiplicativeType.baseChange (K := L)).obj H).X.hom ∧
        QuasiCompact ((MultiplicativeType.baseChange (K := L)).obj H).X.hom ∧
        ∃ aL : ((MultiplicativeType.baseChange (K := L)).obj G).X ≅
            ((MultiplicativeType.baseChange (K := L)).obj H).X ⨯
              (AffineSpace (ULift.{u} (Fin n)) (Spec (.of L))).asOver (Spec (.of L)),
          aL.hom ≫ prod.fst =
            ((MultiplicativeType.baseChange (K := L)).map q).hom.hom ∧
          (aL.hom ≫ prod.snd).left ≫
              AffineSpace.map (ULift.{u} (Fin n))
                (Spec.map (CommRingCat.ofHom (algebraMap k L))) =
            pullback.fst G.X.hom (Spec.map (CommRingCat.ofHom (algebraMap k L))) ≫
              (a.hom ≫ prod.snd).left := by
  sorry

end AlgebraicGeometry

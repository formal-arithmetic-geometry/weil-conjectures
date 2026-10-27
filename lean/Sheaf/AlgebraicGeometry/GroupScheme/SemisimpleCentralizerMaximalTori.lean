module

public import Sheaf.AlgebraicGeometry.GroupScheme.LieCentralizer
public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
import Sheaf.AlgebraicGeometry.MultiplicativeTypeLargestSubtorus
import Sheaf.AlgebraicGeometry.AffineGroupDualNumberCalculus

/-! # Maximal tori in a semisimple Lie centralizer

Source: Milne, Algebraic Groups (2017), Proposition 17.90, printed p.381
(blueprint: lem-sfb-semisimple-centralizer-maximal-tori).

C and j specify the closed subgroup representing the adjoint stabilizer, through
its exact functor of points. Its neutral component uses the existing open-component
construction. Semisimplicity is diagonalizability of the actual faithful differential.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry.GrpObj

/-- Every maximal k-torus in the neutral component of the stabilizer of a geometrically
semisimple tangent vector is maximal in G. This includes zero and central vectors.
Source: Milne, Proposition 17.90, printed p.381
(blueprint: lem-sfb-semisimple-centralizer-maximal-tori).

Proof:
1. By lem-sfb-semisimple-tangent-stabilizer, C is smooth and its Lie algebra contains X.
The open neutral component K contains the infinitesimal point of X, hence X is tangent to K
(lem-sfb-finite-type-group-identity-subgroup and the open-factorization lemma).
After algebraic closure K remains smooth and connected, and T remains maximal by
lem-sfb-maximal-torus-field-extension and lem-sbc-connected-rational-point-geometrically-connected.
2. Apply lem-sfb-neutral-torus-centralizer-cartan-structure inside K over the closure.
The neutral centralizer of T is a product U times T with U smooth connected unipotent.
The whole-torus invariance of X, via lem-sfb-affine-group-dual-number-calculus,
puts X in the Lie algebra of this neutral centralizer, using open factorization again.
3. Embed U into upper unitriangular matrices by
lem-sfb-geometric-unipotence-unitriangular-embedding. The differential of X in that
representation is both diagonalizable, by lem-sfb-algebraic-lie-additive-jordan,
and strictly upper triangular, by lem-sfb-affine-group-lie-tangent-calculus.
It is zero. Injectivity of the embedding differential and the product decomposition
therefore put X in Lie(T) after algebraic closure.
4. Descend subspace membership along the injective field extension: extend a basis of
Lie(T) to a basis of Lie(G); all complementary coordinates vanish after extension,
so already vanish over k. Use lem-sfb-affine-group-lie-tangent-calculus for base change.
5. Any larger torus S containing T is smooth and connected by
lem-sfb-multiplicative-type-largest-subtorus and is commutative by descent from its split form.
Since X belongs to Lie(T), S fixes X after every algebra extension. Thus S factors
through C, and connectedness factors it through K. Maximality in K forces S = T.
No noncentrality, nonzero-vector, reductivity, or perfectness hypothesis is used. -/
theorem semisimpleCentralizer_maximalTori {k : Type u} [Field k]
    (G : Grp (Over (Spec (.of k)))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom] [Smooth G.X.hom]
    [GeometricallyConnected G.X.hom]
    (n : ℕ) (i : G.X ⟶ GeneralLinearGroup (ULift.{u} (Fin n)) k) [IsMonHom i]
    [IsClosedImmersion i.left] (X : Lie G.X)
    (hX : ∃ (P : Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) (AlgebraicClosure k))
      (d : ULift.{u} (Fin n) → AlgebraicClosure k),
      (↑(P⁻¹) : Matrix _ _ _) *
          (GeneralLinearGroup.RationalHom.differential i X).map
            (algebraMap k (AlgebraicClosure k)) * (↑P : Matrix _ _ _) = Matrix.diagonal d)
    (C : Grp (Over (Spec (.of k)))) [IsAffine C.X.left]
    [LocallyOfFiniteType C.X.hom] [QuasiCompact C.X.hom]
    (j : C ⟶ G) (hC : IsLieCentralizer j X)
    (T : Grp (Over (Spec (.of k))))
    (t : T ⟶ Grp.mk (identityComponent C.X))
    (hT : ReductiveTorusCentralizer.IsMaximalTorus t) :
    ReductiveTorusCentralizer.IsMaximalTorus
      (t ≫ (⟨⟨identityComponentι C.X⟩⟩ : Grp.mk (identityComponent C.X) ⟶ C) ≫ j) := sorry

end AlgebraicGeometry.GrpObj

module

public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective

import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import Sheaf.AlgebraicGeometry.RelativeGroupUnitAxisFactorization
import WeilConjectures.AlgebraicGeometry.TensorPullback
import Sheaf.AlgebraicGeometry.ProjectivePolarizationSectionAlgebra

/-!
# Invariant affine covers for smooth projective torus schemes

Source: Milne, Algebraic Groups (2017), Section 13f, Definition 13.45 and Lemma 13.46,
printed p.272, and the agent-formulated linearization argument in the DAG proof
(blueprint: lem-sfb-smooth-projective-torus-invariant-affine-cover).

Milne's lemma treats linear actions. The DAG supplies the reduction of an arbitrary
split-torus action to that case by linearizing the projective hyperplane line bundle.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

/-- A smooth projective scheme over an algebraically closed field has a finite invariant
 affine open cover for any algebraic action of a finite-rank split torus. The restricted
 actions, including their unit and associativity laws, are part of the conclusion.

Source: Milne, Algebraic Groups (2017), Definition 13.45 and Lemma 13.46, printed p.272,
for the eigen-section chart argument; the following linearization reduction is the DAG's
agent-formulated proof (blueprint: lem-sfb-smooth-projective-torus-invariant-affine-cover).

Proof plan, following the eight steps of the node:
1. For empty Y use the empty family. Otherwise projectivity gives properness,
separatedness, finite type and quasi-compactness (lem-pc-projective-proper,
def-weil-proper-morphism, def-weil-finite-type-morphism). Smoothness gives reducedness
(sbc-lem-smooth-geometrically-reduced).
2. Choose a projective closed embedding j and put L = j*O(1). Pullbacks of coordinate
sections generate this invertible module (def-pc-projective-morphism,
def-pc-projective-space-twist, def-pc-module-pullback, def-sc-invertible-module).
3. The projection T times Y to Y is the trivial split-torus torsor. Its Laurent
coordinates give affineness, finite presentation and separation;
lem-trf-split-lattice-torus-projection gives smoothness, surjectivity and connected
geometric fibres, and lem-pc-smooth-flat gives flatness. This includes rank zero.
4. Apply lem-sfb-split-torus-torsor-line-pullback to a*L to obtain p*M isomorphic to a*L.
Restrict at the identity to identify M with L, using
lem-pc-module-pullback-identity-composition. Normalize the resulting isomorphism
p*L to a*L by its identity restriction.
5. The cocycle defect is a global unit on T times T times Y, equal to one on both
identity axes. Lemma lem-sfb-relative-group-unit-axis-factorization makes it one,
since Y is reduced and the relative torus has the properties verified in step 3.
Thus the normalized isomorphism is an algebraic linearization on all test algebras.
6. Lemma lem-sfb-projective-polarization-section-algebra makes V = Gamma(Y,L)
finite-dimensional and the generating coordinate sections make it nonzero.
Lemma lem-sfb-linearized-qcoherent-cohomology-coaction in degree zero supplies the
rational representation on V, with action (g s)(y) = theta(g,g inverse y)s(g inverse y).
7. By lem-sfb-split-torus-representation-weight-decomposition choose a weight basis.
Its nonvanishing opens cover, since the coordinate sections are linear combinations
of that basis. They are affine by lem-sfb-projective-polarization-section-algebra.
8. For a weight section s of character chi, theta(g,y)s(y) = chi(g)s(gy) on every
commutative test algebra. Since chi(g) is a unit, nonvanishing is preserved. The
universal property of an open immersion gives the restricted action. Its laws follow
by composing with the open immersion, a monomorphism (def-weil-open-immersion).
The basis is finite; for the trivial torus only the trivial character occurs. -/
theorem smooth_projective_torus_invariant_affine_cover
    (F : Type u) [Field F] [IsAlgClosed F]
    (T : Grp (Over (Spec (.of F)))) (r : ℕ)
    (_hT : Nonempty (T ≅ MultiplicativeType.splitTorus F r))
    (Y : Over (Spec (.of F))) [Smooth Y.hom] [IsProjective Y.hom]
    (a : ModObj T.X Y) :
    ∃ (n : ℕ) (U : Fin n → Y.left.Opens),
      (⨆ j, U j) = ⊤ ∧ ∀ j : Fin n, IsAffineOpen (U j) ∧
        ∃ aU : ModObj T.X (Over.mk ((U j).ι ≫ Y.hom)),
          aU.smul ≫ (Over.homMk (U j).ι) =
            (T.X ◁ (Over.homMk (U j).ι)) ≫ a.smul := by
  sorry

end AlgebraicGeometry

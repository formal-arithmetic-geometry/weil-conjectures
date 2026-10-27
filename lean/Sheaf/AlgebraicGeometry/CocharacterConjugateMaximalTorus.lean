module

public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.Connected.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Mathlib.Topology.KrullDimension

/-! # Conjugating a cocharacter into a prescribed maximal torus

Source: Milne, Algebraic Groups (2017), Theorem 17.10, printed pp.354--355,
and Sections 12c--12f (blueprint: lem-sfb-cocharacter-conjugate-maximal-torus).

The equality of morphisms and its formula on every algebra's points are both retained.
An A-point of the recorded multiplicative group Spec k[t,t⁻¹] is precisely a unit of A.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- Any cocharacter can be conjugated into the given maximal torus, including the
trivial cocharacter and rank-zero case. Source: Milne, Theorem 17.10, pp.354--355,
and Sections 12c--12f (blueprint: lem-sfb-cocharacter-conjugate-maximal-torus).

Proof:
1. Apply lem-sfb-affine-homomorphism-flat-image to μ to factor it through its affine
finite-type scheme-theoretic image I, with a faithfully flat first map and closed second
map. By lem-sfb-torus-homomorphism-image, I is a torus, including inseparable images.
2. By lem-kun-dimension-finite-type, dim G is bounded. The coordinate and domain clauses
of lem-trf-lattice-torus-coordinates-action and lem-trf-split-lattice-torus-projection
show every torus is reduced and irreducible, including rank zero. The chain definition
def-kun-dimension bounds the dimensions of closed tori in G between zero and dim G.
3. Choose a torus S containing I of greatest dimension. A strictly larger torus R
cannot have the same support: def-weil-closed-immersion would give a nonzero ideal
contained in every prime of its domain coordinate ring. Thus S is a proper closed
subset of R; appending R to a longest irreducible chain in S strictly raises dimension.
This contradicts the choice of S, proving S maximal.
4. Apply lem-sfb-borel-maximal-torus-conjugacy with T₁ = S and T₂ = T to obtain
 g ∈ G(k) satisfying gSg⁻¹ = T as subgroup schemes, hence over every k-algebra.
5. By the group identities of def-sc-group-scheme, conjugation restricts to an
isomorphism S ≅ T. Compose G_m → I → S with this isomorphism to obtain ν. This gives
the asserted morphism equality and, on every A-point, g_A μ_A(t) g_A⁻¹ = i_A(ν_A(t)).
For trivial μ one can take g = 1 and trivial ν directly. -/
theorem cocharacter_conjugate_maximal_torus
    {k : Type u} [Field k] [IsAlgClosed k]
    (G T : Grp (Over (Spec (.of k))))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (i : T ⟶ G) (hT : ReductiveTorusCentralizer.IsMaximalTorus i)
    (mu : Grp.mk (StandardGroupSchemes.multiplicative k) ⟶ G) :
    ∃ (g : 𝟙_ (Over (Spec (.of k))) ⟶ G.X)
      (nu : Grp.mk (StandardGroupSchemes.multiplicative k) ⟶ T),
      (toUnit (StandardGroupSchemes.multiplicative k) ≫ g) * mu.hom.hom *
        (toUnit (StandardGroupSchemes.multiplicative k) ≫ g)⁻¹ =
          nu.hom.hom ≫ i.hom.hom ∧
      ∀ (A : Type u) [CommRing A] [Algebra k A]
        (t : StandardGroupSchemes.affine k A ⟶ StandardGroupSchemes.multiplicative k),
        (toUnit (StandardGroupSchemes.affine k A) ≫ g) * (t ≫ mu.hom.hom) *
          (toUnit (StandardGroupSchemes.affine k A) ≫ g)⁻¹ =
            t ≫ nu.hom.hom ≫ i.hom.hom := by
  sorry

end AlgebraicGeometry

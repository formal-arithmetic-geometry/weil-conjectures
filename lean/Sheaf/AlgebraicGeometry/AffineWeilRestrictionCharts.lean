module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.CategoryTheory.Yoneda
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeDegreeLocallyConstant
import Sheaf.AlgebraicGeometry.FiniteLocallyFreePrincipalBasisCover
import Sheaf.AlgebraicGeometry.AffineFiniteFreeHom
import Sheaf.AlgebraicGeometry.ExistsSchemeOfZariskiCocycle

/-! # Affine charts for restriction of scalars

Source: Stacks Project, more-morphisms.tex, Tags 0BL3 and 05Y6, with the relative
condition imposed by a fibre of postcomposition
(blueprint: lem-sfb-affine-weil-restriction-charts).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Restriction of an affine scheme along a finite locally free map is represented by
an affine scheme over an affine open of the base through which the composite factors.
The right-hand Hom is in `Over S'`: its source has underlying scheme
`pullback (T.hom ≫ i) p` and structure map the second projection. The final equation
states naturality by precomposition for every morphism of `V`-schemes. There are no
finite-type, finite-presentation, positive-rank or constant-rank assumptions.

Source: Stacks Project, more-morphisms.tex, Tags 0BL3 and 05Y6, imposing the
relative condition by a fibre of postcomposition
(blueprint: lem-sfb-affine-weil-restriction-charts).

Proof:
1. Set Z = V ×[S] S' and factor q through Z using the assumed map U → V.
   Pullback associativity identifies T ×[V] Z with T ×[S] S', naturally in T
   (def-pc-fibre-product). Base change preserves finite, flat and locally finitely
   presented morphisms (lem-weil-pbc-finite-morphism-permanence,
   lem-weil-pbc-flat-morphism-base-change, lem-weil-pbc-qcqs-morphism-permanence),
   so Z → V is finite locally free (def-pc-finite-locally-free). Z and U are affine
   over the affine base V (pqf-lem-affine-local-target).
2. Decompose V into its clopen rank loci
   (lem-weil-pbc-finite-locally-free-degree-locally-constant). Cover these by affine
   opens (lem-weil-pbc-affine-opens-basis), and then by finite-free principal charts
   (lem-a1-finite-locally-free-principal-basis-cover), which are affine by
   lem-weil-pbc-principal-localization-open-immersion. This includes rank zero.
   The restrictions U_i are affine by lem-weil-pbc-affine-morphism-permanence.
3. On each chart W_i apply lem-sfb-affine-finite-free-hom to targets U_i and Z_i,
   obtaining affine representatives M_i and N_i of ordinary relative Hom over W_i.
   By lem-galois-yoneda-hom-bijection, postcomposition with q_i gives M_i → N_i,
   while the natural projection to Z_i gives W_i → N_i.
4. Their fibre product R_i represents exactly the maps over Z_i, equivalently over S':
   the fibre equation says that postcomposition with q_i is the canonical projection.
   Pullback universal properties (def-pc-fibre-product) identify these point sets on
   every W_i-scheme and commute with precomposition.
5. Each R_i is affine: M_i → N_i is affine since both schemes are affine
   (pqf-lem-affine-local-target), so its base change to W_i is affine, with affine
   source (lem-weil-pbc-affine-morphism-permanence).
6. On overlaps the two restrictions represent the same functor on all test schemes.
   Yoneda (lem-galois-yoneda-hom-bijection) supplies unique transition isomorphisms;
   its injectivity gives the cocycle and identity conditions. Apply lem-galois-glue
   to obtain a V-scheme R with these charts. Overlaps need not be affine.
7. For an arbitrary test T, the inverse images of W_i cover T
   (lem-weil-pbc-open-preimage-fibre-product). The local bijections glue uniquely
   in both directions (lem-weil-pbc-scheme-morphism-gluing). Pulling back along a
   test morphism gives the same local maps, so uniqueness gives the stated naturality.
8. R → V has affine inverse images R_i of the affine cover W_i, so it is affine
   (pqf-lem-affine-local-target); V affine implies R affine
   (lem-weil-pbc-affine-morphism-permanence). The construction uses arbitrary
   target algebras. Rank-zero charts represent the terminal functor, and empty
   bases and tests are included by the same universal properties and gluing uniqueness.
-/
theorem exists_affine_weil_restriction_charts
    {S S' V U : Scheme.{u}} (p : S' ⟶ S) [p.IsFiniteLocallyFree]
    (i : V ⟶ S) [IsOpenImmersion i] [IsAffine V]
    (q : U ⟶ S') [IsAffine U] (_hfactor : ∃ a : U ⟶ V, a ≫ i = q ≫ p) :
    ∃ (R : Scheme.{u}) (r : R ⟶ V), IsAffine R ∧
      ∃ e : ∀ T : Over V, (T ⟶ Over.mk r) ≃
          ((Over.pullback p).obj ((Over.map i).obj T) ⟶ Over.mk q),
        ∀ (T₁ T₂ : Over V) (a : T₁ ⟶ T₂) (f : T₂ ⟶ Over.mk r),
          e T₁ (a ≫ f) = (Over.pullback p).map ((Over.map i).map a) ≫ e T₂ f := by
  sorry

end AlgebraicGeometry

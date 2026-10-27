module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Yoneda
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.AlgebraicGeometry.Fiber
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Representability

/-!
# An affine-neighbourhood criterion for scheme-valued Weil restriction

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, §7.6, Theorem 4,
printed pp.194–195 (blueprint: lem-sfb-weil-restriction-affine-neighbourhood-criterion).

The functor is the composite of the opposite base-change functor with the
Yoneda presheaf of the given scheme over the source. Thus its restriction maps
are precomposition with the canonical base-change maps.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The Weil restriction along a finite locally free map is represented by a scheme
when finite subsets of every fibre of `Z` over `S` have affine neighbourhoods in `Z`.

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, §7.6, Theorem 4,
printed pp.194–195 (blueprint: lem-sfb-weil-restriction-affine-neighbourhood-criterion).

Proof plan, following the five steps of the DAG node:
1. The functor is a Zariski sheaf. A cover of a test scheme pulls back to a cover
   after base change (`lem-weil-pbc-open-preimage-fibre-product`). Compatible
   morphisms to `Z` glue uniquely (`lem-weil-pbc-scheme-morphism-gluing`), and their
   composites to `S'` agree with the projection, so the glued morphism is over `S'`.
2. Index by affine opens `V` of `S` and affine opens `U` of `Z` mapping into `V`,
   including the empty open. The subfunctor consists of maps whose test scheme
   maps into `V` and whose base change maps into `U`. The two factorizations are
   unique through open immersions (`def-weil-open-immersion`). The affine-chart
   construction (`lem-sfb-affine-weil-restriction-charts`) represents this
   subfunctor by an affine `V`-scheme, hence by a scheme over `S`.
3. For a test map `a : T ×_S S' ⟶ Z`, with projection `r` to `T`, let `C` be the
   closed complement of `a⁻¹(U)`. The map `r` is finite by
   `lem-weil-pbc-finite-morphism-permanence`; its closed image `r(C)` exists by
   `lem-weil-pbc-finite-closed-map-finite-fibres`. The locus is the open
   `b⁻¹(V) \ r(C)`. For every base change, the bad image is the inverse image
   of `r(C)` by `lem-weil-pbc-base-change-image`. Factoring through the opens
   therefore identifies this locus with the pullback of the subfunctor,
   including for nonflat and nonreduced test schemes.
4. At a point `t` of `T`, the image `P` of the fibre of `r` is finite by
   `lem-weil-pbc-finite-closed-map-finite-fibres`. Its points lift to the fibre
   of `Z` over `b(t)`, using `def-pc-fibre-product` and `def-pc-scheme-fibre`.
   Choose finitely many lifts and apply the hypothesis to obtain an affine `U₀`
   containing `P`. Choose an affine base neighbourhood `V` of `b(t)` using
   `lem-weil-pbc-affine-opens-basis`. In the affine `U₀`, the sections whose
   basic opens lie in `U₀ ∩ b_Z⁻¹(V)` form an ideal. It avoids each prime of `P`
   by the basic-open basis (`lem-weil-pbc-spec-localization-away-basic-open`).
   Prime avoidance (`lem-weil-pbc-prime-avoidance`) gives a section outside
   all those primes. Its basic open is affine and contains `P` by
   `lem-weil-pbc-affine-open-section-vanishing-prime`. For empty `P`, use the
   empty affine open. Thus the open loci in step 3 cover every test scheme.
5. Apply `lem-pc-schemes-criterion` to this sheaf and its representable open
   subfunctors. It produces the representing scheme over `S` and the natural
   bijections. All finiteness assumptions concern `p`, not `Z`. -/
theorem weilRestriction_representable_of_affineNeighbourhood
    {S S' Z : Scheme.{u}} (p : S' ⟶ S) [p.IsFiniteLocallyFree] (q : Z ⟶ S')
    (h : ∀ (s : S) (P : Set ↥(pullback (q ≫ p) (S.fromSpecResidueField s))),
      P.Finite → ∃ U : Z.Opens, IsAffineOpen U ∧
        (pullback.fst (q ≫ p) (S.fromSpecResidueField s)) '' P ⊆ (U : Set Z)) :
    ∃ W : Over S, Nonempty (yoneda.obj W ≅ (Over.pullback p).op ⋙ yoneda.obj (Over.mk q)) := by
  sorry

end AlgebraicGeometry

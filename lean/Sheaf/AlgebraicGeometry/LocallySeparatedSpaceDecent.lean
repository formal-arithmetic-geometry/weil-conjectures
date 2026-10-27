module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.Topology.Defs.Filter
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import Mathlib.AlgebraicGeometry.ResidueField
import Sheaf.AlgebraicGeometry.GroupoidScheme
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Locally separated algebraic spaces are decent

Source: Stacks Project, Decent Spaces, Tag 088J (lemma-locally-separated-decent);
decency is Tag 03I8, equivalently Tag 03JV(6)
(blueprint: lem-sfb-locally-separated-space-decent).

The base is the spectrum of the universe lift of the integers. Decency is expanded
on every affine scheme test, without restricting the tests to étale charts.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space over the integers whose absolute diagonal is an immersion is
decent: every map from a field spectrum has quasi-compact affine scheme base changes.
Source: Stacks Project, Decent Spaces, Tags 088J, 03I8 and 03JV(6)
(blueprint: lem-sfb-locally-separated-space-decent).

Proof:
1. Fix a point of `X`, choose an étale chart and a point `v` over it
[lem-a1-space-affine-etale-cover], and put `u = Spec κ(v)`. The canonical map
`u → V` is a monomorphism, by its point and surjective residue-field stalk maps
[lem-weil-pbc-morphism-from-spec-field]. The self-relation `H = u ×_X u`
[lem-trf-space-fibre-products-etale-covers] maps by an immersion to `u ×_Z u`.
Its kernel-relation groupoid operations [def-a1-groupoid-scheme] and
[lem-sfb-field-kernel-relation-immersion-closed] make this a closed immersion.
2. The scheme `u ×_X V` is étale over `u`, hence a coproduct of finite separable
field spectra [lem-weil-pbc-etale-fibre-discrete-separable-points]. Its subscheme
`H` is a union of components [lem-sfb-monomorphism-into-field-coproduct]. It is
affine as a closed subscheme of the affine `u ×_Z u`
[lem-weil-pbc-fibre-product-affine-spectra, def-weil-closed-immersion], and thus
quasi-compact [lem-weil-pbc-affine-scheme-qcqs], so only finitely many components
occur. Both projections of `H` are étale and quasi-compact, using interchange
and [lem-weil-pbc-etale-composition-cancellation]. Apply
[lem-sfb-finite-point-self-relation-field-monomorphism] to obtain a field
monomorphism `j : Spec k → X` representing the chosen point.
3. For an affine étale chart `U = Spec A → X`, write
`F = U ×_X Spec k = ∐ Spec k_i`. Each component maps monomorphically into `U`;
factoring through its residue field [lem-weil-pbc-morphism-from-spec-field]
and applying [lem-sfb-monomorphism-into-field-coproduct] after residue-field
base change identifies `k_i = κ(p_i)` and makes the image points `p_i` distinct.
4. The immersion `q : R = U ×_X U → P = U ×_Z U` factors through a closed
immersion into an open `P'`. The relation diagonal `e : U → R` is étale by
cancellation, hence open by [lem-sfb-space-etale-monomorphism-open]. Its composite
with `q` is the affine closed diagonal, induced by multiplication on `A ⊗_Z A`.
Since `q` is an embedding, `e(U)` is also closed in `R`. Write `R = e(U) ∐ W`.
5. The subset `q'(W)` is closed in `P'` and disjoint from the diagonal. Closure
in `P`, restricted to the open `P'`, agrees with closure in `P'`, so the closure
of `q(W)` avoids the diagonal.
6. For distinct indices, `Spec (k_i ⊗_k k_j)` maps into `W`, since its two images
in `U` are distinct. If the index set were infinite, choose countably many indices;
[lem-sfb-infinite-primes-off-diagonal-closure] makes the closure of these cross
products meet the diagonal, contradicting step 5. Thus the index set is finite,
and `F` is finite over `k` [def-weil-finite-integral-morphism].
7. Apply [lem-sfb-field-monomorphism-finite-chart-decency-criterion] to `j` and
these finite affine étale chart pullbacks. Every representative of the chosen point
is quasi-compact on all affine scheme tests. Every field-valued map represents a
point, giving the assertion. For empty `X` there are no field-valued maps. -/
theorem decent_of_locallySeparated
    (X : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (hdiag : IsRepresentableWith (fun _ _ p ↦ IsImmersion p.left)
      (prod.lift (𝟙 X.obj.obj) (𝟙 X.obj.obj))) :
    ∀ (L : Type u) [Field L]
      (b : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of (ULift.{u} ℤ)))
      (a : yoneda.obj (Over.mk b) ⟶ X.obj.obj)
      (U : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))), IsAffine U.left →
      ∀ t : yoneda.obj U ⟶ X.obj.obj,
        ∃ (V : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) (p : V ⟶ U)
          (q : yoneda.obj V ⟶ yoneda.obj (Over.mk b)),
          IsPullback q (yoneda.map p) a t ∧ CompactSpace V.left := by
  sorry

end AlgebraicGeometry.AlgebraicSpace

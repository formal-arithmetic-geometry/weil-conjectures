/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpacePointTopology
public import WeilConjectures.AlgebraicGeometry.SchemeGroupoidLaws
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.ChartwiseEtalePermanence
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# The Noetherian relation scheme of an affine étale atlas

Source: Stacks Project, Properties of Spaces, Tags 03EA and 03H6; Spaces Cohomology,
Tag 07UV; Morphisms of Spaces, Tags 0467 and 073B; Groupoids, Tag 0231
(blueprint: lem-sfb-noetherian-affine-atlas-relation).

The relation scheme is specified by its representing pullback square, so it is the actual
fibre product over the algebraic space. Its source is the second projection and its target
the first. The groupoid laws determine the usual identity, swap and composition maps:
the two projections jointly determine a map into the relation scheme.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- An affine surjective étale atlas of a Noetherian algebraic space has a Noetherian
relation scheme, with its usual groupoid structure and étale, flat, qcqs projections.
Here `hln`, `hqc`, `hqs` spell out locally Noetherian, quasi-compact, and absolutely
quasi-separated, respectively. The latter tests fibre products of pairs of affine scheme
maps, rather than imposing a separation condition on the structural map to `S`.
Source: Stacks, Properties of Spaces, Tags 03EA and 03H6; Spaces Cohomology, Tag 07UV;
Morphisms of Spaces, Tags 0467 and 073B; Groupoids, Tags 0231 and 0233
(blueprint: lem-sfb-noetherian-affine-atlas-relation).

Proof:
1. Representability of the atlas gives the scheme R = U x_X U. Each projection is a
   scheme test of the atlas, hence étale and flat. The atlas U is locally Noetherian by
   hln. By lem-trf-space-chartwise-etale-permanence, its base change and composite are
   étale, so R is also an étale scheme chart of X and locally Noetherian.
2. With t(a,b)=a and s(a,b)=b, the fibre-product universal property constructs
   e(a)=(a,a), i(a,b)=(b,a), and c((a,b),(b,d))=(a,d). The source, target, unit, inverse
   and associativity laws of def-a1-scheme-groupoid-laws follow componentwise. Both
   parenthesizations of a composable triple give its first and last components.
3. For a scheme T, its field-valued point classes with the topology of
   def-a1-space-point-topology identify with its Zariski point space: use residue-field
   representatives and the identity étale test. An affine U is qcqs by
   lem-weil-pbc-affine-scheme-qcqs and lem-weil-pbc-fibre-product-affine-spectra.
   The qcqs fibre-product lemma lem-sfb-qcqs-space-fibre-product gives qcqs for R,
   since X is qcqs. Thus U and R are quasi-compact and locally Noetherian, hence
   Noetherian schemes. There is no compactness or separation hypothesis on S.
4. Apply lem-sfb-space-qcqs-permanence to each projection from the qcqs space R to
   the quasi-separated space U. Testing on affine opens, and using the identification
   of point spaces in step 3, gives scheme QuasiCompact for both projections and for
   their relative diagonals, hence scheme QuasiSeparated. -/
theorem noetherian_affine_atlas_relation
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hln : ∀ T : X.EtaleSite, IsLocallyNoetherian (X.etaleForget.obj T))
    (hqc : CompactSpace (Point X.obj.obj))
    (hqs : ∀ (V W : Over S) (a : yoneda.obj V ⟶ X.obj.obj)
      (b : yoneda.obj W ⟶ X.obj.obj), IsAffine V.left → IsAffine W.left →
        CompactSpace (Point (Limits.pullback a b)))
    (U : Over S) (p : yoneda.obj U ⟶ X.obj.obj)
    (hp : IsEtale p) (hsurj : IsSurjective p) (haff : IsAffine U.left) :
    IsNoetherian U.left ∧
      ∃ (R : Over S) (t s : R ⟶ U),
        IsPullback (yoneda.map t) (yoneda.map s) p p ∧
        IsNoetherian R.left ∧
        Etale s.left ∧ Etale t.left ∧ Flat s.left ∧ Flat t.left ∧
        QuasiCompact s.left ∧ QuasiCompact t.left ∧
        QuasiSeparated s.left ∧ QuasiSeparated t.left ∧
        ∃ (e : U.left ⟶ R.left) (i : R.left ⟶ R.left)
          (c : Limits.pullback s.left t.left ⟶ R.left),
          Scheme.IsGroupoid s.left t.left e i c := by
  sorry

end AlgebraicGeometry.AlgebraicSpace

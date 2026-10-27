module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Group.Smooth
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
import Sheaf.AlgebraicGeometry.GroupScheme.AffinePointedMapGeneratedSubgroup
import WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Smooth connected relative commutator subgroups

Source: Milne, Algebraic Groups (2017), Definition 6.24 and Remark 6.25(b), p.131;
Propositions 2.46--2.48 and 2.50, pp.54--56; descending central series before
Proposition 6.38, p.133 (blueprint: lem-sfb-smooth-connected-relative-commutator).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry

/-- If `G` is smooth, connected, affine and of finite type over a field and `N` is a smooth
connected normal closed subgroup, there is a smallest closed subgroup `[G,N]` containing
all relative commutators on every algebra. It is smooth, connected, normal and contained
in `N`. Minimality applies to every closed subgroup, with no regularity assumptions.
Source: Milne, Definition 6.24 and Remark 6.25(b), p.131; Propositions 2.46--2.48 and 2.50,
pp.54--56; descending central series before Proposition 6.38, p.133.
(blueprint: lem-sfb-smooth-connected-relative-commutator)

Proof:
1. Put X = G × N and o = (e,e). By lem-weil-pbc-fibre-product-affine-spectra and
   lem-sfb-finite-type-composition-base-change, X and its powers are affine of finite type.
   For an affine source, a map factors through a closed subscheme exactly when its
   coordinate pullback kills the defining ideal (def-weil-affine-spectrum and
   def-weil-closed-immersion); equivalently test its universal algebra-valued point.
2. The group operations (def-sc-group-scheme) give c(g,n) = gng⁻¹n⁻¹ and c(o) = e.
   Normality (def-sc-group-scheme-subgroup) puts c(g,n) in N and gives the conjugation
   morphism G × N → N by the universal-point test. The commutator image is inverse stable:
   c(g,n)⁻¹ = c(g⁻¹,gng⁻¹).
3. The projection X → N is smooth by clause (2) of lem-pc-proper-base-change; compose
   with N → Spec k using lem-trf-smooth-composition. Then
   sbc-lem-smooth-geometrically-reduced makes X geometrically reduced over k.
4. The identity sections and lem-sbc-connected-rational-point-geometrically-connected
   make G and N geometrically connected. Over any extension L/k, apply
   lem-weil-pbc-geometrically-connected-product-components to G_L × N_L → N_L.
   Its components correspond to those of N_L, so X_L is connected and nonempty.
5. Apply lem-sfb-affine-pointed-map-generated-subgroup to (X,o,c). The generated
   D = Spec(k[G]/I), with I the intersection of the positive word-pullback kernels, is
   affine of finite type, geometrically reduced and geometrically connected. By
   lem-sfb-geometrically-reduced-group-smooth it is smooth. At L = k it is connected.
   The descended word pullbacks f_n on k[D] jointly detect zero by the definition of I.
6. Factorization of c gives every asserted R-point lift. If a closed subgroup K contains
   these commutators on every algebra, evaluate at the universal point of X to factor c
   through K. Generated-subgroup minimality yields D ⊆ K. Taking K = N gives D ⊆ N.
7. Conjugation q : G × D → G satisfies q ∘ (id × w_n) = w_n ∘ T_n, where T_n replaces
   every (g_i,n_i) by (hg_ih⁻¹,hn_ih⁻¹); these substitutions are morphisms by step 2.
   Hence (id ⊗ f_n)(q*(a)) = 0 for all a in I, using the affine-product identification
   of lem-weil-pbc-fibre-product-affine-spectra.
8. Swap tensor factors and use lem-sfb-vector-space-tensor-family-zero-detection with
   the jointly zero-detecting f_n to get q*(I) = 0. Thus q factors through D. On all
   R-points hD(R)h⁻¹ ⊆ D(R); applying this also to h⁻¹ gives equality. This is normality
   by def-sc-group-scheme-subgroup. Minimality characterizes the subgroup `[G,N]`.
-/
theorem exists_smooth_connected_relative_commutator {k : Type u} [Field k]
    (G N : Grp (Over (Spec (.of k))))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    [Smooth G.X.hom] [ConnectedSpace G.X.left]
    [IsAffine N.X.left] [LocallyOfFiniteType N.X.hom] [QuasiCompact N.X.hom]
    [Smooth N.X.hom] [ConnectedSpace N.X.left]
    (i : N ⟶ G) [IsClosedSubgroupScheme i.hom.hom]
    [IsNormalSubgroupScheme i.hom.hom] :
    ∃ (D : Grp (Over (Spec (.of k)))) (j : D ⟶ G),
      IsClosedSubgroupScheme j.hom.hom ∧ IsNormalSubgroupScheme j.hom.hom ∧
      IsAffine D.X.left ∧ LocallyOfFiniteType D.X.hom ∧ QuasiCompact D.X.hom ∧
      Smooth D.X.hom ∧ ConnectedSpace D.X.left ∧
      (∃ l : D.X ⟶ N.X, l ≫ i.hom.hom = j.hom.hom) ∧
      (∀ (R : Type u) [CommRing R] [Algebra k R]
        (g : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⟶ G.X)
        (n : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⟶ N.X),
        ∃ d : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⟶ D.X,
          d ≫ j.hom.hom = g * (n ≫ i.hom.hom) * g⁻¹ * (n ≫ i.hom.hom)⁻¹) ∧
      (∀ (K : Grp (Over (Spec (.of k)))) (a : K ⟶ G),
        IsClosedSubgroupScheme a.hom.hom →
        (∀ (R : Type u) [CommRing R] [Algebra k R]
          (g : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⟶ G.X)
          (n : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⟶ N.X),
          ∃ x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⟶ K.X,
            x ≫ a.hom.hom = g * (n ≫ i.hom.hom) * g⁻¹ * (n ≫ i.hom.hom)⁻¹) →
        ∃ l : D.X ⟶ K.X, l ≫ a.hom.hom = j.hom.hom) := by
  sorry

end AlgebraicGeometry

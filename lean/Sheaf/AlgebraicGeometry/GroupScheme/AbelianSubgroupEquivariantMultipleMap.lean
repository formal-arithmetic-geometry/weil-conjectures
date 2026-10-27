module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousQuotient
import Mathlib.CategoryTheory.Yoneda
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.Regular
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Sheaf.AlgebraicGeometry.CommutativeTorsorPositiveWeight
import Mathlib.AlgebraicGeometry.SpreadingOut
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Sheaf.AlgebraicGeometry.GeometricallyIrreducibleProduct

/-! # Equivariant positive-multiple maps to central abelian subgroups

Source: Milne, Algebraic Groups (2017), Proposition 8.23 and Lemma 8.22,
printed pp.152–153.
(blueprint: lem-sfb-abelian-subgroup-equivariant-multiple-map)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- A central closed abelian subgroup of a smooth connected separated finite-type group
admits a scheme morphism equivariant for multiplication by a positive integer.
The morphism need not preserve the identity. The equality is on the fibre product,
so it applies to every test scheme, including nonreduced test schemes.

Source: Milne, Algebraic Groups (2017), Proposition 8.23 and Lemma 8.22,
printed pp.152–153; the positive integer is the degree used in Lemma 8.22.
(blueprint: lem-sfb-abelian-subgroup-equivariant-multiple-map)

Proof plan (the eight steps of the node):
1. The identity sections make G and A nonempty. Use
   lem-sbc-connected-rational-point-geometrically-connected and
   lem-trf-smooth-connected-fibre-normal-integrality to make both geometrically integral.
   Centrality and the monomorphism i imply commutativity of A on affine test schemes;
   the identities glue, giving the group-scheme identity.
2. Apply lem-sfb-algebraic-group-homogeneous-quotient to get p : G → Q with Q separated
   and finite type, and p flat, surjective and finitely presented. Its coset criterion
   gives the isomorphism theta : G × A → G ×_Q G, (g,a) ↦ (g,g i(a)), using
   lem-galois-yoneda-fully-faithful, and gives p(g i(a)) = p(g).
3. Under theta, the base change of p is the smooth projection G × A → G by
   lem-pc-proper-base-change. Apply lem-trf-smooth-fpqc-base-descent and
   lem-sbc-smooth-flat-surjective-source-descent to make p and Q smooth.
   Q is regular by lem-weil-pbc-smooth-scheme-over-field-regular, nonempty and connected
   by surjectivity, and integral by lem-sc-regular-connected-integral.
4. Let K be the function field of Q and V its generic fibre in G. Base change of theta
   makes V a torsor under A_K. Use lem-weil-pbc-flat-morphism-base-change,
   lem-weil-pbc-surjective-base-change and lem-pc-proper-base-change for the hypotheses
   of lem-sfb-commutative-torsor-positive-weight. It supplies n > 0 and f_V : V → A_K
   with the required identity, even if K is imperfect.
5. The generic fibre V is integral with function field k(G): its affine charts are
   localizations of domains over affine opens of Q. Compose f_V with the generic point
   of V and A_K → A. Apply lem-sfb-local-ring-map-spread to extend this map to an open
   neighbourhood U of the generic point of G. The source is locally Noetherian by
   lem-weil-pbc-smooth-scheme-over-field-regular. Apply
   lem-sfb-weil-extension-to-abelian-variety to extend U → A to phi : G → A.
6. The generic-fibre restriction phi_eta and f_V agree at Spec k(G), whose image in V
   is dense. V is reduced and A_K is separated. Apply
   lem-sfb-relative-separated-dominant-ext to conclude phi_eta = f_V on all of V.
7. Put X = G × A and q = p pr_1. Smooth base change and lem-trf-smooth-composition
   make X smooth, hence reduced by sbc-lem-smooth-geometrically-reduced.
   Lemma lem-sc-geometrically-irreducible-product makes X irreducible, hence integral.
   The identity of A makes pr_1 surjective, so q is dominant. The generic fibre
   X_eta = V × A_K has dense image in X, since it contains its generic point.
8. On X_eta the maps phi(g i(a)) and phi(g) + [n]a agree by steps 4 and 6.
   Apply lem-sfb-relative-separated-dominant-ext to the reduced X and separated A
   to obtain equality on X. Pullback gives the formula on every test scheme.
   No normalization at the identity, division by n or commutativity of G is used. -/
theorem exists_abelian_subgroup_equivariant_multiple_map
    (k : Type u) [Field k] [IsAlgClosed k]
    (G A : Over (Spec (.of k))) [GrpObj G] [GrpObj A]
    [Smooth G.hom] [ConnectedSpace G.left] [IsSeparated G.hom]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] [IsAbelianVariety A]
    (i : A ⟶ G) [IsClosedSubgroupScheme i]
    (hcentral : ∀ (R : Type u) [CommRing R] [Algebra k R]
      (a : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⟶ A)
      (g : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⟶ G),
      Commute (a ≫ i) g) :
    ∃ (n : ℕ), 0 < n ∧ ∃ (φ : G ⟶ A),
      lift (fst G A) (snd G A ≫ i) ≫ μ[G] ≫ φ =
        lift (fst G A ≫ φ) (snd G A ≫ (𝟙 A ^ n)) ≫ μ[A] := by
  sorry

end AlgebraicGeometry

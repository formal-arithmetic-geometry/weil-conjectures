module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.Mathlib.RingTheory.Henselian
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.Topology.NoetherianSpace
import Sheaf.AlgebraicGeometry.AffineOpenBoundaryCodimensionOne
import Sheaf.RingTheory.HenselianSmoothAlgebraLifting

/-!
# An affine principal chart and its finite translate cover over a trait

Source: Prasad--Yu, On quasi-reductive group schemes, Proposition 3.1, printed p.5,
proof after reduction to a smooth group over a strictly henselian DVR; the principal
chart is attributed there to Neron Models, p.161, Lemma 6.
(blueprint: lem-sfb-smooth-trait-principal-translate-cover)

For a section `g`, `(toUnit G ≫ g) * 𝟙 G` is left translation on `G`: multiplication
is the existing group operation on morphisms into the group object. Its inverse is
the same expression with `g⁻¹`. No field-only translation interface is used.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- A smooth separated group of finite type over a strictly henselian DVR with
algebraically closed residue field and affine generic fibre has a principal affine
chart meeting the special fibre; finitely many translates and the generic fibre
form a principal affine cover. Source: Prasad--Yu, Proposition 3.1, printed p.5,
and BLR, Neron Models, p.161, Lemma 6.
(blueprint: lem-sfb-smooth-trait-principal-translate-cover)

Proof plan, following the DAG's eleven steps:
1. A DVR is Noetherian (lem-weil-pbc-pid-noetherian-normal); finite type makes G
Noetherian (lem-weil-pbc-finite-type-over-noetherian). It is separated and qcqs
(lem-sc-separated-over-affine-scheme-separated, lem-weil-pbc-qcqs-over-affine).
Smooth affine charts are flat (lem-pc-open-immersion-smooth-composition,
lem-weil-pbc-smooth-ring-map-iff-smooth-affine, lem-weil-pbc-smooth-ring-map-flat),
so multiplication by pi is injective (lem-trf-flat-module-torsionfree-domain).
2. The fibres are finite type (lem-sfb-finite-type-composition-base-change) and
smooth (lem-weil-pbc-smooth-ring-map-base-change-composition). They are Noetherian;
G and its special fibre are reduced and the generic fibre is dense in every component
(lem-trf-smooth-reduced-dense-pullback). Identity sections make both fibres nonempty.
3. There are finitely many generic points (lem-weil-pbc-noetherian-finite-components).
The local dimensions at the generic points of G and its special fibre are zero and
one respectively (lem-weil-pbc-flat-height-formula, lem-weil-pbc-localization-noetherian).
A common affine neighbourhood U exists
(lem-trf-codimension-one-points-affine-neighbourhood).
4. The boundary E has finitely many components
(lem-sc-noetherian-closed-subset-finite-components), with generic points of local
dimension one (lem-sfb-affine-open-boundary-codimension-one). The flat height formula
excludes vertical components; hence E is the closure of its generic fibre.
5. Prime avoidance (lem-weil-pbc-prime-avoidance) on the affine generic fibre gives
a function vanishing on E_K and nonvanishing at every generic point. The comparison
C = A[1/pi] (lem-sfb-qcqs-functions-local-comparison) writes it as h/pi^d.
6. Its germ at a special point is nonzero, since every neighbourhood contains a
generic point where h is nonzero. Krull intersection
(lem-weil-pbc-krull-intersection-jacobson) bounds global pi-divisibility; divide out
the largest power to obtain f not in pi*A with the same generic principal open.
7. The kernel of restriction A to Gamma(G_k) is pi*A: divide locally and glue the
unique quotients using injectivity of pi. Thus f has nonzero reduction. Reducedness
and lem-weil-pbc-qc-scheme-vanishing-section-nilpotent show its principal open meets G_k.
8. The function vanishes on E_K, hence on its closure E; its principal open lies in U.
A principal open of an affine scheme is affine
(lem-weil-pbc-principal-localization-open-immersion).
9. Jacobson density (lem-sc-lft-over-field-jacobson-space) gives a closed point u
in this open on G_k. Closed points are k-rational
(lem-weil-pbc-closed-point-residue-field-base). For every closed y in G_k, lift y*u^-1
to an R-section g (lem-trf-henselian-smooth-algebra-lifting); then y lies in g*G_f.
10. Translates are affine opens by the group diagrams. Their union contains every
closed point of the special fibre, hence the entire fibre by Jacobson density.
Together with G_K they cover G. Quasi-compactness gives finitely many translates;
adjoin the identity section if necessary to make their number positive.
11. Set F(0) = pi*1 and F(j+1) = (L_g^-1)^*f. Local isomorphisms preserve and reflect
units, giving the translated-open identities. A DVR satisfies R[1/pi] = K, so the
zeroth principal open is exactly the generic fibre, which is affine by hypothesis.
No connectedness assumption enters any step. -/
theorem smooth_trait_principal_translate_cover
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsStrictlyHenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (π : R) (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
    (G : Over (Spec (.of R))) [GrpObj G] [Smooth G.hom] [IsSeparated G.hom]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [IsAffine (pullback G.hom (Spec.map (CommRingCat.ofHom (algebraMap R K))))] :
    ∃ (f : Γ(G.left, ⊤)) (n : ℕ) (g : Fin n → (𝟙_ (Over (Spec (.of R))) ⟶ G))
      (F : Fin (n + 1) → Γ(G.left, ⊤)),
      1 ≤ n ∧
      IsAffineOpen (G.left.basicOpen f) ∧
      (∃ x : (pullback G.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) :
          Scheme.{u}),
        (pullback.fst G.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) x ∈
          G.left.basicOpen f) ∧
      F 0 = G.hom.appTop ((Scheme.ΓSpecIso (.of R)).inv π) ∧
      (∀ j : Fin n, F j.succ =
        (((toUnit G ≫ (g j)⁻¹) * 𝟙 G).left.appTop) f) ∧
      (⨆ j : Fin (n + 1), G.left.basicOpen (F j)) = ⊤ ∧
      (∀ j : Fin (n + 1), IsAffineOpen (G.left.basicOpen (F j))) ∧
      Set.range (pullback.fst G.hom (Spec.map (CommRingCat.ofHom (algebraMap R K)))) =
        (G.left.basicOpen (F 0) : Set G.left) ∧
      (∀ j : Fin n, (G.left.basicOpen (F j.succ) : Set G.left) =
        ((toUnit G ≫ g j) * 𝟙 G).left '' (G.left.basicOpen f : Set G.left)) := by
  sorry

end AlgebraicGeometry

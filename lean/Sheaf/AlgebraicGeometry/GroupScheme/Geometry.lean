/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q48
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Differential
public import WeilConjectures.AlgebraicGeometry.SchemeTangentSpace
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme

import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import Sheaf.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent
import Sheaf.AlgebraicGeometry.IrreducibleProductOverField
import Sheaf.AlgebraicGeometry.GroupoidScheme
import Sheaf.AlgebraicGeometry.PerfectFieldGroupoidImageClosure
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.GroupScheme.Separated
import WeilConjectures.AlgebraicGeometry.DensePoints
import WeilConjectures.AlgebraicGeometry.GroupScheme.LieLocalDimension
import WeilConjectures.AlgebraicGeometry.GroupScheme.LieIdentityTangentEquiv
import Sheaf.AlgebraicGeometry.GroupScheme.IdentityLocalDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.NowhereDenseDimensionDrop
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Irreducible
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Topology.Separation.Basic
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.Topology.Constructible

/-!
# Components, images, and equal Lie algebras of algebraic groups

Source: current blueprint, Algebraic groups and Lie algebras, `sk-p-geometry`, all three
paragraphs and the complement; the coefficient convention is `sk-i-cartier`.
(blueprint: sk-p-geometry)

The image is the existing scheme-theoretic image: the theorem asserts that it is reduced,
so it is precisely the reduced induced closed subscheme on the underlying image.
The canonical differential is postcomposition on dual-number tangent vectors, as specified
by `GrpObj.tangentPoint_differential`; `GrpObj.lieIdentityTangentEquiv` identifies its Lie
spaces with the scheme tangent spaces at the identity.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

/-- Components, images, and equal Lie algebras for finite type group schemes over an
algebraically closed field of characteristic zero. Closed subgroup equality is expressed
by the given inclusion being an isomorphism, not by an abstract group isomorphism.
Source: current blueprint, `sk-p-geometry`, all paragraphs and complement.
(blueprint: sk-p-geometry)

Proof plan, following the ten steps of the node:
1. Finite type over Spec L makes G Noetherian
   (lem-weil-pbc-finite-type-over-noetherian). Its finitely many irreducible components
   cover it and each is connected, so there are finitely many connected components
   (lem-sc-noetherian-finite-irreducible-components, lem-sc-irreducible-components-cover).
2. Cartier makes G smooth (lem-sfb-cartier-characteristic-zero-smooth), hence regular
   (lem-weil-pbc-smooth-scheme-over-field-regular). Its local rings are domains
   (lem-sc-regular-local-domain). Distinct irreducible components meeting at x would
   give distinct minimal primes in this domain, using an affine neighbourhood, the open
   component correspondence, and localization of primes
   (lem-sc-components-open-injection,
   lem-weil-pbc-spec-irreducible-components-minimal-primes,
   lem-weil-pbc-primes-of-localization, lem-weil-pbc-affine-open-stalk-localization).
   Thus the components are disjoint, clopen and irreducible.
3. The identity component has its open subgroup structure and is geometrically irreducible
   (lem-sfb-locally-algebraic-group-identity-component). Every component has a closed,
   hence L-rational, point (lem-sc-quasi-compact-kolmogorov-closed-point,
   lem-wf-affine-nullstellensatz-vanishing). Translation by it identifies that component
   with the identity component (lem-sc-translation-automorphism). Each piece of the
   product G times the identity component is irreducible
   (lem-sc-irreducible-product-over-field), and conjugation maps it to a connected subset
   containing 1. Conjugation therefore factors through the open identity component
   (lem-weil-pbc-morphism-factors-through-open-subscheme), proving normality on all
   algebra-valued points.
4. View G and H as groupoids over Spec L (def-a1-groupoid-scheme). The reduced closure
   J of the image is a subgroup (lem-sfb-perfect-field-groupoid-image-closure).
   Cartier reducedness and lem-weil-pbc-reduced-source-factors-through-closed-subscheme
   factor f through J; cancellation of its monomorphism shows this is a homomorphism.
5. J is finite type and Noetherian; G to J is finite type because generators over L
   also generate over an affine coordinate algebra of J. Opens in G are quasi-compact
   (lem-weil-pbc-noetherian-open-subscheme-noetherian), and local finite type over a
   locally Noetherian target is local finite presentation (pqf-lem-lft-fp-locnoeth).
   J is separated (lem-sc-group-scheme-separated-field). Chevalley gives a constructible
   dense image (lem-weil-pbc-chevalley-constructible-image), whose affine restriction is
   constructible (lem-weil-pbc-constructible-open-restriction) and contains a nonempty
   open U (lem-wf-affine-constructible-open).
6. Each fibre over a point of U(L) is nonempty and finite type over L
   (lem-sfb-finite-type-composition-base-change). Closed points and the Nullstellensatz
   give an L-point in that fibre, hence U(L) lies in the rational-point image P.
   Choose u in U(L); translating by its inverse gives an open identity neighbourhood
   W with W(L) contained in P (lem-sc-translation-automorphism).
7. Translates of W(L) make P open in J(L), and the other cosets make its complement
   open. Thus P is closed. Cartier smoothness and lem-pc-rational-points-dense make
   G(L) dense in G; continuity makes P dense in J and hence in J(L). So P = J(L).
   Only translations on rational points are used, not a product-topology assertion.
8. The constructible complement of the scheme image in J, if nonempty, has a nonempty
   locally closed piece and an L-point by the same closed-point and Nullstellensatz
   argument. This contradicts P = J(L). Thus the scheme image is closed with reduced
   induced subgroup J. Since G is reduced, its scheme-theoretic image is reduced;
   uniqueness (lem-weil-pbc-reduced-induced-closed-subscheme) identifies it with J.
9. For a connected G and a closed subgroup K with bijective inclusion differential,
   Cartier makes both smooth. The canonical tangent equivalence
   (lem-ag-lie-identity-tangent-equiv), smooth local dimension
   (lem-ag-smooth-lie-local-dimension), and identity local-to-global dimension
   (lem-ag-group-identity-local-dimension) give dim K = dim G. The ambient group is
   irreducible by step 2 and finite-dimensional (lem-kun-dimension-finite-type).
10. A proper closed support in irreducible G is nowhere dense, so dimension drops
    (lem-sc-hilbert-nowhere-dense-dimension-drop). Equal dimensions force equal supports.
    Cartier reducedness and uniqueness of reduced induced closed subschemes identify
    the given closed immersion with G. If dimension equality is assumed initially,
    the same argument applies directly. This includes dimension zero.
-/
theorem algebraicGroup_geometry
    (L : Type u) [Field L] [IsAlgClosed L] [CharZero L]
    (G : Over (Spec (.of L))) [GrpObj G]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] :
    Finite (ConnectedComponents G.left) ∧
    IsOpenImmersion (GrpObj.identityComponentι G).left ∧
    IsClosedImmersion (GrpObj.identityComponentι G).left ∧
    IrreducibleSpace (GrpObj.identityComponent G).left ∧
    IsNormalSubgroupScheme (GrpObj.identityComponentι G) ∧
    (∀ x : G.left, ∃ g : 𝟙_ (Over (Spec (.of L))) ⟶ G,
      connectedComponent x =
        (GrpObj.mulLeft G g).left '' connectedComponent (GrpObj.onePoint G)) ∧
    (∀ (H : Over (Spec (.of L))) [GrpObj H]
        [LocallyOfFiniteType H.hom] [QuasiCompact H.hom]
        (f : G ⟶ H) [IsMonHom f],
      IsClosed (Set.range f.left) ∧
      IsReduced f.left.image ∧
      Set.range f.left.imageι = Set.range f.left ∧
      ∃ _ : GrpObj (Over.mk (f.left.imageι ≫ H.hom)),
        IsClosedSubgroupScheme
          (Over.homMk (U := Over.mk (f.left.imageι ≫ H.hom)) (V := H) f.left.imageι) ∧
        Set.range (fun x : 𝟙_ (Over (Spec (.of L))) ⟶ G ↦ x ≫ f) =
          Set.range (fun x : 𝟙_ (Over (Spec (.of L))) ⟶
              Over.mk (f.left.imageι ≫ H.hom) ↦
            x ≫ Over.homMk (V := H) f.left.imageι)) ∧
    (∀ [ConnectedSpace G.left] (K : Over (Spec (.of L))) [GrpObj K]
        (i : K ⟶ G) [IsClosedSubgroupScheme i],
      (Function.Bijective (GrpObj.differential i) → IsIso i.left) ∧
      (topologicalKrullDim K.left = topologicalKrullDim G.left → IsIso i.left)) := by
  sorry

end AlgebraicGeometry

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousQuotient
public import Sheaf.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Sites.Precoverage
import Sheaf.AlgebraicGeometry.GroupScheme.IdentityLocalDimension
import Sheaf.AlgebraicGeometry.DimZeroFiniteOverField
import WeilConjectures.AlgebraicGeometry.Dimension
import WeilConjectures.AlgebraicGeometry.IsFiniteOfFpqcCover
import WeilConjectures.AlgebraicGeometry.FlatOfFpqcCover
import WeilConjectures.AlgebraicGeometry.LocallyOfFinitePresentationFpqcDescent
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Nested homogeneous quotients and translated fibres

Source: Milne, Algebraic Groups (2017), Proposition 7.15 and Remark 7.16(a),(b),
printed pp.142--143; Proposition 5.23, printed p.104. Identity components:
Stacks Project, Tags 0B7R, 047R, 047P and 047N.
(blueprint: lem-sfb-nested-homogeneous-quotient-geometry)

Quotients are arbitrary presentations with precisely the properties furnished by
`exists_homogeneousQuotient`; no choice of a quotient scheme is imposed.
Products and pullbacks below are in the category of schemes over Spec k.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- Nested closed subgroups give the canonical faithfully flat finitely presented
quotient morphism, its translated-fibre isomorphism, and finiteness in equal dimension.
The equations on all test schemes specify the displayed isomorphisms on cosets, including
nilpotent test schemes. Uniqueness of π is among all maps compatible with the quotient maps.

Source: Milne, Proposition 7.15, Remark 7.16(a),(b), pp.142--143, and
Proposition 5.23, p.104 (blueprint: lem-sfb-nested-homogeneous-quotient-geometry).

Proof (steps 1--6 of the node):
1. Apply lem-sfb-algebraic-group-homogeneous-quotient to (G,H), (G,J), (J,H).
   Closed subgroups are separated and finite type. Their quotient maps are fpqc.
   J/H is flat over k; pqf-lem-lft-fp-locnoeth makes it locally finitely presented.
2. The H-coset criterion and H ⊆ J show that qJ agrees on the kernel pair of qH.
   Descend qJ using lem-weil-pbc-fpqc-representable-descent, giving the unique π.
3. Descend (g,j) ↦ (g,qH(gj)) along 1 × r. For the inverse, fpqc locally lift x to a
   in G. The J-coset criterion gives j = g⁻¹a in J; its H-coset is independent of a.
   Gluing by representable descent gives the inverse. Group cancellation verifies
   both composites; lem-galois-fpqc-covering-base-change supplies all local covers.
4. The pullback of π is the projection G × (J/H) → G. Base change preserves flatness
   and local finite presentation; lem-weil-pbc-fpqc-descend-flat and
   lem-weil-pbc-fpqc-descend-locally-finite-presentation descend them. Surjectivity
   follows from qJ = qH ≫ π. Use lem-weil-pbc-qcqs-morphism-permanence for qcqs.
5. Pull the isomorphism back along g : Spec k → G; def-pc-fibre-product identifies
   this with the whole fibre over qJ(g), with map jH ↦ gjH.
6. By lem-sfb-homogeneous-quotient-krull-dimension, equal subgroup dimensions make
   J/H zero-dimensional. Use lem-pc-scheme-dimension-local-rings and
   lem-pc-algebraic-dim-zero-affine-finite, then finite-morphism base change and
   lem-weil-pbc-fpqc-descend-finite along qJ to conclude finiteness of π. -/
theorem nested_homogeneousQuotient_geometry
    (k : Type u) [Field k] [IsAlgClosed k]
    (G H J : Over (Spec (.of k))) [GrpObj G] [GrpObj H] [GrpObj J]
    [IsAffine G.left] [Smooth G.hom] [ConnectedSpace G.left]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    (i : H ⟶ J) (j : J ⟶ G) [IsClosedSubgroupScheme i] [IsClosedSubgroupScheme j]
    (X Y Z : Over (Spec (.of k))) (qH : G ⟶ X) (qJ : G ⟶ Y) (r : J ⟶ Z)
    (hX : IsSeparated X.hom ∧ LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom ∧
      Flat qH.left ∧ Surjective qH.left ∧ LocallyOfFinitePresentation qH.left ∧
      QuasiCompact qH.left ∧ QuasiSeparated qH.left ∧
      (∀ (T : Over (Spec (.of k))) (a b : T ⟶ G),
        a ≫ qH = b ≫ qH ↔ a⁻¹ * b ∈ Set.range (fun l : T ⟶ H ↦ l ≫ (i ≫ j))) ∧
      (∀ (T : Over (Spec (.of k))) (x : T ⟶ X),
        ∃ (I : Type u) (T' : I → Over (Spec (.of k))) (f : ∀ t, T' t ⟶ T),
          Presieve.ofArrows (fun t ↦ (T' t).left) (fun t ↦ (f t).left) ∈
            Scheme.fpqcPrecoverage T.left ∧
          ∀ t, ∃ a : T' t ⟶ G, a ≫ qH = f t ≫ x))
    (hY : IsSeparated Y.hom ∧ LocallyOfFiniteType Y.hom ∧ QuasiCompact Y.hom ∧
      Flat qJ.left ∧ Surjective qJ.left ∧ LocallyOfFinitePresentation qJ.left ∧
      QuasiCompact qJ.left ∧ QuasiSeparated qJ.left ∧
      (∀ (T : Over (Spec (.of k))) (a b : T ⟶ G),
        a ≫ qJ = b ≫ qJ ↔ a⁻¹ * b ∈ Set.range (fun l : T ⟶ J ↦ l ≫ j)) ∧
      (∀ (T : Over (Spec (.of k))) (x : T ⟶ Y),
        ∃ (I : Type u) (T' : I → Over (Spec (.of k))) (f : ∀ t, T' t ⟶ T),
          Presieve.ofArrows (fun t ↦ (T' t).left) (fun t ↦ (f t).left) ∈
            Scheme.fpqcPrecoverage T.left ∧
          ∀ t, ∃ a : T' t ⟶ G, a ≫ qJ = f t ≫ x))
    (hZ : IsSeparated Z.hom ∧ LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom ∧
      Flat r.left ∧ Surjective r.left ∧ LocallyOfFinitePresentation r.left ∧
      QuasiCompact r.left ∧ QuasiSeparated r.left ∧
      (∀ (T : Over (Spec (.of k))) (a b : T ⟶ J),
        a ≫ r = b ≫ r ↔ a⁻¹ * b ∈ Set.range (fun l : T ⟶ H ↦ l ≫ i)) ∧
      (∀ (T : Over (Spec (.of k))) (x : T ⟶ Z),
        ∃ (I : Type u) (T' : I → Over (Spec (.of k))) (f : ∀ t, T' t ⟶ T),
          Presieve.ofArrows (fun t ↦ (T' t).left) (fun t ↦ (f t).left) ∈
            Scheme.fpqcPrecoverage T.left ∧
          ∀ t, ∃ a : T' t ⟶ J, a ≫ r = f t ≫ x)) :
    ∃ π : X ⟶ Y,
      qH ≫ π = qJ ∧
      (∀ π' : X ⟶ Y, qH ≫ π' = qJ → π' = π) ∧
      Flat π.left ∧ Surjective π.left ∧ LocallyOfFinitePresentation π.left ∧
      QuasiCompact π.left ∧ QuasiSeparated π.left ∧
      (∃ e : G ⊗ Z ≅ pullback qJ π,
        e.hom ≫ pullback.fst qJ π = fst G Z ∧
        ∀ (T : Over (Spec (.of k))) (g : T ⟶ G) (a : T ⟶ J),
          lift g (a ≫ r) ≫ e.hom ≫ pullback.snd qJ π = (g * (a ≫ j)) ≫ qH) ∧
      (∀ g : 𝟙_ (Over (Spec (.of k))) ⟶ G,
        ∃ e : Z ≅ pullback π (g ≫ qJ),
          r ≫ e.hom ≫ pullback.fst π (g ≫ qJ) =
            ((toUnit J ≫ g) * j) ≫ qH) ∧
      (topologicalKrullDim H.left = topologicalKrullDim J.left → IsFinite π.left) := by
  sorry

/-- For an arbitrary closed subgroup J, the reduction of its clopen identity component
is a smooth connected subgroup of the same dimension, and its homogeneous quotient maps
finitely and faithfully flatly to G/J. U has the actual open-subscheme structure and its
reduction is the nilradical subscheme, rather than an unspecified reduced model.

Source: Milne, Remark 7.16(b), p.143; Stacks Project, Tags 0B7R, 047R, 047P and 047N
(blueprint: lem-sfb-nested-homogeneous-quotient-geometry).

Proof (step 7 of the node, using steps 1--6 as above):
1. Apply lem-sfb-locally-algebraic-group-identity-component to J to obtain the clopen
   neutral component U and its smooth connected reduction H with its subgroup structure.
2. The inclusion H → J is closed: its ideal is the nilradical on U and the unit ideal
   on the complementary clopen. Composing with J → G gives a closed subgroup of G.
3. The identity local rings of J and U agree. Apply lem-ag-group-identity-local-dimension
   to both to get dim J = dim U; reduction is a homeomorphism, so dim H = dim U.
4. Apply lem-sfb-algebraic-group-homogeneous-quotient to (G,H). Steps 1--6 of
   lem-sfb-nested-homogeneous-quotient-geometry give the unique compatible map to Y,
   finite by equal dimension, flat and surjective. -/
theorem reduced_identityComponent_homogeneousQuotient_finite
    (k : Type u) [Field k] [IsAlgClosed k]
    (G J : Over (Spec (.of k))) [GrpObj G] [GrpObj J]
    [IsAffine G.left] [Smooth G.hom] [ConnectedSpace G.left]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    (j : J ⟶ G) [IsClosedSubgroupScheme j]
    (Y : Over (Spec (.of k))) (qJ : G ⟶ Y)
    (hY : IsSeparated Y.hom ∧ LocallyOfFiniteType Y.hom ∧ QuasiCompact Y.hom ∧
      Flat qJ.left ∧ Surjective qJ.left ∧ LocallyOfFinitePresentation qJ.left ∧
      QuasiCompact qJ.left ∧ QuasiSeparated qJ.left ∧
      (∀ (T : Over (Spec (.of k))) (a b : T ⟶ G),
        a ≫ qJ = b ≫ qJ ↔ a⁻¹ * b ∈ Set.range (fun l : T ⟶ J ↦ l ≫ j)) ∧
      (∀ (T : Over (Spec (.of k))) (x : T ⟶ Y),
        ∃ (I : Type u) (T' : I → Over (Spec (.of k))) (f : ∀ t, T' t ⟶ T),
          Presieve.ofArrows (fun t ↦ (T' t).left) (fun t ↦ (f t).left) ∈
            Scheme.fpqcPrecoverage T.left ∧
          ∀ t, ∃ a : T' t ⟶ G, a ≫ qJ = f t ≫ x)) :
    ∃ U : J.left.Opens,
      (U : Set J.left) = connectedComponent (GrpObj.onePoint J) ∧
      IsClosed (U : Set J.left) ∧
      Smooth (U.toScheme.nilradical.subschemeι ≫ U.ι ≫ J.hom) ∧
      ConnectedSpace U.toScheme.nilradical.subscheme ∧
      topologicalKrullDim U.toScheme.nilradical.subscheme = topologicalKrullDim J.left ∧
      ∃ gH : GrpObj (Over.mk (U.toScheme.nilradical.subschemeι ≫ U.ι ≫ J.hom)),
        @IsClosedSubgroupScheme k _ _ J gH _
          (Over.homMk (U.toScheme.nilradical.subschemeι ≫ U.ι)) ∧
        ∃ (X : Over (Spec (.of k)))
            (qH : G ⟶ X) (π : X ⟶ Y),
          IsSeparated X.hom ∧ LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom ∧
          Flat qH.left ∧ Surjective qH.left ∧ LocallyOfFinitePresentation qH.left ∧
          QuasiCompact qH.left ∧ QuasiSeparated qH.left ∧
          (∀ (T : Over (Spec (.of k))) (a b : T ⟶ G),
            a ≫ qH = b ≫ qH ↔ a⁻¹ * b ∈ Set.range
              (fun h : T ⟶ Over.mk (U.toScheme.nilradical.subschemeι ≫ U.ι ≫ J.hom) ↦
                h ≫ Over.homMk (U.toScheme.nilradical.subschemeι ≫ U.ι) ≫ j)) ∧
          (∀ (T : Over (Spec (.of k))) (x : T ⟶ X),
            ∃ (I : Type u) (T' : I → Over (Spec (.of k))) (f : ∀ t, T' t ⟶ T),
              Presieve.ofArrows (fun t ↦ (T' t).left) (fun t ↦ (f t).left) ∈
                Scheme.fpqcPrecoverage T.left ∧
              ∀ t, ∃ a : T' t ⟶ G, a ≫ qH = f t ≫ x) ∧
          qH ≫ π = qJ ∧
          (∀ π' : X ⟶ Y, qH ≫ π' = qJ → π' = π) ∧
          IsFinite π.left ∧ Flat π.left ∧ Surjective π.left := by
  sorry

end AlgebraicGeometry

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q149
-/
module

public import Sheaf.AlgebraicGeometry.SolvableGroupStructure
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.RingTheory.Finiteness.Subalgebra
import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
import Mathlib.RingTheory.FinitePresentation
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import Sheaf.AlgebraicGeometry.FinitePresentationFamilyDescent
import WeilConjectures.AlgebraicGeometry.DescendAffine
import Mathlib.RingTheory.FiniteStability
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.CategoryTheory.Yoneda
import Sheaf.AlgebraicGeometry.DescendSmoothQcqs
import WeilConjectures.AlgebraicGeometry.DescendClosedImmersion
import WeilConjectures.AlgebraicGeometry.DescendFlatFinitePresentation
import WeilConjectures.AlgebraicGeometry.DescendSurjective
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Sheaf.AlgebraicGeometry.StandardGroupSchemes
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
import Sheaf.AlgebraicGeometry.GroupScheme.SmoothUnipotentExtension

/-! # Spreading a specified normal unipotent subgroup

Source: Conrad, Reductive group schemes, Exercise 3.4.1(i)-(ii), printed p.104;
Milne, Algebraic Groups (2017), Corollary 16.24 and Section 6.45.
(blueprint: lem-sfb-normal-unipotent-subgroup-spreading)
-/

@[expose] public noncomputable section

set_option autoImplicit false


universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj

namespace AlgebraicGeometry.NormalUnipotentSubgroupSpreading

/-- Pull back group schemes along the spectrum of the specified ring homomorphism.
This is the actual pullback functor with its induced group operations.
Source: Conrad, Exercise 3.4.1(ii)
(blueprint: lem-sfb-normal-unipotent-subgroup-spreading). -/
abbrev scalarChange {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    Grp (Over (Spec (.of R))) ⥤ Grp (Over (Spec (.of S))) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom f))).mapGrp

/-- The canonical projection from a scalar extension to its original group scheme.
Source: Conrad, Exercise 3.4.1(ii)
(blueprint: lem-sfb-normal-unipotent-subgroup-spreading). -/
abbrev projection {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (G : Grp (Over (Spec (.of R)))) : ((scalarChange f).obj G).X.left ⟶ G.X.left :=
  pullback.fst G.X.hom (Spec.map (CommRingCat.ofHom f))

/-- Compatibility of the specified inclusion with the model's scalar extension.
The comparison is an isomorphism over K preserving multiplication, and its two
composites to J agree. With their common K-structure this fixes the map to J_K.
Source: Conrad, Exercise 3.4.1(ii)
(blueprint: lem-sfb-normal-unipotent-subgroup-spreading). -/
def IdentifiesInclusion
    {F K : Type u} [Field F] [Field K] [Algebra F K]
    (J : Grp (Over (Spec (.of F)))) (N : Grp (Over (Spec (.of K))))
    (i : N ⟶ (scalarChange (algebraMap F K)).obj J)
    (A : Subalgebra F K) (M : Grp (Over (Spec (.of A))))
    (j : M ⟶ (scalarChange (algebraMap F A)).obj J) : Prop :=
  ∃ e : ((scalarChange A.val.toRingHom).obj M).X ≅ N.X, IsMonHom e.hom ∧
    projection A.val.toRingHom M ≫ j.hom.hom.left ≫ projection (algebraMap F A) J =
      e.hom.left ≫ i.hom.hom.left ≫ projection (algebraMap F K) J

/-- A specified smooth connected nontrivial closed normal unipotent subgroup over an
algebraically closed extension spreads to a finitely generated subalgebra, with all
geometric fibres retaining these properties. The final equation fixes the inclusion:
after the group isomorphism, its projection to J is the given inclusion's projection.
Together with being over Spec K this identifies the maps into the actual J_K pullback.

Source: Conrad, Reductive group schemes, Exercise 3.4.1(i)-(ii), printed p.104;
Milne, Algebraic Groups (2017), Corollary 16.24 and Section 6.45.
(blueprint: lem-sfb-normal-unipotent-subgroup-spreading)

Proof plan, following the eight steps of the DAG node:
1. K is perfect. Apply lem-sfb-perfect-unipotent-additive-series to N, which is affine
   of finite type as a closed subgroup of J_K. Nontriviality gives positive length.
   Use lem-sfb-affine-normal-quotient-geometry for fppf quotient maps to G_a, with
   the specified successive kernels. Finite type over a field is finite presentation
   by lem-weil-pbc-finite-type-noetherian-finite-presentation.
2. Finitely generated F-subalgebras of K form a directed set with union K. Apply
   lem-weil-pbc-limit-affine-transition, finite-presentation-family-descent and
   descend-affine to obtain affine models of the finitely many groups. Keep J_A,
   the identity group and G_a as the canonical models. Products are fibre products;
   finite-presentation-base-change-composition gives their finite presentation.
3. The arrow and equality clauses of thm-pd-spreading-out descend multiplication,
   unit, inverse, inclusions and quotient maps and all their identities. Normality
   on all algebras and lem-galois-yoneda-fully-faithful supply the conjugation map
   J_K times N to N; descend it and its identity in J along with the other maps.
4. Form each actual fibre product with the unit of G_a. Its coordinate algebra is
   a quotient by the single pulled-back coordinate. Descend the inverse of the
   kernel comparison and both inverse identities by thm-pd-spreading-out. Thus
   the kernel assertion, not merely the zero composite, holds at the stage.
5. Apply descend-smooth-qcqs, descend-closed-immersion,
   descend-flat-finite-presentation and descend-surjective to obtain all desired
   properties at one stage. All models and maps are affine of finite presentation.
   Base-change permanence retains earlier properties under further refinement.
   The descended conjugation identity proves normality on every A-algebra;
   the closed immersion gives injectivity there.
6. At every algebraically closed E receiving A, base change preserves smoothness,
   closed immersions, flatness, surjectivity, finite presentation and the kernel
   squares. Each quotient map is an fppf cover, so sections lift fppf locally and
   two lifts differ by the specified kernel. The fppf-to-fpqc comparison and
   fpqc-representable-descent identify the represented fppf quotient with G_a.
7. Induct backwards along the series from the trivial group. The affine-space
   smoothness and affine-projection connected-fibre results apply to G_a, whose
   faithful two-dimensional upper unitriangular representation is unipotent.
   Apply lem-sfb-exact-algebraic-group-property-permanence for connectedness and
   lem-sfb-smooth-unipotent-extension for the recorded geometric matrix unipotence.
8. Positive length gives a surjection from the first group to G_a on every fibre.
   The trivial group maps only to its zero section, which misses 1, so each fibre
   is nontrivial. The descended inclusion and comparison isomorphism identify its
   K-base change with the given inclusion. No reductivity or connectedness of J
   and no perfectness of F were used.
-/
theorem exists_model
    {F K : Type u} [Field F] [Field K] [Algebra F K] [IsAlgClosed K]
    (J : Grp (Over (Spec (.of F))))
    [Smooth J.X.hom] [IsAffineHom J.X.hom]
    [LocallyOfFiniteType J.X.hom] [QuasiCompact J.X.hom]
    (N : Grp (Over (Spec (.of K))))
    (i : N ⟶ (scalarChange (algebraMap F K)).obj J)
    [IsClosedSubgroupScheme i.hom.hom] [IsNormalSubgroupScheme i.hom.hom]
    [Smooth N.X.hom] [ConnectedSpace N.X.left]
    (hN : SolvableGroupStructure.IsUnipotent N)
    (hne : ¬ Nonempty (N ≅ Grp.trivial (Over (Spec (.of K))))) :
    ∃ (A : Subalgebra F K), A.FG ∧
      ∃ (M : Grp (Over (Spec (.of A))))
        (j : M ⟶ (scalarChange (algebraMap F A)).obj J),
        Smooth M.X.hom ∧ IsAffineHom M.X.hom ∧
        LocallyOfFinitePresentation M.X.hom ∧
        IsClosedImmersion j.hom.hom.left ∧
        (∀ (B : Type u) [CommRing B] [Algebra A B],
          (IsMonHom.monoidHom j.hom.hom
            (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A B))))).range.Normal) ∧
        IdentifiesInclusion J N i A M j ∧
        ∀ (E : Type u) [Field E] [IsAlgClosed E] (a : A →+* E),
          ¬ Nonempty ((scalarChange a).obj M ≅ Grp.trivial (Over (Spec (.of E)))) ∧
          Smooth ((scalarChange a).obj M).X.hom ∧
          ConnectedSpace ((scalarChange a).obj M).X.left ∧
          SolvableGroupStructure.IsUnipotent ((scalarChange a).obj M) ∧
          IsClosedSubgroupScheme ((scalarChange a).map j).hom.hom ∧
          IsNormalSubgroupScheme ((scalarChange a).map j).hom.hom := by
  sorry

end AlgebraicGeometry.NormalUnipotentSubgroupSpreading

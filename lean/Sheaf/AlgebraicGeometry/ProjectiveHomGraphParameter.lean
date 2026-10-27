/-
Copyright (c) 2026 SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q67
-/
module

public import Sheaf.AlgebraicGeometry.RelativeMorphismsPresheaf
public import Sheaf.AlgebraicGeometry.ProjectiveFibreHilbertPolynomial
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Stalk
import Sheaf.AlgebraicGeometry.GraphsOpenInHilbert
import Sheaf.AlgebraicGeometry.ProjectiveHilbertPolynomialRepresentability
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.Topology.NoetherianSpace

/-! # Projective Hom parameters and the reduced closure of a generic point

Source: Stacks Project, quot.tex, Tags 0D1A--0D1B; schemes.tex, Tag 01J3;
de Jong, Families of curves and alterations, Section 3.9, printed p.609.
(blueprint: lem-sfb-projective-hom-graph-parameter)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- The relative morphism functor is the disjoint union of its graph-polynomial components,
which are open in H-projective finite-type schemes. `RepresentableBy` includes naturality
of the classifying bijections for every test-scheme morphism, hence arbitrary base change.
Evaluation is written as a map to `Q`; pairing it with the parameter projection gives the
stated map to `Q_M`. The same convention is used for a generic relative morphism.

The ideal `I` is required to be exactly the vanishing ideal of the closure of the image
of the classifying point, so `I.subscheme` is its actual reduced closure. The pullback
square with top-right and top-left both `Spec k(S)` identifies its generic fibre canonically
with `Spec k(S)`. The function-field isomorphism is normalized by the same generic map.
The last identity is the restriction of universal evaluation to this closure, pulled back
to that generic fibre. There are no assumptions on nodal fibres, normality or rational maps.

Source: Stacks Project, Tags 0D1A--0D1B and 01J3; de Jong, Families of curves and
alterations, Section 3.9, printed p.609.
(blueprint: lem-sfb-projective-hom-graph-parameter)

Proof plan, following the nine steps of the node:
1. Apply lem-sfb-projective-hilbert-polynomial-representability to the specified closed
   embedding of `W ×_S Q`. It requires no flatness of this ambient scheme. Its components
   are H-projective, separated and finite type, with universal families under base change.
2. By lem-kun-projective-implies-proper both source and target are proper. Apply
   lem-sfb-graphs-open-in-hilbert using flatness and finite presentation of the source.
   The proper and projective Hilbert functors agree since the ambient scheme is proper,
   using lem-weil-pbc-proper-base-change and lem-weil-pbc-closed-immersion-proper.
   The open graph locus represents the relative morphism functor and gives evaluation.
3. Intersect the graph locus with the open and closed polynomial components. A point
   over the function field belongs to one component, as does its topological closure.
4. Apply lem-weil-pbc-reduced-induced-closed-subscheme to that closure. The same reduced
   induced structure is closed inside the selected component. A one-point closure is
   nonempty irreducible, and its reduced structure is integral by def-pc-integral-scheme.
5. Each projective Hilbert component is Noetherian by
   lem-weil-pbc-finite-type-over-noetherian. Its closed subsets have the minimal condition
   by lem-weil-pbc-noetherian-scheme-closed-subsets-minimal, so every subset is compact
   by lem-sfb-noetherian-space-compact-subsets. Thus the open graph component is
   quasi-compact over its Hilbert component and finite type by
   lem-weil-pbc-qc-open-immersion-finite-type. The closure inclusion is finite type by
   lem-weil-pbc-closed-immersion-proper. Compose using
   lem-sfb-finite-type-composition-base-change, and use pqf-lem-lft-fp-locnoeth.
6. The composite immersion in the separated Hilbert component is a monomorphism.
   Pulling back its closed diagonal gives the closure's diagonal, by def-pc-fibre-product
   and lem-weil-pbc-closed-immersion-base-change. Hence the closure is separated over S.
7. On affine charts over `Spec A` in S, the generic point gives `B → K`. Its prime kernel
   cuts out the reduced closure, by the affine formula in
   lem-weil-pbc-reduced-induced-closed-subscheme. The injections `B/ker → K` glue the
   factorization of the classifying point through the closure.
8. By lem-sc-integral-function-field-affine-fraction, `K = Frac A`. For
   `A ⊆ D = B/ker ⊆ K`, localization gives `D ⊗_A K = K` and `Frac D = K`.
   The chart identifications of lem-weil-pbc-fibre-product-affine-spectra and
   lem-weil-pbc-open-fibre-product glue the canonical generic-fibre identification.
   The same fraction-field lemma identifies the closure's function field with K.
9. Restrict the universal evaluation to the actual closure. Naturality of the classifying
   bijections shows its pullback along the generic factorization is the original map.
   Step 8 identifies this pullback with its generic fibre. -/
theorem exists_projective_hom_graph_parameter
    (S : Scheme.{u}) [IsLocallyNoetherian S] [CompactSpace S] [IsIntegral S]
    {W Q : Scheme.{u}} (f : W ⟶ S) (g : Q ⟶ S)
    [IsHProjective f] [Flat f] [LocallyOfFinitePresentation f] [IsHProjective g]
    (N : ℕ) (i : pullback f g ⟶ ℙ(ULift.{u} (Fin (N + 1)); S))
    [IsClosedImmersion i]
    (hi : i ≫ (ℙ(ULift.{u} (Fin (N + 1)); S) ↘ S) = pullback.fst f g ≫ f) :
    ∃ (M : Over S) (e : (relativeMorphismsPresheaf f g).RepresentableBy M)
      (MP HP : NumericalHilbertPolynomial → Over S) (μ : ∀ P, MP P ⟶ M)
      (j : ∀ P, MP P ⟶ HP P),
      Nonempty (IsColimit (Cofan.mk M μ)) ∧
      (∀ P, IsHProjective (HP P).hom ∧ LocallyOfFiniteType (HP P).hom ∧
        QuasiCompact (HP P).hom ∧ IsOpenImmersion (j P).left) ∧
      (∀ (P : NumericalHilbertPolynomial) (T : Over S) (a : T ⟶ M),
        HasProjectiveFibreHilbertPolynomial (pullback.fst f g ≫ f) i T
          (relativeMorphismGraph f g T (e.homEquiv a)).ker P.1 ↔
            ∃! b : T ⟶ MP P, b ≫ μ P = a) ∧
      ∃ ev : pullback M.hom f ⟶ Q,
        ev = (e.homEquiv (𝟙 M)).left ∧
        (∀ (T : Over S) (a : T ⟶ M),
          (e.homEquiv a).left = ((Over.pullback f).map a).left ≫ ev) ∧
        (∀ uη : (relativeMorphismsPresheaf f g).obj
            (op (Over.mk (S.fromSpecStalk (genericPoint S)))),
          ∃ (m : Over.mk (S.fromSpecStalk (genericPoint S)) ⟶ M),
            e.homEquiv m = uη ∧
            ∃ (P : NumericalHilbertPolynomial)
              (mP : Over.mk (S.fromSpecStalk (genericPoint S)) ⟶ MP P)
              (I : M.left.IdealSheafData),
              mP ≫ μ P = m ∧
              I = Scheme.IdealSheafData.vanishingIdeal (.closure (Set.range m.left)) ∧
              ∃ (hR : IsIntegral I.subscheme)
                (a : Over.mk (S.fromSpecStalk (genericPoint S)) ⟶
                  Over.mk (I.subschemeι ≫ M.hom))
                (c : I.subscheme ⟶ (MP P).left),
                IsClosedImmersion c ∧ c ≫ (μ P).left = I.subschemeι ∧
                IsSeparated (I.subschemeι ≫ M.hom) ∧
                LocallyOfFiniteType (I.subschemeι ≫ M.hom) ∧
                QuasiCompact (I.subschemeι ≫ M.hom) ∧
                LocallyOfFinitePresentation (I.subschemeι ≫ M.hom) ∧
                a.left ≫ I.subschemeι = m.left ∧
                IsPullback a.left (𝟙 (Spec S.functionField))
                  (I.subschemeι ≫ M.hom) (S.fromSpecStalk (genericPoint S)) ∧
                (∃ eK : I.subscheme.functionField ≅ S.functionField,
                  Spec.map eK.hom ≫ I.subscheme.fromSpecStalk (genericPoint I.subscheme) =
                    a.left) ∧
                ((Over.pullback f).map a).left ≫
                  ((Over.pullback f).map (Over.homMk I.subschemeι rfl)).left ≫ ev =
                    uη.left) := by
  sorry

end AlgebraicGeometry

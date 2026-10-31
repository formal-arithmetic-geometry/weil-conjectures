/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Comma.Over.Pullback
import WeilConjectures.AlgebraicGeometry.Morphisms.ProjectiveBaseChange
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Product
import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.CurveDegreeTensorAdditive
import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Representability
import Mathlib.AlgebraicGeometry.Gluing

/-!
# Isomorphism graphs of projective flat curves

Source: Stacks Project, Tag 0DSQ; scheme realization by projective graphs using
Tags 0D01, 0D1B, 0DPN and 0DPP (blueprint: lem-sfb-projective-curve-isom-graphs).

Base changes are written `T ×_S X`, with projection to `T` first. Isomorphisms over `T`
are isomorphisms in `Over T`. Naturality uses the canonical pullback maps, so includes
nonreduced test schemes and arbitrary changes of base without a Noetherian hypothesis
on the new base. Closed subschemes are represented by their closed immersions; changing
the source of an immersion by an isomorphism gives the same closed subscheme.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The isomorphism functor of two projective flat finitely presented families with
geometric fibres of dimension at most one is a separated scheme of finite presentation.
The bijections are natural for every morphism of test schemes. A point determines a
closed graph with invertible projections, and the inverse-projection formula recovers
its isomorphism. Conversely every such closed subscheme determines a unique point.

Source: Stacks Project, Tag 0DSQ (lemma-curves-diagonal-separated-fp), with the scheme
realization from Tags 0D01, 0D1B, 0DPN and 0DPP
(blueprint: lem-sfb-projective-curve-isom-graphs).

Proof:
1. Choose projective embeddings and their degree-one invertible modules L and N.
   Projectivity gives properness (lem-pc-projective-proper). Restrict over Noetherian
   affine opens of S, using lem-pc-projective-base-change and the qcqs permanence
   lemmas. Segre embeds the product with polarization pr_X^*L tensor pr_Y^*N
   (lem-chow-segre).
2. Shrink the affine opens so the four fibre Euler characteristics of O_X, L, O_Y, N
   are constant (lem-sfb-proper-flat-sheaf-euler-local-constancy). Denote the resulting
   linear polynomials by P_X and P_Y; their values persist after field base change.
3. The projective Hilbert scheme is the disjoint union of its projective polynomial
   strata (lem-sfb-projective-hilbert-polynomial-representability). Intersect the two
   graph opens on which the first and second projections are isomorphisms
   (lem-sfb-graphs-open-in-hilbert, applied also after exchanging the factors).
4. The two inverse constructions send a graph to p_Y composed with p_X inverse,
   and an isomorphism to its graph. The identities for projections and their inverses
   persist under all pullbacks, including pullback to nonreduced test schemes.
5. Tensor-degree additivity for arbitrary proper schemes of dimension at most one
   (lem-trf-curve-degree-tensor-additive) gives the fixed graph Euler polynomial
   R(n) = P_X(n) + P_Y(n) - P_Y(0). Pullback by an isomorphism preserves Euler
   characteristic. Segre identifies the polarization with O(1); the eventual
   coordinate-ring/Euler comparison identifies R with the Hilbert polynomial
   (lem-sfb-projective-coordinate-ring-euler-polynomial). Empty fibres have polynomial
   zero, and unequal constant Euler characteristics give no isomorphisms.
6. Thus the double graph open lies in the single Noetherian projective stratum H_R.
   Its open subscheme is Noetherian and quasi-compact; it is separated and locally
   of finite presentation, hence of finite presentation over the affine base
   (lem-weil-pbc-finite-type-over-noetherian, the Noetherian-open lemma,
   lem-weil-pbc-proper-fp-permanence, qcqs permanence, pqf-lem-lft-fp-locnoeth).
7. Isomorphisms and their inverses glue uniquely on base-open covers by
   lem-weil-pbc-scheme-morphism-gluing. Hence the isomorphism functor is a Zariski sheaf.
8. These local graph representatives form representable open subfunctors covering
   that sheaf. Glue them by lem-pc-schemes-criterion. Their overlap identifications
   preserve graphs, since the representing formulas agree.
9. Separatedness, local finite presentation and quasi-compactness are local on the
   target (lem-sfb-separated-lfp-target-open-locality,
   lem-pc-quasi-compact-local-on-target). The closed diagonal is quasi-compact, giving
   quasi-separatedness and therefore finite presentation. Naturality of the graph
   bijections identifies the pullback of J along any S' to S with the isomorphism
   functor of the pulled-back families, with no Noetherian condition on S'. -/
theorem exists_projective_curve_isom_graphs
    {S X Y : Scheme.{u}} [IsLocallyNoetherian S] (f : X ⟶ S) (g : Y ⟶ S)
    [IsHProjective f] [IsHProjective g] [Flat f] [Flat g]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    [LocallyOfFinitePresentation g] [QuasiCompact g] [QuasiSeparated g]
    (hX : ∀ s : S,
      topologicalKrullDim (pullback f
        (Spec.map (CommRingCat.ofHom
          (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
            S.fromSpecResidueField s) : Scheme.{u}) ≤ 1)
    (hY : ∀ s : S,
      topologicalKrullDim (pullback g
        (Spec.map (CommRingCat.ofHom
          (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
            S.fromSpecResidueField s) : Scheme.{u}) ≤ 1) :
    ∃ J : Over S, IsSeparated J.hom ∧ LocallyOfFinitePresentation J.hom ∧
      QuasiCompact J.hom ∧ QuasiSeparated J.hom ∧
      ∃ e : ∀ T : Over S, (T ⟶ J) ≃
        (Over.mk (pullback.fst T.hom f) ≅ Over.mk (pullback.fst T.hom g)),
        (∀ (T' T : Over S) (h : T' ⟶ T) (a : T ⟶ J),
          ((Over.pullback f).map h).left ≫ (e T a).hom.left =
            (e T' (h ≫ a)).hom.left ≫ ((Over.pullback g).map h).left) ∧
        (∀ (T : Over S) (a : T ⟶ J),
          ∃ (D : Scheme.{u})
            (i : D ⟶ pullback (pullback.fst T.hom f) (pullback.fst T.hom g)),
            IsClosedImmersion i ∧
            ∃ (p : D ≅ pullback T.hom f) (q : D ≅ pullback T.hom g),
              i ≫ pullback.fst _ _ = p.hom ∧
              i ≫ pullback.snd _ _ = q.hom ∧ p.inv ≫ q.hom = (e T a).hom.left) ∧
        (∀ (T : Over S) (D : Scheme.{u})
          (i : D ⟶ pullback (pullback.fst T.hom f) (pullback.fst T.hom g)),
          IsClosedImmersion i →
          ∀ (p : D ≅ pullback T.hom f) (q : D ≅ pullback T.hom g),
            i ≫ pullback.fst _ _ = p.hom → i ≫ pullback.snd _ _ = q.hom →
            ∃! a : T ⟶ J, (e T a).hom.left = p.inv ≫ q.hom) := by
  sorry

end AlgebraicGeometry

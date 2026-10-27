module

public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Sheaf.AlgebraicGeometry.SemisimpleGroupSchemePoint
public import Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces
public import Sheaf.AlgebraicGeometry.GroupNeutralComponentTranslates

import Sheaf.AlgebraicGeometry.ConstantSourceClosedFactorizationLocus
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.AlgebraicGeometry.TorusFixedSchemeSmooth
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.AlgebraicGeometry.GroupScheme.CentralMaximalTorusNilpotent
import Sheaf.AlgebraicGeometry.PerfectSolvableUnipotentTorus
import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
import Sheaf.AlgebraicGeometry.CentralTorusFaithfulWeightBlocks
import Sheaf.AlgebraicGeometry.GmRepresentationWeightBasis
import Sheaf.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import WeilConjectures.Mathlib.RingTheory.Nullstellensatz

/-! # Structure of the neutral centralizer of a maximal torus

Source: Milne, Algebraic Groups (2017), Proposition 17.28, p.360;
Theorem 16.47 and Corollary 16.48, p.341; proof of Theorem 17.33(a), p.362
(blueprint: lem-sfb-neutral-torus-centralizer-cartan-structure).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- The neutral centralizer is smooth, connected, solvable and a direct product of
its unipotent part and the given maximal torus. Its tori and semisimple rational
points lie in that torus, and its rational normalizer quotient is finite.
Source: Milne, Proposition 17.28, p.360; Theorem 16.47 and Corollary 16.48, p.341;
proof of Theorem 17.33(a), p.362
(blueprint: lem-sfb-neutral-torus-centralizer-cartan-structure).

Proof, following the nine steps of the node:
1. Apply lem-sfb-constant-source-closed-factorization-locus to (t,g) ↦ (tg,gt)
   and the diagonal of G. Affineness implies separatedness by
   lem-weil-pbc-affine-source-morphism-separated. The resulting closed locus F
   represents the centralizer on every algebra, including all further extensions.
   It is stable under multiplication and inversion. Under conjugation by T it is
   the fixed scheme, hence smooth by lem-sfb-torus-fixed-scheme-smooth.
2. By lem-sfb-group-neutral-component-translates, C = F⁰ is clopen and connected.
   It is smooth by lem-weil-pbc-smooth-restrict-open-subschemes. The Laurent
   polynomial coordinate ring of T is a domain, including rank zero, so T is
   connected. Its inclusion in F therefore factors through C by
   lem-weil-pbc-morphism-factors-through-open-subscheme. T is central in C and
   remains maximal there, since any larger torus would also be a torus in G.
3. Apply lem-sfb-central-maximal-torus-nilpotent to C. Its central series implies
   termination of the scheme-theoretic derived series and also the finite
   subnormal-series solvability needed by lem-sfb-perfect-solvable-unipotent-torus.
   Since k is perfect, the latter gives smooth connected normal unipotent U and
   a torus quotient D = C/U.
4. By lem-sfb-affine-normal-quotient-geometry, U is the scheme-theoretic kernel
   of q : C → D. By lem-sfb-solvable-torus-complements, q restricted to T is an
   isomorphism. Set τ = (q restricted to T)⁻¹q. Multiplication U × T → C has
   inverse c ↦ (cτ(c)⁻¹,τ(c)); the first coordinate lies in the kernel. Check both
   composites on every algebra. Centrality of T makes this a group isomorphism
   for the direct product law, with the displayed multiplication as its map.
5. Project any torus S in C to U. Use
   lem-sfb-geometric-unipotence-unitriangular-embedding and
   lem-sfb-diagonalizable-to-unipotent-trivial to see that this projection is
   trivial: a split torus is the diagonalizable group of its integer character
   lattice. Thus S factors through T. Applying this to an automorphism of C
   and its inverse shows that every automorphism preserves T.
6. Choose a faithful representation of G with
   lem-sfb-central-torus-faithful-weight-blocks, using the rank-zero central torus.
   Apply lem-sfb-gm-representation-weight-basis to the commuting factors of T
   to diagonalize T. If a semisimple point s of G lies in C, write it as ut.
   By lem-sfb-rational-representation-unipotent-point the matrix of u is unipotent.
   It commutes with the diagonalizable matrix of t. Uniqueness in
   lem-sfb-multiplicative-jordan-linear-compatibility makes the unipotent part
   of the diagonalizable matrix of s equal to 1. Faithfulness gives u = 1.
7. Represent the normalizer of C by intersecting the closed factorization loci
   for conjugation and inverse conjugation, using
   lem-sfb-constant-source-closed-factorization-locus. This is a closed affine
   finite-type subgroup P with exactly the stated normalizer points. By
   lem-sfb-locally-algebraic-group-identity-component, M = (P⁰)red is smooth,
   connected and has the same space as P⁰. C embeds into M: its image lies in
   P⁰ by connectedness and factors through the reduction by
   sbc-lem-smooth-geometrically-reduced.
8. Conjugation by M(k) preserves T by step 5. The closed factorization locus
   for T × M → C to land in T contains every rational point of reduced M.
   By lem-wf-affine-nullstellensatz-vanishing it is all of M, so conjugation
   restricts to T. By lem-sfb-connected-action-torus-rigidity this action is
   trivial. Hence M lands in F, and connectedness factors it through C by
   lem-weil-pbc-morphism-factors-through-open-subscheme. Thus M = C.
9. By lem-sfb-group-neutral-component-translates, P has finitely many components,
   each a rational translate of P⁰. Field-valued points kill nilpotents, so
   P⁰(k) = M(k) = C(k). Each component therefore gives one coset. Inversion
   identifies left and right coset sets, proving the displayed finiteness.
   No connectedness assertion about the full centralizer F is used. -/
theorem neutral_torus_centralizer_cartan_structure
    (k : Type u) [Field k] [IsAlgClosed k]
    (G T : Grp (Over (Spec (.of k))))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (iT : T ⟶ G) (hT : ReductiveTorusCentralizer.IsMaximalTorus iT) :
    ∃ (F : Grp (Over (Spec (.of k)))) (iF : F ⟶ G),
      IsClosedSubgroupScheme iF.hom.hom ∧
      ∃ (_ : LocallyOfFiniteType F.X.hom) (_ : QuasiCompact F.X.hom),
        (∀ (A : Type u) [CommRing A] [Algebra k A],
          Set.range (fun f : StandardGroupSchemes.affine k A ⟶ F.X ↦ f ≫ iF.hom.hom) =
            ReductiveTorusCentralizer.centralizerPoints iT A) ∧
        ∃ (C : Grp (Over (Spec (.of k))))
          (eC : C ≅ Grp.mk (GrpObj.identityComponent F.X))
          (iC : C ⟶ G) (jT : T ⟶ C),
          eC.hom.hom.hom ≫ GrpObj.identityComponentι F.X ≫ iF.hom.hom = iC.hom.hom ∧
          IsClosedSubgroupScheme iC.hom.hom ∧
          SolvableGroupStructure.IsAlgebraic C ∧
          Smooth C.X.hom ∧ ConnectedSpace C.X.left ∧
          IsSolvableGroupScheme C.X ∧
          jT ≫ iC = iT ∧
          (∃ (U : Grp (Over (Spec (.of k)))) (jU : U ⟶ C) (e : U ⊗ T ≅ C),
            IsClosedSubgroupScheme jU.hom.hom ∧
            SolvableGroupStructure.IsAlgebraic U ∧
            Smooth U.X.hom ∧ ConnectedSpace U.X.left ∧
            SolvableGroupStructure.IsUnipotent U ∧
            e.hom.hom.hom =
              (fst U.X T.X ≫ jU.hom.hom) * (snd U.X T.X ≫ jT.hom.hom)) ∧
          (∀ (S : Grp (Over (Spec (.of k)))) (jS : S ⟶ C),
            IsClosedSubgroupScheme jS.hom.hom → MultiplicativeType.IsTorus S →
              ∃ f : S ⟶ T, f ≫ jT = jS) ∧
          (∀ s : StandardGroupSchemes.affine k k ⟶ G.X,
            IsSemisimpleGroupSchemePoint G.X s →
              s ∈ Set.range (fun c : StandardGroupSchemes.affine k k ⟶ C.X ↦
                c ≫ iC.hom.hom) →
              s ∈ Set.range (fun t : StandardGroupSchemes.affine k k ⟶ T.X ↦
                t ≫ iT.hom.hom)) ∧
          Finite (RankOneRoots.Weyl iC) := by
  sorry

end AlgebraicGeometry

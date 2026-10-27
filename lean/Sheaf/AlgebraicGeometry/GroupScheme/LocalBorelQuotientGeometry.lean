module

public import Sheaf.AlgebraicGeometry.GroupScheme.RelativeAdjointWeights
public import Sheaf.AlgebraicGeometry.GroupScheme.Borel
public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.FinitePresentation
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.RingTheory.FiniteProjectivePrimeLocalFree
import Sheaf.AlgebraicGeometry.GroupScheme.BorelOppositeRootDichotomy
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
import Sheaf.AlgebraicGeometry.GroupScheme.BorelSchemeNormalizer

/-! # Borel quotients of split reductive groups over local rings

Source: Conrad, Reductive group schemes, Definition 5.1.1, Proposition 5.2.3,
Corollaries 5.2.5 and 5.2.8, Theorem 5.2.11 and Corollary 5.2.13, pp.136, 152--159.
(blueprint: lem-sfb-local-borel-quotient-geometry)

The quotient is characterized by its right-multiplication kernel pair and fppf
local lifts on all test schemes. These characterize the sheafification of the
presheaf of right cosets, including on nonaffine test schemes. We use actual
characters for the roots, so the statement is independent of a choice of basis
of X*(T) = Z^r. Character inversion is negation in that lattice.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- The radical, retraction, semidirect multiplication and represented fppf quotient
properties, for specified maps over any scheme S. The normality condition is on
all test schemes. The radical condition is maximality among smooth connected
normal unipotent subgroup schemes of each geometric fibre. The quotient conditions
are precisely the local-surjectivity and equivalence-relation characterization
of the fppf sheafification of right cosets.
Source: Conrad, Corollaries 5.2.5 and 5.2.8, pp.153--156.
(blueprint: lem-sfb-local-borel-quotient-geometry). -/
def LocalBorelGeometry {S : Scheme.{u}} {H T B U : Grp (Over S)}
    (j : T ⟶ B) (iB : B ⟶ H) (iU : U ⟶ B) (p : B ⟶ T)
    (Q : Over S) (π : H.X ⟶ Q) : Prop :=
  Smooth U.X.hom ∧ IsClosedImmersion iU.hom.hom.left ∧
  (∀ W : Over S, (IsMonHom.monoidHom iU.hom.hom W).range.Normal) ∧
  j ≫ p = 𝟙 T ∧
  IsPullback iU.hom.hom (toUnit U.X) p.hom.hom η[T.X] ∧
  IsIso ((fst T.X U.X ≫ j.hom.hom) * (snd T.X U.X ≫ iU.hom.hom)) ∧
  (∀ (F : Type u) [Field F] [IsAlgClosed F] (s : Spec (.of F) ⟶ S),
    ConnectedSpace ((Over.pullback s).mapGrp.obj U).X.left ∧
    SolvableGroupStructure.IsUnipotent ((Over.pullback s).mapGrp.obj U) ∧
    ∀ (N : Grp (Over (Spec (.of F))))
      (iN : N ⟶ (Over.pullback s).mapGrp.obj B),
      IsClosedSubgroupScheme iN.hom.hom → IsNormalSubgroupScheme iN.hom.hom →
      Smooth N.X.hom → ConnectedSpace N.X.left → SolvableGroupStructure.IsUnipotent N →
      ∃ f : N ⟶ (Over.pullback s).mapGrp.obj U,
        f ≫ (Over.pullback s).mapGrp.map iU = iN) ∧
  Smooth Q.hom ∧ IsProper Q.hom ∧
  Flat π.left ∧ Surjective π.left ∧ QuasiCompact π.left ∧
  LocallyOfFinitePresentation π.left ∧
  IsPullback (fst H.X B.X)
    (fst H.X B.X * (snd H.X B.X ≫ iB.hom.hom)) π π ∧
  ∀ (W : Over S) (x : W ⟶ Q),
    ∃ (I : Type u) (V : I → Over S) (f : ∀ i, V i ⟶ W),
      Presieve.ofArrows (fun i ↦ (V i).left) (fun i ↦ (f i).left) ∈
        Scheme.fppfPrecoverage W.left ∧
      ∀ i, ∃ g : V i ⟶ H.X, g ≫ π = f i ≫ x

/-- A Borel through a split maximal torus over a nonzero Noetherian local ring
has its relative unipotent radical and torus retraction, a smooth proper flag
quotient with a faithfully flat quasi-compact locally finitely presented torsor,
and a positive/negative root partition unchanged on every geometric fibre.
All geometric maps retain the stated properties after every scheme base change.

Source: Conrad, Definition 5.1.1, Proposition 5.2.3, Corollaries 5.2.5 and 5.2.8,
Theorem 5.2.11 and Corollary 5.2.13, pp.136, 152--159.
(blueprint: lem-sfb-local-borel-quotient-geometry).

Proof plan (the twelve steps of the DAG):
1. Finite-type algebras over A are Noetherian by
   lem-weil-pbc-finite-type-algebra-noetherian. Closed subgroup ideals are finite;
   lem-weil-pbc-finite-type-noetherian-finite-presentation gives all needed
   finite-presentation assertions for B, T and maps of affine groups.
2. Apply lem-sfb-relative-tangent-weight-base-change to conjugation on H and B.
   The finite projective weight summands are free over A by
   lem-weil-pbc-finite-projective-prime-local-free; their nonvanishing is detected
   on the closed geometric fibre. Tangent inclusions preserve the weights.
3. By lem-sfb-relative-diagonalizable-character-duality characters over the local
   base and over each geometric fibre have the same integer labels. Apply
   lem-sfb-borel-opposite-root-dichotomy on the closed fibre for the partition.
4. Choose a regular cocharacter on that fibre using
   lem-sfb-regular-cocharacter-borel-description and lift its integer tuple.
   The tangent formulas of lem-sfb-reductive-cocharacter-parabolic-geometry and
   lem-sfb-relative-dynamic-subgroups identify the nonnegative part with Lie(B).
   The weight maps are isomorphisms over A by the determinant unit criterion.
5. Form the dynamic subgroups of H and B with lem-sfb-relative-dynamic-subgroups.
   The nonnegative subgroup of B has its whole tangent module. Apply
   lem-sfb-smooth-subgroup-tangent-generation on each fibre and then
   lem-sfb-flat-geometric-fibre-open-criterion to identify it with B.
6. Embed B in the nonnegative subgroup of H; the same tangent and fibre argument
   identifies them. Regularity identifies the zero subgroup with T. The dynamic
   kernel U and evaluation p give the retraction and semidirect multiplication.
7. The fibrewise kernel is unipotent, connected and normal. By
   lem-sfb-reductive-borel-pair-structure it lies in the unipotent radical.
   Conversely lem-sfb-unipotent-to-multiplicative-trivial kills that radical
   under p, proving equality with the kernel on every geometric fibre.
8. Apply lem-sfb-relative-smooth-subgroup-normalizer to B. Its geometric fibres
   equal B by lem-sfb-borel-scheme-normalizer. The flat fibre criterion identifies
   B with its normalizer; lem-pc-smooth-flat supplies flatness of B, not of N.
9. Geometric flag quotients are projective by
   lem-sfb-reductive-cocharacter-parabolic-geometry. Apply
   lem-sfb-relative-self-normalizing-quotient for the smooth proper quotient,
   local lifts and right torsor. Smoothness gives flatness and local presentation.
10. H is Noetherian by lem-weil-pbc-finite-type-over-noetherian; inverse images
    of affine opens are quasi-compact by lem-sfb-noetherian-open-immersion-qc.
11. Both the dynamic subgroup construction and the self-normalizing quotient
    commute with arbitrary base change. Pull back all specified maps and their
    formulas; they agree on affine overlaps and under successive base changes.
12. If T = H, then B = H. There are no roots, the dynamic kernel is trivial,
    p is the identity and the coset sheaf is represented by the base. Rank zero,
    nonreduced A and arbitrary residue characteristic are included.
-/
theorem local_borel_quotient_geometry
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (H T B : Grp (Over (Spec (.of A))))
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [LocallyOfFinitePresentation H.X.hom]
    [Smooth T.X.hom] [Smooth B.X.hom]
    (j : T ⟶ B) (iB : B ⟶ H)
    [IsClosedImmersion j.hom.hom.left] [IsClosedImmersion iB.hom.hom.left]
    (r : ℕ) (e : T ≅ RingGroupSchemes.splitTorus A r)
    (hred : ∀ (F : Type u) [Field F] [IsAlgClosed F] [Algebra A F],
      ReductiveTorusCentralizer.IsReductive
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap A F)))).mapGrp.obj H))
    (hmax : ∀ (F : Type u) [Field F] [IsAlgClosed F] [Algebra A F],
      ReductiveTorusCentralizer.IsMaximalTorus
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap A F)))).mapGrp.map
          (j ≫ iB)))
    (hB : ∀ (F : Type u) [Field F] [IsAlgClosed F] [Algebra A F],
      IsBorelGroupScheme
        (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap A F)))).mapGrp.map
          iB).hom.hom)) :
    ∃ (U : Grp (Over (Spec (.of A)))) (iU : U ⟶ B) (p : B ⟶ T)
      (Q : Over (Spec (.of A))) (π : H.X ⟶ Q),
      LocalBorelGeometry j iB iU p Q π ∧
      (∀ (S' : Scheme.{u}) (f : S' ⟶ Spec (.of A)),
        LocalBorelGeometry ((Over.pullback f).mapGrp.map j)
          ((Over.pullback f).mapGrp.map iB) ((Over.pullback f).mapGrp.map iU)
          ((Over.pullback f).mapGrp.map p)
          ((Over.pullback f).obj Q) ((Over.pullback f).map π)) ∧
      (∀ χ : T ⟶ RingGroupSchemes.multiplicative A,
        (χ ∈ RelativeAdjointWeights.rootsOver (j ≫ iB) A ↔
          χ ∈ RelativeAdjointWeights.rootsOver j A ∨
          ∃ ψ ∈ RelativeAdjointWeights.rootsOver j A, χ.hom.hom = ψ.hom.hom⁻¹) ∧
        (χ ∈ RelativeAdjointWeights.rootsOver j A →
          ¬ ∃ ψ ∈ RelativeAdjointWeights.rootsOver j A, χ.hom.hom = ψ.hom.hom⁻¹)) ∧
      (∀ (F : Type u) [Field F] [IsAlgClosed F] [Algebra A F],
        Function.Bijective
          (fun χ : T ⟶ RingGroupSchemes.multiplicative A ↦
            (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap A F)))).mapGrp.map χ) ∧
        ∀ χ : T ⟶ RingGroupSchemes.multiplicative A,
          (χ ∈ RelativeAdjointWeights.rootsOver (j ≫ iB) A ↔
            χ ∈ RelativeAdjointWeights.rootsOver (j ≫ iB) F) ∧
          (χ ∈ RelativeAdjointWeights.rootsOver j A ↔
            χ ∈ RelativeAdjointWeights.rootsOver j F)) ∧
      (IsIso (j ≫ iB) → Nonempty (U ≅ Grp.trivial _) ∧ Nonempty (Q ≅ 𝟙_ _)) := by
  sorry

end AlgebraicGeometry

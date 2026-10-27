module

public import Sheaf.AlgebraicGeometry.SpaceDimensionFlatCondition
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.SpaceAffineHomComparison
public import Sheaf.TraceFormula.CompleteAlgebraDevissage
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.RingTheory.FinitePresentation
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Sheaf.AlgebraicGeometry.CompleteDevissageDimensionPreparation
import Sheaf.AlgebraicGeometry.SmoothTopDimensionRankDecomposition
import Sheaf.TraceFormula.LocalUIFlatCokernel
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # Local dimension-filtered flattening from a complete affine dévissage

Source: Stacks Project, flat.tex, Tag 05UF, using algebraic dévissage in Tag 05HX
and the all-chart formulation in spaces-flat.tex, Tag 0CWS
(blueprint: lem-sfb-affine-complete-devissage-dimension-flattening).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Spec A with its unique map to Spec Z; the terminal-slice equivalence retains
exactly the given scheme. Source: Stacks, Tags 05UF and 05HX, absolute-base convention
(blueprint: lem-sfb-affine-complete-devissage-dimension-flattening). -/
def affineDevissageScheme (A : Type u) [CommRing A] :
    Over (Spec (.of (ULift.{u} ℤ))) :=
  (Over.equivalenceOfIsTerminal specULiftZIsTerminal).inverse.obj (Spec (.of A))

/-- The map Spec A to Spec R induced by the specified algebra structure, over Spec Z.
Source: Stacks, Tags 05UF and 05HX
(blueprint: lem-sfb-affine-complete-devissage-dimension-flattening). -/
def affineDevissageArrow (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    affineDevissageScheme A ⟶ affineDevissageScheme R :=
  (Over.equivalenceOfIsTerminal specULiftZIsTerminal).inverse.map
    (Spec.map (CommRingCat.ofHom (algebraMap R A)))

/-- The actual global sections of M on Spec A, with A acting through the canonical
A to Gamma(Spec A,O) isomorphism. Restriction to the identity chart is the recorded
Zariski restriction, whose sections are the original small-étale sections on opens.
Source: Stacks, Tags 05UF and 03DX
(blueprint: lem-sfb-affine-complete-devissage-dimension-flattening). -/
def affineDevissageSections (A : Type u) [CommRing A]
    (M : (schemeSpace (affineDevissageScheme A)).Modules) : ModuleCat.{u} A :=
  (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of A)).inv.hom).obj
    (ModuleCat.of _ Γ(((schemeRestriction (schemeSpace (affineDevissageScheme A))
      (affineIdentityChart (affineDevissageScheme A))).obj M), ⊤))

/-- Complete algebra dévissage represents dimension-d flatness near the chosen prime.
The existence of a finite-module instance in hdev is part of admitting the recorded
complete dévissage, rather than an extra finiteness assumption. Monicity and the
lift equivalence give exactly the singleton-or-empty functor on every V-scheme;
restriction maps are forced by uniqueness. No purity or properness is assumed.

Source: Stacks Project, flat.tex, Tags 05UF, 05HX and 05HY; spaces-flat.tex, Tag 0CWS
(blueprint: lem-sfb-affine-complete-devissage-dimension-flattening).

Proof:
1. Use lem-trf-scheme-zariski-etale-quasi-coherent-equivalence and
   lem-sfb-scheme-etale-module-exact-finiteness-comparison to pass to the Zariski
   module. Its affine sections are finitely presented by
   lem-weil-pbc-finite-presentation-affine-sections. Induct simultaneously for all
   affine pairs and all d on the length of the algebra dévissage. At length zero,
   its sections vanish, so the tilde/Gamma counit of
   lem-weil-pbc-affine-tilde-gamma-adjunction makes M zero. The identity represents
   every flatness condition. Otherwise use
   lem-sfb-complete-devissage-fp-dimension-preparation to shrink the base: every term
   and cokernel is finitely presented and the first smooth algebra has geometrically
   integral fibres of a constant dimension a, universally bounding transcendence degree.
2. Set Z_1 = Spec A_1 and Y_1 = Spec B_1. The first module identification and
   the tilde/Gamma adjunction identify M with the closed direct image of G on Z_1;
   the finite projection to Y_1 identifies its direct image with E = tilde M_1.
   Apply lem-sfb-finite-pushforward-dimension-flatness to both maps. For every base
   test T and every b, P_b(X,M;T) is equivalent to P_b(Y_1,E;T), on all charts.
3. If a < d, the preparation's universal degree bound makes P_d vacuous on Y_1.
   Thus the identity represents the required functor.
4. If a = d, lem-sfb-smooth-top-dimension-rank-decomposition expresses the functor
   as the finite sheaf coproduct of H_r for 0 <= r <= c. By
   lem-sfb-smooth-generic-rank-locus-representability each H_r is represented by a
   locally closed immersion S_r of finite presentation. Their finite disjoint union
   represents the sheaf coproduct: maps into it are clopen partitions with maps
   into the summands. Rank uniqueness makes the union map monic; finite presentation
   follows on its finitely many summands, with quasi-compact inverse images and
   isomorphic diagonal. The equivalence in step 2 gives the original functor.
5. If a > d, the first fibre's generic point has degree a >= d+1, so E is base-flat
   there. The chosen alpha_1 is an isomorphism over its residue field. Apply
   lem-sfb-local-flat-generic-basis-universal-injectivity and shrink again. For
   Q = coker alpha_1, the free-to-E-to-Q sequence is exact and universally exact
   over every base test, by the universal injectivity and
   lem-weil-pbc-tensor-right-exact on affine opens and then on stalks.
6. At a stalk let U be the free term, V the middle term and W the cokernel. The
   smooth structure makes U base-flat. If V is flat, lem-trf-local-ui-flat-cokernel
   makes W flat. Conversely, tensor an injection L to L' with this universally exact
   sequence. Flatness of W forces any killed element in L tensor V to lift from
   L tensor U. Universal injectivity in the L' row and flatness of U kill that lift.
   Thus V is flat. Therefore E and tilde Q have identical P_b conditions for all b.
7. The cokernel tail is a complete algebra dévissage of Q/B_1/R of strictly smaller
   length, including the empty tail when the original length is one. Preparation
   gives its finite-presentation hypotheses, and step 6 gives P_(d+1). Apply the
   induction hypothesis and steps 2 and 6. All comparisons are of subterminal
   functors and commute with restriction. Use
   lem-sfb-space-dimension-flatness-base-change-sheaf and affine covers to glue the
   unique lifts on arbitrary scheme tests. No ordering of the smooth dimensions,
   support purity or properness was used. -/
theorem exists_affine_completeDevissage_dimension_flattening
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A]
    (M : (schemeSpace (affineDevissageScheme A)).Modules) [M.IsFinitePresentation]
    (p : Ideal R) [p.IsPrime]
    (hdev : ∃ hfinite : Module.Finite A (affineDevissageSections A M),
      Nonempty (@CompleteAlgebraDevissage R A _ _ _ inferInstance p inferInstance
        (affineDevissageSections A M) _ _ hfinite))
    (d : ℕ)
    (hflat : dimensionFlatCondition (dimensionFlatBaseMap (affineDevissageArrow R A))
      M (d + 1) (𝟙 (affineDevissageScheme R))) :
    ∃ (V : (Spec (.of R)).Opens), (⟨p, inferInstance⟩ : PrimeSpectrum R) ∈ V ∧
      ∃ (Z : Scheme.{u}) (z : Z ⟶ V.toScheme),
        Mono z ∧ LocallyOfFinitePresentation z ∧ QuasiCompact z ∧
        QuasiCompact (pullback.diagonal z) ∧
        ∀ (B : Scheme.{u}) (b : B ⟶ V.toScheme),
          dimensionFlatCondition (dimensionFlatBaseMap (affineDevissageArrow R A)) M d
            (Over.homMk (b ≫ V.ι) :
              Over.mk ((b ≫ V.ι) ≫ (affineDevissageScheme R).hom) ⟶
                affineDevissageScheme R) ↔
            ∃! l : B ⟶ Z, l ≫ z = b := by
  sorry

end AlgebraicGeometry.AlgebraicSpace

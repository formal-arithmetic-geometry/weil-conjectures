module

public import Sheaf.AlgebraicGeometry.RelativeSplitTorusMatrixSheaf
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Functoriality
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Bracket
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.SmoothRelativeDifferentialsFiniteLocallyFree
import Sheaf.RepresentationTheory.RelativeTorusBundleWeights
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Kaehler.TensorProduct

/-! # Relative centralizers and normalizers of a split torus

Source: Conrad, Reductive group schemes, Proposition 2.1.2, Lemma 2.2.4,
Remark 2.2.7 and Appendix B.1 (blueprint: lem-sfb-relative-torus-centralizer-normalizer).
The predicates test all scheme extensions. The Lie condition uses the full torus
on infinitesimal points, including nonreduced test schemes in positive characteristic.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.RelativeTorusCentralizerNormalizer

/-- The universal commuting condition, tested after every scheme extension.
Source: Conrad, Definition 2.2.1 (blueprint: lem-sfb-relative-torus-centralizer-normalizer). -/
def centralizerPoints {S : Scheme.{u}} {T G : Grp (Over S)} (j : T ⟶ G)
    (W : Over S) : Set (W ⟶ G.X) :=
  {g | ∀ (V : Over S) (a : V ⟶ W) (t : V ⟶ T.X),
    Commute (a ≫ g) (t ≫ j.hom.hom)}

/-- The universal normalizing condition is equality of the conjugate subgroup functor.
Both containments are required. Source: Conrad, Section 2.1
(blueprint: lem-sfb-relative-torus-centralizer-normalizer). -/
def normalizerPoints {S : Scheme.{u}} {T G : Grp (Over S)} (j : T ⟶ G)
    (W : Over S) : Set (W ⟶ G.X) :=
  {g | ∀ (V : Over S) (a : V ⟶ W),
    (fun h : V ⟶ G.X ↦ (a ≫ g) * h * (a ≫ g)⁻¹) ''
      Set.range (fun t : V ⟶ T.X ↦ t ≫ j.hom.hom) =
        Set.range (fun t : V ⟶ T.X ↦ t ≫ j.hom.hom)}

/-- Representation as a subgroup of G on all test schemes; restriction is composition.
Source: Conrad, Definition 2.2.1 (blueprint: lem-sfb-relative-torus-centralizer-normalizer). -/
def RepresentsCentralizer {S : Scheme.{u}} {T G C : Grp (Over S)}
    (j : T ⟶ G) (i : C ⟶ G) : Prop :=
  ∀ W : Over S, Set.range (fun c : W ⟶ C.X ↦ c ≫ i.hom.hom) = centralizerPoints j W

/-- Representation of the normalizer as a subgroup functor, with its actual inclusion.
Source: Conrad, Proposition 2.1.2
(blueprint: lem-sfb-relative-torus-centralizer-normalizer). -/
def RepresentsNormalizer {S : Scheme.{u}} {T G N : Grp (Over S)}
    (j : T ⟶ G) (i : N ⟶ G) : Prop :=
  ∀ W : Over S, Set.range (fun n : W ⟶ N.X ↦ n ≫ i.hom.hom) = normalizerPoints j W

/-- The canonical unit coordinates of the published Laurent split-torus model.
The first component of matrix_sheaf_classification is uniquely determined by its
coordinate normalization: the underlying ring value of coordinate i is the pullback
of RelativeSplitTorus.coordinate S r i. Thus this choice postpones only the proof of
that uniquely normalized identification, not any unspecified geometric data.
Source: Conrad, Appendix B.1; Milne, Theorem 12.9
(blueprint: lem-sfb-relative-torus-centralizer-normalizer). -/
def coordinates (S : Scheme.{u}) (r : ℕ) (W : Over S) :
    (W ⟶ (RelativeSplitTorus.model S r).X) ≃* (Fin r → Γ(W.left, ⊤)ˣ) :=
  (Classical.choose RelativeSplitTorus.matrix_sheaf_classification) S r W

/-- The matrix-sigma locus, specified by the Laurent-monomial formula after every
extension. On disconnected tests different matrices are permitted on different clopen
pieces; this predicate describes just the piece with the specified constant matrix.
Source: Conrad, Appendix B.1 (blueprint: lem-sfb-relative-torus-centralizer-normalizer). -/
def matrixPoints {S : Scheme.{u}} {G : Grp (Over S)} {r : ℕ}
    (j : (RelativeSplitTorus.model S r).toGrp ⟶ G)
    (σ : (Matrix (Fin r) (Fin r) ℤ)ˣ) (W : Over S) : Set (W ⟶ G.X) :=
  {g | ∀ (V : Over S) (a : V ⟶ W) (t : V ⟶ (RelativeSplitTorus.model S r).X),
    ∃ t' : V ⟶ (RelativeSplitTorus.model S r).X,
      (a ≫ g) * (t ≫ j.hom.hom) * (a ≫ g)⁻¹ = t' ≫ j.hom.hom ∧
        ∀ k : Fin r, coordinates S r V t' k =
          ∏ i : Fin r, coordinates S r V t i ^ (σ.val k i)}

/-- The actual differential on identity tangent modules, using the published canonical
Lie-to-infinitesimal-points equivalence and composition with the group homomorphism.
Source: Conrad, Lemma 2.2.4 (blueprint: lem-sfb-relative-torus-centralizer-normalizer). -/
def lieMap {S : Scheme.{u}} {H G : Grp (Over S)} (i : H ⟶ G) :
    GrpObj.Lie H.X → GrpObj.Lie G.X :=
  fun v ↦ GrpObj.lieEquiv G.X
    (GrpObj.infPointsMap i.hom.hom ((GrpObj.lieEquiv H.X).symm v))

/-- Full torus invariance of a tangent vector. The corresponding dual-number point
must commute universally with the torus. This tests the whole group coaction,
not the differential of the torus action.
Source: Conrad, Lemma 2.2.4 (blueprint: lem-sfb-relative-torus-centralizer-normalizer). -/
def lieInvariants {S : Scheme.{u}} {T G : Grp (Over S)} (j : T ⟶ G) :
    Set (GrpObj.Lie G.X) :=
  {v | ((GrpObj.lieEquiv G.X).symm v).val ∈ centralizerPoints j (Scheme.dualNumbersOver S)}

/-- The canonical base-change identification of the Lie sheaf. Its cotangent dual
sends every pulled-back differential da at the identity to d(p-sharp a) at the
base-changed identity, on every open. The evaluation equation specifies the dual
map. HEq only transports sections across the equality e_B followed by p = b followed
by e; it imposes the ordinary equality under that canonical transport.
Source: Conrad, Lemma 2.2.4, p.66; Stacks, Tags 01UM and 00RV
(blueprint: lem-sfb-relative-torus-centralizer-normalizer). -/
def HasCanonicalLieBaseChange {S B : Scheme.{u}} (G : Grp (Over S)) (b : B ⟶ S) : Prop :=
  ∃ (c : (Scheme.Modules.pullback b).obj (GrpObj.omega G.X) ≅
        GrpObj.omega ((Over.pullback b).mapGrp.obj G).X)
    (l : (Scheme.Modules.pullback b).obj (GrpObj.lieAlgebraSheaf G.X) ≅
        GrpObj.lieAlgebraSheaf ((Over.pullback b).mapGrp.obj G).X),
    (∀ (U : G.X.left.Opens) (a : Γ(G.X.left, U)),
      HEq
        (c.hom.app (b ⁻¹ᵁ (GrpObj.unitSection G.X ⁻¹ᵁ U))
          (Scheme.Modules.pullbackUnitApp b (GrpObj.omega G.X)
            (GrpObj.unitSection G.X ⁻¹ᵁ U)
            (Scheme.Modules.pullbackUnitApp (GrpObj.unitSection G.X)
              G.X.hom.relativeDifferentials U (G.X.hom.relativeDifferentialsDerivation.d a))))
        (Scheme.Modules.pullbackUnitApp
          (GrpObj.unitSection ((Over.pullback b).mapGrp.obj G).X)
          ((Over.pullback b).mapGrp.obj G).X.hom.relativeDifferentials
          ((pullback.fst G.X.hom b) ⁻¹ᵁ U)
          (((Over.pullback b).mapGrp.obj G).X.hom.relativeDifferentialsDerivation.d
            ((pullback.fst G.X.hom b).app U a)))) ∧
    (c.hom ⊗ₘ l.hom) ≫
        Scheme.Modules.dualEvaluation (GrpObj.omega ((Over.pullback b).mapGrp.obj G).X) =
      (Functor.Monoidal.μIso (Scheme.Modules.pullback b)
        (GrpObj.omega G.X) (GrpObj.lieAlgebraSheaf G.X)).hom ≫
          (Scheme.Modules.pullback b).map (Scheme.Modules.dualEvaluation (GrpObj.omega G.X)) ≫
            (Scheme.Modules.pullbackObjUnitIso b).hom

/-- Relative smooth centralizers and normalizers of a closed split torus, their
identity tangent modules and all constant action-matrix loci.
Source: Conrad, Proposition 2.1.2, Lemma 2.2.4, Remark 2.2.7 and Appendix B.1
(blueprint: lem-sfb-relative-torus-centralizer-normalizer).

Proof, following the node's eight steps:
1. On Spec A write G = Spec B and T = Spec A[Z^r]. The kernel of B onto A[Z^r]
   is finitely generated, using lem-weil-pbc-finite-presentation-surjection-kernel-fg
   on a polynomial presentation; this does not require A Noetherian.
2. Expand conjugation minus the inclusion on finitely many algebra generators in
   the Laurent basis. Their finitely many coefficients define the closed centralizer.
3. Expand both conjugation directions on ideal generators for T. The coefficient
   ideal defines exactly the normalizer. Laurent bases persist under any scalar
   extension, so both constructions commute with arbitrary base change and glue.
   The functorial group laws restrict to these closed subschemes.
4. Lift a centralizing point across a square-zero quotient using smoothness of G.
   Apply lem-sfb-split-torus-infinitesimal-conjugacy to conjugation and j; correct
   the lift by a point reducing to 1. This proves smoothness of C.
5. For N lift the locally constant action matrix across the nilpotent thickening,
   using lem-sfb-relative-split-torus-matrix-sheaf, then the same infinitesimal
   conjugacy lemma corrects an arbitrary lift. This also works on disconnected tests.
6. Smooth relative differentials are finite locally free by
   lem-ag-smooth-relative-differentials-finite-locally-free. Pull back to the identity
   and dualize. The dual-number description identifies Lie with derivations; the
   differential base-change theorem identifies these bundles under every base change.
7. By lem-sfb-relative-torus-bundle-weights the invariant bundle is the zero-weight
   summand. A dual-number point lies in C exactly when the full torus fixes it.
   Thus the image of the actual tangent map is precisely this invariant module,
   after every base change; no infinitesimal replacement of torus invariance is used.
8. Apply the relative matrix-sheaf classification to the universal normalizer point.
   Its locally constant matrix has clopen fibres, which cover N and represent the
   specified Laurent-monomial loci. Pulling back these opens gives the same loci
   after every base change. Rank zero has the unique empty invertible matrix,
   C = N = G, and Lie invariants equal the whole tangent module. -/
theorem relative_torus_centralizer_normalizer
    {S : Scheme.{u}} (G : Grp (Over S))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [LocallyOfFinitePresentation G.X.hom]
    (r : ℕ) (j : (RelativeSplitTorus.model S r).toGrp ⟶ G)
    [IsClosedImmersion j.hom.hom.left] :
    ∃ (C N : Grp (Over S)) (iC : C ⟶ G) (iN : N ⟶ G)
      (U : (Matrix (Fin r) (Fin r) ℤ)ˣ → N.X.left.Opens),
      IsClosedImmersion iC.hom.hom.left ∧ IsClosedImmersion iN.hom.hom.left ∧
      Smooth C.X.hom ∧ IsAffineHom C.X.hom ∧ LocallyOfFinitePresentation C.X.hom ∧
      Smooth N.X.hom ∧ IsAffineHom N.X.hom ∧ LocallyOfFinitePresentation N.X.hom ∧
      RepresentsCentralizer j iC ∧ RepresentsNormalizer j iN ∧
      Set.range (lieMap iC) = lieInvariants j ∧
      (GrpObj.lieAlgebraSheaf G.X).IsFiniteLocallyFree ∧
      (∀ (B : Scheme.{u}) (b : B ⟶ S),
        RepresentsCentralizer ((Over.pullback b).mapGrp.map j)
          ((Over.pullback b).mapGrp.map iC) ∧
        RepresentsNormalizer ((Over.pullback b).mapGrp.map j)
          ((Over.pullback b).mapGrp.map iN) ∧
        Set.range (lieMap ((Over.pullback b).mapGrp.map iC)) =
          lieInvariants ((Over.pullback b).mapGrp.map j) ∧
        HasCanonicalLieBaseChange G b ∧ HasCanonicalLieBaseChange C b) ∧
      (∀ σ : (Matrix (Fin r) (Fin r) ℤ)ˣ, IsClosed (U σ : Set N.X.left)) ∧
      (⨆ σ : (Matrix (Fin r) (Fin r) ℤ)ˣ, U σ) = ⊤ ∧
      (∀ (σ : (Matrix (Fin r) (Fin r) ℤ)ˣ) (W : Over S) (n : W ⟶ N.X),
        Set.range n.left ⊆ U σ ↔ n ≫ iN.hom.hom ∈ matrixPoints j σ W) ∧
      (∀ (B : Scheme.{u}) (b : B ⟶ S) (σ : (Matrix (Fin r) (Fin r) ℤ)ˣ)
        (W : Over B) (n : W ⟶ ((Over.pullback b).mapGrp.obj N).X),
        Set.range n.left ⊆ (pullback.fst N.X.hom b) ⁻¹' (U σ : Set N.X.left) ↔
          ((Over.mapPullbackAdj b).homEquiv W N.X).symm n ≫ iN.hom.hom ∈
            matrixPoints j σ ((Over.map b).obj W)) := by
  sorry

end AlgebraicGeometry.RelativeTorusCentralizerNormalizer

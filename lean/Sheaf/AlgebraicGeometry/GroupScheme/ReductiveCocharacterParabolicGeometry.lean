module

public import Mathlib.Topology.Connected.Basic

public import Mathlib.Algebra.Algebra.Defs

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

public import Mathlib.CategoryTheory.Monoidal.Grp

public import Sheaf.AlgebraicGeometry.TorusCharacterTangentWeights

public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType

public import Sheaf.AlgebraicGeometry.SolvableGroupStructure

public import Sheaf.AlgebraicGeometry.StandardGroupSchemes

public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Sheaf.AlgebraicGeometry.CocharacterLimitSmoothStructure
public import Sheaf.AlgebraicGeometry.GroupScheme.SplitUnipotentSeries
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Integral

import Sheaf.AlgebraicGeometry.TorusFixedSchemeSmooth
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
import Mathlib.AlgebraicGeometry.Scheme
import Sheaf.AlgebraicGeometry.GeometricallyConnectedAlgebraicClosure
import Sheaf.AlgebraicGeometry.AffineGroupDualNumberCalculus
import Sheaf.AlgebraicGeometry.GmRepresentationWeightBasis
import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousQuotient
import Mathlib.CategoryTheory.Sites.Precoverage
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.MorphismProperty.Descent
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
import Sheaf.AlgebraicGeometry.CocharacterConjugateMaximalTorus
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations
import Sheaf.AlgebraicGeometry.GroupScheme.BorelRootProductCoordinates
import Sheaf.AlgebraicGeometry.GroupScheme.BorelQuotientProperGeometry
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import WeilConjectures.AlgebraicGeometry.IsProperOfFieldBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Reductive cocharacter parabolics and their projective quotients

Source: Milne, Algebraic Groups (2017), Theorem 13.33, pp.265--266;
Proposition 17.60, p.372; Proposition 21.29, pp.433--434; Theorem 25.1, p.544.
(blueprint: lem-sfb-reductive-cocharacter-parabolic-geometry).

The predicates below package the subgroups, limit retraction, and quotient in this
statement. Representability is on all commutative algebras, including nonreduced ones.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry.ReductiveCocharacter

/-- The represented limit subgroups, with their smoothness and geometric connectedness.
Evaluation at zero specifies the retraction, and the pullback specifies its kernel.
Source: Milne, Theorem 13.33(a),(b),(e), pp.265--266.
(blueprint: lem-sfb-reductive-cocharacter-parabolic-geometry). -/
def LimitGeometry {k : Type u} [Field k]
    {G P U Z : Grp (Over (Spec (.of k)))}
    (lam : Grp.mk (StandardGroupSchemes.multiplicative k) ⟶ G)
    (iP : P ⟶ G) (iU : U ⟶ G) (iZ : Z ⟶ G)
    (jU : U ⟶ P) (jZ : Z ⟶ P) (r : P ⟶ Z) : Prop :=
  IsClosedSubgroupScheme iP.hom.hom ∧ IsClosedSubgroupScheme iU.hom.hom ∧
    IsClosedSubgroupScheme iZ.hom.hom ∧
    Smooth P.X.hom ∧ Smooth U.X.hom ∧ Smooth Z.X.hom ∧
    GeometricallyConnected P.X.hom ∧ GeometricallyConnected U.X.hom ∧
    GeometricallyConnected Z.X.hom ∧
    (∀ (A : CommAlgCat.{u} k) (g : StandardGroupSchemes.affine k A ⟶ G.X),
      (∃ p, p ≫ iP.hom.hom = g) ↔ g ∈ CocharacterLimit.parabolicPoints lam A) ∧
    (∀ (A : CommAlgCat.{u} k) (g : StandardGroupSchemes.affine k A ⟶ G.X),
      (∃ p, p ≫ iU.hom.hom = g) ↔ g ∈ CocharacterLimit.unipotentPoints lam A) ∧
    (∀ (A : CommAlgCat.{u} k) (g : StandardGroupSchemes.affine k A ⟶ G.X),
      (∃ p, p ≫ iZ.hom.hom = g) ↔ g ∈ CocharacterLimit.centralizerPoints lam A) ∧
    jU ≫ iP = iU ∧ jZ ≫ iP = iZ ∧ jZ ≫ r = 𝟙 Z ∧
    IsNormalSubgroupScheme jU.hom.hom ∧
    IsPullback jU.hom.hom (toUnit U.X) r.hom.hom η[Z.X] ∧
    ∀ (A : CommAlgCat.{u} k) (p : StandardGroupSchemes.affine k A ⟶ P.X)
      (q : StandardGroupSchemes.affine k A ⊗ StandardGroupSchemes.additive k ⟶ G.X),
      CocharacterLimit.IsOrbitExtension lam A (p ≫ iP.hom.hom) q →
        lift (𝟙 _) 1 ≫ q = p ≫ r.hom.hom ≫ iZ.hom.hom

/-- Multiplication is the semidirect-product isomorphism, with its actual group law.
Source: Milne, Theorem 13.33(b), p.266.
(blueprint: lem-sfb-reductive-cocharacter-parabolic-geometry). -/
def SemidirectGeometry {k : Type u} [Field k]
    {P U Z : Grp (Over (Spec (.of k)))}
    (jU : U ⟶ P) (jZ : Z ⟶ P) : Prop :=
  ∃ (e : U.X ⊗ Z.X ≅ P.X) (c : Z.X ⊗ U.X ⟶ U.X),
    e.hom = (fst _ _ ≫ jU.hom.hom) * (snd _ _ ≫ jZ.hom.hom) ∧
    c ≫ jU.hom.hom =
      (fst _ _ ≫ jZ.hom.hom) * (snd _ _ ≫ jU.hom.hom) * (fst _ _ ≫ jZ.hom.hom)⁻¹ ∧
    ∀ (A : CommAlgCat.{u} k) (v w : StandardGroupSchemes.affine k A ⟶ U.X)
      (z t : StandardGroupSchemes.affine k A ⟶ Z.X),
      (lift v z ≫ e.hom) * (lift w t ≫ e.hom) =
        lift (v * (lift z w ≫ c)) (z * t) ≫ e.hom

/-- The smooth projective quotient and its right P-torsor. The smooth surjective
finitely presented covering, together with its displayed kernel pair, identifies
its represented fppf sheaf with the sheafification of the right-coset presheaf.
Source: Milne, Theorems 5.28, 8.43 and 25.1, pp.105,161,544.
(blueprint: lem-sfb-reductive-cocharacter-parabolic-geometry). -/
def QuotientGeometry {k : Type u} [Field k]
    {G P : Grp (Over (Spec (.of k)))} (iP : P ⟶ G)
    (X : Over (Spec (.of k))) (q : G.X ⟶ X) : Prop :=
  Smooth X.hom ∧ IsProjective X.hom ∧ GeometricallyIntegral X.hom ∧
    Smooth q.left ∧ Surjective q.left ∧ LocallyOfFinitePresentation q.left ∧
    QuasiCompact q.left ∧ QuasiSeparated q.left ∧ GeometricallyIntegral q.left ∧
    IsPullback (fst G.X P.X)
      (fst G.X P.X * (snd G.X P.X ≫ iP.hom.hom)) q q

/-- Nonzero integer pairings with every nontrivial adjoint character. We test the
recorded tangent character spaces after algebraic closure, where torus points are
Zariski dense. Nontriviality of the composed character is exactly n_alpha ≠ 0,
including when the characteristic divides n_alpha.
Source: Milne, Proposition 21.29, pp.433--434.
(blueprint: lem-sfb-reductive-cocharacter-parabolic-geometry). -/
def IsRegular {k : Type u} [Field k] {G T : Grp (Over (Spec (.of k)))}
    (iT : T ⟶ G) (nu : Grp.mk (StandardGroupSchemes.multiplicative k) ⟶ T) : Prop :=
  ∀ a : ModObj ((MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj T).X
      ((MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj G).X,
    a.smul =
      (fst _ _ ≫ ((MultiplicativeType.baseChange (K := AlgebraicClosure k)).map iT).hom.hom) *
        snd _ _ *
      (fst _ _ ≫ ((MultiplicativeType.baseChange (K := AlgebraicClosure k)).map iT).hom.hom)⁻¹ →
    ∀ chi : (MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj T ⟶
        Grp.mk (StandardGroupSchemes.multiplicative (AlgebraicClosure k)),
      chi.hom.hom ≠ 1 →
      @TorusCharacterTangent.weightSpace (AlgebraicClosure k) _
        ((MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj T)
        ((MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj G) a chi ≠ ⊥ →
      ((MultiplicativeType.baseChange (K := AlgebraicClosure k)).map nu).hom.hom ≫
        chi.hom.hom ≠ 1

/-- Cocharacter limit subgroups over an arbitrary field, their split unipotent radical,
projective homogeneous quotient, canonical field extension, and regular centralizer.
Source: Milne, Theorem 13.33(a)--(e), pp.265--266; Proposition 17.60, p.372;
Theorem 25.1, p.544; Proposition 21.29, pp.433--434.
(blueprint: lem-sfb-reductive-cocharacter-parabolic-geometry).

Proof plan (the eleven steps of the DAG):
1. Apply lem-sfb-smooth-affine-concentrator to G and its identity to represent P,U.
   The coefficients of c*(f)-1 tensor f represent Z; lem-sfb-torus-fixed-scheme-smooth
   makes Z smooth. Product and inverse orbit extensions give subgroup structures.
2. Polynomial-to-Laurent restriction is injective over every algebra. Thus the
   multiplicative action identities extend across zero. Evaluation gives r, with
   r|Z = id and kernel U. Multiplication and g ↦ (g r(g)⁻¹,r(g)) are inverse;
   expanding products gives (u,z)(v,w) = (u z v z⁻¹,z w).
3. The defining test-algebra functors and evaluation commute with every field
   extension. Over the algebraic closure, lem-sfb-cocharacter-limit-smooth-structure
   gives connectedness; lem-weil-geometrically-connected-algebraic-closure descends it.
4. lem-sfb-affine-group-dual-number-calculus and lem-sfb-gm-representation-weight-basis
   give Lie(U) as the positive integer weights. There are no invariants, so apply
   lem-sfb-split-torus-no-invariants-unipotence to get the split additive series.
5. lem-sfb-algebraic-group-homogeneous-quotient supplies q. Its coset criterion gives
   the displayed kernel pair. The fppf covering and its pullbacks locally lift every
   test point, proving the sheafification property, also after field extension.
6. Pull q back by itself and use lem-trf-smooth-fpqc-base-descent for smoothness.
   lem-sbc-smooth-flat-surjective-source-descent makes X smooth. Surjectivity gives
   geometric connectedness; lem-trf-smooth-connected-fibre-normal-integrality makes
   G and X geometrically integral.
7. Over the algebraic closure, lem-sfb-reductive-borel-pair-structure and
   lem-sfb-cocharacter-conjugate-maximal-torus put lambda in a maximal torus.
   Choose a regular integral perturbation preserving its nonzero root signs;
   lem-sfb-regular-cocharacter-borel-description gives its Borel B.
8. lem-sfb-reductive-root-subgroup-parametrizations and
   lem-sfb-borel-root-product-coordinates show B is contained in P on all algebras.
   lem-sfb-nested-homogeneous-quotient-geometry maps G/B onto G/P. Apply
   lem-sfb-borel-quotient-proper-geometry, lem-weil-pbc-image-universally-closed and
   lem-pc-proper-descends-field to obtain properness of X.
9. lem-sfb-affine-homogeneous-quotient-projective-immersion embeds X into projective
   space; lem-weil-pbc-proper-over-separated makes the immersion proper and
   lem-weil-pbc-proper-immersion-closed makes it closed, giving projectivity.
10. On an algebraically closed geometric fibre choose a rational point using
   lem-sc-lft-over-field-jacobson-space and lem-weil-pbc-closed-point-residue-field-base.
   The torsor identifies it with P. Smoothness and geometric connectedness imply
   integral geometric fibres by lem-trf-smooth-connected-fibre-normal-integrality.
11. Extend the split maximal torus using lem-sfb-maximal-torus-field-extension.
   lem-sfb-reductive-rank-one-reflections gives the adjoint weight decomposition;
   regularity implies Lie(Z)=Lie(T). Apply lem-sfb-smooth-subgroup-tangent-generation
   over the algebraic closure; faithful scalar extension descends Z=T.
-/
theorem reductive_cocharacter_parabolic_geometry {k : Type u} [Field k]
    (G : Grp (Over (Spec (.of k)))) (hG : ReductiveTorusCentralizer.IsReductive G)
    (lam : Grp.mk (StandardGroupSchemes.multiplicative k) ⟶ G) :
    GeometricallyIntegral G.X.hom ∧
    ∃ (P U Z : Grp (Over (Spec (.of k)))) (iP : P ⟶ G) (iU : U ⟶ G) (iZ : Z ⟶ G)
      (jU : U ⟶ P) (jZ : Z ⟶ P) (r : P ⟶ Z)
      (X : Over (Spec (.of k))) (q : G.X ⟶ X),
      LimitGeometry lam iP iU iZ jU jZ r ∧ SemidirectGeometry jU jZ ∧
      SolvableGroupStructure.IsUnipotent U ∧ (∃ n : ℕ, SplitUnipotentLength U n) ∧
      QuotientGeometry iP X q ∧
      (∀ (L : Type u) [Field L] [Algebra k L],
        ∃ e : Grp.mk (StandardGroupSchemes.multiplicative L) ≅
            (MultiplicativeType.baseChange (K := L)).obj
              (Grp.mk (StandardGroupSchemes.multiplicative k)),
          e.hom.hom.hom.left ≫
              pullback.fst (StandardGroupSchemes.multiplicative k).hom
                (Spec.map (CommRingCat.ofHom (algebraMap k L))) =
            Spec.map (CommRingCat.ofHom
              (LaurentPolynomial.eval₂ (LaurentPolynomial.C.comp (algebraMap k L))
                (unitOfInvertible (LaurentPolynomial.T 1)))) ∧
          LimitGeometry (e.hom ≫ (MultiplicativeType.baseChange (K := L)).map lam)
            ((MultiplicativeType.baseChange (K := L)).map iP)
            ((MultiplicativeType.baseChange (K := L)).map iU)
            ((MultiplicativeType.baseChange (K := L)).map iZ)
            ((MultiplicativeType.baseChange (K := L)).map jU)
            ((MultiplicativeType.baseChange (K := L)).map jZ)
            ((MultiplicativeType.baseChange (K := L)).map r) ∧
          QuotientGeometry ((MultiplicativeType.baseChange (K := L)).map iP)
            ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj X)
            ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map q)) ∧
      ∀ (T : Grp (Over (Spec (.of k)))) (iT : T ⟶ G),
        ReductiveTorusCentralizer.IsMaximalTorus iT →
        (∃ n : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus k n)) →
        ∀ nu : Grp.mk (StandardGroupSchemes.multiplicative k) ⟶ T,
          nu ≫ iT = lam → IsRegular iT nu →
          ∃ e : T ≅ Z, e.hom ≫ iZ = iT := by
  sorry

end AlgebraicGeometry.ReductiveCocharacter

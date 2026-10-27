module

public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations
public import Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces
public import Sheaf.AlgebraicGeometry.GroupScheme.CocharacterContractingPoints
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Sheaf.AlgebraicGeometry.GmRepresentationWeightBasis
import Sheaf.AlgebraicGeometry.TransverseSubgroupProductOpen
import Sheaf.AlgebraicGeometry.GroupScheme.AffinePointedMapGeneratedSubgroup
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import WeilConjectures.Mathlib.RingTheory.Nullstellensatz

/-! # The contracting triangular cell for rank-one generators

Source: Milne, Algebraic Groups (2017), Theorem 23.31, p.494; the triangular-cell
argument 23.22--23.23, pp.491--492; Theorem 13.33, pp.265--266
(blueprint: lem-sfb-contracting-rank-one-cell).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- Independent rank-one generators with mixed commutation have a contracting dense
open triangular cell. Products and intersections retain their scheme structures.
No reductivity assumption is made on G.

Source: Milne, Theorem 23.31, p.494; 23.22--23.23, pp.491--492; Theorem 13.33,
pp.265--266; Steinberg (1999), 5.6--5.10
(blueprint: lem-sfb-contracting-rank-one-cell).

Proof plan:
1. Apply lem-sfb-cocharacter-limit-smooth-structure to λ and -λ, obtaining the
   contracting groups U₊, U₋, the centralizer Z and the limit-exists groups P₊, P₋.
   Use lem-sfb-central-torus-faithful-weight-blocks and
   lem-sfb-gm-representation-weight-basis: matrices are upper/lower block triangular,
   Z is block diagonal and U₊, U₋ have identity diagonal blocks. This proves
   P₊ ∩ P₋ = Z and U₋ ∩ P₊ = 1 on all algebras. The Lie decomposition and
   lem-sfb-transverse-subgroup-product-open give the open cell U₋ × Z × U₊.
2. The root conjugation formula contracts each positive root group by tⁿ and each
   negative root group by t⁻ⁿ. Minimality gives U ⊆ U₊ and V ⊆ U₋. Apply
   lem-sfb-affine-pointed-map-generated-subgroup to palindromic root-word spaces,
   which are affine spaces, then lem-sfb-geometrically-reduced-group-smooth:
   U,V are smooth connected and unipotent. The word-ideal construction and
   lem-wf-affine-nullstellensatz-vanishing make rational root words schematically
   dense. Apply lem-sfb-reductive-rank-one-reflections and
   lem-sfb-smooth-subgroup-tangent-generation to each Jα: signed roots and T
   generate it, hence generate G. Palindromic word spaces including T have Laurent
   polynomial coordinate domains, giving schematic density of their rational words.
3. Conjugation by T preserves each word ideal coefficient by coefficient, so it
   normalizes U,V. Let C be the reduced closure of V(F)T(F)U(F). It is stable under
   left V(F), T(F) and right U(F), T(F).
4. Use lem-sfb-opposite-root-sl2-parametrizations and the matrix identity
   x₊(a)x₋(b)=x₋(b/d)h(d)x₊(a/d), d=1+ab invertible. Induct on the length of a
   negative root word after a positive root element. Unequal indices commute;
   equal indices use this identity on d ≠ 0. The Nullstellensatz and injectivity
   of polynomial localization extend the containment to d=0 in every characteristic.
5. Negative root-word density gives uα(a)V(F) ⊆ C(F). Right stability implies
   every positive root element preserves C. Thus the dense rational generating
   subgroup lies in C, so C=G.
6. Inside the open chart U₋ × Z × U₊, the map V × T × U is a closed immersion
   with dense image. The chart is reduced by sbc-lem-smooth-geometrically-reduced,
   so its defining ideal vanishes. Hence it is the whole chart. Pull back along
   the axes to obtain V=U₋, T=Z, U=U₊ on all test algebras, including nonreduced ones.
7. The cocharacter semidirect products identify TU=P₊ and TV=P₋, so both are
   smooth connected closed subgroups and their intersection is T. By
   lem-sfb-smooth-unipotent-solvable the kernels U,V have finite normal series
   with commutative quotients. The derived series lies successively in these terms;
   since the torus quotient is commutative, the derived series of TU,TV terminates. -/
theorem contracting_rankOne_cell
    (F : Type u) [Field F] [IsAlgClosed F]
    (G T : Grp (Over (Spec (.of F))))
    (hG : SolvableGroupStructure.IsAlgebraic G)
    (hGsmooth : Smooth G.X.hom) (hGconnected : ConnectedSpace G.X.left)
    (iT : T ⟶ G) (hT : ReductiveTorusCentralizer.IsMaximalTorus iT)
    (r : ℕ) (hsplit : Nonempty (T ≅ MultiplicativeType.splitTorus F r))
    [IsCommMonObj T.X] [IsCommMonObj (StandardGroupSchemes.multiplicative F)]
    (D : Finset (Additive (RankOneRoots.Character T))) (hne : D.Nonempty)
    (hnonzero : ∀ α : D, α.val ≠ 0)
    (hindep : LinearIndependent ℤ (fun α : D ↦ α.val))
    (J : D → Grp (Over (Spec (.of F)))) (iJ : ∀ α : D, J α ⟶ G)
    (tJ : ∀ α : D, T ⟶ J α)
    (hJclosed : ∀ α : D, IsClosedSubgroupScheme (iJ α).hom.hom)
    (hJred : ∀ α : D, ReductiveTorusCentralizer.IsReductive (J α))
    (hJT : ∀ α : D, ReductiveTorusCentralizer.IsMaximalTorus (tJ α))
    (hJTcomp : ∀ α : D, tJ α ≫ iJ α = iT)
    (aJ : ∀ α : D, ModObj T.X (J α).X)
    (haJ : ∀ α : D, (aJ α).smul = RankOneRoots.adjointMap (tJ α))
    (hroots : ∀ α : D, RankOneRoots.roots T (J α) (aJ α) =
      {α.val.toMul, α.val.toMul⁻¹})
    (Ua Va : D → Grp (Over (Spec (.of F))))
    (jUa : ∀ α : D, Ua α ⟶ J α) (jVa : ∀ α : D, Va α ⟶ J α)
    (hUa : ∀ α : D,
      IsClosedSubgroupScheme (jUa α).hom.hom ∧ Smooth (Ua α).X.hom ∧
      ConnectedSpace (Ua α).X.left ∧
      @TorusCharacterTangent.IsStable F _ T (J α) (aJ α) _ (jUa α) ∧
      (GrpObj.differential (jUa α).hom.hom).toLinearMap.range =
        RankOneRoots.weight T (J α) (aJ α) α.val.toMul)
    (hVa : ∀ α : D,
      IsClosedSubgroupScheme (jVa α).hom.hom ∧ Smooth (Va α).X.hom ∧
      ConnectedSpace (Va α).X.left ∧
      @TorusCharacterTangent.IsStable F _ T (J α) (aJ α) _ (jVa α) ∧
      (GrpObj.differential (jVa α).hom.hom).toLinearMap.range =
        RankOneRoots.weight T (J α) (aJ α) α.val.toMul⁻¹)
    (hgenerate : ∀ (K : Grp (Over (Spec (.of F)))) (k : K ⟶ G),
      IsClosedSubgroupScheme k.hom.hom →
      (∀ α : D, ∃ f : J α ⟶ K, f ≫ k = iJ α) → ∃ f : G ⟶ K, f ≫ k = 𝟙 G)
    (hmixed : ∀ (α β : D), α ≠ β → ∀ (W : Over (Spec (.of F)))
      (v : W ⟶ (Va α).X) (x : W ⟶ (Ua β).X),
      Commute (v ≫ (jVa α ≫ iJ α).hom.hom) (x ≫ (jUa β ≫ iJ β).hom.hom))
    (U V : Grp (Over (Spec (.of F)))) (iU : U ⟶ G) (iV : V ⟶ G)
    (hUclosed : IsClosedSubgroupScheme iU.hom.hom)
    (hVclosed : IsClosedSubgroupScheme iV.hom.hom)
    (hUcontains : ∀ α : D, ∃ f : Ua α ⟶ U, f ≫ iU = jUa α ≫ iJ α)
    (hVcontains : ∀ α : D, ∃ f : Va α ⟶ V, f ≫ iV = jVa α ≫ iJ α)
    (hUmin : ∀ (K : Grp (Over (Spec (.of F)))) (k : K ⟶ G),
      IsClosedSubgroupScheme k.hom.hom →
      (∀ α : D, ∃ f : Ua α ⟶ K, f ≫ k = jUa α ≫ iJ α) →
      ∃ f : U ⟶ K, f ≫ k = iU)
    (hVmin : ∀ (K : Grp (Over (Spec (.of F)))) (k : K ⟶ G),
      IsClosedSubgroupScheme k.hom.hom →
      (∀ α : D, ∃ f : Va α ⟶ K, f ≫ k = jVa α ≫ iJ α) →
      ∃ f : V ⟶ K, f ≫ k = iV)
    (aG : ModObj T.X G.X) (haG : aG.smul = RankOneRoots.adjointMap iT)
    (lam : RankOneRoots.Cocharacter T) (n : ℕ) (hn : 0 < n)
    (hpair : ∀ α : D, lam.hom.hom ≫ α.val.toMul.hom.hom =
      (𝟙 (StandardGroupSchemes.multiplicative F)) ^ n) :
    Smooth U.X.hom ∧ ConnectedSpace U.X.left ∧ SolvableGroupStructure.IsUnipotent U ∧
    Smooth V.X.hom ∧ ConnectedSpace V.X.left ∧ SolvableGroupStructure.IsUnipotent V ∧
    @TorusCharacterTangent.IsStable F _ T G aG _ iU ∧
    @TorusCharacterTangent.IsStable F _ T G aG _ iV ∧
    IsOpenImmersion
      ((fst (V.X ⊗ T.X) U.X ≫
        ((fst V.X T.X ≫ iV.hom.hom) * (snd V.X T.X ≫ iT.hom.hom))) *
        (snd (V.X ⊗ T.X) U.X ≫ iU.hom.hom)).left ∧
    DenseRange
      ((fst (V.X ⊗ T.X) U.X ≫
        ((fst V.X T.X ≫ iV.hom.hom) * (snd V.X T.X ≫ iT.hom.hom))) *
        (snd (V.X ⊗ T.X) U.X ≫ iU.hom.hom)).left ∧
    (∀ W : Over (Spec (.of F)),
      Set.range (fun x : W ⟶ U.X ↦ x ≫ iU.hom.hom) =
        {g | CocharacterContraction.Contracts G (lam ≫ iT) W g}) ∧
    (∀ W : Over (Spec (.of F)),
      Set.range (fun x : W ⟶ V.X ↦ x ≫ iV.hom.hom) =
        {g | CocharacterContraction.Contracts G (lam⁻¹ ≫ iT) W g}) ∧
    (∀ (A : Type u) [CommRing A] [Algebra F A],
      ReductiveTorusCentralizer.centralizerPoints (lam ≫ iT) A =
        Set.range (fun x : StandardGroupSchemes.affine F A ⟶ T.X ↦ x ≫ iT.hom.hom)) ∧
    ∃ (P Q : Grp (Over (Spec (.of F)))) (p : P ⟶ G) (q : Q ⟶ G)
      (tP : T ⟶ P) (uP : U ⟶ P) (tQ : T ⟶ Q) (vQ : V ⟶ Q),
      IsClosedSubgroupScheme p.hom.hom ∧ IsClosedSubgroupScheme q.hom.hom ∧
      tP ≫ p = iT ∧ uP ≫ p = iU ∧ tQ ≫ q = iT ∧ vQ ≫ q = iV ∧
      IsIso ((fst T.X U.X ≫ tP.hom.hom) * (snd T.X U.X ≫ uP.hom.hom)) ∧
      IsIso ((fst T.X V.X ≫ tQ.hom.hom) * (snd T.X V.X ≫ vQ.hom.hom)) ∧
      Smooth P.X.hom ∧ ConnectedSpace P.X.left ∧ IsSolvableGroupScheme P.X ∧
      Smooth Q.X.hom ∧ ConnectedSpace Q.X.left ∧ IsSolvableGroupScheme Q.X ∧
      IsPullback tP.hom.hom tQ.hom.hom p.hom.hom q.hom.hom := by
  sorry

end AlgebraicGeometry

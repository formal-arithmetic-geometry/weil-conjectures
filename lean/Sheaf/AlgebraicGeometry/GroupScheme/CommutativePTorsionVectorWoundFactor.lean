module

public import Sheaf.AlgebraicGeometry.GroupScheme.Wound
public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
import Mathlib.AlgebraicGeometry.Noetherian

/-! # The canonical vector factor of a commutative p-torsion group

Source: Conrad, The structure of solvable groups over general fields (2014),
Theorem 2.6 and Corollary 2.7, printed pp.12--13
(blueprint: lem-sfb-commutative-p-torsion-vector-wound-factor).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry.VectorWoundFactor

/-- The stated product decomposition, retaining the two specified subgroup inclusions.
The map tested for being an isomorphism is multiplication of those inclusions.
Source: Conrad, Theorem 2.6, printed p.12
(blueprint: lem-sfb-commutative-p-torsion-vector-wound-factor). -/
def IsDecomposition {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]
    {H V W : Grp (Over (Spec (.of k)))} (i : V ⟶ H) (j : W ⟶ H) : Prop :=
  IsClosedSubgroupScheme i.hom.hom ∧ IsClosedSubgroupScheme j.hom.hom ∧
    SolvableGroupStructure.IsAlgebraic V ∧ SolvableGroupStructure.IsAlgebraic W ∧
    Smooth V.X.hom ∧ Smooth W.X.hom ∧ ConnectedSpace V.X.left ∧ ConnectedSpace W.X.left ∧
    IsIso ((fst V.X W.X ≫ i.hom.hom) * (snd V.X W.X ≫ j.hom.hom)) ∧
    (∃ d : ℕ, Nonempty (V ≅
      ∏ᶜ (fun _ : Fin d ↦ Grp.mk (StandardGroupSchemes.additive k)))) ∧
    IsWoundGroup ((MultiplicativeType.baseChange (K := K)).obj W)

/-- Every pointed affine-line scheme map factors through the specified subgroup.
Source: Conrad, Theorem 2.6, printed p.12
(blueprint: lem-sfb-commutative-p-torsion-vector-wound-factor). -/
def ContainsPointedLines {k : Type u} [Field k]
    {H V : Grp (Over (Spec (.of k)))} (i : V ⟶ H) : Prop :=
  ∀ f : StandardGroupSchemes.additive k ⟶ H.X,
    (1 : 𝟙_ (Over (Spec (.of k))) ⟶ StandardGroupSchemes.additive k) ≫ f = 1 →
      ∃ g : StandardGroupSchemes.additive k ⟶ V.X, g ≫ i.hom.hom = f

/-- After scalar extension the subgroup is the smallest closed subgroup containing
all pointed affine-line maps, with containment expressed scheme-theoretically.
Source: Conrad, Theorem 2.6, printed pp.12--13
(blueprint: lem-sfb-commutative-p-torsion-vector-wound-factor). -/
def IsGeneratedByPointedLines {k : Type u} [Field k]
    {H V : Grp (Over (Spec (.of k)))} (i : V ⟶ H) : Prop :=
  ContainsPointedLines i ∧
    ∀ (J : Grp (Over (Spec (.of k)))) (j : J ⟶ H),
      IsClosedSubgroupScheme j.hom.hom → ContainsPointedLines j →
        ∃ a : V ⟶ J, a ≫ j = i

/-- The canonical vector factor and a separably wound complement of a smooth connected
commutative p-torsion affine group over an arbitrary positive-characteristic field.
Source: Conrad, Theorem 2.6 and Corollary 2.7, printed pp.12--13
(blueprint: lem-sfb-commutative-p-torsion-vector-wound-factor).

Proof:
1. Apply lem-sfb-smooth-p-torsion-additive-embedding to embed H as a closed subgroup
   of E = Ga^N. Connectedness and perfection are unnecessary for that embedding.
2. The family of all pointed affine-line maps over K is Galois-stable. Apply
   lem-sfb-galois-stable-affine-line-generated-subgroup to descend its smallest
   containing closed subgroup to a smooth connected subgroup V over k.
3. Intersecting any containing subgroup of E_K with H_K shows that this same family
   generates V_K in E_K. Apply lem-sfb-affine-line-generated-vector-subgroup-straightening
   to obtain V = Ga^d and a retraction r : E -> V. Its restriction to H has kernel W.
   The inverse maps (v,w) -> v+w and x -> (r(x),x-r(x)) give the product decomposition.
4. The projection H -> W is surjective with section, so W is connected. It is affine
   finite type as a closed coordinate intersection. Apply pqf-lem-lft-fp-locnoeth over
   Spec k to obtain local finite presentation. Lift a first-order thickening map to H
   by smoothness and compose with the projection to W. The infinitesimal criterion
   in def-sbc-smooth-morphisms proves W smooth.
5. Embed E in upper unitriangular matrices with its coordinates in the first row;
   restricting gives faithful unipotent representations of H and W. Translate any
   affine-line map to W_K by minus its value at zero. The pointed map factors through
   V_K and W_K, whose intersection is trivial; hence it is zero and W_K is wound.
6. In any other decomposition V' times W', pointed affine-line maps project to zero
   in W'_K. Minimality gives V_K contained in V'_K. Conversely the coordinate axes
   of V'_K factor through V_K, and their sums give the reverse inclusion. Inclusions
   of defining ideals descend through the faithfully flat field extension K/k,
   proving uniqueness as a subgroup of H, with the inclusions respected.
7. If V is trivial, H_K is wound; scalar extension detects equality of maps from
   the affine line, so translation makes every k-map constant. If V is nontrivial,
   a coordinate axis in Ga^d gives a nonconstant map to H, excluding woundness.
   The trivial group and d = 0 are included. No uniqueness of W is claimed: graphs
   of homomorphisms W -> V can give different complements. -/
theorem commutative_p_torsion_vector_wound_factor {k : Type u} [Field k]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (H : Grp (Over (Spec (.of k)))) [IsAffine H.X.left]
    [LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]
    [Smooth H.X.hom] [ConnectedSpace H.X.left] [IsCommMonObj H.X]
    (hp : ∀ (R : Type u) [CommRing R] [Algebra k R]
      (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⟶ H.X), x ^ p = 1)
    (K : Type u) [Field K] [Algebra k K] [IsSepClosure k K] :
    ∃ (V W : Grp (Over (Spec (.of k)))) (i : V ⟶ H) (j : W ⟶ H),
      IsDecomposition K i j ∧
      IsGeneratedByPointedLines ((MultiplicativeType.baseChange (K := K)).map i) ∧
      (Nonempty (V ≅ Grp.trivial (Over (Spec (.of k)))) ↔ IsWoundGroup H) ∧
      ∀ (V' W' : Grp (Over (Spec (.of k)))) (i' : V' ⟶ H) (j' : W' ⟶ H),
        IsDecomposition K i' j' → ∃ e : V ≅ V', e.hom ≫ i' = i := by
  sorry

end AlgebraicGeometry.VectorWoundFactor

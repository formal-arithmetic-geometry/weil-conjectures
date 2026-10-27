module

public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import Sheaf.AlgebraicGeometry.TorusCharacterTangentWeights
public import Sheaf.AlgebraicGeometry.SolvableGroupStructure
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Differential
public import Mathlib.Algebra.DirectSum.Internal
import Sheaf.AlgebraicGeometry.GmRepresentationWeightBasis
import Sheaf.AlgebraicGeometry.TorusFixedSchemeSmooth
import Sheaf.AlgebraicGeometry.TransverseSubgroupProductOpen
import WeilConjectures.AlgebraicGeometry.Regular

/-! # Smooth connected cocharacter limit subgroups

Source: Milne, Algebraic Groups (2017), Definition 13.21, Propositions 13.23--13.24
and 13.29, Theorem 13.33(a)--(c),(e), pp.261--266, and Example 14.13, p.283
(blueprint: lem-sfb-cocharacter-limit-smooth-structure).

The limit conditions use morphisms on the affine line, not just field-valued points.
The semidirect product is specified by its product scheme and its point multiplication.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry.CocharacterLimit

/-- An extension of the conjugation orbit to the affine line over A. The open inclusion
is Spec of k[t] → k[t,t⁻¹], tensored with Spec A. This is equivalently an A-morphism
A¹_A → G_A, by the product universal property. Source: Milne, Proposition 13.24, p.262
(blueprint: lem-sfb-cocharacter-limit-smooth-structure). -/
def IsOrbitExtension {k : Type u} [Field k]
    {G : Grp (Over (Spec (.of k)))}
    (lam : Grp.mk (StandardGroupSchemes.multiplicative k) ⟶ G)
    (A : CommAlgCat.{u} k) (g : StandardGroupSchemes.affine k A ⟶ G.X)
    (q : StandardGroupSchemes.affine k A ⊗ StandardGroupSchemes.additive k ⟶ G.X) : Prop :=
  (𝟙 (StandardGroupSchemes.affine k A) ⊗ₘ
      StandardGroupSchemes.map k (Polynomial.toLaurentAlg (R := k))) ≫ q =
    (snd _ _ ≫ lam.hom.hom) * (fst _ _ ≫ g) * (snd _ _ ≫ lam.hom.hom)⁻¹

/-- The parabolic limit subfunctor, on every commutative test algebra.
Source: Milne, pp.263--264, definition of P_G(λ)
(blueprint: lem-sfb-cocharacter-limit-smooth-structure). -/
def parabolicPoints {k : Type u} [Field k]
    {G : Grp (Over (Spec (.of k)))}
    (lam : Grp.mk (StandardGroupSchemes.multiplicative k) ⟶ G)
    (A : CommAlgCat.{u} k) : Set (StandardGroupSchemes.affine k A ⟶ G.X) :=
  {g | ∃ q, IsOrbitExtension lam A g q}

/-- The contraction subfunctor requires the value at zero to be the group identity.
The identity point of the additive group is its zero section.
Source: Milne, Proposition 13.29, p.264
(blueprint: lem-sfb-cocharacter-limit-smooth-structure). -/
def unipotentPoints {k : Type u} [Field k]
    {G : Grp (Over (Spec (.of k)))}
    (lam : Grp.mk (StandardGroupSchemes.multiplicative k) ⟶ G)
    (A : CommAlgCat.{u} k) : Set (StandardGroupSchemes.affine k A ⟶ G.X) :=
  {g | ∃ q, IsOrbitExtension lam A g q ∧ lift (𝟙 _) 1 ≫ q = 1}

/-- The centralizer subfunctor tests commutation after every algebra map A → B.
Source: Milne, p.264, definition of Z_G(λ), and Section 1 on functorial centralizers
(blueprint: lem-sfb-cocharacter-limit-smooth-structure). -/
def centralizerPoints {k : Type u} [Field k]
    {G : Grp (Over (Spec (.of k)))}
    (lam : Grp.mk (StandardGroupSchemes.multiplicative k) ⟶ G)
    (A : CommAlgCat.{u} k) : Set (StandardGroupSchemes.affine k A ⟶ G.X) :=
  {g | ∀ (B : CommAlgCat.{u} k) (f : A ⟶ B)
    (s : StandardGroupSchemes.affine k B ⟶ StandardGroupSchemes.multiplicative k),
    (StandardGroupSchemes.map k f.hom ≫ g) * (s ≫ lam.hom.hom) =
      (s ≫ lam.hom.hom) * (StandardGroupSchemes.map k f.hom ≫ g)}

/-- Representability, smoothness, connectedness, semidirect product, unipotence and
integer-character Lie weights of the three cocharacter limit functors.
Source: Milne, Theorem 13.33(a)--(c),(e), pp.265--266; Propositions 13.23--13.24
and 13.29, pp.261--264; Example 14.13, p.283
(blueprint: lem-sfb-cocharacter-limit-smooth-structure).

Proof for stage 3, following the node's seven steps:
1. Apply lem-sfb-central-torus-faithful-weight-blocks with the trivial central torus
   to embed G in GL_N, N > 0. Apply lem-sfb-gm-representation-weight-basis to λ and
   order the weights m_i decreasingly. The conjugate entry is t^(m_i-m_j) g_ij.
   Over every A, polynomiality means the negative-weight entries vanish; the limit
   is block diagonal. Its invertible diagonal blocks give an invertible polynomial
   matrix. Limit one means identity diagonal blocks. Commutation with the universal
   Laurent unit means all unequal-weight entries vanish, including over nonreduced A.
2. Intersect G with these block matrix subschemes. An ambient orbit extension factors
   through G since A[t] injects into A[t,t⁻¹]. Apply lem-sfb-smooth-affine-concentrator
   with Z = G and Z = {e} to get P and U smooth; apply lem-sfb-torus-fixed-scheme-smooth
   to conjugation to get Z smooth. The same applies to the negative cocharacter.
3. Uniqueness of extension respects products and inverses. Evaluation at zero gives
   q : P → Z, identity on Z, with kernel U. Thus U is normal in P. Multiplication and
   g ↦ (g q(g)⁻¹, q(g)) are inverse morphisms U × Z ≅ P. Their transported group law
   is (u,z)(u',z') = (u (z u' z⁻¹), z z'), exactly the displayed point formula.
4. Apply lem-sfb-gm-representation-weight-basis to differentiated conjugation. For
   D = k[ε]/ε² the matrix I+εv has orbit I+Σ εt^n v_n. Extension removes n < 0;
   limit one also removes n = 0; constant orbit removes n ≠ 0. Factorization through
   G still holds over D, giving the three equalities of tangent subspaces. The
   character weightSpace uses this actual dual-number action, not the differential
   of t ↦ t^n; hence it also distinguishes weights in positive characteristic.
5. The chosen faithful representation embeds U in upper unitriangular matrices.
   Consequently (u-I)^N = 0 on every geometric point, proving IsUnipotent U.
6. The negative contraction group and P have trivial intersection on all algebras,
   complementary Lie images by step 4, and are smooth by step 2. Apply
   lem-sfb-transverse-subgroup-product-open to obtain an open immersion U_- × P → G.
7. By lem-weil-pbc-smooth-scheme-over-field-regular and lem-sc-regular-connected-integral,
   G is integral. The nonempty big cell is irreducible, hence connected. Projection
   onto P is surjective since it has the identity section, so P is connected.
   The split maps P → Z and P → U likewise prove Z and U connected.
-/
theorem smooth_connected_structure
    {k : Type u} [Field k] [IsAlgClosed k]
    (G : Grp (Over (Spec (.of k))))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (lam : Grp.mk (StandardGroupSchemes.multiplicative k) ⟶ G) :
    ∃ (P U Z : Grp (Over (Spec (.of k)))) (iP : P ⟶ G) (iU : U ⟶ G) (iZ : Z ⟶ G),
      IsClosedSubgroupScheme iP.hom.hom ∧ IsClosedSubgroupScheme iU.hom.hom ∧
      IsClosedSubgroupScheme iZ.hom.hom ∧
      Smooth P.X.hom ∧ Smooth U.X.hom ∧ Smooth Z.X.hom ∧
      ConnectedSpace P.X.left ∧ ConnectedSpace U.X.left ∧ ConnectedSpace Z.X.left ∧
      (∀ (A : CommAlgCat.{u} k) (g : StandardGroupSchemes.affine k A ⟶ G.X),
        (∃ p, p ≫ iP.hom.hom = g) ↔ g ∈ parabolicPoints lam A) ∧
      (∀ (A : CommAlgCat.{u} k) (g : StandardGroupSchemes.affine k A ⟶ G.X),
        (∃ p, p ≫ iU.hom.hom = g) ↔ g ∈ unipotentPoints lam A) ∧
      (∀ (A : CommAlgCat.{u} k) (g : StandardGroupSchemes.affine k A ⟶ G.X),
        (∃ p, p ≫ iZ.hom.hom = g) ↔ g ∈ centralizerPoints lam A) ∧
      (∃ j : U ⟶ P, j ≫ iP = iU ∧ IsNormalSubgroupScheme j.hom.hom) ∧
      (∃ (e : U.X ⊗ Z.X ≅ P.X) (c : Z.X ⊗ U.X ⟶ U.X),
        e.hom ≫ iP.hom.hom = (fst _ _ ≫ iU.hom.hom) * (snd _ _ ≫ iZ.hom.hom) ∧
        c ≫ iU.hom.hom =
          (fst _ _ ≫ iZ.hom.hom) * (snd _ _ ≫ iU.hom.hom) * (fst _ _ ≫ iZ.hom.hom)⁻¹ ∧
        ∀ (A : CommAlgCat.{u} k) (u u' : StandardGroupSchemes.affine k A ⟶ U.X)
          (z z' : StandardGroupSchemes.affine k A ⟶ Z.X),
          (lift u z ≫ e.hom) * (lift u' z' ≫ e.hom) =
            lift (u * (lift z u' ≫ c)) (z * z') ≫ e.hom) ∧
      SolvableGroupStructure.IsUnipotent U ∧
      ∃ (a : ModObj (StandardGroupSchemes.multiplicative k) G.X)
        (chi : ℤ → (Grp.mk (StandardGroupSchemes.multiplicative k) ⟶
          Grp.mk (StandardGroupSchemes.multiplicative k)))
        (W : ℤ → Submodule k (GrpObj.Lie G.X)),
        a.smul = (fst _ _ ≫ lam.hom.hom) * (snd _ _) *
          (fst _ _ ≫ lam.hom.hom)⁻¹ ∧
        (∀ n : ℤ, (chi n).hom.hom = (𝟙 (StandardGroupSchemes.multiplicative k)) ^ n ∧
          W n = @TorusCharacterTangent.weightSpace k _
            (Grp.mk (StandardGroupSchemes.multiplicative k)) G a (chi n)) ∧
        DirectSum.IsInternal W ∧
        (GrpObj.differential iZ.hom.hom).toLinearMap.range = W 0 ∧
        (GrpObj.differential iU.hom.hom).toLinearMap.range = ⨆ (n : ℤ) (_ : 0 < n), W n ∧
        (GrpObj.differential iP.hom.hom).toLinearMap.range = ⨆ (n : ℤ) (_ : 0 ≤ n), W n := by
  sorry

end AlgebraicGeometry.CocharacterLimit

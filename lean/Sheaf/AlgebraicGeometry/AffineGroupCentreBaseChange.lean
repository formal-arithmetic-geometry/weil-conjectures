module

public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Sheaf.AlgebraicGeometry.SolvableGroupStructure
public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.Connected.Basic
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # The scheme-theoretic centre and field base change

Source: Milne, Algebraic Groups (2017), Proposition 1.92 and the following paragraph,
printed pp.33--34 (blueprint: lem-sfb-affine-group-centre-base-change).

The centre condition is the recorded universal centralizer condition for the identity
homomorphism. The scalar-extension assertion uses the actual pullback inclusion: its
image subfunctor equals the centre subfunctor over the extended field. Thus the equality
is one of closed subgroup schemes, retaining nilpotents, and not only of field-valued points.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The centre of an affine finite-type group scheme is represented by a closed normal
commutative subgroup scheme, and its formation commutes with every field extension.
The two set equalities identify the image subfunctors of the inclusions on all algebras.
In particular the second equality identifies the actual pulled-back closed subgroup with
Z(G_K), as a closed subgroup of G_K. No smoothness or connectedness is assumed.

Source: Milne, Algebraic Groups (2017), Proposition 1.92 and the following paragraph,
printed pp.33--34 (blueprint: lem-sfb-affine-group-centre-base-change).

Proof plan:
1. Write G = Spec B. The affine-target morphism equivalence identifies G times G with
   Spec (B tensor B); finite generation gives finite type, and the multiplication map
   B tensor B to B is surjective, so the diagonal is closed and G is separated.
2. Apply lem-sfb-constant-source-closed-factorization-locus to Y = S = G, X = G times G,
   W the diagonal, and (h,g) mapping to (h,ghg^{-1}). Its closed locus L represents the
   condition that conjugation by g on G_T is the identity.
3. For T = Spec A this implies commutation on all A-algebras. Conversely test on
   A tensor B and the universal point; commutation there identifies the two morphisms.
   Thus the image of L(A) is centralizerPoints (identity G) A, naturally in A.
4. Identity, products, inverses and conjugates preserve the condition, so L is a closed
   normal subgroup. Taking the second central point as test point gives commutativity;
   equality of the multiplication morphisms is tested on the universal pair on L times L.
5. For K/k, the base-change clause of the factorization-locus lemma identifies L_K with
   the same conjugation locus in G_K. The fibre-product universal property identifies
   G times T with G_K times T over K for every K-scheme T. Step 3 over K gives the
   second subfunctor equality. On affine coordinates, L_K is Spec(C/I C), C = B tensor K.
   Equality is scheme-theoretic: two closed subschemes having these factorization
   conditions have ideals I,J with J contained in I by testing C to C/I, and conversely
   I contained in J by testing C to C/J. This proves equality as closed subgroup schemes. -/
theorem exists_affine_group_centre_baseChange {k : Type u} [Field k]
    (G : Grp (Over (Spec (.of k)))) (hG : SolvableGroupStructure.IsAlgebraic G) :
    ∃ (Z : Grp (Over (Spec (.of k)))) (i : Z ⟶ G),
      SolvableGroupStructure.IsAlgebraic Z ∧
      IsClosedSubgroupScheme i.hom.hom ∧ IsNormalSubgroupScheme i.hom.hom ∧
      IsCommMonObj Z.X ∧
      (∀ (A : Type u) [CommRing A] [Algebra k A],
        ReductiveTorusCentralizer.centralizerPoints (𝟙 G) A =
          Set.range (fun z : StandardGroupSchemes.affine k A ⟶ Z.X ↦ z ≫ i.hom.hom)) ∧
      ∀ (K : Type u) [Field K] [Algebra k K],
        IsClosedSubgroupScheme ((MultiplicativeType.baseChange (K := K)).map i).hom.hom ∧
        IsNormalSubgroupScheme ((MultiplicativeType.baseChange (K := K)).map i).hom.hom ∧
        IsCommMonObj ((MultiplicativeType.baseChange (K := K)).obj Z).X ∧
        ∀ (A : Type u) [CommRing A] [Algebra K A],
          ReductiveTorusCentralizer.centralizerPoints
              (𝟙 ((MultiplicativeType.baseChange (K := K)).obj G)) A =
            Set.range (fun z : StandardGroupSchemes.affine K A ⟶
              ((MultiplicativeType.baseChange (K := K)).obj Z).X ↦
                z ≫ ((MultiplicativeType.baseChange (K := K)).map i).hom.hom) := by
  sorry

end AlgebraicGeometry

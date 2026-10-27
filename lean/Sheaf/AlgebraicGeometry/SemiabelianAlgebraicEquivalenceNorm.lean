module

public import Sheaf.AlgebraicGeometry.LineAlgebraicEquivalence
public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.AlgebraicGeometry.Ample
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.LocallySurjective
import Sheaf.AlgebraicGeometry.CubicalRigidifiedLine
import WeilConjectures.AlgebraicGeometry.AmplePullback
import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
import Sheaf.AlgebraicGeometry.RelativeAmpleAbsoluteTwist
import Sheaf.AlgebraicGeometry.AffineInvertibleFiniteSetSection
import WeilConjectures.AlgebraicGeometry.AffineCapSectionOpen
import WeilConjectures.AlgebraicGeometry.AmplePositiveTensorPower
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree

/-! # Algebraically trivial lines on a semiabelian variety

Source: Raynaud, Faisceaux amples sur les schemas en groupes et les espaces homogenes,
IV and XI; Moret-Bailly, Pinceaux de varietes abeliennes, I 5 and II 3.3.3.
The geometric algebraic-equivalence and nonsplit formulation is the agent prerequisite
in the DAG, rather than a verbatim source theorem
(blueprint: lem-sfb-semiabelian-algebraic-equivalence-norm).

The exact sequence is over the algebraic closure. Algebraic equivalence uses the
recorded smooth connected parameter families there. Both conclusions are over k.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry.Scheme.Modules

/-- Inversion dualizes a geometrically algebraically trivial line on a semiabelian
variety, its norm is trivial, and tensoring by it preserves absolute ampleness.
Over the algebraic closure, `IsAbelianVariety` is precisely a proper smooth
geometrically connected group scheme. The kernel square and fppf local surjectivity
express the exact sequence, with no splitting hypothesis over the original field.

Source: Raynaud, Faisceaux amples, IV and XI; Moret-Bailly I 5 and II 3.3.3.
The proof below is the agent argument recorded in the DAG
(blueprint: lem-sfb-semiabelian-algebraic-equivalence-norm).

Proof:
1. Choose a frame of the identity fibre of T. By
   lem-sfb-semiabelian-picard-multiplicative-torsor its frame torsor has a
   multiplication equivariant for scalar multiplication. Local frames give
   p1*T tensor p2*T isomorphic to m*T. Pull back along x maps to (x,-x), and
   use the identity frame to trivialize the constant line. Rank-one evaluation
   identifies the second factor with the dual. This works over k itself.
   Iterating multiplication also gives [n]*T isomorphic to T to the n-th power.
2. For ampleness extend k to its algebraic closure, using
   lem-sfb-space-relative-ampleness-fpqc-descent for the faithfully flat affine
   quasi-compact field extension; separability is unnecessary. Relative ampleness
   over a field is absolute ampleness, and tensor pullback respects tensor products.
   Write Q=P tensor T and N=P tensor inversion*P. Step 1 identifies
   Q tensor inversion*Q with N.
3. Rigidify Q at the identity and apply lem-sfb-semiabelian-cubical-rigidification
   over the normal algebraically closed field. Pull the alternating tensor in
   def-sfb-cubical-rigidified-line back along x maps to ([j]x,x,-x).
   For the classes q_j of [j]*Q it gives q_(j+1)+q_(j-1)=2q_j+q_1+q_(-1),
   with q_0=0. Induction yields q_j=j[Q]+j(j-1)/2 ([Q]+[inversion*Q]).
   Thus [n]*Q is Q to the n-th power tensor N to the n(n-1)/2-th power.
4. If P is ample, inversion is an affine isomorphism, so its pullback is ample by
   lem-weil-pbc-pullback-ample-invertible. The ample-tensor theorem lem-sc-ample-tensor
   makes N ample; no properness of H is required.
5. Q is relatively ample for the identity: on each affine V, use
   lem-sfb-affine-invertible-finite-set-section with the singleton x, and
   lem-sc-affine-cap-section-open to get an affine nonvanishing locus through x.
   Apply lem-sfb-relative-ample-absolute-twist to obtain a bound a0 such that
   Q tensor N to the a-th power is ample for all a at least a0.
6. Choose such an a with n=2a+1 invertible in the field. In characteristic two
   every odd n works, in odd characteristic p take a large multiple of p, and
   in characteristic zero there is no restriction. Step 3 identifies [n]*Q with
   (Q tensor N to the a-th power) to the n-th power, ample by
   lem-sc-ample-positive-tensor-power. By lem-sfb-semiabelian-invertible-multiplication,
   [n] is finite etale surjective, hence finite locally free. Apply
   lem-sfb-finite-locally-free-ample-reflection to obtain ampleness of Q.
   Dualizing every family shows T-dual is geometrically algebraically trivial;
   applying the forward implication to Q and T-dual gives the converse.
   Descend both directions back to k using step 2.
-/
theorem semiabelian_algebraic_equivalence_norm
    {k : Type u} [Field k] (H : Grp (Over (Spec (.of k))))
    [IsCommMonObj H.X] [Smooth H.X.hom] [IsSeparated H.X.hom]
    [LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]
    (_hsemi : ∃ (r : ℕ) (A : Grp (Over (Spec (.of (AlgebraicClosure k)))))
      (i : MultiplicativeType.splitTorus (AlgebraicClosure k) r ⟶
        (MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj H)
      (q : (MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj H ⟶ A),
      IsAbelianVariety A.X ∧
      IsPullback i.hom.hom
        (toUnit (MultiplicativeType.splitTorus (AlgebraicClosure k) r).X)
        q.hom.hom η[A.X] ∧
      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (Spec (.of (AlgebraicClosure k))))
        (yoneda.map q.hom.hom))
    (P T : H.X.left.Modules) [P.IsInvertible] [T.IsInvertible]
    (_hT : AreAlgebraicallyEquivalent
      ((MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj H).X
      ((tensorPullback (pullback.fst H.X.hom
        (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))).obj T)
      (𝟙_ (((MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj H).X.left.Modules))) :
    Nonempty ((tensorPullback (ι[H.X]).left).obj T ≅ dual T) ∧
      Nonempty (T ⊗ (tensorPullback (ι[H.X]).left).obj T ≅ 𝟙_ H.X.left.Modules) ∧
      (IsAmple H.X.left (P ⊗ T) ↔ IsAmple H.X.left P) := by
  sorry

end AlgebraicGeometry.Scheme.Modules

module

public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Sheaf.AlgebraicGeometry.GroupScheme.Semisimple
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Sheaf.AlgebraicGeometry.GroupScheme.CentralTorusDerivedProduct
import Sheaf.AlgebraicGeometry.MultiplicativeIsogenyComposition
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! # A central cover of a reductive group by a torus and a simply connected group

Source: Milne, Algebraic Groups (2017), Proposition 21.60(a)--(c), p.442;
Proposition 19.21(c), pp.401--402; Theorem 18.25 and Remark 18.27, p.393;
Definition 18.1 and Proposition 19.15.
(blueprint: lem-sfb-reductive-torus-simply-connected-cover)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- A reductive group over an algebraically closed field has a faithfully flat cover
by a split torus times a semisimple simply connected group, with finite central
scheme-theoretic kernel and injective coordinate pullback. Simple connectedness is
expressed by the central-isogeny criterion, with surjectivity on schemes, rather
than surjectivity on points of a particular field. Centrality is tested on every
scheme over the base and therefore on every scalar algebra, including nonreduced ones.

Source: Milne, Proposition 21.60(a)--(c), p.442, Proposition 19.21(c), pp.401--402,
Theorem 18.25 and Remark 18.27, p.393, Definition 18.1 and Proposition 19.15.
(blueprint: lem-sfb-reductive-torus-simply-connected-cover)

Proof plan:
1. Apply lem-sfb-reductive-radical-quotient to get the central radical torus R and
   semisimple G/R. Over the algebraically closed field, choose R isomorphic to the
   split torus T of rank r, allowing r = 0.
2. Apply lem-sfb-central-torus-semisimple-derived-product. The derived group D is
   semisimple and multiplication R times D to G is faithfully flat with finite
   central kernel of multiplicative type, including its nonreduced scheme structure.
3. Apply lem-sfb-semisimple-multiplicative-universal-cover to obtain a semisimple
   simply connected S and a faithfully flat covering S to D with finite central
   multiplicative kernel N. The trivial group D is allowed.
4. By lem-trf-split-lattice-torus-projection and lem-trf-smooth-composition the
   products T times D and T times S are smooth. The same torus lemma gives geometric
   connectedness of T, and lem-weil-pbc-geometrically-connected-product-components
   makes the products connected. Their coordinate tensor algebras are finitely
   generated, so these products are affine of finite type.
5. The product of T isomorphic to R with S to D is a homomorphism with kernel
   1 times N. Its coordinate extension is faithfully flat: for a module M over
   F[T] tensor F[D], scalar extension is M tensor over F[D] with F[S], which is
   exact and detects zero by the faithful flatness already obtained.
6. Compose this product map with R times D to G. Apply
   lem-sfb-multiplicative-isogeny-composition to obtain faithful flatness and a
   finite central scheme-theoretic kernel.
7. Apply lem-weil-pbc-faithfully-flat-ideal-contraction at the zero ideal to get
   injectivity of the coordinate pullback. The constructions allow r = 0 and S = 1;
   for G = 1 both factors can be trivial. -/
theorem reductive_torus_simplyConnected_cover {F : Type u} [Field F] [IsAlgClosed F]
    (G : Grp (Over (Spec (.of F)))) (hG : ReductiveTorusCentralizer.IsReductive G) :
    ∃ (r : ℕ) (S : Grp (Over (Spec (.of F)))),
      IsSemisimpleGroupScheme S.X ∧
      (∀ (S' : Over (Spec (.of F))) [GrpObj S'],
        IsSemisimpleGroupScheme S' → ∀ (f : S' ⟶ S.X) [IsMonHom f],
        Surjective f.left → IsFinite (GrpObj.ker f).hom →
        (∀ (Z : Over (Spec (.of F))) (x : Z ⟶ GrpObj.ker f) (s : Z ⟶ S'),
          (x ≫ GrpObj.kerι f) * s = s * (x ≫ GrpObj.kerι f)) → IsIso f) ∧
      ∃ (p : (MultiplicativeType.splitTorus F r).X ⊗ S.X ⟶ G.X) (_ : IsMonHom p),
        p.left.appTop.hom.FaithfullyFlat ∧
        IsFinite (GrpObj.ker p).hom ∧
        (∀ (Z : Over (Spec (.of F))) (x : Z ⟶ GrpObj.ker p)
          (g : Z ⟶ (MultiplicativeType.splitTorus F r).X ⊗ S.X),
          (x ≫ GrpObj.kerι p) * g = g * (x ≫ GrpObj.kerι p)) ∧
        Function.Injective p.left.appTop.hom := by
  sorry

end AlgebraicGeometry

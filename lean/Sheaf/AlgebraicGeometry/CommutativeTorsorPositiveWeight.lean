module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import WeilConjectures.AlgebraicGeometry.DensePoints
import WeilConjectures.FieldTheory.FiniteGaloisReceivingSeparableExtensions
import WeilConjectures.AlgebraicGeometry.FiniteGaloisTensorDecomposition
import WeilConjectures.AlgebraicGeometry.FiniteGaloisTensorCoproduct
import WeilConjectures.AlgebraicGeometry.FpqcMorphismsDescend
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Positive-weight morphisms from commutative group torsors

Source: Milne, Algebraic Groups (2017), Lemma 8.22, printed p.152, including its proof.
(blueprint: lem-sfb-commutative-torsor-positive-weight)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- A torsor under a smooth separated geometrically integral commutative group scheme
of finite type admits a morphism of positive weight. The action and its laws are
morphisms over Spec k; no rational point of the torsor is chosen or assumed.
Source: Milne, Algebraic Groups (2017), Lemma 8.22, printed p.152.
(blueprint: lem-sfb-commutative-torsor-positive-weight)

Proof:
1. The structure map of V is flat, surjective and quasi-compact. After pulling it
   back along itself, the torsor isomorphism identifies it with the smooth projection
   V times H to V. Smooth base change (lem-pc-proper-base-change) and fpqc descent
   (lem-trf-smooth-fpqc-base-descent) therefore make V smooth. Surjectivity makes V nonempty.
2. Density of separable closed points (lem-pc-dense-separable-points) supplies a point
   with finite separable residue field. Embed that field in a finite Galois extension L/k
   by lem-weil-pbc-finite-galois-receiving-separable-extensions, obtaining p in V(L).
3. For any point b over an extension E, the torsor isomorphism gives an inverse d_b
   to translation H_E to V_E. Associativity gives d_b(v+h)=d_b(v)+h on every test scheme.
   These are morphism identities by the fibre-product universal property
   (def-pc-fibre-product) and the group laws (def-sc-group-scheme).
4. Let Gamma=Aut_k(L) and n=|Gamma|>0. The finite Galois tensor decomposition
   (lem-exc-finite-galois-tensor-decomposition and
   lem-exc-finite-galois-algebra-tensor-decomposition) identifies the double overlap
   with copies of Spec L indexed by Gamma. Sum d_(sigma p) over all sigma in Gamma,
   retaining repetitions. Transport by tau carries d_b to d_(tau b); commutativity
   makes this sum F invariant under Gamma.
5. Spec L to Spec k is an fpqc cover (def-weil-pbc-fpqc-covering and
   lem-weil-pbc-field-extension-base-change-faithfully-flat). Invariance says that F
   respects the descent data on each component of the overlap. Surjectivity in
   lem-galois-fpqc-morphisms-descend descends F to a k-morphism phi.
6. Summing the identities in step 3 gives F(v+h)=F(v)+nh as an identity of morphisms.
   The repeated-sum map [n] commutes with scalar extension (def-sc-group-scheme).
7. Injectivity in lem-galois-fpqc-morphisms-descend, with source V times H, descends
   that identity to k. If V already has a k-point b, d_b itself has weight one.
   The general construction needs neither a k-point nor division by n. -/
theorem commutative_torsor_positive_weight (k : Type u) [Field k]
    (H V : Over (Spec (.of k))) [GrpObj H] [IsCommMonObj H]
    [Smooth H.hom] [IsSeparated H.hom] [LocallyOfFiniteType H.hom] [QuasiCompact H.hom]
    [GeometricallyIntegral H.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [Flat V.hom] [Surjective V.hom]
    (a : V ⊗ H ⟶ V)
    (hunit : ∀ (T : Over (Spec (.of k))) (v : T ⟶ V), lift v 1 ≫ a = v)
    (hassoc : ∀ (T : Over (Spec (.of k))) (v : T ⟶ V) (g h : T ⟶ H),
      lift (lift v g ≫ a) h ≫ a = lift v (g * h) ≫ a)
    [IsIso (lift (fst V H) a)] :
    ∃ (n : ℕ), 0 < n ∧ ∃ (φ : V ⟶ H),
      a ≫ φ = lift (fst V H ≫ φ) (snd V H ≫ (𝟙 H ^ n)) ≫ μ[H] := by
  sorry

end AlgebraicGeometry

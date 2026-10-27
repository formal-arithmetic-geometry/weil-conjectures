module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.RingTheory.Finiteness.Defs
import WeilConjectures.AlgebraicGeometry.LocallyOfFiniteTypeOfIsLocallyQuasiFinite
import Sheaf.RingTheory.QuasiFiniteAtPrimeZeroFibreDimension
import WeilConjectures.Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres
import Sheaf.AlgebraicGeometry.SpaceSmoothReducedLocality
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Artinian.Module

/-!
# Reduced locally quasi-finite algebraic spaces over a field

Source: Stacks Project, Spaces over Fields, Tag 06S0,
Lemma `lemma-locally-quasi-finite-over-field`, (1) implies (5), reduced specialization
(blueprint: lem-sfb-reduced-quasifinite-space-field-decomposition).

The disjoint union is a coproduct of schemes with its canonical map to the field spectrum.
Its represented presheaf is therefore already over the field, so the displayed presheaf
isomorphism is precisely an isomorphism of algebraic spaces over that field.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A reduced algebraic space locally quasi-finite over a field is a disjoint union of
spectra of finite field extensions. The index set may be empty or infinite; the field
extensions need not be separable.

Source: Stacks Project, Spaces over Fields, Tag 06S0,
Lemma `lemma-locally-quasi-finite-over-field`, (1) implies (5), reduced specialization
(blueprint: lem-sfb-reduced-quasifinite-space-field-decomposition).

Proof:
1. For every etale scheme chart V, local quasi-finiteness implies local finite type by
   lem-weil-pbc-lqf-locally-finite-type. On an affine neighbourhood Spec A of each point,
   pqf-def-quasifinite gives a finite-type quasi-finite ring map k -> A at its prime.
   By lem-weil-pbc-ring-quasifinite-zero-fibre-dimension the local fibre dimension is zero.
   Since the base is Spec k, the fibre algebra is A tensor_k k = A. The neighbourhood
   infimum of def-kun-topological-dimension-at-point then gives local dimension zero on V
   and hence on X; the empty case has empty supremum.
2. Apply lem-sfb-zero-dimensional-field-space-components. It identifies X over k with
   a disjoint union of Spec A_i for nonzero local Artinian finite-dimensional k-algebras.
   No separation or quasi-compactness hypothesis is required.
3. The reduced etale atlas in the hypothesis is smooth by
   lem-weil-pbc-etale-smooth-zero-dimensional-fibres and remains surjective after X is
   represented by a scheme. Descent in lem-sfb-space-smooth-reduced-locality makes X
   reduced. Each open component is reduced; the local-ring/section equivalence in
   def-pc-reduced-scheme makes its coordinate algebra A_i reduced.
4. By lem-sfb-reduced-artinian-residue-product, A_i is its product of residue fields.
   Locality makes this the single residue field at its unique maximal ideal. Transport
   the field structure to the same ring A_i, calling it K_i. Its unital k-algebra map
   is injective because k is a field and A_i is nonzero. Its vector-space dimension is
   still finite. The rings and structure maps did not change, so the coproduct
   identification remains over k. For empty X take the empty index set. -/
theorem exists_iso_coproduct_spec_finite_fields_of_reduced_locallyQuasiFinite
    (k : Type u) [Field k] (X : AlgebraicSpace (Spec (.of k)))
    (hreduced : ∃ (U : Over (Spec (.of k))) (a : yoneda.obj U ⟶ X.obj.obj),
      IsEtale a ∧ IsSurjective a ∧
        ∀ x : U.left, _root_.IsReduced (U.left.presheaf.stalk x))
    (hquasifinite : ∀ (V : Over (Spec (.of k))) (a : yoneda.obj V ⟶ X.obj.obj),
      IsEtale a → V.hom.IsLocallyQuasiFinite) :
    ∃ (I : Type u) (K : I → Type u) (_ : ∀ i, Field (K i)) (_ : ∀ i, Algebra k (K i)),
      (∀ i, Module.Finite k (K i)) ∧
        Nonempty (X.obj.obj ≅ yoneda.obj (Over.mk
          (Sigma.desc fun i : I ↦ Spec.map (CommRingCat.ofHom (algebraMap k (K i)))))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace

module

public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import Mathlib.RingTheory.Bialgebra.Hom
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Sheaf.RingTheory.HopfAlgebra.ReducedCoreNilpotentFibre

/-! # Faithful flatness of a finite type commutative Hopf algebra inclusion

Source: Milne, Algebraic Groups (2017), Theorem 3.31, printed pp. 73--74;
Definitions 3.3 and 3.8, printed pp. 65--67, for the Hopf algebra convention.
(blueprint: lem-sfb-hopf-subalgebra-faithfully-flat)
-/

@[expose] public section

universe u v w

namespace HopfAlgebra

/-- An injective homomorphism between finite type commutative Hopf algebras over any
field makes its codomain faithfully flat over its domain, using the module structure
induced by that homomorphism. A `BialgHom` preserves comultiplication and counit;
`hS` explicitly requires preservation of the antipode. For a commutative algebra,
`antipodeAlgHom` expresses the antipode as an algebra homomorphism.

Source: Milne, Algebraic Groups (2017), Theorem 3.31, printed pp. 73--74;
Definitions 3.3 and 3.8, printed pp. 65--67.
(blueprint: lem-sfb-hopf-subalgebra-faithfully-flat)

Proof plan:
1. Extend scalars to an algebraic closure `K` of `k` (def-weil-algebraic-closure).
   The maps from `A` and `B` to their scalar extensions are faithfully flat by
   lem-weil-pbc-field-extension-base-change-faithfully-flat. The same lemma for
   `D = k` and lem-trf-flat-tensor-preserves-injection show that the extended map
   is injective. Algebra generators extend to generators. Extend all Hopf maps
   using lem-weil-pbc-algebra-tensor-pushout-universal-property; their identities
   extend by tensoring. It suffices to prove the algebraically closed case and descend.
2. By lem-sfb-hopf-reduced-core-nilpotent-fibre choose a finite type reduced Hopf
   subalgebra `C` of `A`, with `D = A/(C⁺A)` having nilpotent augmentation ideal.
   Put `E = B/(i(C⁺)B)`. The composite `C → B` is injective and Hopf, hence faithfully
   flat by lem-sfb-reduced-target-dominant-group-flatness. Only `C` is reduced here.
3. Apply lem-sfb-hopf-relative-kernel-shear. Its quotient Hopf map `α : D → E`
   and shear isomorphisms identify `i ⊗[C] 1` with `α ⊗[k] 1`. Flatness of `B/C`
   and lem-trf-flat-tensor-preserves-injection make the first map injective.
   The counit makes `B` nonzero. A nonempty vector-space basis makes `B` faithfully
   flat over `k`: tensoring a complex gives a nonempty direct sum of copies, which
   is exact exactly when the complex is. Thus α is injective by
   lem-trf-faithfully-flat-ltensor-injective-reflection, interchanging tensor factors.
4. The quotient Hopf algebras `D,E` are finite type. Lift a vector-space basis of
   `E/(α(D⁺)E)` to `E`. By lem-sfb-nilpotent-hopf-basis-lifting the lifts exhibit
   `E` as a direct sum of copies of `D`. The counit makes this quotient nonzero,
   so the basis is nonempty. Tensoring with this free module preserves and reflects
   exactness coordinate by coordinate; hence α is faithfully flat.
5. By lem-weil-pbc-faithfully-flat-base-change, `α ⊗[k] 1` is faithfully flat:
   its codomain is `E ⊗[D] (D ⊗[k] B)` under `e ⊗ (d ⊗ b) ↦ eα(d) ⊗ b`,
   with inverse `e ⊗ b ↦ e ⊗ (1 ⊗ b)`. Transfer through the shears to
   `i ⊗[C] 1`. Put `R = A ⊗[C] B`; `A → R` is faithfully flat by base change
   from `C → B`. For a complex `L` of `A`-modules, the associativity isomorphism
   `R ⊗[A] (L ⊗[A] B) ≃ (R ⊗[A] L) ⊗[R] (B ⊗[C] B)` sends
   `(a ⊗ b) ⊗ (l ⊗ x)` to `((a ⊗ b) ⊗ l) ⊗ (x ⊗ 1)`; its inverse sends
   `((a ⊗ b) ⊗ l) ⊗ (x ⊗ y)` to `(a ⊗ by) ⊗ (l ⊗ x)`.
   Faithful flatness on both sides shows that `L ⊗[A] B` is exact iff `L` is exact.
6. Apply the algebraically closed case to the scalar extension from step 1.
   The canonical isomorphism
   `A_K ⊗[A] (L ⊗[A] B) ≃ (A_K ⊗[A] L) ⊗[A_K] B_K`
   sends `(a ⊗ c) ⊗ (l ⊗ b)` to `((a ⊗ 1) ⊗ l) ⊗ (b ⊗ c)`;
   the inverse sends `((a ⊗ c) ⊗ l) ⊗ (b ⊗ d)` to `(a ⊗ cd) ⊗ (l ⊗ b)`.
   Faithful flatness of `A → A_K` and of `A_K → B_K` now shows that tensoring
   with `B` preserves and reflects exactness over `A`, as required. -/
theorem faithfullyFlat_of_injective
    (k : Type u) (A : Type v) (B : Type w) [Field k] [CommRing A] [CommRing B]
    [HopfAlgebra k A] [HopfAlgebra k B]
    (hA : (algebraMap k A).FiniteType) (hB : (algebraMap k B).FiniteType)
    (i : A →ₐc[k] B) (hi : Function.Injective i)
    (hS : ∀ a : A, antipode k (i a) = i (antipode k a)) :
    @Module.FaithfullyFlat A B _ _ i.toAlgHom.toRingHom.toAlgebra.toModule := by
  sorry

end HopfAlgebra

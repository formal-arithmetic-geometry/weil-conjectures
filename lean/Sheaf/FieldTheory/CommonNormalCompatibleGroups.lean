module

public import Sheaf.FieldTheory.FieldTower
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.Algebra.Group.Prod

import WeilConjectures.FieldTheory.CommonExtensionFields
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.FieldTheory.Normal.Basic
import WeilConjectures.FieldTheory.NormalExtensionFixedFieldPurelyInseparable

/-!
# Simultaneous normal constants and compatible finite product groups

Source: ILO, Travaux de Gabber, X 2.3 Step 2, printed pp. 150–151, graph enlargement
before (2.b), with the finite-family field elaboration in the DAG; Stacks Tags 09DT,
0BME (2), and 030M (2). (blueprint: lem-sfb-common-normal-compatible-groups)
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

namespace Field

/-- A finite family of finite extensions and finite group actions admits simultaneous
normal constants and the compatible subgroups of the specified product group.

Source: ILO, Travaux de Gabber, X 2.3 Step 2, pp. 150–151, graph enlargement before
(2.b); Stacks Tags 09DT, 0BME (2), 030M (2).
(blueprint: lem-sfb-common-normal-compatible-groups)

Proof:
1. Enumerate the finite family. Starting from e, successively use
   lem-weil-common-extension-fields to put the previous field and the next F i into
   a common field, identifying their copies of e. Take their compositum and apply
   lem-weil-pbc-compositum-degree-bound. Products of the two finite spanning sets
   span this compositum over e, so the iteration gives a finite common extension.
   Compose the previous embeddings with the inclusions at every step.
2. Apply lem-weil-pbc-finite-extension-in-finite-normal-extension to this extension.
   Compose its embeddings with the resulting inclusion to obtain the maps emb i.
3. By lem-weil-pbc-finite-extension-finitely-many-embeddings there are finitely many
   e-algebra maps K to K, hence finitely many automorphisms. The product group is
   finite. The map a to (a,1) is a section of its first projection.
4. For each i, take Gamma i to be precisely the compatible pairs. Identities are
   compatible. Multiplying two compatibility equations and using the homomorphism
   law of rho proves closure under multiplication. Composing a compatibility equation
   with the two inverse automorphisms proves closure under inverses. Restricting the
   ith coordinate projection gives the homomorphism r i.
5. Given j in J i, conjugate rho i j by emb i to an automorphism of its image field.
   By lem-sfb-normal-intermediate-isomorphism-lifts this extends to an e-automorphism
   a of K. Pair a with the tuple having coordinate j at i and identity elsewhere.
   This lies in Gamma i and maps to j, proving surjectivity, without faithfulness.
6. An element of ker (r i) has identity ith coordinate, so its first coordinate fixes
   emb i pointwise. Conversely, pair any such fixing automorphism with the identity
   tuple to obtain an element of ker (r i). These are the two subgroup inclusions
   in the asserted equality after applying the first projection.
7. The first projection is surjective, so its image is the full automorphism group.
   Apply lem-weil-pbc-normal-extension-fixed-field-purely-inseparable to identify its
   fixed field as purely inseparable over e. No separability is used. -/
theorem exists_common_normal_compatible_groups
    (e : Type u) [Field e] (I : Type w) [Finite I] [Nonempty I]
    (F : I → Type v) [∀ i, Field (F i)] [∀ i, Algebra e (F i)]
    [∀ i, Module.Finite e (F i)]
    (J : I → Type z) [∀ i, Group (J i)] [∀ i, Finite (J i)]
    (rho : ∀ i, J i →* (F i ≃ₐ[e] F i)) :
    ∃ (K : Type (max u v)) (_ : Field K) (_ : Algebra e K)
      (_ : Module.Finite e K) (_ : Normal e K) (emb : ∀ i, F i →ₐ[e] K),
      Finite (K ≃ₐ[e] K) ∧
      Finite ((K ≃ₐ[e] K) × (∀ t, J t)) ∧
      Function.Surjective (MonoidHom.fst (K ≃ₐ[e] K) (∀ t, J t)) ∧
      (∃ (Gamma : I → Subgroup ((K ≃ₐ[e] K) × (∀ t, J t)))
        (r : ∀ i, Gamma i →* J i),
        (∀ (i : I) (g : (K ≃ₐ[e] K) × (∀ t, J t)),
          g ∈ Gamma i ↔ g.1.toAlgHom.comp (emb i) = (emb i).comp (rho i (g.2 i)).toAlgHom) ∧
        (∀ (i : I) (g : Gamma i), r i g = g.val.2 i) ∧
        (∀ i : I, Function.Surjective (r i)) ∧
        (∀ i : I, (r i).ker.map
          ((MonoidHom.fst (K ≃ₐ[e] K) (∀ t, J t)).comp (Gamma i).subtype) =
            (emb i).fieldRange.fixingSubgroup)) ∧
      IsPurelyInseparable e
        (IntermediateField.fixedField (MonoidHom.fst (K ≃ₐ[e] K) (∀ t, J t)).range) := by
  sorry

end Field

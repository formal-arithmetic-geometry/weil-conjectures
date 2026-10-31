/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Native.NativeOpenTensorDescentData

/-! # Normalized native open tensor restriction descent

Source: Stacks 0GL1, 06YN and 012Z; native open tensor proof steps 3--6.
(blueprint: lem-sf-native-open-tensor-restriction-descent)
-/

@[expose] public noncomputable section

set_option autoImplicit false

attribute [local irreducible]
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedClosedComparison

universe u a b

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

variable {U Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ Z) [IsOpenImmersion j]
  [j.IsOver (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]

/-- Totalize the balanced restriction comparison and descend it to the derived category.

Source: Stacks Project, sites-cohomology.tex, Lemma pullback-tensor-product,
K-flat resolutions (Tag 06YS), and homology.tex, associated simple complex (Tag 012Z).
(blueprint: lem-sf-native-open-tensor-restriction-descent)

Proof: use the supplied representative models, summand insertions and sheaf
comparisons. The six equalities in hm identify each with the actual native
function, so all the native model naturality and sheaf-map properties transfer.
The preservation field is the given restriction property of s.

Then s.restriction_forget identifies the underlying map with the canonical
balanced pullback tensor comparison. That comparison is natural in both sheaves;
faithfulness of forgetting Frobenius proves the same naturality for the specified
Weil map. Restriction preserves coproducts and is additive, so apply these maps
and their inverses in every bidegree and sum over p+q=n. Naturality with the two
differentials, including the sign (-1)^p on the second one, gives a chain
isomorphism. Its composite with the image of each actual insertion is the given
sheaf map followed by the target insertion, yielding the first conclusion.
Use the flat-term equivariant K-flat resolutions on the twisted action site.
The hypothesis s.restriction_kflat keeps restriction inside the resolving
subcategory. On pairs of representatives compose inverse native tensor models,
Q of the total comparison, and the exact-derived restriction factors, obtaining
an isomorphism between the restrictions of the two derived bifunctors.
The models are natural by nativeDerivedTensor_models.choose_spec. Fully faithful
restriction to the resolving representatives descends this comparison and its
inverse, including naturality, to all derived inputs. Cancelling the model
isomorphisms gives exactly OpenTensorRestrictionNormalization. This constructs
rho rather than asserting that an arbitrary isomorphism has the normalization.
Retain the same comparison with exactly the native functor types and its
heterogeneous equality to the generic comparison.
The zero and empty cases use the same coproduct maps. -/
theorem native_open_tensor_restriction_descent (s : NativeOpenTensorData k₀ l j)
    (m : OpenTensorDescentModels (nativeOpenTensorDescentInput k₀ l j))
    (hm : NativeOpenTensorModelsCompatibility k₀ l j s m) :
    Nonempty (NativeOpenTensorRestrictionDescentData k₀ l j s m) := by
  sorry

end AlgebraicGeometry.ProEtaleWeilSheaf

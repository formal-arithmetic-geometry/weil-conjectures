/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Sheaf.AlgebraicGeometry.BoundedConstructibleHomOfPreserves
public import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale

/-!
# The restricted tensor–Hom adjunction under preservation hypotheses

Source: Weil conjectures blueprint, main-20261015, `sec-six-functors-basics`,
`sk-def-sfb-dc-restricted-functors/def-sfb-dc-tensor-hom-adjunction.md`
(blueprint: def-sfb-dc-tensor-hom-adjunction).

Both preservation hypotheses are retained for an arbitrary commutative condensed ring.
The tensor restriction is the `ObjectProperty.lift` specified by `def-sfb-dc-tensor`.
The Hom restriction and its identity-component comparison are those of `def-sfb-dc-hom`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Opposite

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- For fixed bounded constructible `K`, restrict the ambient relative derived tensor–Hom
adjunction along the fully faithful inclusion of bounded constructible module objects.

Source: blueprint `sk-def-sfb-dc-restricted-functors/def-sfb-dc-tensor-hom-adjunction.md`
(blueprint: def-sfb-dc-tensor-hom-adjunction).

Construction, following the node's three steps:
1. Use `derivedTensorHomAdjunction Λ K.obj` on the ambient ordinary derived category of
module objects over `condensedRingObj Λ X.left`. This is the relative derived tensor
over the pulled-back ring object, with its closed internal Hom.
2. The two preservation hypotheses put all tensor and Hom values back in the full
subcategory. The fixed-`K` tensor lift commutes with inclusion by `liftCompιIso`;
the specified Hom restriction uses `boundedConstructibleHomOfPreservesObjCompatibility`.
Both comparisons have identity components.
3. Apply `Adjunction.restrictFullyFaithful` with these comparisons. Its Hom equivalence
is inclusion, the ambient Hom equivalence, then the inverse inclusion; its inverse uses
the inverse ambient equivalence. Ambient naturality gives naturality in both variables.
The unit and counit are the images of the respective identities under these equivalences,
so inclusion identifies them with the ambient unit and counit. No adjunction is chosen. -/
noncomputable def boundedConstructibleTensorHomAdjunctionOfPreserves
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom]
    (hT : ∀ A B : BoundedConstructible (condensedRingObj Λ X.left),
      boundedConstructible (condensedRingObj Λ X.left)
        (((derivedTensor Λ X.left).obj A.obj).obj B.obj))
    (hH : ∀ A B : BoundedConstructible (condensedRingObj Λ X.left),
      boundedConstructible (condensedRingObj Λ X.left)
        (((derivedHom Λ X.left).obj (op A.obj)).obj B.obj))
    (K : BoundedConstructible (condensedRingObj Λ X.left)) :
    (boundedConstructible (condensedRingObj Λ X.left)).lift
        ((boundedConstructible _).ι ⋙ (derivedTensor Λ X.left).obj K.obj)
        (fun A ↦ hT K A) ⊣
      (boundedConstructibleHomOfPreserves Λ ℓ X hH).obj (op K) :=
  (derivedTensorHomAdjunction Λ K.obj).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (ObjectProperty.liftCompιIso _ _ _).symm
    (boundedConstructibleHomOfPreservesObjCompatibility Λ ℓ X hH K).symm

end AlgebraicGeometry.ProEtale.CondensedRing

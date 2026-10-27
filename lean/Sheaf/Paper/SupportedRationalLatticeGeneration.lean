/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M5
-/
module

public import Sheaf.Paper.SupportedCoefficientLocalization
public import Sheaf.Paper.QcqsOpenClosedTree
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-! # Finite generation by localized supported integral models

Source: steps 1--3 and 7 of lem-sfb-supported-rational-model-rigidity-transfer;
qcqs stratified integral lattices and Stacks Project, Tag 09AH.
(blueprint: lem-sfb-supported-rational-lattice-generation).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Rationalizations of integral finite local models, with their actual support functors.
Isomorphisms are taken in the ordinary derived category, with no restriction on maps
between the generators.
Source: steps 1--3 of the supported rational transfer argument
(blueprint: lem-sfb-supported-rational-lattice-generation). -/
def IsLocalizedSupportedModel
    {R K : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj K] [IsCommMonObj K]
    (a : Mon.mk R ⟶ Mon.mk K) (T : Scheme.{u}) :
    ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj K T))) :=
  fun M ↦ ∃ (S : Scheme.{u}) (tree : QcqsOpenClosedTree T) (p : tree.Path S)
    (H : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj R S)),
    HasFiniteConstantLocalModel R S H ∧
    Nonempty (M ≅ (DerivedCategory.singleFunctor _ 0).obj
      ((Mod.extendScalars (coefficientMap a.hom T)).obj ((p.extension R).obj H)))

/-- Every supported rational finite model is a finite extension of localized supported
integral finite models. The coefficient map is compatible with the regular telescope
at every scheme. This statement contains no closed-pair or cohomological hypothesis.

Source: steps 1--3 and 7 of lem-sfb-supported-rational-model-rigidity-transfer;
qcqs stratified integral lattices and Stacks Project, Tag 09AH.
(blueprint: lem-sfb-supported-rational-lattice-generation).

Proof: Transport the standard inclusion Z_ell -> Q_ell or O_E -> E along the two
specified ring isomorphisms. For Q_ell use the bottom finite intermediate field.
The coefficient-localization theorem, transported along these isomorphisms, gives
the specified regular telescope and exactness at every scheme. On each qcqs source
of a path a finite scalar model over the field is lisse: finite presentation over
the scalar field gives a finite basis, and the constant finite-free comparison
identifies its pullback with a finite power of the coefficient ring. Apply the
finite-extension stratified integral-lattice theorem. Refine the one-vertex tree
by its finite constructible lattice partition, using actual scheme factorizations.
On each nonempty refined leaf pull back its lisse integral lattice; empty leaves
carry zero. Each lattice is a finite scalar local model. Append its branch to the
original support path, adjoining complementary sibling leaves, so the appended
path is again admissible. The lattice-tree scalar comparison, and the open and
closed projection formulas on the original path, identify the rational supported
leaf with the scalar extension of its integral supported branch model. Exactness
of all edge functors carries each open-closed short exact sequence to a short
exact sequence on the root. Its degree-zero complexes give a distinguished
triangle. Induct on the finite refined tree and combine the extension products
by associativity; each leaf supplies one generator, and the root gives the
claimed finite iterated extension. All maps of these triangles are the actual
maps over K; no descent of transition maps is required. Rank zero, varying ranks,
empty sources and the root path are included. -/
theorem supported_rational_lattice_generation
    (ℓ : ℕ) [Fact ℓ.Prime]
    (R K : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] [MonObj K] [IsCommMonObj K]
    (hRK :
      (Nonempty (Mon.mk R ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∧
        Nonempty (Mon.mk K ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ]))) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk R ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E)) ∧
        Nonempty (Mon.mk K ≅ Mon.mk (Profinite.continuousMapRingObj E))))
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T] :
    ∃ a : Mon.mk R ⟶ Mon.mk K, IsEllLocalizationCoefficient ℓ a ∧
      ∀ (S : Scheme.{u}) (tree : QcqsOpenClosedTree T) (p : tree.Path S)
        (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj K S)),
        HasFiniteConstantLocalModel K S L →
        ∃ n : ℕ, (IsLocalizedSupportedModel a T).extensionProductIter n
          ((DerivedCategory.singleFunctor _ 0).obj ((p.extension K).obj L)) := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing

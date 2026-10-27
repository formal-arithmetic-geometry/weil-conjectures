/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G7
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.QcqsOpenClosedTree
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Filtered.Basic

/-! # The explicit derived hull of supported finite scalar models

The two definitions are moved verbatim from SupportedImageBoundedDerivedGeneration
so the independent kernel-generation and support-extension inputs can use the same hull.
Source: blueprint latest, det-sf-comp-coherence-refinement.proof.md, (2), first paragraph
(blueprint: lem-sfb-supported-image-bounded-derived-generation).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The admissible full replete classes defining the hull in the node. Triangulated
means zero, all integer shifts and distinguished-triangle extensions. The remaining
clauses specify actual retract diagrams, all small derived products, all supported
finite scalar models in degree zero, and strict filtered diagrams with a common
termwise lower bound. Colimits of complexes are computed termwise in module sheaves.
Arbitrary limiting cones and colimiting cocones express the usual universal properties
without making choices of products or colimits.
Source: blueprint latest, det-sf-comp-coherence-refinement.proof.md, (2), first paragraph;
the explicit hull paragraph of the structural image-generation input
(blueprint: lem-sfb-supported-image-bounded-derived-generation). -/
def IsSupportedImageGenerationClass (X : Scheme.{u})
    (P : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))) : Prop :=
  P.IsTriangulated ∧ P.IsClosedUnderIsomorphisms ∧
  (∀ (K L : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (i : K ⟶ L) (p : L ⟶ K), i ≫ p = 𝟙 K → P L → P K) ∧
  (∀ (I : Type (u + 1))
    (K : I → DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (c : Fan K), IsLimit c → (∀ i : I, P (K i)) → P c.pt) ∧
  (∀ (tree : QcqsOpenClosedTree X) (S : Scheme.{u}) (p : tree.Path S)
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)),
    HasFiniteConstantLocalModel Λ S L →
      P ((DerivedCategory.singleFunctor _ 0).obj ((p.extension Λ).obj L))) ∧
  (∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ)
    (a : ℤ) (c : Cocone D), IsColimit c →
    (∀ i : I, (D.obj i).IsStrictlyGE a) →
    (∀ i : I, P (DerivedCategory.Q.obj (D.obj i))) → P (DerivedCategory.Q.obj c.pt))

/-- The intersection of exactly the full replete classes in the preceding definition.
This is the specified hull, with no replacement by a localizing or constructible hull.
Source: blueprint latest, det-sf-comp-coherence-refinement.proof.md, (2), first paragraph;
the explicit hull paragraph of the structural image-generation input
(blueprint: lem-sfb-supported-image-bounded-derived-generation). -/
def supportedImageGenerationHull (X : Scheme.{u}) : ObjectProperty (DerivedCategory
    (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :=
  fun K ↦ ∀ P : ObjectProperty (DerivedCategory
    (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
    IsSupportedImageGenerationClass Λ X P → P K

end AlgebraicGeometry.ProEtale.CondensedRing

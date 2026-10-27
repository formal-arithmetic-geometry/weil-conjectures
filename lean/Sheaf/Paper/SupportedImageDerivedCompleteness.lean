/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Sheaf.Paper.QcqsOpenClosedTree
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.SixFunctors.ProEtale.DerivedCompletion
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Abelian.Images
import Sheaf.Paper.SupportedKernelImageBaseComplete
import Sheaf.Paper.SupportedKernelImageExtensionComplete

/-!
# Derived completeness of supported integral kernels and images

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 3.4.14 and
Sections 3.4--3.5; Stacks Tags 09AA, 09AH, 09BM, 09BN for support operations
(blueprint: lem-sfb-supported-image-derived-completeness).

Paths in the existing finite open-closed tree encode all support chains over an
affine scheme: every vertex is qcqs, and a complementary sibling can be a leaf.
The root path encodes the empty chain. The extension functor uses the actual
open extension by zero and closed direct image, before the site-object pullback.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The ordinary categorical kernel and image of any map between finite scalar local
models are derived complete, on their source and after any allowed support chain
and affine pro-etale restriction. Completeness uses the specified quotient-tower
augmentation in the ordinary uncompleted internal-module derived category.

Source: Bhatt--Scholze, Lemma 3.4.14, Proposition 3.5.1 and Definition 3.5.2;
HRS Section 7.1.1 for scalar local models; Stacks Tags 09AA, 09AH, 09BM, 09BN
for the supported specialization. The exact reference for support preservation
is WANTED, as recorded in the node.
(blueprint: lem-sfb-supported-image-derived-completeness)

Proof: supported_kernel_image_base_complete applies finite-model completeness,
the strict section-action comparison, the normalized principal-completion model
comparison, and complete_heart_kernels to the actual map. Exact equivalences transport
its kernel and image conclusions back to internal modules. Apply
supported_extension_derived_complete to each resulting complete module. That theorem
uses the complementary support restrictions, their actual units and counits, and joint
isomorphism detection to preserve completeness under each open or closed extension.
Induction gives the finite path; strict completion comparison gives the final pro-etale
restriction. The empty path, zero maps and torsion scalar models are included.
-/
theorem supported_kernel_image_derived_complete
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsAffine X]
    {S : Scheme.{u}} (tree : QcqsOpenClosedTree X) (p : tree.Path S)
    (L M : AdicCompletion.Modules l E S) (f : L ⟶ M)
    (hL : HasFiniteConstantLocalModel (DerivedNakayama.integerRing l E) S L)
    (hM : HasFiniteConstantLocalModel (DerivedNakayama.integerRing l E) S M)
    (U : X.ProEt) [IsAffine U.left] :
    IsDerivedComplete l E S ((DerivedCategory.singleFunctor _ 0).obj (kernel f)) ∧
    IsDerivedComplete l E S ((DerivedCategory.singleFunctor _ 0).obj (image f)) ∧
    IsDerivedComplete l E U.left ((DerivedCategory.singleFunctor _ 0).obj
      ((CondensedRing.upperStar (DerivedNakayama.integerRing l E) U.hom).obj
        ((p.extension (DerivedNakayama.integerRing l E)).obj (kernel f)))) ∧
    IsDerivedComplete l E U.left ((DerivedCategory.singleFunctor _ 0).obj
      ((CondensedRing.upperStar (DerivedNakayama.integerRing l E) U.hom).obj
        ((p.extension (DerivedNakayama.integerRing l E)).obj (image f)))) := by
  obtain ⟨hK, hI⟩ := supported_kernel_image_base_complete l E L M f hL hM
  exact ⟨hK, hI, supported_extension_derived_complete l E p (kernel f) hK U,
    supported_extension_derived_complete l E p (image f) hI U⟩

end AlgebraicGeometry.ProEtale

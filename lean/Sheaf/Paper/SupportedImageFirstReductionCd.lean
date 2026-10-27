/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y7
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.QcqsOpenClosedTree
public import Sheaf.Paper.CondensedQcqsPushforwardContinuity
public import Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension
public import Sheaf.SixFunctors.ProEtale.DerivedCompletion
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale

/-! # First coefficient reduction of actual supported integral images

Source: the integral clause of the agent obligation motivated by Hemo--Richarz--Scholbach,
Section 8, condition (8.1) and Lemma 8.6. The exact generality is WANTED.
(blueprint: lem-sfb-supported-image-first-reduction-cd).

Only reduction modulo the uniformizer is asserted here. Higher powers are handled
by the coefficient triangles in DerivedNakayamaResolution, in the parent module.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- The first actual derived reduction of a supported integral image has the torsion
cohomological bound. No reduction of the map or topological closure of its image is used.

Source: Hemo--Richarz--Scholbach, Section 8, condition (8.1), proof of Lemma 8.6;
the first-power case of the agent obligation
`lem-sfb-supported-image-torsion-reductions-cd`. Exact generality WANTED.
(blueprint: lem-sfb-supported-image-first-reduction-cd).

Proof obligation: use the two-term coefficient resolution to identify the restricted
first reduction with [N -- pi --> N] in degrees -1,0, where N is the actual pulled-back
supported image. Scalar forgetting identifies module-derived sections with the ordinary
abelian derived evaluation of that complex. On a small affine etale presentation of U,
the assumed torsion dimension bound passes to U by the affine-limit theorem. A valid
comparison or direct first-reduction estimate must then show vanishing above d for this
specific complex. The old proposed comparison argument requires Noetherianity of S;
its unrestricted local nonpositivity assertion is false. Thus that argument cannot
supply this remaining geometric step. The first-power assertion is retained for
re-review, with no counterexample to this global conclusion claimed. Once this step
is proved, higher powers require only the exact coefficient triangles and no additional
geometric input. Zero images, the empty support chain and empty schemes give zero;
there is no added nonzero or Noetherian hypothesis, and d=0 is included.
-/
-- STATEMENT-DISPUTED: the available local comparison theorem requires Noetherian S.
-- This first-power global obligation remains open; the refuted local theorem is not used.
theorem supported_image_first_reduction_cohomology_vanishes
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) [IsAffine X] (d : ℕ)
    (_hcd : ∀ (V : Scheme.{u}) (v : V ⟶ X) [IsAffine V] [Etale v],
      V.HasTorsionEtaleCohomologicalDimensionLE d)
    {S : Scheme.{u}} (tree : QcqsOpenClosedTree X) (p : tree.Path S)
    (U : Scheme.{u}) (v : U ⟶ X) (_hv : proAffineEtale v) :
    ∀ (E : Type u) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
        (L M : AdicCompletion.Modules ℓ E S) (f : L ⟶ M),
      HasFiniteConstantLocalModel (DerivedNakayama.integerRing ℓ E) S L →
      HasFiniteConstantLocalModel (DerivedNakayama.integerRing ℓ E) S M →
      ∀ (q : ℤ), (d : ℤ) < q →
        IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} q).obj
          ((condensedModuleSections (DerivedNakayama.integerRing ℓ E) U).rightDerivedFunctor.obj
            ((AdicCompletion.restrict ℓ E U 0).obj
              ((AdicCompletion.derivedReduction ℓ E U 0).obj
                ((DerivedCategory.singleFunctor _ 0).obj
                  ((CondensedRing.upperStar (DerivedNakayama.integerRing ℓ E) v).obj
                    ((p.extension (DerivedNakayama.integerRing ℓ E)).obj (image f)))))))) := by
  sorry

end AlgebraicGeometry.ProEtale

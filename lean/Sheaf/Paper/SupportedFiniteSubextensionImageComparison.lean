/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.Paper.QcqsOpenClosedTree
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.CondensedQcqsPushforwardContinuity
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Abelian.Images
import Sheaf.AlgebraicGeometry.QuasiCompactOpenIntersection
import Sheaf.Paper.CoefficientFiniteDescentLisse
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import Sheaf.Paper.QlbarTailModuleColimit
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.Paper.CartesianCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuitySections
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison

/-! # Supported-image bounds for finite-subextension-valued coefficients

Source: Hemo--Richarz--Scholbach, Constructible sheaves on schemes, Lemma 7.9
and the proof of Lemma 8.6; supported-image deduction in the reviewed DAG
(blueprint: lem-sfb-supported-continuous-omega-image-comparison).

The coefficient ring is the finite-subextension-valued condensed algebraic closure.
Paths in finite qcqs open-closed trees encode the actual support chains. Every chain
in the node extends to such a tree by adding complementary siblings as leaves:
all its vertices are qcqs since the root is affine. Paths can stop at any vertex,
and the root path is the empty chain. No support factorization is replaced.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- A uniform upper bound for supported images over every finite intermediate field
holds with the same bound over the finite-subextension-valued condensed algebraic
closure. Images are images of arbitrary actual module morphisms, and sections are
ordinary uncompleted module-derived sections valued in abelian groups.

Source: Hemo--Richarz--Scholbach, Lemma 7.9, Proposition 5.2, Lemma 5.3 and
proof of Lemma 8.6; supported-image deduction in the reviewed DAG
(blueprint: lem-sfb-supported-continuous-omega-image-comparison).

Proof plan, following the five steps of the node:
1. All vertices of the support chain are qcqs. Start with the affine root; a qc
   open in a qcqs scheme is qcqs by finite affine covers and qc intersections
   (lem-weil-pbc-affine-scheme-qcqs, pqf-lem-qs-intersection-qc and
   lem-weil-pbc-quasi-separated-affine-cover-criterion). A closed subscheme has
   affine closed inverse images of affine charts and qc intersections, giving the
   same conclusion (def-weil-closed-immersion). Finitely presented scalar modules
   over the algebraic closure are finite dimensional, hence finite free, so the
   two local-model modules are lisse, including rank zero.
2. Descend both lisse objects to a common finite field E. The Hom-surjectivity
   clause descends the actual map after enlarging E once more, with equality of
   actual maps after extension isomorphisms (det-lem-coefficient-finite-descent-lisse).
   All later scalar extensions remain allowed finite scalar local models.
3. Finite-field and algebraic-closure scalar extension are exact by their tensor
   adjunctions and flatness (lem-sfb-subfield-flat, lem-sfb-qlbar-flat and
   sk-def-sfb-change-of-scalars). Thus they preserve the kernel/cokernel expression
   for the ordinary image. The directed tail coefficient colimit and the tensor
   adjunction identify the algebraic-closure image with the filtered colimit of
   finite-field images, after restricting scalars to E
   (lem-sfb-qlbar-tail-module-colimit). No closure or completion is involved.
4. Pass to underlying abelian sheaves using
   def-weil-pbc-internal-abelian-sheaf-module-equivalence and
   lem-weil-pbc-module-sheaves-colimits-forgetful. Open extension and inverse image
   preserve colimits by their left adjunctions. Each closed direct image preserves
   filtered colimits because its target is qcqs and its open complement is qc
   (lem-weil-pbc-proetale-ringed-open-closed). The underlying functors agree with
   abelian extension, direct image and inverse image by
   def-sfb-module-open-lower-shriek, def-sfb-module-lower-star,
   sk-prop-sfb-cartesian-coefficients and def-sfb-module-upper-lower-adjunction.
   Induction through the given chain identifies the supported pulled-back image
   with the colimit of the same supported finite-field images and transition maps.
5. The affine test U is qcqs. Bounded-below cohomology continuity applied to these
   degree-zero underlying abelian sheaves, with common lower bound zero, identifies
   each cohomology group with the filtered colimit of the finite-field groups
   (det-pe-bounded-continuity-sections). Small-site K-injective existence and
   Grothendieck enough injectives give the module/abelian evaluation comparison
   (prop-pur-kinjective-resolutions-exist, lem-sp-grothendieck-enough-injectives,
   lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison), transported through
   the internal module equivalence. These are exactly the module-derived groups
   below. For q > h every finite-field group is zero by the hypothesis, on the
   same chain, X and U. Their filtered colimit is zero, with no increase of h.
-/
theorem supported_finite_subextension_image_cohomology_vanishes
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) [IsAffine X] (h : ℕ)
    (hfinite : ∀ (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (S : Scheme.{u}) (tree : QcqsOpenClosedTree X) (p : tree.Path S)
      (L M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E) S))
      (g : L ⟶ M),
      HasFiniteConstantLocalModel (Profinite.continuousMapRingObj E) S L →
      HasFiniteConstantLocalModel (Profinite.continuousMapRingObj E) S M →
      ∀ (U : X.ProEt) [IsAffine U.left] (q : ℤ), (h : ℤ) < q →
        IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} q).obj
          ((condensedModuleSections
              (Profinite.continuousMapRingObj E) U.left).rightDerivedFunctor.obj
            ((DerivedCategory.singleFunctor _ 0).obj
              ((CondensedRing.upperStar (Profinite.continuousMapRingObj E) U.hom).obj
                ((p.extension (Profinite.continuousMapRingObj E)).obj (image g)))))))
    (S : Scheme.{u}) (tree : QcqsOpenClosedTree X) (p : tree.Path S)
    (L M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) S))
    (f : L ⟶ M)
    (hL : HasFiniteConstantLocalModel (Profinite.padicAlgClRingObj ℓ) S L)
    (hM : HasFiniteConstantLocalModel (Profinite.padicAlgClRingObj ℓ) S M)
    (U : X.ProEt) [IsAffine U.left] (q : ℤ) (hq : (h : ℤ) < q) :
    IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} q).obj
      ((condensedModuleSections
          (Profinite.padicAlgClRingObj ℓ) U.left).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) U.hom).obj
            ((p.extension (Profinite.padicAlgClRingObj ℓ)).obj (image f)))))) := by
  sorry

end AlgebraicGeometry.ProEtale

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.ProEtaleOperations
import Sheaf.CategoryTheory.RingedSiteGrothendieckAbelian
import Sheaf.AlgebraicGeometry.ProEtaleAffineAcyclicHypercover
import Sheaf.AlgebraicGeometry.ProEtaleHypercoverComputesBoundedComplex
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimits
import Sheaf.Algebra.Homology.BoundedBelowInjectiveResolution
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# The sectionwise pushforward continuity comparison

Source: Hemo--Richarz--Scholbach, Constructible sheaves, Lemma 5.3(1).
(blueprint: lem-weil-pbc-condensed-qcqs-pushforward-local-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

set_option synthInstance.maxHeartbeats 100000 in
-- Colimit inference for internal module objects needs a larger search budget.
set_option synthInstance.maxSize 4096 in
/-- The canonical pushforward continuity comparison is invertible after evaluation
at one affine weakly contractible target object.

Source: Hemo--Richarz--Scholbach, Lemma 5.3(1), sectionwise hypercover calculation.
(blueprint: lem-weil-pbc-condensed-qcqs-pushforward-local-comparison).

Proof: the good truncation projection is a quasi-isomorphism because cohomology
vanishes below the common bound a. Its target has zero terms below a. The inverse
image W of V is qcqs: base change preserves quasi-compactness and quasi-separatedness
of f, and V is affine. Choose an affine weakly contractible hypercover of W. On each
term, evaluation of module sheaves is exact and commutes with filtered colimits.
Form the alternating section bicomplex and its signed total. In degree r its
nonzero diagonal has indices 0 through r-a, so only finite products occur. The
hypercover resolution identifies this total with derived sections on W, naturally
in the coefficient complex and its maps. Exact filtered colimits identify the
homology of the total colimit with the colimit of total homology. On K-injective
resolutions, pushforward evaluated at V is evaluation at W. Evaluation at the
weakly contractible V is exact, so it commutes with pushforward cohomology. These
identifications send each original cocone leg to its sectionwise hypercover leg;
the colimit universal property therefore identifies the asserted map with the
invertible hypercover comparison. The finite diagonal remains empty below a,
and the argument also applies to an empty W. -/
theorem condensed_qcqs_pushforward_local_comparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
        (condensedRingObj Λ X)) ℤ)
    (a : ℤ) (ha : ∀ (i : I) (n : ℤ), n < a → IsZero ((D.obj i).homology n))
    (q : ℤ) (V : Y.ProEt) (hV : IsAffine V.left)
    (hweak : ∀ (F G : Sheaf (Scheme.ProEt.topology Y) (Type (u + 1))) (g : F ⟶ G),
      Epi g → Function.Surjective (g.hom.app (op V))) :
    IsIso (((Mod.forget (condensedRingObj Λ Y)).map
      (colimit.desc
        (D ⋙ (DerivedCategory.Q ⋙ (CondensedRing.lowerStar Λ f).rightDerivedFunctor ⋙
          DerivedCategory.homologyFunctor _ q))
        ((DerivedCategory.Q ⋙ (CondensedRing.lowerStar Λ f).rightDerivedFunctor ⋙
          DerivedCategory.homologyFunctor _ q).mapCocone
          ((Cocone.precompose (Functor.whiskerLeft D
            ((ComplexShape.embeddingUpIntGE a).πTruncGENatTrans _))).obj
              (colimit.cocone
                (D ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor _)))))).hom.app
                  (op V)) := by
  sorry

end AlgebraicGeometry.ProEtale

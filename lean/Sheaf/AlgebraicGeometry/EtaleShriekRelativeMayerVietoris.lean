/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Sheaf.AlgebraicGeometry.DerivedCategories
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Sheaf.AlgebraicGeometry.EtaleShriekQcqsComposition

/-!
# Relative Mayer--Vietoris for etale compact support

Source: Stacks Project, more-etale.tex, Tag 0GKN, lemma-relative-mayer-vietoris,
finite-ring bounded-below specialization
(blueprint: lem-weil-pbc-etale-shriek-relative-mayer-vietoris).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Etale

/-- Relative Mayer--Vietoris for any chosen compactifications.
Source: Stacks Project, Tag 0GKN, lemma-relative-mayer-vietoris.
(blueprint: lem-weil-pbc-etale-shriek-relative-mayer-vietoris).

Proof:
1. The quasi-separated affine-cover criterion and qcqs morphism permanence show that
   U, V and their intersection are qcqs and their inclusions are quasi-compact;
   their composites with f remain separated and of finite type.
2. Use the constant-ring module equivalence to work with module-valued sheaves.
   Extension by zero and its adjunction give the signed maps from the intersection
   to the two opens and the sum of counits to the original sheaf. Their stalks
   are the exact sequences with maps (1,-1) and (1,1), or the identity off the
   intersection. Exactness and conservativity of geometric stalks, together with
   the faithful scalar-forgetting functor, give a short exact sequence of sheaves.
3. Represent K by a bounded-below complex. Exact restriction and extension by zero
   give a short exact sequence of complexes, hence the distinguished triangle
   by the complex-SES triangle lemma; all objects retain the common lower bound.
4. For the compactification cX, extension by zero induces a triangulated functor.
   Grothendieck abelian module categories have functorial K-injective resolutions,
   and the left-exact additive proper pushforward has a triangulated right derived
   functor. Negative vanishing preserves the bounded-below subcategory. Apply
   this composite to the triangle, using additivity and shift compatibility.
5. For each open inclusion use its compactification by the identity of X.
   Its shriek is extension by zero. The qcqs shriek-composition lemma identifies
   its composite with the candidate attached to each prescribed cU, cV and cW.
   Transport the three arrows by these isomorphisms and their shifted versions;
   invariance of distinguished triangles under isomorphism yields the assertion.
-/
theorem exists_distinguished_relativeMayerVietoris
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (U V : X.Opens) (hU : IsCompact (U : Set X)) (hV : IsCompact (V : Set X))
    (hcover : U ⊔ V = ⊤)
    (cU : Compactification (U.ι ≫ f)) (cV : Compactification (V.ι ≫ f))
    (cW : Compactification ((U ⊓ V).ι ≫ f)) (cX : Compactification f)
    (K : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ∃ (α : (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cW).obj
        (((upperStar (ModuleCat.{u + 1} Λ) (U ⊓ V).ι).mapDerivedCategoryPlus).obj K) ⟶
      ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cU).obj
        (((upperStar (ModuleCat.{u + 1} Λ) U.ι).mapDerivedCategoryPlus).obj K) ⊞
      (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cV).obj
        (((upperStar (ModuleCat.{u + 1} Λ) V.ι).mapDerivedCategoryPlus).obj K)))
      (β : ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cU).obj
        (((upperStar (ModuleCat.{u + 1} Λ) U.ι).mapDerivedCategoryPlus).obj K) ⊞
      (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cV).obj
        (((upperStar (ModuleCat.{u + 1} Λ) V.ι).mapDerivedCategoryPlus).obj K)) ⟶
        (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cX).obj K)
      (δ : (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cX).obj K ⟶
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cW).obj
        (((upperStar (ModuleCat.{u + 1} Λ) (U ⊓ V).ι).mapDerivedCategoryPlus).obj K))⟦(1 : ℤ)⟧),
      Triangle.mk α β δ ∈ distTriang
        (_root_.DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) := by
  sorry

end AlgebraicGeometry.Etale

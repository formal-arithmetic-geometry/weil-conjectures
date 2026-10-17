/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import Sheaf.AlgebraicGeometry.UniversalHomeomorphismInvariance
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.CategoryTheory.MateIsoAlongEquivalences
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact

/-!
# Descent of open direct image and exchange along finite radicial covers

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/lem-fin-radicial-exchange-descent.md
(blueprint: lem-fin-radicial-exchange-descent).

All base changes are arbitrary Cartesian presentations. The canonical module exchange
is `Etale.derivedBaseChangeMap`, retained by the recorded base-change-map dependency.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Bounded constructibility and universal Noetherian exchange for an open direct image
 descend along a finite surjective radicial morphism of bases.
Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/lem-fin-radicial-exchange-descent.md
(blueprint: lem-fin-radicial-exchange-descent).

Proof plan (the seven steps of the node):
1. A finite surjective radicial morphism is a universal homeomorphism, as are its
   base changes (finite-integral and universal-homeomorphism base-change lemmas).
2. Topological invariance gives exact equivalences on etale module sheaves and hence
   on derived categories. The mate-isomorphism lemma identifies the canonical exchange
   for this cover as an isomorphism, intertwining the two direct images.
3. Constructibility descends through this equivalence: descend the constructible
   locally closed strata through the homeomorphism, compare their reductions, and use
   the equivalence of etale sites to descend finite constant trivializations.
4. Exact inverse image commutes with cohomology and reflects zero objects. Thus the
   assumed bounded constructibility upstairs descends to the original direct image.
5. For a Noetherian test T over S, its pullback T' over S' is Noetherian: the projection
   to T is finite, hence finite type and quasi-compact. It is a universal homeomorphism.
6. Canonical inverse-image compositors are coherent by their adjunction normalization.
   Module structures are determined by their underlying action. Derived localization
   preserves these comparisons; mate pasting therefore gives the equality of the two
   exchanges along T' to T to S and T' to S' to S.
7. Upstairs exchange and the cover exchanges are invertible. Cancel the latter in the
   pasting equality and use conservativity of inverse image along T' to T. This proves
   exchange for every Noetherian T, together with bounded constructibility from step 4.
-/
theorem finite_radicial_exchange_descent
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {S S' X Y : Scheme.{u}} (v : S' ⟶ S)
    [IsFinite v] [Surjective v] [UniversallyInjective v]
    (aX : X ⟶ S) (aY : Y ⟶ S)
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (j : X ⟶ Y) [IsOpenImmersion j] (hj : j ≫ aY = aX)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : Scheme.IsConstructibleEtaleModuleSheaf F)
    {X' Y' : Scheme.{u}} (pX : X' ⟶ X) (pY : Y' ⟶ Y)
    (bY : Y' ⟶ S') (j' : X' ⟶ Y')
    (hY : IsPullback pY bY aY v) (hX : IsPullback pX j' j pY)
    (hbounded : DerivedCategory.isBoundedConstructible Λ Y'
      ((R((j')_*[ModuleCat.{u + 1} Λ])).obj
        ((L((pX)^*[ModuleCat.{u + 1} Λ])).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F))))
    (hexchange : ∀ (T : Scheme.{u}) [IsNoetherian T] (t : T ⟶ S')
      (XT YT : Scheme.{u}) (qX : XT ⟶ X') (qY : YT ⟶ Y')
      (bT : YT ⟶ T) (jT : XT ⟶ YT),
      IsPullback qY bT bY t → ∀ sq : IsPullback qX jT j' qY,
        IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
          ((L((pX)^*[ModuleCat.{u + 1} Λ])).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))) :
    DerivedCategory.isBoundedConstructible Λ Y
      ((R((j)_*[ModuleCat.{u + 1} Λ])).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) ∧
    ∀ (T : Scheme.{u}) [IsNoetherian T] (t : T ⟶ S)
      (XT YT : Scheme.{u}) (qX : XT ⟶ X) (qY : YT ⟶ Y)
      (bT : YT ⟶ T) (jT : XT ⟶ YT),
      IsPullback qY bT aY t → ∀ sq : IsPullback qX jT j qY,
        IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) := by
  sorry

end AlgebraicGeometry.Etale

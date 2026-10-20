/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q115
-/
module

public import Sheaf.Paper.OrientedNearbyCycles
public import Sheaf.CategoryTheory.Sites.OrientedProductUniversal
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.PUnit

import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.CategoryTheory.Sites.GeometricMorphism
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.AlgebraicGeometry.EtaleToposPointsGeometric
import Sheaf.CategoryTheory.Sites.OrientedAffineSliceSite
import Sheaf.CategoryTheory.Sites.OrientedProductLargeSites
import Sheaf.Paper.FinitarySiteEnoughPoints

/-!
# Conservativity of specialization-triple points of the vanishing topos

Source: ILO, Exposé XI 1.8, 1.10(b), and the finite-cover construction in 2.5;
Stacks Project, Tags 00YQ, 04HU, 010N and 05RT
(blueprint: lem-trf-oriented-product-points-conservative).

We present the category of sets by the one-object site with trivial topology, so the
existing constant-module inverse image applies directly to the canonical triple points.
-/

@[expose] public section

universe u v s

open CategoryTheory CategoryTheory.Limits CategoryTheory.AdicSites

namespace AlgebraicGeometry.OrientedNearbyCycles

noncomputable section

/-- The one-object presentation of sets. Source: ILO XI 1.8, points with source sets
(blueprint: lem-trf-oriented-product-points-conservative). -/
def punctualSite : Site.{s} :=
  ⟨Discrete PUnit.{s + 1}, ⊥⟩

/-- The explicit equivalence from sheaves on the punctual site to sets, by evaluation
at its unique object. Source: ILO XI 1.8
(blueprint: lem-trf-oriented-product-points-conservative). -/
def punctualEquivalence :
    Sheaf punctualSite.{s}.topology (Type s) ≌ Type s :=
  (sheafBotEquivalence (C := Discrete PUnit.{s + 1}) (Type s)).trans
    ((Discrete.opposite PUnit.{s + 1}).congrLeft.trans (Functor.equiv (C := Type s)))

/-- Transport the usual small étale sheaves to the dependency's `AsSmall` presentation.
Source: ILO XI 1.8, independence of the site presentation
(blueprint: lem-trf-oriented-product-points-conservative). -/
def etaleSheafEquivalence (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology (Type (max (u + 1) v)) ≌
      Sheaf (etaleTopology.{u, v} X) (Type (max (u + 1) v)) :=
  let e : X.Etale ≌ EtaleSite.{u, v} X := AsSmall.equiv
  e.sheafCongr X.smallEtaleTopology (e.inverse.inducedTopology X.smallEtaleTopology) _

/-- The geometric stalk/skyscraper point, transported through the two explicit site
equivalences. Its inverse image is the pointed-neighbourhood colimit, not an arbitrary
functor. Source: ILO XI 1.8; Stacks 04HU
(blueprint: lem-trf-oriented-product-points-conservative). -/
def geometricEtalePoint {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) :
    GeometricMorphism
      (Sheaf punctualSite.{max (u + 1) v}.topology (Type (max (u + 1) v)))
      (Sheaf (etaleTopology.{u, v} X) (Type (max (u + 1) v))) where
  inverse := (etaleSheafEquivalence X).inverse ⋙
    (Scheme.pointSmallEtale x).sheafFiber ⋙ punctualEquivalence.{max (u + 1) v}.inverse
  direct := punctualEquivalence.{max (u + 1) v}.functor ⋙
    (Scheme.pointSmallEtale x).skyscraperSheafFunctor ⋙ (etaleSheafEquivalence X).functor
  adj := (etaleSheafEquivalence X).symm.toAdjunction.comp
    ((Scheme.pointSmallEtale x).skyscraperSheafAdjunction.comp
      punctualEquivalence.{max (u + 1) v}.symm.toAdjunction)
  leftExact := by
    let : AB5OfSize.{u, u} (Type (max (u + 1) v)) :=
      AB5OfSize_of_univLE.{u, u, max (u + 1) v, max (u + 1) v}
        (Type (max (u + 1) v))
    infer_instance

/-- The point corresponding to `(x,y,c)`, with the orientation `y ⇒ f(x)` on direct
images. It is the dependency's universal compatible lift, including both projection
identifications. Source: ILO XI 1.8 and Theorem 1.4
(blueprint: lem-trf-oriented-product-points-conservative). -/
def triplePoint {T B : Scheme.{u}} (f : T ⟶ B)
    {Ω Ξ : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
    (x : Spec (.of Ω) ⟶ T) (y : Spec (.of Ξ) ⟶ B)
    (c : ((geometricEtalePoint.{u, v} y).comp (identity _)).direct ⟶
      ((geometricEtalePoint.{u, v} x).comp (etaleMorphism f)).direct) :=
  (lift f _ (sheaf_isTopos punctualSite.{max (u + 1) v}.topology)
    (geometricEtalePoint x) (geometricEtalePoint y) c).morphism

/-- The canonical exact constant-coefficient module inverse image at a triple point.
Source: ILO XI 1.8 and the inverse-image convention of def-trf-oriented-nearby-cycles
(blueprint: lem-trf-oriented-product-points-conservative). -/
def tripleModules {T B : Scheme.{u}} (f : T ⟶ B)
    {Ω Ξ : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
    (x : Spec (.of Ω) ⟶ T) (y : Spec (.of Ξ) ⟶ B)
    (c : ((geometricEtalePoint.{u, v} y).comp (identity _)).direct ⟶
      ((geometricEtalePoint.{u, v} x).comp (etaleMorphism f)).direct) :=
  moduleMorphism (vanishingDatum.{u, v} f) punctualSite.{max (u + 1) v}
    (triplePoint f x y c)

/-- Triple points jointly reflect isomorphisms on constant-module sheaves and their
unbounded derived category. Source: ILO XI 1.8, 1.10(b), and 2.5; Stacks 00YQ and 05RT
(blueprint: lem-trf-oriented-product-points-conservative).

Proof:
1. Compose any point with the projections and use lem-trf-etale-topos-points-geometric
   to identify them with geometric stalks. Conjugate its orientation to obtain `c`.
   Uniqueness in lem-trf-oriented-product-universal identifies it with `triplePoint`.
   If T is empty the triple site has empty type-(a) covers and its topos is degenerate;
   the empty family is conservative, on both sheaves and derived objects.
2. Refine an arbitrary triple to affine triples, first covering the middle étale object
   by affines, then using type-(a) and type-(c) covers, then affine covers of the two
   outside objects. Use lem-weil-pbc-affine-etale-essentially-small-cover; no finite
   cover or affine intersection is asserted for an arbitrary scheme.
3. For an affine triple Z, lem-trf-oriented-affine-slice-site presents the slice over
   its associated representable by a small finite-limit site with finite covering
   refinements. Apply lem-trf-finitary-site-enough-points there (Stacks 00YQ). Each of
   its points composes to a triple point by step 1. Thus a map invertible at all triple
   points restricts to an isomorphism on this slice. Its global sections give bijectivity
   on Z, by the last clause of the affine-slice lemma.
4. Glue over the affine-triple covers using def-weil-pbc-sites-and-cohomology. First
   prove injectivity on all triples by separatedness; then lift uniquely on affine
   members and use that injectivity on arbitrary overlaps to glue. This proves
   conservativity for sheaves of sets.
5. Forget module operations and apply step 4. The inverse of an invertible underlying
   module map preserves addition and scalars by injectivity of that map. This proves
   the sheaf clause, using def-weil-sheaf-of-modules-category and the exact inverse-image
   construction of def-trf-oriented-nearby-cycles.
6. Exactness gives Hⁿ(z* K) ≅ z* Hⁿ(K) naturally, by
   lem-weil-pbc-exact-functor-complex-cohomology. These comparisons descend through the
   quasi-isomorphism localization def-weil-abstract-derived-category, for all integers
   and all unbounded complexes, without a truncation or limit argument.
7. If every derived pullback of a map is invertible, step 6 and the sheaf clause make
   all its cohomology maps invertible. Apply lem-weil-pbc-unbounded-derived-iso-cohomology.
   Conversely every functor preserves an inverse, proving both reverse implications. -/
theorem orientedProduct_points_conservative {T B : Scheme.{u}} (f : T ⟶ B)
    (Λ : Type v) [CommRing Λ] :
    (∀ {F G : (vanishingDatum.{u, v} f).modules (Coeff.{u, v} Λ)} (a : F ⟶ G),
      IsIso a ↔ ∀ (Ω Ξ : Type u) [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
        (x : Spec (.of Ω) ⟶ T) (y : Spec (.of Ξ) ⟶ B)
        (c : ((geometricEtalePoint.{u, v} y).comp (identity _)).direct ⟶
          ((geometricEtalePoint.{u, v} x).comp (etaleMorphism f)).direct),
        IsIso (((tripleModules f x y c).modulePull (Coeff.{u, v} Λ)).map a)) ∧
    (∀ {K L : VanishingDerived f Λ} (a : K ⟶ L),
      IsIso a ↔ ∀ (Ω Ξ : Type u) [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
        (x : Spec (.of Ω) ⟶ T) (y : Spec (.of Ξ) ⟶ B)
        (c : ((geometricEtalePoint.{u, v} y).comp (identity _)).direct ⟶
          ((geometricEtalePoint.{u, v} x).comp (etaleMorphism f)).direct),
        IsIso (((tripleModules f x y c).pull (Coeff.{u, v} Λ)).map a)) := by
  sorry

end

end AlgebraicGeometry.OrientedNearbyCycles

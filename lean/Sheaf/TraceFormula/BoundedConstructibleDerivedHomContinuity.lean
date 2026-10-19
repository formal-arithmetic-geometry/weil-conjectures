/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

import Sheaf.TraceFormula.ConstructibleEtaleExtContinuity
import Sheaf.AlgebraicGeometry.DerivedInverseImageComposition
import Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison
import WeilConjectures.CategoryTheory.TruncationTriangle
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Continuity of bounded constructible derived Hom

Source: Stacks Project, Derived Categories, Tags 0149 and 08J5, and Etale Cohomology,
Tag 09YU (blueprint: lem-trf-bounded-constructible-derived-hom-continuity).

The canonical maps are built from exact étale inverse image, its derived composition
comparison, and the induced maps on Hom.  Filtered-colimit continuity is expressed by
surjectivity and eventual equality of representatives, which is equivalent to the
canonical filtered-colimit Hom comparison being an isomorphism.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The Hom group between inverse images of two derived objects, with an integer shift.
Source: Tags 09YU and 0149 (blueprint: lem-trf-bounded-constructible-derived-hom-continuity). -/
def boundedConstructibleDerivedHom {S T : Scheme.{u}}
    {A : Type (u + 1)} [CommRing A] (f : T ⟶ S)
    (P Q : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))) (n : ℤ) :
    Type (u + 1) :=
  ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj P ⟶
    ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj Q)⟦n⟧)

/-- The canonical derived composition isomorphism for a pair of inverse images.
Source: Tag 0D6D (blueprint: lem-trf-bounded-constructible-derived-hom-continuity). -/
noncomputable def boundedConstructibleDerivedHomCompIso {S T Y : Scheme.{u}}
    {A : Type (u + 1)} [CommRing A] (f : T ⟶ S) (g : Y ⟶ T) (h : Y ⟶ S)
    (w : h = g ≫ f)
    (P : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.obj P ≅
      (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.obj
        ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj P) :=
  ((Functor.mapDerivedCategoryNatIso
    (upperStarComp (ModuleCat.{u + 1} A) g f h w)).app P) ≪≫
    (Functor.mapDerivedCategoryCompIso
      (upperStar (ModuleCat.{u + 1} A) f)
      (upperStar (ModuleCat.{u + 1} A) g)).app P

/-- The canonical map on derived Hom induced by exact étale inverse image.
Source: Tags 0D6D and 09YU (blueprint: lem-trf-bounded-constructible-derived-hom-continuity). -/
noncomputable def boundedConstructibleDerivedHomPullback {S T Y : Scheme.{u}}
    {A : Type (u + 1)} [CommRing A] (f : T ⟶ S) (g : Y ⟶ T) (h : Y ⟶ S)
    (w : h = g ≫ f)
    (P Q : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (n : ℤ) (a : boundedConstructibleDerivedHom f P Q n) :
    boundedConstructibleDerivedHom h P Q n :=
  (boundedConstructibleDerivedHomCompIso f g h w P).hom ≫
    (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.map a ≫
    ((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.commShiftIso n).hom.app
      ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj Q) ≫
    ((boundedConstructibleDerivedHomCompIso f g h w Q).inv)⟦n⟧'

/-- The canonical transport of a shifted derived Hom through an exact inverse image.
The formula uses the functor's `commShiftIso`, the shifted morphism, and the canonical
`shiftFunctorComm` comparison.
Source: Tags 0149 and 0D6D
(blueprint: lem-trf-bounded-constructible-derived-hom-continuity). -/
noncomputable def boundedConstructibleDerivedHomShiftTransport {S T : Scheme.{u}}
    {A : Type (u + 1)} [CommRing A] (f : T ⟶ S) (m n : ℤ)
    (P Q : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (a : boundedConstructibleDerivedHom f P Q n) :
    boundedConstructibleDerivedHom f ((shiftFunctor _ m).obj P) ((shiftFunctor _ m).obj Q) n :=
  ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.commShiftIso m).hom.app P ≫ (a⟦m⟧') ≫
    (shiftFunctorComm _ n m).hom.app
      ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj Q) ≫
    (((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.commShiftIso m).inv.app Q)⟦n⟧'

/-- The canonical limit leg from a later stage to the inverse limit.
Source: Tag 09YU (blueprint: lem-trf-bounded-constructible-derived-hom-continuity). -/
noncomputable def boundedConstructibleDerivedHomLeg {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) {i j : I} (hij : i ≤ j)
    {A : Type (u + 1)} [CommRing A]
    (P Q : DerivedCategory (Sheaf (D.obj (op i)).smallEtaleTopology
      (ModuleCat.{u + 1} A))) (n : ℤ)
    (a : boundedConstructibleDerivedHom (D.map (homOfLE hij).op) P Q n) :
    boundedConstructibleDerivedHom (c.π.app (op i)) P Q n :=
  boundedConstructibleDerivedHomPullback (D.map (homOfLE hij).op) (c.π.app (op j))
    (c.π.app (op i)) (c.w (homOfLE hij).op).symm P Q n a

/-- The canonical transition map from one later stage to a still later stage.
Source: Tag 09YU (blueprint: lem-trf-bounded-constructible-derived-hom-continuity). -/
noncomputable def boundedConstructibleDerivedHomTransition {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) {i j k : I} (hij : i ≤ j) (hjk : j ≤ k)
    {A : Type (u + 1)} [CommRing A]
    (P Q : DerivedCategory (Sheaf (D.obj (op i)).smallEtaleTopology
      (ModuleCat.{u + 1} A))) (n : ℤ)
    (a : boundedConstructibleDerivedHom (D.map (homOfLE hij).op) P Q n) :
    boundedConstructibleDerivedHom (D.map (homOfLE (hij.trans hjk)).op) P Q n :=
  boundedConstructibleDerivedHomPullback (D.map (homOfLE hij).op) (D.map (homOfLE hjk).op)
    (D.map (homOfLE (hij.trans hjk)).op)
    (D.map_comp (homOfLE hjk).op (homOfLE hij).op) P Q n a

/-- The continuity and compatibility clauses of bounded constructible derived Hom continuity.
The maps in every field are the canonical maps defined above; no unrelated map or
choice is part of this interface. Source: Tags 0149, 09YU and 08J5
(blueprint: lem-trf-bounded-constructible-derived-hom-continuity). -/
structure BoundedConstructibleDerivedHomContinuityData {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) {i : I}
    {A : Type (u + 1)} [CommRing A]
    (P Q : DerivedCategory (Sheaf (D.obj (op i)).smallEtaleTopology
      (ModuleCat.{u + 1} A))) (n : ℤ) : Prop where
  descends : ∀ (a : boundedConstructibleDerivedHom (c.π.app (op i)) P Q n),
    ∃ (j : I) (hij : i ≤ j)
      (b : boundedConstructibleDerivedHom (D.map (homOfLE hij).op) P Q n),
      boundedConstructibleDerivedHomLeg D c hij P Q n b = a
  eventually_equal : ∀ (j k : I) (hij : i ≤ j) (hik : i ≤ k)
      (a : boundedConstructibleDerivedHom (D.map (homOfLE hij).op) P Q n)
      (b : boundedConstructibleDerivedHom (D.map (homOfLE hik).op) P Q n),
      boundedConstructibleDerivedHomLeg D c hij P Q n a =
        boundedConstructibleDerivedHomLeg D c hik P Q n b →
      ∃ (l : I) (hjl : j ≤ l) (hkl : k ≤ l),
        boundedConstructibleDerivedHomTransition D hij hjl P Q n a =
          boundedConstructibleDerivedHomTransition D hik hkl P Q n b
  composition : ∀ {j : I} (hij : i ≤ j)
      {R : DerivedCategory (Sheaf (D.obj (op i)).smallEtaleTopology
        (ModuleCat.{u + 1} A))} (m p : ℤ) (h : p + n = m)
      (a : boundedConstructibleDerivedHom (D.map (homOfLE hij).op) P Q n)
      (b : boundedConstructibleDerivedHom (D.map (homOfLE hij).op) Q R p),
      boundedConstructibleDerivedHomLeg D c hij P R m (ShiftedHom.comp a b h) =
        ShiftedHom.comp (boundedConstructibleDerivedHomLeg D c hij P Q n a)
          (boundedConstructibleDerivedHomLeg D c hij Q R p b) h
  shift : ∀ (j : I) (hij : i ≤ j) (m : ℤ)
      (a : boundedConstructibleDerivedHom (D.map (homOfLE hij).op) P Q n),
    boundedConstructibleDerivedHomLeg D c hij
        ((shiftFunctor _ m).obj P) ((shiftFunctor _ m).obj Q) n
        (boundedConstructibleDerivedHomShiftTransport (D.map (homOfLE hij).op) m n
          (P := P) (Q := Q) a) =
      boundedConstructibleDerivedHomShiftTransport (c.π.app (op i)) m n
        (P := P) (Q := Q)
        (boundedConstructibleDerivedHomLeg D c hij P Q n a)

  later : ∀ (j k : I) (hij : i ≤ j) (hjk : j ≤ k)
      (a : boundedConstructibleDerivedHom (D.map (homOfLE hij).op) P Q n),
      boundedConstructibleDerivedHomLeg D c (hij.trans hjk) P Q n
        (boundedConstructibleDerivedHomTransition D hij hjk P Q n a) =
        boundedConstructibleDerivedHomLeg D c hij P Q n a

/-- Bounded constructible derived Hom is continuous along an affine inverse system.
For every integer shift, the canonical filtered-colimit comparison is an isomorphism;
`descends` and `eventually_equal` are its surjectivity and injectivity, while the final
three fields retain compatibility with composition, shifts, and passage to later stages.
No local-freeness, projectivity, or finite-Tor hypothesis is imposed.

Source: Stacks Project, Derived Categories, Tags 0149 and 08J5, and Etale Cohomology,
Tag 09YU (blueprint: lem-trf-bounded-constructible-derived-hom-continuity).

Proof, following the four steps of the node:
1. For constructible sheaves, `lem-trf-constructible-etale-ext-continuity` supplies
   nonnegative degrees. For negative n, the standard t-structure
   (`def-sbc-standard-tstructure-derived-category`, `def-weil-t-structure`) puts a sheaf
   in degrees at most zero and its target shifted by n in degrees at least -n > 0.
   Orthogonality gives zero Hom at every stage and at the limit. Exact inverse image
   (`prop-weil-pbc-inverse-image-modules-exact`) preserves these sheaves. For shifted
   sheaves F[-a], G[-b], replace n by n+a-b, giving all integer degrees.
2. Fix a shifted constructible target. Pull the source truncation triangles at stage i
   to every later stage and the limit. Exact inverse image is triangulated
   (`lem-sf-exact-functor-derived-triangulated`) and preserves cohomology and truncations
   (`lem-weil-pbc-truncation-triangle`). Apply the Hom-out-of-triangle sequence and its
   rotated five-term segment (`lem-weil-pbc-hom-out-of-triangle-exact`,
   `lem-weil-pbc-hom-into-triangle-exact`). Filtered-colimit exactness
   (`lem-weil-pbc-filtered-colimit-abelian-groups-exact`) gives a commutative exact ladder.
   With four vertical isomorphisms, `lem-weil-pbc-five-lemma` gives the middle one.
   If source cohomology lies in [a,b], its truncations from a-1 to b give a finite
   Postnikov tower, starting at zero, with pieces H^q(P)[-q]. Induction proves continuity
   for the source against every shifted constructible sheaf.
3. Fix this arbitrary bounded constructible source and repeat the same argument with the
   Hom-into-triangle sequence and the finite Postnikov tower of the target. The preceding
   step supplies all shifted-sheaf pieces, hence all bounded constructible targets.
4. The comparisons come from exact inverse image and its canonical composition
   isomorphisms (`lem-weil-pbc-derived-inverse-image-composition`). Their associativity
   and unit equations identify pullback of a shifted composite with the composite of
   pullbacks (`lem-weil-pbc-ext-exact-functor-composition-comparison`). Naturality of
   the Hom ladders propagates the identities through the Postnikov induction. The
   same naturality with the canonical shift comparisons gives the shift square; the
   cone equation and composition coherence give the later-stage square.
-/
theorem bounded_constructible_derived_hom_continuity
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, IsNoetherian (D.obj i)]
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (_hc : IsLimit c) (i : I)
    {A : Type (u + 1)} [CommRing A] [Finite A]
    (P Q : DerivedCategory (Sheaf (D.obj (op i)).smallEtaleTopology
      (ModuleCat.{u + 1} A)))
    (hP : DerivedCategory.TStructure.t.bounded P ∧
      ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
        ((DerivedCategory.homologyFunctor
          (Sheaf (D.obj (op i)).smallEtaleTopology (ModuleCat.{u + 1} A)) q).obj P))
    (hQ : DerivedCategory.TStructure.t.bounded Q ∧
      ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
        ((DerivedCategory.homologyFunctor
          (Sheaf (D.obj (op i)).smallEtaleTopology (ModuleCat.{u + 1} A)) q).obj Q)) :
    ∀ n : ℤ, BoundedConstructibleDerivedHomContinuityData D c P Q n := by
  sorry

end AlgebraicGeometry.Etale

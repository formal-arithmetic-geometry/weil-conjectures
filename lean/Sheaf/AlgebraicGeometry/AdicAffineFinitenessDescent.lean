/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.TruncationTriangle
import Sheaf.Algebra.Homology.RingedSiteRestrictionKFlat
import Sheaf.Paper.RingedDerivedSliceLocalization
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses

/-!
# Conditional affine descent for native adic finiteness

Source: `WeilConjectures/SixFunctors/ProEtale/Adic/LowerStar.lean`, the bounded
and finite-open-cover devissage (142-397) and target localization (440-566)
(blueprint: lem-sf-adic-affine-finiteness-descent).

`AdicSheaf` uses the sheaf of locally finite continuous `PadicAlgCl l`-valued
functions. Its ordinary direct image has the action induced by precomposition.
The affine finiteness input is a hypothesis, for the same coefficient field and
base field throughout. The conclusion concerns the actual total derived direct image.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- Native adic finiteness descends from affine sources and targets to quasi-compact,
quasi-separated locally finite-type morphisms with quasi-compact target.

Source: `WeilConjectures/SixFunctors/ProEtale/Adic/LowerStar.lean`, lines 142-566;
only its finite-cover descent is used, with affine finiteness left as a hypothesis
(blueprint: lem-sf-adic-affine-finiteness-descent).

Proof:
1. A field is Noetherian, so every scheme locally of finite type over K is locally
   Noetherian. Module sheaves form a Grothendieck abelian category with K-injective
   resolutions. Direct image is additive and left exact; its total right derived
   functor is triangulated. Bounded constructible objects form a triangulated
   subcategory, by lem-sf-native-adic-bounded-constructible-triangulated.
2. For a fixed affine morphism, extend the sheaf hypothesis to bounded constructible
   complexes by induction along the canonical truncation triangles: the successive
   terms are the constructible cohomology sheaves, shifted by their degrees.
3. Open restriction preserves cohomology and constructibility, by exact restriction
   to the localized ringed site and lem-sf-native-adic-constructible-pullback. The
   two-open Mayer-Vietoris triangle, lem-sf-native-adic-mayer-vietoris-triangle,
   gives finiteness on a union from finiteness on its two members and overlap.
   The empty scheme has zero module category and supplies the empty-cover case.
4. Strong induction proves finiteness on any finite union from an intersection-closed
   class of opens on which it holds. The overlap of the first member with the union
   of the remaining members is a union of strictly fewer members of the same class.
5. Over an affine target, the source is qcqs. A quasi-compact open contained in an
   affine open has a finite affine cover whose finite intersections are affine
   (taken inside that affine open). Step 2 applies to those affine restrictions;
   step 4 proves finiteness on this quasi-compact open.
6. The quasi-compact opens contained in some affine open form an intersection-closed
   class: quasi-separatedness makes their intersections quasi-compact. Step 5
   applies to every member. A finite affine cover of the source and step 4 give
   finiteness over the affine target. No arbitrary affine intersection is assumed affine.
7. Cover the quasi-compact target by finitely many affine opens. Base change preserves
   finite type and quasi-separatedness. Step 6 applies to each restricted morphism.
   Ringed derived slice localization, identified with the small pro-etale site of
   each open, identifies the restricted derived image with that restricted morphism's
   derived image. The coefficient maps on both sides are precomposition of functions.
8. Exact restriction commutes with cohomology. Constructibility glues by its Zariski
   local definition. Choose the minimum of the finitely many lower bounds and maximum
   of their upper bounds. Outside that interval each cohomology sheaf vanishes on
   the cover, hence vanishes by the sheaf axiom. For empty target any interval works.
-/
theorem adicAffineFinitenessDescent
    (l : ℕ) [Fact l.Prime] (K : Type u) [Field K] [IsAlgClosed K]
    (_hK : ringChar K ≠ l)
    (h_affine : ∀ (A B : Scheme.{u}) [IsAffine A] [IsAffine B]
      (t : B ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType t]
      (g : A ⟶ B) [LocallyOfFiniteType g] (M : AdicSheaf l A),
      IsAdicConstructibleSheaf M →
        DerivedCategory.TStructure.t.bounded
            ((adicLowerStar l g).rightDerivedFunctor.obj
              ((DerivedCategory.singleFunctor _ 0).obj M)) ∧
          _root_.DerivedCategory.homologyProperty (adicConstructibleSheaf l B)
            ((adicLowerStar l g).rightDerivedFunctor.obj
              ((DerivedCategory.singleFunctor _ 0).obj M)))
    {X Y : Scheme.{u}} (s : Y ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType s] [CompactSpace Y]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f]
    (L : DerivedCategory (AdicSheaf l X))
    (hL : DerivedCategory.TStructure.t.bounded L)
    (hLc : _root_.DerivedCategory.homologyProperty (adicConstructibleSheaf l X) L) :
    DerivedCategory.TStructure.t.bounded ((adicLowerStar l f).rightDerivedFunctor.obj L) ∧
      _root_.DerivedCategory.homologyProperty (adicConstructibleSheaf l Y)
        ((adicLowerStar l f).rightDerivedFunctor.obj L) := by
  sorry

end AlgebraicGeometry.ProEtale

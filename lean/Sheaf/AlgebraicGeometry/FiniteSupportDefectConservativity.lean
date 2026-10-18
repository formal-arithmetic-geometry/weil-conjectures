/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q93
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.AlgebraicGeometry.OpenClosedRecollement
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.SixFunctors.Finite.Stalk
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Derived direct image detects a defect with finite closed support

Source: Varshavsky, Lefschetz–Verdier trace formula and a generalization of a theorem
of Fujiwara (arXiv:math/0505564), §§3.2.2(I), 3.2.4
(blueprint: lem-trf-finite-support-defect-conservativity).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Derived direct image detects zero objects and reflects isomorphisms on bounded
complexes supported on a closed subscheme finite over the base. The open immersion
in the support hypothesis is the inclusion of the complement of the closed image.
Source: Varshavsky, Lefschetz–Verdier trace formula and a generalization of a theorem
of Fujiwara (arXiv:math/0505564), §§3.2.2(I), 3.2.4
(blueprint: lem-trf-finite-support-defect-conservativity).

Proof:
1. Vanishing on the complementary open means all cohomology sheaves vanish there,
by exactness of inverse image and conservativity of geometric stalks
(lemma-weil-pbc-geometric-stalk-conservative). Open--closed recollement
(lem-cbc-open-closed-recollement) identifies K with i_* i^* K, with i_* exact.
2. Composition of derived direct images
(lem-weil-pbc-ringed-topoi-derived-pushforward-composition) identifies its image under
Rh_* with R(i ≫ h)_* i^* K. Finite direct image is exact
(lemma-weil-pbc-finite-direct-image-exact); this also holds for module sheaves by the
faithful exact forgetful functor (lem-weil-pbc-module-sheaves-colimits-forgetful).
Thus the exact-functor comparison (lem-weil-pbc-exact-functor-derived-functor) gives
H^q(Rh_* K) = (i ≫ h)_* H^q(i^* K).
3. The finite geometric-fibre stalk formula (lemma-weil-pbc-finite-stalk-formula)
identifies each stalk with a finite product of the stalks upstairs. If it is zero,
every factor is zero. Conservative geometric stalks then show all H^q(i^* K) vanish,
so K is zero. The converse is preservation of zero by derived direct image.
Empty fibres and the zero complex are included in this argument.
4. The cone of a map between supported bounded objects is again supported and bounded,
by its long exact cohomology sequence. Derived direct image is triangulated, as is
the termwise exact finite direct image (lem-sf-exact-functor-derived-triangulated).
Its image map is invertible exactly when the image cone is zero. Apply step 3 to the
cone, which is zero exactly when the original map is invertible. -/
theorem finiteSupportDefectConservativity
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {W S V : Scheme.{u}} (h : W ⟶ S) (i : V ⟶ W)
    [IsClosedImmersion i] [IsFinite (i ≫ h)]
    (K : _root_.DerivedCategory.Bounded (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (_hK : IsZero
      ((upperStar (ModuleCat.{u + 1} A)
        (Scheme.Opens.ι (X := W)
          ⟨(Set.range i.base)ᶜ,
            i.isClosedEmbedding.isClosed_range.isOpen_compl⟩)).mapDerivedCategory.obj K.obj)) :
    (IsZero ((lowerStar (ModuleCat.{u + 1} A) h).rightDerivedFunctor.obj K.obj) ↔
      IsZero K.obj) ∧
    ∀ (L : _root_.DerivedCategory.Bounded
        (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A))),
      IsZero
        ((upperStar (ModuleCat.{u + 1} A)
          (Scheme.Opens.ι (X := W)
            ⟨(Set.range i.base)ᶜ,
              i.isClosedEmbedding.isClosed_range.isOpen_compl⟩)).mapDerivedCategory.obj L.obj) →
      ∀ (f : K ⟶ L),
        IsIso ((lowerStar (ModuleCat.{u + 1} A) h).rightDerivedFunctor.map f.hom) ↔
          IsIso f := by
  sorry

end AlgebraicGeometry.Etale

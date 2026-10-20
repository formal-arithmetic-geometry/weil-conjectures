/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechTotalComplex
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Split finite ordered Čech rows for injective étale module sheaves

Source: Stacks Project, Tags 02FU, 08FI, 0136 and 0137, and the current blueprint proof
of finite-type constructibility, paragraph 2.
(blueprint: lem-dg-etale-injective-finite-cech-rows)

We use the project's fixed-coefficient encoding `Sheaf ... (ModuleCat A)` of modules
over the constant ring sheaf, as authorized in `def-weil-pbc-etale-sheaves`. The ringed-site
encoding is `ringedSiteModules ((constantSheaf ... RingCat).obj (RingCat.of A))`.
Restriction is the recorded inverse image in its existing sectionwise restriction model.
Finite products present the finite direct sums; the universal property and component
formulas determine the row and augmentation up to their unique coordinate isomorphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The étale test object `W ×_X V`, viewed over `X`.
Source: Stacks, Tag 02FU, sectionwise description of the covering resolution.
(blueprint: lem-dg-etale-injective-finite-cech-rows) -/
def finiteCechTestObject {X : Scheme.{u}} (W : X.Etale) (V : X.Opens) : X.Etale :=
  (MorphismProperty.Over.map ⊤ (inferInstance : AlgebraicGeometry.Etale V.ι)).obj
    ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ V.ι).obj W)

/-- Projection of an intersection test object to its original test object.
Source: Stacks, Tag 02FU, augmentation by restrictions.
(blueprint: lem-dg-etale-injective-finite-cech-rows) -/
def finiteCechTestProjection {X : Scheme.{u}} (W : X.Etale) (V : X.Opens) :
    finiteCechTestObject W V ⟶ W :=
  MorphismProperty.Over.homMk (pullback.fst W.hom V.ι) (by
    dsimp [finiteCechTestObject]
    exact pullback.condition)

/-- Inclusion of intersection test objects induced by an inclusion of opens.
Source: Stacks, Tag 02FU, face restriction maps.
(blueprint: lem-dg-etale-injective-finite-cech-rows) -/
def finiteCechTestInclusion {X : Scheme.{u}} (W : X.Etale)
    {V V' : X.Opens} (h : V ≤ V') :
    finiteCechTestObject W V ⟶ finiteCechTestObject W V' :=
  MorphismProperty.Over.homMk
    (pullback.lift (pullback.fst W.hom V.ι)
      (pullback.snd W.hom V.ι ≫ X.homOfLE h) (by
        rw [Category.assoc, X.homOfLE_ι]
        exact pullback.condition)) (by
    change _ ≫ (pullback.snd W.hom V'.ι ≫ V'.ι) =
      pullback.snd W.hom V.ι ≫ V.ι
    rw [← Category.assoc, pullback.lift_snd, Category.assoc, X.homOfLE_ι])

/-- Direct image of restriction to an open, in the sectionwise restriction model.
The restriction model is the existing `openImmersionRestriction`, canonically isomorphic
to the recorded inverse image `upperStar` by `upperStarIsoOpenImmersionRestriction`.
Source: Stacks, Tags 03DH and 08FI.
(blueprint: lem-dg-etale-injective-finite-cech-rows) -/
def finiteCechOpenTerm {X : Scheme.{u}} (A : Type (u + 1)) [CommRing A]
    (J : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (V : X.Opens) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  (lowerStar (ModuleCat.{u + 1} A) V.ι).obj
    ((openImmersionRestriction (ModuleCat.{u + 1} A) V.ι).obj J)

/-- The finite ordered augmented Čech row has injective terms and split cycle inclusions.
Source: Stacks, Tags 02FU, 08FI, 0136 and 0137; current blueprint proof of
`thm-dg-finite-type-constructibility`, paragraph 2.
(blueprint: lem-dg-etale-injective-finite-cech-rows)

Proof: Identify the open étale site with the localized site. Restriction has the exact
left adjoint extension by zero, and thus preserves injectives. Its exactness and its
right adjoint direct image imply that direct image preserves injectives too. This also
handles empty intersections: modules on the empty scheme vanish by the empty-cover axiom.
Finite sums are products in the abelian category, and products of injectives are injective.
The displayed face maps are linear and natural. Two successive deletions cancel with
opposite signs, giving square zero and compatibility with the restriction augmentation.
On a test object contained in the kth covering open, insert k into each increasing tuple,
with sign (-1) to the number of entries preceding k, and put zero when k is already in
the tuple. The deletion/insertion calculation gives dh+hd=1, also at augmentation and
at the top degree. These local contractions prove exactness of the sheaf complex.
Starting with the injective cycle J, split its inclusion into the first injective term.
The next cycle is a retract of that term, hence injective; repeat to obtain all cycle
retractions. This includes the terminal zero cycle. If r=0 the covering condition forces
X empty, and J is zero. No affine, separated, finite-type or coefficient finiteness
hypothesis is used. -/
theorem dg_etale_injective_finite_cech_rows
    (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (r : ℕ) (U : Fin r → X.Opens) (hU : iSup U = ⊤)
    (J : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) [Injective J] :
    ∃ (T : ℕ → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
      (π : ∀ (p : ℕ) (t : Fin (p + 1) ↪o Fin r),
        T p ⟶ finiteCechOpenTerm A J (alternatingCechIntersection U t))
      (d : ∀ p : ℕ, T p ⟶ T (p + 1))
      (hdd : ∀ p : ℕ, d p ≫ d (p + 1) = 0)
      (ε : J ⟶ T 0),
      (∀ p : ℕ, Nonempty (IsLimit (Fan.mk (T p) (π p)))) ∧
      (∀ (p : ℕ) (t : Fin (p + 2) ↪o Fin r) (W : X.Etale)
        (s : (T p).obj.obj (op W)),
        ((π (p + 1) t).hom.app (op W)) (((d p).hom.app (op W)) s) =
          ∑ a : Fin (p + 2), (-1 : ℤ) ^ a.val •
            J.obj.map (finiteCechTestInclusion W
              (alternatingCechIntersection_face_le U p t a)).op
              (((π p ((Fin.succAboveOrderEmb a).trans t)).hom.app (op W)) s)) ∧
      (∀ (t : Fin 1 ↪o Fin r) (W : X.Etale) (s : J.obj.obj (op W)),
        ((π 0 t).hom.app (op W)) ((ε.hom.app (op W)) s) =
          J.obj.map (finiteCechTestProjection W (alternatingCechIntersection U t)).op s) ∧
      (∀ p : ℕ, r ≤ p → IsZero (T p)) ∧
      (∃ hε : ε ≫ d 0 = 0, (ShortComplex.mk ε (d 0) hε).Exact) ∧
      Mono ε ∧
      (∀ p : ℕ, (CochainComplex.of T d hdd).ExactAt (p + 1)) ∧
      (∀ p : ℕ, IsSplitMono (kernel.ι (d p))) ∧
      (∀ p : ℕ, Injective (T p)) ∧
      (r = 0 → IsZero J) := by
  sorry

end AlgebraicGeometry.Etale

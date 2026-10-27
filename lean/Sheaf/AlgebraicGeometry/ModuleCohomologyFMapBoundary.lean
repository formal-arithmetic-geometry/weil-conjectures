/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q146
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Homology.ExactSequence
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyBoundary
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import Sheaf.AlgebraicGeometry.GlobalSectionsLeftExact
import WeilConjectures.CategoryTheory.Abelian.HorseshoeDerivedTriangleComparison
import WeilConjectures.CategoryTheory.Abelian.NatComplexDerivedBoundary
import WeilConjectures.AlgebraicGeometry.FlatModulePullbackExact
import WeilConjectures.CategoryTheory.Abelian.HorseshoeResolutions
import Sheaf.CategoryTheory.InjectiveResolutionSESComplexes
import WeilConjectures.AlgebraicGeometry.BasicPropertiesLinearity
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapFunctorial
import WeilConjectures.AlgebraicGeometry.PushforwardInjectivesSectionsQuasiIso
import WeilConjectures.CategoryTheory.PushoutShortExactSequence
import WeilConjectures.AlgebraicGeometry.Modules.Ext

/-! # Coefficient f-maps commute with module cohomology boundaries

Source: Stacks Project, cohomology.tex, Equation 01F9 and Remark 01FB;
derived.tex, Tag 05TE. The compatibility is the resolution argument of the node,
not a verbatim assertion of either tag
(blueprint: lem-sfb-module-cohomology-fmap-boundary).

The two linear maps in the conclusion have exactly the specified canonical underlying
f-maps. Since the forgetful functor is faithful, each linear lift is uniquely determined.
The final equality is in modules over the source scheme's global section ring; target
scalars are restricted along the scheme morphism's map on global sections.
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Canonical coefficient f-maps between two short exact module rows commute with their
canonical cohomology connecting maps. No flatness, quasi-coherence or acyclicity is assumed.
The canonical boundaries use the standard derived categories, so their construction adds
no existence hypotheses. The underlying-map equalities specify the canonical f-maps,
rather than leaving the two linear maps unconstrained.

Source: Stacks Project, cohomology.tex, Equation 01F9, Remark 01FB and
Equation cohomology-modules; derived.tex, Tag 05TE
(blueprint: lem-sfb-module-cohomology-fmap-boundary).

Proof:
1. By lem-weil-pbc-scheme-modules-enough-injectives and
lem-weil-pbc-injective-resolution-ses choose compatible injective horseshoes J of E and
I of F. Their rows split degreewise, so pushforward and sections preserve those rows.
2. Put A = f_* I. The compatible augmentations s : E[0] -> J and a : E[0] -> A define
Q_j = coker(s_j, -a_j). The snake lemma (lem-weil-pbc-snake-lemma-abelian) gives an exact
row Q, including both endpoints, since each graph map is monic. The maps b : J -> Q and
t : A -> Q respect the rows and satisfy b s = t a.
3. Let C_j = coker(s_j). The resolution augmentation is a quasi-isomorphism, so C_j is
acyclic. The degreewise pushout lemma (lem-weil-pbc-pushout-short-exact-sequence) gives
0 -> A_j -> Q_j -> C_j -> 0. Its long exact sequence
(lem-weil-pbc-complex-ses-homology-long-exact) proves that each t_j is a quasi-isomorphism.
4. By lem-weil-pbc-injective-resolution-ses-complexes resolve Q by an exact nonnegative
injective row K with quasi-isomorphisms r_j. Set lambda = r t and beta = r b, in usual
composition order. Injectivity of K_1 splits this row. The augmentation equation is the
one in def-weil-pbc-module-cohomology-fmap. By
lem-weil-pbc-module-pushforward-injectives-sections-quasi-iso, sections of lambda induce
isomorphisms, without requiring pushforward to preserve injectives.
5. Apply lem-sc-p1-horseshoe-derived-triangle-comparison to global sections on both schemes,
which are additive and left exact by lem-sc-global-sections-left-exact. The image rows and
their zero extensions are exact because they split. Together with
lem-sc-p1-nat-complex-derived-boundary, the endpoint equations identify the canonical
moduleCohomologyBoundary with the boundaries of the section horseshoes, fixing the sign.
6. For both row maps beta and lambda use lem-weil-pbc-complex-ses-connecting-formula:
lift a third-term cocycle z to w in the middle, and lift dw to x in the first term.
Its boundary is [x]. A row map sends these lifts to lifts of the image cocycle, so its
boundary is [m_1 x]. Changing the lift adds a boundary. This proves both boundary squares.
7. Invert the homology maps of sections of lambda, and combine the squares of step 6.
Use lem-weil-pbc-module-cohomology-fmap-functorial (independence) to identify the result
with the specified f-maps, and cancel the resolution comparisons using step 5.
8. The theorem lem-weil-pbc-module-cohomology-fmap-basic-linearity supplies the uniquely
specified linear lifts below. Boundaries are already module-linear; restriction of
scalars changes no underlying elements. Faithfulness gives the displayed module equality.
For a flat pullback the pullback row is exact by
lem-weil-pbc-flat-module-pullback-exact-pushforward-injective, and the adjunction unit of
lem-pc-module-pullback-adjunction supplies the two squares by naturality. Compatible maps
over an automorphism are also instances of the same unrestricted statement. -/
theorem moduleCohomologyFMap_boundary
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (E : ShortComplex (SheafOfModules.{u} Y.ringCatSheaf))
    (F : ShortComplex (SheafOfModules.{u} X.ringCatSheaf))
    (hE : E.ShortExact) (hF : F.ShortExact)
    (φ₁ : E.X₁ ⟶ (pushforward f).obj F.X₁)
    (φ₂ : E.X₂ ⟶ (pushforward f).obj F.X₂)
    (φ₃ : E.X₃ ⟶ (pushforward f).obj F.X₃)
    (_h₁₂ : φ₁ ≫ (pushforward f).map F.f = E.f ≫ φ₂)
    (_h₂₃ : φ₂ ≫ (pushforward f).map F.g = E.g ≫ φ₃)
    (q : ℕ) :
    ∃ (T₁ : (RingedSpace.moduleCohomology Y.toRingedSpace (q + 1)).obj E.X₁ ⟶
          (ModuleCat.restrictScalars f.appTop.hom).obj
            ((RingedSpace.moduleCohomology X.toRingedSpace (q + 1)).obj F.X₁))
      (T₃ : (RingedSpace.moduleCohomology Y.toRingedSpace q).obj E.X₃ ⟶
          (ModuleCat.restrictScalars f.appTop.hom).obj
            ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F.X₃)),
      (forget₂ _ AddCommGrpCat.{u}).map T₁ = moduleCohomologyFMap f φ₁ (q + 1) ∧
      (forget₂ _ AddCommGrpCat.{u}).map T₃ = moduleCohomologyFMap f φ₃ q ∧
      (@RingedSpace.moduleCohomologyBoundary Y.toRingedSpace
          (HasDerivedCategory.standard _) (HasDerivedCategory.standard _) E hE q) ≫ T₁ =
        T₃ ≫ (ModuleCat.restrictScalars f.appTop.hom).map
          (@RingedSpace.moduleCohomologyBoundary X.toRingedSpace
            (HasDerivedCategory.standard _) (HasDerivedCategory.standard _) F hF q) := by
  sorry

end AlgebraicGeometry.Scheme.Modules

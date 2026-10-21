/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.CategoryTheory.CondensedEquivariantBarData
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Sheaf.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.CategoryTheory.ColimitSites
import Sheaf.CategoryTheory.CohomologyColimitSites
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Filtered-colimit continuity of derived profinite functions

Source: Stacks Project, Sites Cohomology, Tag 0GN3 (lemma-colim-global), on coherent
profinite slice sites; the derived internal-function formulation evaluates on profinite
parameters (blueprint: lem-sfb-profinite-derived-functions-filtered-colimit).

The comparison uses compatible nonnegative injective resolutions. Its source is the
localization of the termwise colimit of the internal-Hom complexes, exactly the colimit
specified in the node. The existing free internal module is used throughout.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CondensedBar

namespace CategoryTheory.ProfiniteDerivedFunctions

/-- Apply the specified internal Hom termwise. The free object is the existing composite
of the free-abelian-sheaf and free-internal-module adjunctions, on the representable of P.
Source: Stacks 08J7 and the free-module clause of the node
(blueprint: lem-sfb-profinite-derived-functions-filtered-colimit). -/
def onComplexes (R : Ring.{u}) (P : Profinite.{u}) :
    CochainComplex (Modules R) ℤ ⥤ CochainComplex (Modules R) ℤ :=
  (ihom (freeParameter R P)).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Linearize the actual continuous map of profinite parameter sets using the existing
free-forgetful adjunction. Source: Stacks 08J7, parameter precomposition
(blueprint: lem-sfb-profinite-derived-functions-filtered-colimit). -/
def freeParameterMap (R : Ring.{u}) {P' P : Profinite.{u}} (f : P' ⟶ P) :
    freeParameter R P' ⟶ freeParameter R P :=
  (Sheaf.composeAndSheafify (coherentTopology Profinite.{u}) AddCommGrpCat.free.{u + 1} ⋙
    Mod.free R.toMon.X).map
    (((coherentTopology Profinite.{u}).uliftYoneda.{u + 1}).map f)

/-- Precomposition by the linearized parameter map, on complexes. This is the actual
contravariant internal-Hom map. Source: Stacks 08J7, functoriality of internal Hom
(blueprint: lem-sfb-profinite-derived-functions-filtered-colimit). -/
def parameterRestriction (R : Ring.{u}) {P' P : Profinite.{u}} (f : P' ⟶ P) :
    onComplexes R P ⟶ onComplexes R P' :=
  (MonoidalClosed.pre (freeParameterMap R f)).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The localized canonical map induced by a compatible cocone of complexes. When the
complexes resolve the modules and the vertex resolves their colimit, compatibility of
the augmentations pins this map to the original module coprojections.
Source: Stacks 0GN3, its canonical coefficient comparison, and 08J7
(blueprint: lem-sfb-profinite-derived-functions-filtered-colimit). -/
def comparison (R : Ring.{u}) (P : Profinite.{u})
    {I : Type (u + 1)} [SmallCategory I]
    {K : I ⥤ CochainComplex (Modules R) ℤ} (c : Cocone K) :
    DerivedCategory.Q.obj (colimit (K ⋙ onComplexes R P)) ⟶
      DerivedCategory.Q.obj ((onComplexes R P).obj c.pt) :=
  DerivedCategory.Q.map
    (colimit.desc (K ⋙ onComplexes R P) ((onComplexes R P).mapCocone c))

/-- The defining normalization: the comparison after each coprojection is precisely
internal Hom of that resolution's coefficient map, localized in the ordinary derived
category. Source: Stacks 0GN3, the canonical map in lemma-colim-global
(blueprint: lem-sfb-profinite-derived-functions-filtered-colimit).
Proof: use the defining equation of colimit.desc, then functoriality of localization. -/
theorem comparison_coprojection (R : Ring.{u}) (P : Profinite.{u})
    {I : Type (u + 1)} [SmallCategory I]
    {K : I ⥤ CochainComplex (Modules R) ℤ} (c : Cocone K) (i : I) :
    DerivedCategory.Q.map (colimit.ι (K ⋙ onComplexes R P) i) ≫ comparison R P c =
      DerivedCategory.Q.map ((onComplexes R P).map (c.ι.app i)) := by
  sorry

/-- Derived functions on a profinite parameter commute with the specified exact filtered
colimit of modules placed in degree zero. All compatible nonnegative injective resolutions
and all augmentation-preserving lifts of the original coprojections are allowed.

Source: Stacks 0GN3 (lemma-colim-global), on coherent profinite slices, and 08J7
(blueprint: lem-sfb-profinite-derived-functions-filtered-colimit).

Proof:
1. Finite jointly surjective profinite families give a subcanonical coherent site.
   Transport internal modules through the section-action equivalence. The normalized
   symmetric tensor comparison identifies the two internal-Hom functors and their derived
   functors. The forgetful functor is exact, faithful and preserves colimits.
2. Cohomology on every profinite test object commutes with filtered colimits. Apply the
   cohomology-of-colimit-sites theorem to the constant site system after adjoining an
   initial zero coefficient to the filtered index. Its comparison uses exactly the original
   coprojections. Equivalently apply 0GN3 on the coherent slice site.
3. For the inclusion of abelian sheaves into presheaves, the q-th derived cohomology
   presheaf evaluates to H^q(W,-). Thus its filtered-colimit comparison is an isomorphism,
   objectwise, for each q separately; negative degrees vanish on nonnegative resolutions.
4. The free-representable derived-functions model identifies underlying RH_P with exact
   sheafification of the presheaf model precomposed by W maps to W times P. These two exact
   functors preserve colimits. Exactness of filtered colimits then identifies the cohomology
   of the termwise colimit with the colimit of the cohomologies. Step 3 proves that the
   specified comparison is a quasi-isomorphism. Faithful exact forgetting detects this.
   Localization makes it invertible. No product over unbounded cohomological degrees occurs.
5. Augmentation compatibility identifies every cocone leg with the derived image of the
   original coefficient coprojection; comparison_coprojection fixes their colimit map.
   The following two naturality equations give coefficient and parameter functoriality.
-/
theorem comparison_isIso (R : Ring.{u}) (P : Profinite.{u})
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (M : I ⥤ Modules R) (K : I ⥤ CochainComplex (Modules R) ℤ)
    (s : M ⋙ HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0 ⟶ K)
    (c : Cocone K)
    (sLimit : (HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).obj
      (colimit M) ⟶ c.pt)
    (hs : ∀ i : I, QuasiIso (s.app i))
    (hI : ∀ (i : I) (n : ℤ), Injective ((K.obj i).X n))
    (hneg : ∀ (i : I) (n : ℤ), n < 0 → IsZero ((K.obj i).X n))
    (hsLimit : QuasiIso sLimit)
    (hILimit : ∀ n : ℤ, Injective (c.pt.X n))
    (hnegLimit : ∀ n : ℤ, n < 0 → IsZero (c.pt.X n))
    (hcompat : ∀ i : I, s.app i ≫ c.ι.app i =
      (HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map
        (colimit.ι M i) ≫ sLimit) :
    IsIso (comparison R P c) := by
  sorry

/-- Naturality in diagrams and their module maps, on every compatible chain lift. In
particular, when augmentations identify f and g with a map of coefficient diagrams and
its induced colimit map, this is the required derived comparison square.
Source: Stacks 0GN3 and 08J7, coefficient functoriality
(blueprint: lem-sfb-profinite-derived-functions-filtered-colimit).
Proof: after each colimit coprojection the equation is functoriality of internal Hom
applied to h. The colimit universal property gives equality, and localization preserves it.
-/
theorem comparison_naturality (R : Ring.{u}) (P : Profinite.{u})
    {I : Type (u + 1)} [SmallCategory I]
    {K L : I ⥤ CochainComplex (Modules R) ℤ} (c : Cocone K) (d : Cocone L)
    (f : K ⟶ L) (g : c.pt ⟶ d.pt)
    (h : ∀ i : I, f.app i ≫ d.ι.app i = c.ι.app i ≫ g) :
    DerivedCategory.Q.map (colimMap (Functor.whiskerRight f (onComplexes R P))) ≫
        comparison R P d =
      comparison R P c ≫ DerivedCategory.Q.map ((onComplexes R P).map g) := by
  sorry

/-- Naturality under every continuous map of profinite parameters, with restriction given
by precomposition on the original free modules. Source: Stacks 08J7 and 0GN3
(blueprint: lem-sfb-profinite-derived-functions-filtered-colimit).
Proof: the naturality of internal-Hom precomposition makes the square commute on each
cocone leg. Apply the colimit universal property and then localization. No resolution
change is needed, since the same coefficient resolutions compute both parameter functors.
-/
theorem comparison_parameterNaturality (R : Ring.{u}) {P' P : Profinite.{u}} (f : P' ⟶ P)
    {I : Type (u + 1)} [SmallCategory I]
    {K : I ⥤ CochainComplex (Modules R) ℤ} (c : Cocone K) :
    DerivedCategory.Q.map (colimMap (Functor.whiskerLeft K (parameterRestriction R f))) ≫
        comparison R P' c =
      comparison R P c ≫ DerivedCategory.Q.map ((parameterRestriction R f).app c.pt) := by
  sorry

end CategoryTheory.ProfiniteDerivedFunctions

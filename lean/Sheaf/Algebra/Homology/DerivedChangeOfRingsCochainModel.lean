/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Sheaf.CategoryTheory.RingedSiteModules

/-!
# Derived change of rings with separate localization universes

Source: Stacks Project, sites-cohomology.tex, Tags 06YT, 06YY; derived.tex, Tag 06XN.
(blueprint: lem-pur-derived-change-of-rings).
This is the same universal pair on cochain complexes, allowing different morphism
universes for the two derived categories. The ordinary functor is fixed on objects
and maps; the derived pair is determined up to its unique counit-compatible isomorphism.
-/

@[expose] public section
set_option autoImplicit false
universe u v r wO wS
open CategoryTheory

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}]
  {O S : Sheaf J CommRingCat.{r}} (φ : O ⟶ S)
  [HasDerivedCategory.{wO}
    (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O))]
  [HasDerivedCategory.{wS}
    (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J S))]

/-- A presentation of the derived change-of-rings universal pair, including its actual
ordinary scalar-extension functor, pointwise (everywhere defined) existence and its
canonical K-flat computations.
Source: Stacks 06YY (blueprint: lem-pur-derived-change-of-rings). -/
structure DerivedChangeOfRingsCochainModel where
  /-- Ordinary sheafified extension of scalars. -/
  E : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J O) ⥤
    ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J S)
  /-- Its prescribed object function. -/
  obj_eq : ∀ M, E.obj M = changeOfRings φ M
  /-- Its prescribed map function. -/
  map_eq : ∀ {M N} (f : M ⟶ N), E.map f =
    eqToHom (obj_eq M) ≫ changeOfRingsHom φ M f ≫ eqToHom (obj_eq N).symm
  /-- Ordinary extension is additive. -/
  [additive : E.Additive]
  /-- Extension preserves quasi-isomorphisms between K-flat complexes. -/
  preserves : ∀ {P Q : CochainComplex
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J O)) ℤ}
    (f : P ⟶ Q), CochainComplex.IsKFlatIndependentCoefficients (R := O) P →
    CochainComplex.IsKFlatIndependentCoefficients (R := O) Q → QuasiIso f →
      QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map f)
  /-- The derived extension. -/
  T : DerivedCategory (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J O)) ⥤
    DerivedCategory (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J S))
  /-- The derived extension is everywhere defined: the termwise extension followed by
  localization has a pointwise left derived functor. -/
  pointwise : (E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).HasPointwiseLeftDerivedFunctor
    (HomologicalComplex.quasiIso
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J O)) (.up ℤ))
  /-- Its universal counit on complexes. -/
  ε : DerivedCategory.Q ⋙ T ⟶
    E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  /-- Universal left-derived property. -/
  universal : T.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso _ (.up ℤ))
  /-- Exactness as a triangulated functor. -/
  triangulated : ∃ (_ : T.CommShift ℤ), T.IsTriangulated
  /-- The canonical counit computes derived extension on K-flat models. -/
  computes : ∀ P : CochainComplex
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J O)) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := O) P → IsIso (ε.app P)

attribute [instance] DerivedChangeOfRingsCochainModel.additive

/-- Existence of derived extension with its natural K-flat model identifications, with
independent source and target localization universes.
Source: Stacks 06YT, 06YY and 06XN (blueprint: lem-pur-derived-change-of-rings).
Proof: construct E by sectionwise scalar extension followed by module sheafification.
Its maps are the sheafifications of id tensor f, so E is additive. The cone of a
quasi-isomorphism between K-flat complexes is acyclic and K-flat; tensoring its
K-flat comparison with the new ring leaves it acyclic (06YT). Thus E preserves these
quasi-isomorphisms. Resolve every complex by a K-flat complex (06YS), and apply the
resolving-class construction (06XN), which gives the universal counit and its
invertibility on K-flat representatives, and its pointwise existence at every complex
(computed by a K-flat resolution, Stacks 05SV and 06XN). Precompose the homotopy-category
counit with the homotopy quotient and its localization comparison to obtain the displayed
cochain counit. This changes neither its universal property nor its K-flat components.
Ordinary extension preserves shifts and cones, so the derived functor is triangulated.
All constructions take place separately in the two selected localization categories;
no equality between their Hom universes is used. -/
theorem nonempty_derivedChangeOfRingsCochainModel :
    Nonempty (DerivedChangeOfRingsCochainModel.{u, v, r, wO, wS} φ) := by
  sorry

end SheafOfModules

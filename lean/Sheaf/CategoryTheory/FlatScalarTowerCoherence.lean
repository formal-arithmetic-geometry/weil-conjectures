/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Sheaf.CategoryTheory.SheafTensor
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf

/-!
# Coherence of exact scalar extension for sheaf module objects

Source: blueprint main-20261015, `sk-thm-sfb-qlbar-two-colimit`, proof (4) and the final
cocone paragraph; Stacks Tag 03CZ (blueprint: lem-sfb-flat-scalar-tower-coherence).

The comparisons are the existing `Mod.extendScalarsComp` (in the inverse orientation)
and `Mod.extendScalarsId`. The derived comparisons below apply the existing exact-functor
localization construction to these specified maps. The predicates package the clauses
without choosing a second tensor product or a second extension functor.
-/

@[expose] public section

universe u v uS vS w wA wB wC wR

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonObj

namespace CategoryTheory.Mod

/-- A specified comparison restricts to every preserved full subcategory, with precisely
its ambient components in both directions. Thus any equation between composites of these
components is an equation of restricted morphisms as well, by faithfulness of inclusion.
Source: blueprint proof (4), final cocone paragraph
(blueprint: lem-sfb-flat-scalar-tower-coherence). -/
def ScalarComparisonRestricts {D : Type u} [Category.{v} D]
    {E : Type uS} [Category.{vS} E] {F G : D ⥤ E} (e : F ≅ G) : Prop :=
  ∀ (P : ObjectProperty D) (Q : ObjectProperty E)
    (hF : ∀ X : P.FullSubcategory, Q (F.obj X.obj))
    (hG : ∀ X : P.FullSubcategory, Q (G.obj X.obj)),
    ∃ r : Q.lift (P.ι ⋙ F) hF ≅ Q.lift (P.ι ⋙ G) hG,
      (∀ X : P.FullSubcategory, (r.hom.app X).hom = e.hom.app X.obj) ∧
      (∀ X : P.FullSubcategory, (r.inv.app X).hom = e.inv.app X.obj)

section Ambient

variable {H : Type u} [Category.{v} H] [MonoidalCategory H] [BraidedCategory H]
  [HasCoequalizers H]
  [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- The two quotient-map equations expressing `c ⊗ (b ⊗ m) ↦ c ψ(b) ⊗ m`
and `c ⊗ m ↦ c ⊗ (1 ⊗ m)`, and restriction of this same comparison.
They assert equations of sheaf morphisms, so do not assume sections are pure tensors.
Source: Stacks 03CZ; blueprint proof (4)
(blueprint: lem-sfb-flat-scalar-tower-coherence). -/
def ScalarExtensionTensorLaws : Prop :=
  ∀ (A B C : H) [MonObj A] [MonObj B] [MonObj C]
    [IsCommMonObj A] [IsCommMonObj B] [IsCommMonObj C]
    (f : A ⟶ B) [IsMonHom f] (g : B ⟶ C) [IsMonHom g] (M : Mod H A),
    (C ◁ extendπ f M ≫ extendπ g ((extendScalars f).obj M) ≫
        ((extendScalarsComp f g).inv.app M).hom =
      (α_ C B M.X).inv ≫ (C ◁ g ≫ μ[C]) ▷ M.X ≫ extendπ (f ≫ g) M) ∧
    (extendπ (f ≫ g) M ≫ ((extendScalarsComp f g).hom.app M).hom =
      C ◁ extendUnitHom f M ≫ extendπ g ((extendScalars f).obj M)) ∧
    ScalarComparisonRestricts (extendScalarsComp f g).symm

/-- The identity extension has action as its map, and the two identity comparisons
are the corresponding unit identifications. Source: Stacks 03CZ; blueprint proof (4)
(blueprint: lem-sfb-flat-scalar-tower-coherence). -/
def ScalarExtensionUnitLaws : Prop :=
  (∀ (A : H) [MonObj A] [IsCommMonObj A] (M : Mod H A),
    extendπ (𝟙 A) M ≫ ((extendScalarsId (R := A)).hom.app M).hom = γ[A,M.X] ∧
    ((extendScalarsId (R := A)).inv.app M).hom = extendUnitHom (𝟙 A) M ∧
    ScalarComparisonRestricts (extendScalarsId (R := A))) ∧
  (∀ (A B : H) [MonObj A] [MonObj B] [IsCommMonObj A] [IsCommMonObj B]
    (f : A ⟶ B) [IsMonHom f] (M : Mod H A),
    (extendScalarsComp (𝟙 A) f).inv.app M ≫
        eqToHom (by simp only [Category.id_comp, Functor.id_obj]) =
      (extendScalars f).map ((extendScalarsId (R := A)).hom.app M) ∧
    (extendScalarsComp f (𝟙 B)).inv.app M ≫
        eqToHom (by simp only [Category.comp_id, Functor.id_obj]) =
      (extendScalarsId (R := B)).hom.app ((extendScalars f).obj M))

/-- The ordinary four-ring coherence equation. The final `eqToHom` only identifies
`(f ≫ g) ≫ h` with `f ≫ (g ≫ h)`; it is not a new comparison.
Source: Stacks 03CZ; blueprint proof (4)
(blueprint: lem-sfb-flat-scalar-tower-coherence). -/
def ScalarExtensionTowerLaws : Prop :=
  ∀ (A B C R : H) [MonObj A] [MonObj B] [MonObj C] [MonObj R]
    [IsCommMonObj A] [IsCommMonObj B] [IsCommMonObj C] [IsCommMonObj R]
    (f : A ⟶ B) [IsMonHom f] (g : B ⟶ C) [IsMonHom g]
    (h : C ⟶ R) [IsMonHom h] (M : Mod H A),
    (extendScalars h).map ((extendScalarsComp f g).inv.app M) ≫
        (extendScalarsComp (f ≫ g) h).inv.app M ≫
        eqToHom (by simp only [Category.assoc]) =
      (extendScalarsComp g h).inv.app ((extendScalars f).obj M) ≫
        (extendScalarsComp f (g ≫ h)).inv.app M

end Ambient

section Derived

variable {H : Type u} [Category.{v} H] [MonoidalCategory H] [BraidedCategory H]
  [HasCoequalizers H]
  [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {A B C : H} [MonObj A] [MonObj B] [MonObj C]
  [IsCommMonObj A] [IsCommMonObj B] [IsCommMonObj C]
  [Abelian (Mod H A)] [Abelian (Mod H B)] [Abelian (Mod H C)]
  [HasDerivedCategory.{wA} (Mod H A)] [HasDerivedCategory.{wB} (Mod H B)]
  [HasDerivedCategory.{wC} (Mod H C)]
  (f : A ⟶ B) [IsMonHom f] (g : B ⟶ C) [IsMonHom g]
  [(extendScalars f).Additive] [(extendScalars g).Additive]
  [(extendScalars (f ≫ g)).Additive]
  [PreservesFiniteLimits (extendScalars f)] [PreservesFiniteColimits (extendScalars f)]
  [PreservesFiniteLimits (extendScalars g)] [PreservesFiniteColimits (extendScalars g)]
  [PreservesFiniteLimits (extendScalars (f ≫ g))]
  [PreservesFiniteColimits (extendScalars (f ≫ g))]

/-- The derived comparison obtained by applying the ordinary comparison in each degree
and localizing. This uses the canonical localization comparisons for composite exact
functors, rather than choosing an unspecified isomorphism.
Source: Stacks 015F and 04VG; blueprint proof (4)
(blueprint: lem-sfb-flat-scalar-tower-coherence). -/
noncomputable def flatDerivedScalarComp :
    (extendScalars f).mapDerivedCategory ⋙ (extendScalars g).mapDerivedCategory ≅
      (extendScalars (f ≫ g)).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (extendScalars f) (extendScalars g)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (extendScalarsComp f g).symm

end Derived

section DerivedUnit

variable {H : Type u} [Category.{v} H] [MonoidalCategory H] [BraidedCategory H]
  [HasCoequalizers H]
  [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  (A : H) [MonObj A] [IsCommMonObj A] [Abelian (Mod H A)]
  [HasDerivedCategory.{wA} (Mod H A)]
  [(extendScalars (𝟙 A)).Additive]
  [PreservesFiniteLimits (extendScalars (𝟙 A))]
  [PreservesFiniteColimits (extendScalars (𝟙 A))]

/-- The derived identity comparison, obtained from the ordinary action map termwise.
Source: Stacks 015F and 04VG; blueprint proof (4)
(blueprint: lem-sfb-flat-scalar-tower-coherence). -/
noncomputable def flatDerivedScalarId :
    (extendScalars (𝟙 A)).mapDerivedCategory ≅ 𝟭 (DerivedCategory (Mod H A)) :=
  Functor.mapDerivedCategoryNatIso (extendScalarsId (R := A)) ≪≫
    Functor.mapDerivedCategoryIdIso (Mod H A)

end DerivedUnit

section DerivedLaws

variable {H : Type u} [Category.{v} H] [MonoidalCategory H] [BraidedCategory H]
  [HasCoequalizers H]
  [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- The four-ring equality on unbounded derived categories, for exact extensions along
all six maps of the tower. The comparison is the localized termwise comparison defined
above, also on preserved full subcategories.
Source: Stacks 015F and 04VG; blueprint proof (4)
(blueprint: lem-sfb-flat-scalar-tower-coherence). -/
def FlatDerivedScalarTowerLaws : Prop :=
  ∀ (A B C R : H) [MonObj A] [MonObj B] [MonObj C] [MonObj R]
    [IsCommMonObj A] [IsCommMonObj B] [IsCommMonObj C] [IsCommMonObj R]
    [Abelian (Mod H A)] [HasDerivedCategory.{wA} (Mod H A)]
    [Abelian (Mod H B)] [HasDerivedCategory.{wB} (Mod H B)]
    [Abelian (Mod H C)] [HasDerivedCategory.{wC} (Mod H C)]
    [Abelian (Mod H R)] [HasDerivedCategory.{wR} (Mod H R)]
    (f : A ⟶ B) [IsMonHom f] (g : B ⟶ C) [IsMonHom g]
    (h : C ⟶ R) [IsMonHom h]
    [(extendScalars (f)).Additive]
    [PreservesFiniteLimits (extendScalars (f))]
    [PreservesFiniteColimits (extendScalars (f))]
    [(extendScalars (g)).Additive]
    [PreservesFiniteLimits (extendScalars (g))]
    [PreservesFiniteColimits (extendScalars (g))]
    [(extendScalars (h)).Additive]
    [PreservesFiniteLimits (extendScalars (h))]
    [PreservesFiniteColimits (extendScalars (h))]
    [(extendScalars (f ≫ g)).Additive]
    [PreservesFiniteLimits (extendScalars (f ≫ g))]
    [PreservesFiniteColimits (extendScalars (f ≫ g))]
    [(extendScalars (g ≫ h)).Additive]
    [PreservesFiniteLimits (extendScalars (g ≫ h))]
    [PreservesFiniteColimits (extendScalars (g ≫ h))]
    [(extendScalars ((f ≫ g) ≫ h)).Additive]
    [PreservesFiniteLimits (extendScalars ((f ≫ g) ≫ h))]
    [PreservesFiniteColimits (extendScalars ((f ≫ g) ≫ h))]
    [(extendScalars (f ≫ g ≫ h)).Additive]
    [PreservesFiniteLimits (extendScalars (f ≫ g ≫ h))]
    [PreservesFiniteColimits (extendScalars (f ≫ g ≫ h))]
    (K : DerivedCategory (Mod H A)),
    ((extendScalars h).mapDerivedCategory.map ((flatDerivedScalarComp f g).hom.app K) ≫
        (flatDerivedScalarComp (f ≫ g) h).hom.app K ≫
        eqToHom (by simp only [Category.assoc]) =
      (flatDerivedScalarComp g h).hom.app ((extendScalars f).mapDerivedCategory.obj K) ≫
        (flatDerivedScalarComp f (g ≫ h)).hom.app K) ∧
    ScalarComparisonRestricts (flatDerivedScalarComp f g) ∧
    ScalarComparisonRestricts (flatDerivedScalarComp g h) ∧
    ScalarComparisonRestricts (flatDerivedScalarComp (f ≫ g) h) ∧
    ScalarComparisonRestricts (flatDerivedScalarComp f (g ≫ h))

/-- Both identity compatibilities after termwise extension and localization, including
restriction of the action identification to preserved full subcategories.
Source: Stacks 015F and 04VG; blueprint proof (4)
(blueprint: lem-sfb-flat-scalar-tower-coherence). -/
def FlatDerivedScalarUnitLaws : Prop :=
  ∀ (A B : H) [MonObj A] [MonObj B] [IsCommMonObj A] [IsCommMonObj B]
    [Abelian (Mod H A)] [HasDerivedCategory.{wA} (Mod H A)]
    [Abelian (Mod H B)] [HasDerivedCategory.{wB} (Mod H B)]
    (f : A ⟶ B) [IsMonHom f]
    [(extendScalars (f)).Additive]
    [PreservesFiniteLimits (extendScalars (f))]
    [PreservesFiniteColimits (extendScalars (f))]
    [(extendScalars (𝟙 A)).Additive]
    [PreservesFiniteLimits (extendScalars (𝟙 A))]
    [PreservesFiniteColimits (extendScalars (𝟙 A))]
    [(extendScalars (𝟙 B)).Additive]
    [PreservesFiniteLimits (extendScalars (𝟙 B))]
    [PreservesFiniteColimits (extendScalars (𝟙 B))]
    [(extendScalars (𝟙 A ≫ f)).Additive]
    [PreservesFiniteLimits (extendScalars (𝟙 A ≫ f))]
    [PreservesFiniteColimits (extendScalars (𝟙 A ≫ f))]
    [(extendScalars (f ≫ 𝟙 B)).Additive]
    [PreservesFiniteLimits (extendScalars (f ≫ 𝟙 B))]
    [PreservesFiniteColimits (extendScalars (f ≫ 𝟙 B))]
    (K : DerivedCategory (Mod H A)),
    ((flatDerivedScalarComp (𝟙 A) f).hom.app K ≫
        eqToHom (by simp only [Category.id_comp, Functor.id_obj]) =
      (extendScalars f).mapDerivedCategory.map ((flatDerivedScalarId A).hom.app K)) ∧
    ((flatDerivedScalarComp f (𝟙 B)).hom.app K ≫
        eqToHom (by simp only [Category.comp_id, Functor.id_obj]) =
      (flatDerivedScalarId B).hom.app ((extendScalars f).mapDerivedCategory.obj K)) ∧
    ScalarComparisonRestricts (flatDerivedScalarId A) ∧
    ScalarComparisonRestricts (flatDerivedScalarId B) ∧
    ScalarComparisonRestricts (flatDerivedScalarComp (𝟙 A) f) ∧
    ScalarComparisonRestricts (flatDerivedScalarComp f (𝟙 B))

end DerivedLaws

/-- Package of the ordinary tensor, unit and tower equations and their exact-derived
counterparts, on one fixed braided monoidal category. Coequalizers and tensor preservation
are quantified as proof-valued infrastructure: the sheaf tensor supplies them, and the
package works for any choices of their witnesses. Exactness and abelianness are assumed
only in the derived clauses, and only for the rings and maps in the particular tower.
Source: blueprint proof (4); Stacks 03CZ, 015F and 04VG
(blueprint: lem-sfb-flat-scalar-tower-coherence). -/
def FlatScalarTowerCoherence {H : Type u} [Category.{v} H]
    [MonoidalCategory H] [BraidedCategory H] : Prop :=
  HasCoequalizers H ∧
  (∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorLeft X) ∧
    PreservesColimitsOfSize.{0, 0} (tensorRight X)) ∧
  ∀ [HasCoequalizers H]
    [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorRight X)],
    ScalarExtensionTensorLaws (H := H) ∧
    ScalarExtensionUnitLaws (H := H) ∧
    ScalarExtensionTowerLaws (H := H) ∧
    FlatDerivedScalarTowerLaws.{u, v, wA, wB, wC, wR} (H := H) ∧
    FlatDerivedScalarUnitLaws.{u, v, wA, wB} (H := H)

/-- Canonical scalar-extension comparisons on abelian sheaves satisfy the tensor formulas,
all tower and identity equations, and their exact-derived and full-subcategory versions.

Source: blueprint main-20261015, `sk-thm-sfb-qlbar-two-colimit`, proof (4) and final
cocone paragraph; Stacks 03CZ, 0B65, 015F and 04VG
(blueprint: lem-sfb-flat-scalar-tower-coherence).

Proof, following the ten steps of the node:
1. The closed sheaf tensor preserves colimits on either side, and its Grothendieck
abelian category has coequalizers. The specified extensions are therefore defined.
2. Compose `extendHomEquiv` for two maps. Restriction along a composite has the same
underlying action as successive restriction. The composite bijection takes a map h to
h after the two extension units, m ↦ 1 ⊗ (1 ⊗ m).
3. Uniqueness of left adjoints, with its unit equation (Stacks 0B65), gives precisely
`extendScalarsComp.symm`, normalized by sending the composite unit to the direct unit.
4. The coequalizer balancing relation moves b into the outer factor. Linearity and the
normalization give c ⊗ (b ⊗ m) ↦ c g(b) ⊗ m. The inverse sends c ⊗ m to
c ⊗ (1 ⊗ m). These are the two quotient-map equations in `ScalarExtensionTensorLaws`.
5. Compose three Hom bijections. Both paths around the four-ring square become the
direct extension unit when precomposed with the three units. Injectivity of the
bijection gives their equality, with the displayed associativity transport.
6. For identity maps the action coequalizes the defining pair. Its composite with the
unit is the identity by unitality; the reverse composite is the identity by the Hom
bijection. Both identity comparisons have the same unit normalization, proving the
unit equations, including the all-identity case.
7. Under the additional abelian and exactness hypotheses, termwise extension preserves
quasi-isomorphisms and induces `mapDerivedCategory` on the unbounded localizations
(Stacks 015F). No boundedness or resolution hypothesis is needed.
8. Apply the ordinary comparison in every degree. Naturality makes a chain map with
chain-map inverse; tower and unit equalities hold degree by degree.
9. Extend the termwise isomorphisms through localization (Stacks 04VG), using
`mapDerivedCategoryCompIso` and `mapDerivedCategoryNatIso`. Their factorization equations
identify them with the maps in step 8. Faithfulness of precomposition with localization
on natural transformations proves the derived tower and identity equations.
10. At an object of a preserved full subcategory both endpoints lie in the target full
subcategory. Lift the comparison and its inverse by fullness. Their ambient components
are unchanged, giving `ScalarComparisonRestricts`. Naturality and all equations descend
by faithfulness, for ordinary and derived categories alike.
-/
theorem sheaf_flatScalarTowerCoherence
    {S : Type uS} [Category.{vS} S] [EssentiallySmall.{w} S]
    (J : GrothendieckTopology S) :
    @FlatScalarTowerCoherence.{_, _, wA, wB, wC, wR} (Sheaf J Ab.{w}) _
      (sfbSheafTensorStructure (A := Ab.{w}) J).monoidal
      (sfbSheafTensorStructure (A := Ab.{w}) J).symmetric.toBraidedCategory := by
  sorry

end CategoryTheory.Mod

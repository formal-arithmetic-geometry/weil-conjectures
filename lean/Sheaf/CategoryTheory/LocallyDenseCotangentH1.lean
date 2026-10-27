/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q65
-/
module

public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules

/-!
# Locally dense subpresheaves and first cotangent homology

Source: Stacks Project, Modules on Sites, Tag 08TY, final two paragraphs of the
proof of the claim (blueprint: lem-sfb-locally-dense-cotangent-h1).

The auxiliary declarations construct the canonical sectionwise kernels and their
maps, then apply Mathlib's abelian and module sheafification functors. The ring-level
kernel is exactly `Algebra.H1Cotangent`, using the canonical polynomial presentation.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace CommRingCat

/-- Bundle the canonical presentation kernel as a module; no new kernel is defined.
Source: Stacks 08TY and Algebra 00S0
(blueprint: lem-sfb-locally-dense-cotangent-h1). -/
noncomputable def h1CotangentModule {R S : CommRingCat.{u}} (f : R ⟶ S) : ModuleCat.{u} S :=
  letI := f.hom.toAlgebra
  ModuleCat.of S (Algebra.H1Cotangent R S)

/-- The map of canonical presentation kernels induced by a commuting ring square.
The designated section in the target canonical presentation is `s ↦ X s`, so the
polynomial map sends `X s` to `X (g' s)` and coefficients along `g`.
Source: Stacks 08TY and Algebra 00S1
(blueprint: lem-sfb-locally-dense-cotangent-h1). -/
noncomputable def h1CotangentModuleMap
    {R S R' S' : CommRingCat.{u}} {f : R ⟶ S} {f' : R' ⟶ S'}
    {g : R ⟶ R'} {g' : S ⟶ S'} (fac : g ≫ f' = f ≫ g') :
    h1CotangentModule f ⟶ (ModuleCat.restrictScalars g'.hom).obj (h1CotangentModule f') :=
  letI := f.hom.toAlgebra
  letI := f'.hom.toAlgebra
  letI := g.hom.toAlgebra
  letI := g'.hom.toAlgebra
  letI := (g ≫ f').hom.toAlgebra
  haveI : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower R S S' :=
    IsScalarTower.of_algebraMap_eq' (congrArg Hom.hom fac)
  ModuleCat.ofHom (Y := (ModuleCat.restrictScalars g'.hom).obj (h1CotangentModule f'))
    (Algebra.H1Cotangent.map R R' S S')

end CommRingCat

namespace CategoryTheory

variable {E : Type u} [SmallCategory E]

/-- The canonical restriction map on sectionwise first cotangent homology.
Source: Stacks 08TY, restrictions on the canonical kernel presheaf
(blueprint: lem-sfb-locally-dense-cotangent-h1). -/
noncomputable def firstCotangentRestriction
    {A D : Eᵒᵖ ⥤ CommRingCat.{u}} (a : A ⟶ D) {U V : Eᵒᵖ} (f : U ⟶ V) :
    CommRingCat.h1CotangentModule (a.app U) ⟶
      (ModuleCat.restrictScalars (D.map f).hom).obj
        (CommRingCat.h1CotangentModule (a.app V)) :=
  CommRingCat.h1CotangentModuleMap (g' := D.map f) (a.naturality f)

/-- Identity restriction law for the kernel presheaf.
Source: Stacks 08TY and Algebra 00S1
(blueprint: lem-sfb-locally-dense-cotangent-h1).
Proof: the ring-presheaf identity laws identify the square with an identity square.
The canonical polynomial lift sends each variable to itself. Apply
`Algebra.Extension.H1Cotangent.map_eq` followed by `H1Cotangent.map_id`.
The displayed restriction-of-scalars isomorphism only transports the identity ring map. -/
theorem firstCotangentRestriction_id
    {A D : Eᵒᵖ ⥤ CommRingCat.{u}} (a : A ⟶ D) (U : Eᵒᵖ) :
    firstCotangentRestriction a (𝟙 U) =
      (ModuleCat.restrictScalarsId' ((D ⋙ forget₂ CommRingCat RingCat).map (𝟙 U)).hom
        (congrArg RingCat.Hom.hom ((D ⋙ forget₂ CommRingCat RingCat).map_id U))).inv.app
          (CommRingCat.h1CotangentModule (a.app U)) := by
  sorry

/-- Composite restriction law for the kernel presheaf.
Source: Stacks 08TY and Algebra 00S1
(blueprint: lem-sfb-locally-dense-cotangent-h1).
Proof: the ring-presheaf composition laws identify the composite restriction square.
Its canonical polynomial lift and the composite of the two canonical lifts induce
identical maps by `Algebra.Extension.H1Cotangent.map_eq`. Now use
`H1Cotangent.map_comp`; the last isomorphism transports scalar restriction along
`D.map (f ≫ g) = D.map f ≫ D.map g`. -/
theorem firstCotangentRestriction_comp
    {A D : Eᵒᵖ ⥤ CommRingCat.{u}} (a : A ⟶ D)
    {U V W : Eᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    firstCotangentRestriction a (f ≫ g) =
      firstCotangentRestriction a f ≫
        (ModuleCat.restrictScalars (D.map f).hom).map (firstCotangentRestriction a g) ≫
        (ModuleCat.restrictScalarsComp' (D.map f).hom (D.map g).hom (D.map (f ≫ g)).hom
          (congrArg CommRingCat.Hom.hom (D.map_comp f g))).inv.app
            (CommRingCat.h1CotangentModule (a.app W)) := by
  sorry

/-- The sectionwise kernel module in the statement, with canonical restriction maps.
Source: Stacks 08TY, proof of the claim
(blueprint: lem-sfb-locally-dense-cotangent-h1). -/
noncomputable def firstCotangentPresheaf
    {A D : Eᵒᵖ ⥤ CommRingCat.{u}} (a : A ⟶ D) :
    PresheafOfModules.{u} (D ⋙ forget₂ CommRingCat RingCat) where
  obj U := CommRingCat.h1CotangentModule (a.app U)
  map f := firstCotangentRestriction a f
  map_id := firstCotangentRestriction_id a
  map_comp := firstCotangentRestriction_comp a

/-- The sectionwise comparison as a linear map after scalar restriction.
Source: Stacks 08TY, the canonical kernel map
(blueprint: lem-sfb-locally-dense-cotangent-h1). -/
noncomputable def firstCotangentComparisonApp
    {A D B : Eᵒᵖ ⥤ CommRingCat.{u}} (a : A ⟶ D) (i : D ⟶ B) (U : Eᵒᵖ) :
    (firstCotangentPresheaf a).obj U ⟶
      ((PresheafOfModules.restrictScalars
        (Functor.whiskerRight i (forget₂ CommRingCat RingCat))).obj
          (firstCotangentPresheaf (a ≫ i))).obj U :=
  CommRingCat.h1CotangentModuleMap
    (f := a.app U) (f' := (a ≫ i).app U)
    (g := 𝟙 (A.obj U)) (g' := i.app U) (by simp)

/-- Naturality of the sectionwise kernel comparison, including varying base rings.
Source: Stacks 08TY, canonical maps in the claim, and Algebra 00S1
(blueprint: lem-sfb-locally-dense-cotangent-h1).
Proof: apply the composition law for presentation kernel maps to both sides of the
square. Naturality of `i` identifies their maps on coefficient and target rings.
Independence of lifts (`Algebra.Extension.H1Cotangent.map_eq`) identifies the two
maps, with the displayed restrictions of scalars expressing their common linearity. -/
theorem firstCotangentPresheafMap_naturality
    {A D B : Eᵒᵖ ⥤ CommRingCat.{u}} (a : A ⟶ D) (i : D ⟶ B)
    {U V : Eᵒᵖ} (f : U ⟶ V) :
    (firstCotangentPresheaf a).map f ≫
        (ModuleCat.restrictScalars
          ((D ⋙ forget₂ CommRingCat RingCat).map f).hom).map
            (firstCotangentComparisonApp a i V) =
      firstCotangentComparisonApp a i U ≫
        ((PresheafOfModules.restrictScalars
          (Functor.whiskerRight i (forget₂ CommRingCat RingCat))).obj
            (firstCotangentPresheaf (a ≫ i))).map f := by
  sorry

/-- The canonical kernel comparison as a morphism of presheaves of modules over `D`.
Source: Stacks 08TY, the map in the claim
(blueprint: lem-sfb-locally-dense-cotangent-h1). -/
noncomputable def firstCotangentPresheafMap
    {A D B : Eᵒᵖ ⥤ CommRingCat.{u}} (a : A ⟶ D) (i : D ⟶ B) :
    firstCotangentPresheaf a ⟶
      (PresheafOfModules.restrictScalars (Functor.whiskerRight i
        (forget₂ CommRingCat RingCat))).obj (firstCotangentPresheaf (a ≫ i)) where
  app := firstCotangentComparisonApp a i
  naturality := firstCotangentPresheafMap_naturality a i

/-- The underlying abelian presheaf comparison.
Source: Stacks 08TY, the displayed map of first homology presheaves
(blueprint: lem-sfb-locally-dense-cotangent-h1). -/
noncomputable def firstCotangentAbelianMap
    {A D B : Eᵒᵖ ⥤ CommRingCat.{u}} (a : A ⟶ D) (i : D ⟶ B) :
    (firstCotangentPresheaf a).presheaf ⟶ (firstCotangentPresheaf (a ≫ i)).presheaf :=
  (PresheafOfModules.toPresheaf _).map (firstCotangentPresheafMap a i)

/-- The canonical module sheaf associated to the sectionwise kernel presheaf over
an already sheafified target ring.
Source: Stacks 08TY and 03CY
(blueprint: lem-sfb-locally-dense-cotangent-h1). -/
noncomputable def firstCotangentModuleSheaf
    (J : GrothendieckTopology E) (B : Sheaf J CommRingCat.{u})
    {A : Eᵒᵖ ⥤ CommRingCat.{u}} (a : A ⟶ B.obj) :
    ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B) :=
  (PresheafOfModules.sheafification
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj B)
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).obj)).obj
      (firstCotangentPresheaf a)

/-- Module sheafification of the kernel presheaf over a subpresheaf of the target.
The locally bijective inclusion identifies its ring sheafification with `B`.
Source: Stacks 08TY and 03CY
(blueprint: lem-sfb-locally-dense-cotangent-h1). -/
noncomputable def locallyDenseFirstCotangentSource
    (J : GrothendieckTopology E) (B : Sheaf J CommRingCat.{u})
    {A D : Eᵒᵖ ⥤ CommRingCat.{u}} (a : A ⟶ D) (i : D ⟶ B.obj)
    (hi : ∀ U : Eᵒᵖ, Function.Injective (i.app U))
    (hden : Presheaf.IsLocallySurjective J
      (Functor.whiskerRight i (forget₂ CommRingCat RingCat))) :
    ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B) :=
  letI := Presheaf.isLocallyInjective_of_injective J
    (Functor.whiskerRight i (forget₂ CommRingCat RingCat)) hi
  letI := hden
  (PresheafOfModules.sheafification
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj B)
    (Functor.whiskerRight i (forget₂ CommRingCat RingCat))).obj (firstCotangentPresheaf a)

/-- The canonical `B`-linear sheaf comparison, obtained by the unique extension in
module sheafification, rather than choosing any map or isomorphism.
Source: Stacks 08TY and 03CY
(blueprint: lem-sfb-locally-dense-cotangent-h1). -/
noncomputable def locallyDenseFirstCotangentModuleMap
    (J : GrothendieckTopology E) (B : Sheaf J CommRingCat.{u})
    {A D : Eᵒᵖ ⥤ CommRingCat.{u}} (a : A ⟶ D) (i : D ⟶ B.obj)
    (hi : ∀ U : Eᵒᵖ, Function.Injective (i.app U))
    (hden : Presheaf.IsLocallySurjective J
      (Functor.whiskerRight i (forget₂ CommRingCat RingCat))) :
    locallyDenseFirstCotangentSource J B a i hi hden ⟶
      firstCotangentModuleSheaf J B (a ≫ i) :=
  letI := Presheaf.isLocallyInjective_of_injective J
    (Functor.whiskerRight i (forget₂ CommRingCat RingCat)) hi
  letI := hden
  (PresheafOfModules.sheafificationHomEquiv
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj B)
    (Functor.whiskerRight i (forget₂ CommRingCat RingCat))).symm
      (firstCotangentPresheafMap a i ≫
        (PresheafOfModules.restrictScalars
          (Functor.whiskerRight i (forget₂ CommRingCat RingCat))).map
            ((PresheafOfModules.sheafificationAdjunction
              (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj B)
              (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).obj)).unit.app
                (firstCotangentPresheaf (a ≫ i))))

/-- A locally dense subpresheaf of algebras induces an isomorphism of sheafified first
cotangent homology, both as abelian sheaves and with their canonical `B`-module structures.
Source: Stacks Project, Modules on Sites, Tag 08TY, final two paragraphs of the claim;
Tag 03CY for the module structures
(blueprint: lem-sfb-locally-dense-cotangent-h1).

Proof, following the six DAG steps:
1. For each object set `R = A(U)`, `D = C(U)`, `S = B(U)` and use the nonempty
   directed family of subalgebras `D[F]` generated by finite subsets `F` of `S`.
   Its union is `S`; the canonical presentation kernel maps compose by 00S1.
2. Local density and finite composition and pullback of covers give a common cover
   on which every element of `F` belongs to `C`. Polynomial evaluation then factors
   the restriction from `D[F]` through `C` on that cover. For empty `F` use the
   identity cover.
3. For local injectivity subtract two kernel sections with the same image. The
   directed-union cotangent lemma, clause (ii), kills their difference in a finite
   `D[F]`. The factorization in step 2 and functoriality kill it on a cover in `C`.
4. For local surjectivity, clause (i) of that lemma represents a kernel section of
   `B` at some finite `D[F]`. The same factorization produces local preimages in
   `C`; composition of kernel maps proves that they map to the required restrictions.
5. The locally bijective sheafification criterion gives the abelian isomorphism.
   Applied to the inclusion it identifies the sheafification of `C` with `B`;
   multiplicativity follows after a common cover for two sections, then separatedness.
6. The maps of kernels are `C`-linear. The module-sheafification adjunction of 03CY
   extends them to the displayed canonical `B`-linear map, whose underlying abelian
   map is the one in step 5. The inverse of a bijective `B`-linear map is `B`-linear.
-/
theorem locallyDense_firstCotangent_isIso
    (J : Precoverage E) (_hJ : J.IsSiteForCoverings)
    (A B : Sheaf J.toGrothendieck CommRingCat.{u})
    (D : Eᵒᵖ ⥤ CommRingCat.{u}) (a : A.obj ⟶ D) (i : D ⟶ B.obj)
    (hi : ∀ U : Eᵒᵖ, Function.Injective (i.app U))
    (hden : Presheaf.IsLocallySurjective J.toGrothendieck
      (Functor.whiskerRight i (forget₂ CommRingCat RingCat))) :
    IsIso ((presheafToSheaf J.toGrothendieck AddCommGrpCat.{u}).map
      (firstCotangentAbelianMap a i)) ∧
    IsIso (locallyDenseFirstCotangentModuleMap J.toGrothendieck B a i hi hden) := by
  sorry

end CategoryTheory

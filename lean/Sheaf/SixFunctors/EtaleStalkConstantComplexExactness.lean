/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.AlgebraicGeometry.PointedEtaleStalk
public import Sheaf.CategoryTheory.ConstantRingModuleSheaves
public import Sheaf.CategoryTheory.SiteConstantModuleFunctorGeneral
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-! # Exact étale module stalks and constant complexes

Source: Stacks Project, Modules on Sites, Tags 03EI and 04EQ; Étale Cohomology,
Tag 03PT; Homology, Tag 010N.
(blueprint: lem-sfb-etale-stalk-constant-complex-exactness).

The stalk is the recorded pointed-neighbourhood colimit after restricting sectionwise
along the constant-ring unit. Thus its A-action is the germ action, not an extra choice.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]

/-- The existing constant ring sheaf.
Source: Stacks 03EI (blueprint: lem-sfb-etale-stalk-constant-complex-exactness). -/
abbrev etaleConstantComplexRing : Sheaf T.smallEtaleTopology RingCat.{u + 1} :=
  (constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj (RingCat.of A)

/-- The recorded category of genuine modules over the constant ring sheaf.
Source: Stacks 03DA (blueprint: lem-sfb-etale-stalk-constant-complex-exactness). -/
abbrev etaleConstantComplexModules :=
  ringedSiteModules.{u + 1} (etaleConstantComplexRing T A)

/-- The existing constant module presheaf followed by module sheafification.
Source: Stacks 03EI (blueprint: lem-sfb-etale-stalk-constant-complex-exactness). -/
abbrev etaleConstantComplexFunctor :
    ModuleCat.{u + 1} A ⥤ etaleConstantComplexModules T A :=
  siteConstantModuleFunctorGeneral T.smallEtaleTopology A

variable {T} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]

/-- Take the pointed-neighbourhood colimit of sectionwise A-modules, with scalars
restricted along A → A_T(U). Its underlying colimit is `pointedEtaleStalk` of the
restricted sheaf, and its germs are `pointedEtaleGerm`.
Source: Stacks 04EQ and 03PT
(blueprint: lem-sfb-etale-stalk-constant-complex-exactness). -/
def etaleConstantModuleStalkFunctor (t : Spec (.of Ω) ⟶ T) :
    etaleConstantComplexModules T A ⥤ ModuleCat.{u + 1} A :=
  constantRingModuleRestriction T.smallEtaleTopology A ⋙ (pointSmallEtale t).sheafFiber

/-- The constant-module functor is additive.
Source: Stacks 03EI (blueprint: lem-sfb-etale-stalk-constant-complex-exactness).
Proof: addition of linear maps is sectionwise on constant presheaves. Module
sheafification has the underlying additive sheafification and preserves these sums. -/
theorem etaleConstantComplexFunctor_additive :
    (etaleConstantComplexFunctor T A).Additive := by
  sorry

attribute [instance] etaleConstantComplexFunctor_additive

/-- The module stalk functor is additive.
Source: Stacks 04EQ (blueprint: lem-sfb-etale-stalk-constant-complex-exactness).
Proof: scalar restriction retains the underlying additive maps; germs of sums are
sums of germs in the filtered module colimit. The colimit injections jointly detect
this identity. -/
theorem etaleConstantModuleStalkFunctor_additive (t : Spec (.of Ω) ⟶ T) :
    (etaleConstantModuleStalkFunctor A t).Additive := by
  sorry

attribute [instance] etaleConstantModuleStalkFunctor_additive

/-- Both functors are exact on their abelian module categories.
Source: Stacks 03EI, 03DA, 04EQ and Homology 010N
(blueprint: lem-sfb-etale-stalk-constant-complex-exactness).
Proof: constant module presheaves preserve short exact sequences sectionwise.
Module sheafification has exact underlying abelian sheafification. The faithful
module-to-abelian forgetful functor preserves kernels and cokernels, so reflects
short exactness. This proves constant-module exactness. For the stalk, forgetting
scalars and taking the exact geometric abelian stalk gives a short exact sequence
of groups. Its maps are A-linear for the constant-germ action, and their kernels,
images and surjectivity do not change upon forgetting scalars. Thus the module
stalk is exact. An additive functor preserving short exact sequences preserves
kernels and cokernels by the two image sequences, hence finite limits and colimits. -/
theorem etale_stalk_constant_exact (t : Spec (.of Ω) ⟶ T) :
    PreservesFiniteLimits (etaleConstantComplexFunctor T A) ∧
    PreservesFiniteColimits (etaleConstantComplexFunctor T A) ∧
    PreservesFiniteLimits (etaleConstantModuleStalkFunctor A t) ∧
    PreservesFiniteColimits (etaleConstantModuleStalkFunctor A t) := by
  sorry

/-- Natural linear cohomology comparisons in every integer degree.
Source: Stacks Homology 010N
(blueprint: lem-sfb-etale-stalk-constant-complex-exactness).
Proof: exactness identifies the kernels of mapped differentials and images of
preceding differentials with the images of the original cycles and boundaries.
Their quotients give the displayed isomorphisms. The kernel and cokernel universal
properties give naturality for complex maps. All constructions are in the module
categories, so the comparisons are A-linear and A_T-linear respectively. Only
adjacent differentials enter, so no bound on the complexes is needed. -/
theorem etale_stalk_constant_cohomology (t : Spec (.of Ω) ⟶ T) (n : ℤ) :
    Nonempty (((etaleConstantModuleStalkFunctor A t).mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u + 1} A) (.up ℤ) n) ≅
        (HomologicalComplex.homologyFunctor (etaleConstantComplexModules T A) (.up ℤ) n ⋙
          etaleConstantModuleStalkFunctor A t)) ∧
    Nonempty (((etaleConstantComplexFunctor T A).mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.homologyFunctor (etaleConstantComplexModules T A) (.up ℤ) n) ≅
        (HomologicalComplex.homologyFunctor (ModuleCat.{u + 1} A) (.up ℤ) n ⋙
          etaleConstantComplexFunctor T A)) := by
  sorry

/-- Both termwise functors preserve acyclicity and quasi-isomorphisms, unboundedly.
Source: Stacks Homology 010N
(blueprint: lem-sfb-etale-stalk-constant-complex-exactness).
Proof: the natural cohomology comparisons identify the homology of each mapped
complex with the image of its original homology. Additive functors send zero
objects to zero objects, which proves preservation of acyclicity. Naturality
conjugates the homology map of a mapped quasi-isomorphism to the functor's image
of an invertible homology map. That image is invertible in every degree. -/
theorem etale_stalk_constant_preserves (t : Spec (.of Ω) ⟶ T) :
    (∀ C : CochainComplex (etaleConstantComplexModules T A) ℤ,
      C.Acyclic →
        (((etaleConstantModuleStalkFunctor A t).mapHomologicalComplex (.up ℤ)).obj C).Acyclic) ∧
    (∀ E : CochainComplex (ModuleCat.{u + 1} A) ℤ,
      E.Acyclic →
        (((etaleConstantComplexFunctor T A).mapHomologicalComplex (.up ℤ)).obj E).Acyclic) ∧
    (∀ {C D : CochainComplex (etaleConstantComplexModules T A) ℤ} (f : C ⟶ D),
      QuasiIso f → QuasiIso
        (((etaleConstantModuleStalkFunctor A t).mapHomologicalComplex (.up ℤ)).map f)) ∧
    (∀ {E F : CochainComplex (ModuleCat.{u + 1} A) ℤ} (f : E ⟶ F),
      QuasiIso f → QuasiIso
        (((etaleConstantComplexFunctor T A).mapHomologicalComplex (.up ℤ)).map f)) := by
  sorry

/-- The natural chain retraction is normalized by constant germs; the stalk of A_T
is A with its ordinary scalar action.
Source: Stacks 03PT (2), 03EI and 04EQ
(blueprint: lem-sfb-etale-stalk-constant-complex-exactness).
Proof: the underlying abelian constant-germ map is invertible by 03PT. Linearity
of the module-sheafification unit gives η(am)=aη(m), and functoriality of that unit
gives naturality in all module maps. Apply this to each differential: the degreewise
constant-germ maps commute with the differential, hence define a chain isomorphism.
The inverses commute with differentials by multiplying the same identities by the
component inverses. Apply module naturality to every component of a complex map to
obtain chain naturality. For the regular module A_T, the ring sheafification unit
is multiplicative and sends 1 to 1; its germ identifies the scalar action with the
ordinary action of A on itself. No step uses finiteness or bounds. -/
theorem etale_stalk_constant_complex_retraction (t : Spec (.of Ω) ⟶ T) :
    (∃ η : 𝟭 (CochainComplex (ModuleCat.{u + 1} A) ℤ) ≅
        (etaleConstantComplexFunctor T A).mapHomologicalComplex (.up ℤ) ⋙
          (etaleConstantModuleStalkFunctor A t).mapHomologicalComplex (.up ℤ),
      ∀ (E : CochainComplex (ModuleCat.{u + 1} A) ℤ) (n : ℤ) (e : E.X n),
        ((η.hom.app E).f n) e =
          (pointedEtaleGerm
            ((constantRingModuleRestriction T.smallEtaleTopology A).obj
              ((etaleConstantComplexFunctor T A).obj (E.X n))) t
            (Etale.mk (𝟙 T)) (Over.homMk t (Category.comp_id t)))
              ((toSheafify T.smallEtaleTopology
                ((siteConstantModulePresheafGeneral (C := T.Etale) A).obj
                  (E.X n)).presheaf).app (op (Etale.mk (𝟙 T))) e)) ∧
    (∃ ε : ModuleCat.of A A ≅ (etaleConstantModuleStalkFunctor A t).obj
        (SheafOfModules.unit (etaleConstantComplexRing T A)),
      ∀ a : A, ε.hom a =
        (pointedEtaleGerm
          ((constantRingModuleRestriction T.smallEtaleTopology A).obj
            (SheafOfModules.unit (etaleConstantComplexRing T A))) t
          (Etale.mk (𝟙 T)) (Over.homMk t (Category.comp_id t)))
            ((toSheafify T.smallEtaleTopology
              ((Functor.const T.Etaleᵒᵖ).obj (RingCat.of A))).app
                (op (Etale.mk (𝟙 T))) a)) := by
  sorry

end AlgebraicGeometry.Scheme

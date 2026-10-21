/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Topology.ContinuousMapCondensedRing
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Derived global sections and the norm topology on algebraic-closure coefficients

Source: blueprint main-20261015, `sk-thm-sf-ctf-stability-direct-images.proof.md`,
paragraph (3), the agent coefficient-topology obligation
(blueprint: lem-sfb-norm-algcl-cohomology-topology-comparison).

The inclusion of the finite-subextension-valued sheaf into all continuous functions
is constructed sectionwise. After restriction to the finite coefficient field, its
image in the derived category is tensored with V. This is the actual map represented
on a flat-term K-flat resolution by z tensor v mapping to c(z) tensor v.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.NormAlgclComparison

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- Sectionwise inclusion of finite-subextension-valued continuous functions.
Source: the coefficient inclusion in paragraph (3) of the source proof
(blueprint: lem-sfb-norm-algcl-cohomology-topology-comparison). -/
def coefficientInclusionRing :
    Profinite.padicAlgClCondensedRing.{u} ℓ ⟶
      Profinite.continuousMapRingSheaf (PadicAlgCl ℓ) :=
  ⟨{ app := fun S ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          ((PadicAlgCl.finiteIntermediateFieldValued ℓ S.unop).subtype.comp
            ULift.ringEquiv.toRingHom))
     naturality := fun _ _ _ ↦ rfl }⟩

/-- The same inclusion as a morphism of the recorded condensed ring objects.
Source: paragraph (3), c:C to B
(blueprint: lem-sfb-norm-algcl-cohomology-topology-comparison). -/
def coefficientInclusion :
    Profinite.padicAlgClRingObj.{u} ℓ ⟶
      Profinite.continuousMapRingObj (PadicAlgCl ℓ) :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (coefficientInclusionRing ℓ)

/-- The inclusion respects units and multiplication, since it comes from ring maps.
Source: paragraph (3), c:C to B
(blueprint: lem-sfb-norm-algcl-cohomology-topology-comparison). -/
instance coefficientInclusion_isMonHom : IsMonHom (coefficientInclusion.{u} ℓ) :=
  inferInstanceAs (IsMonHom ((sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (coefficientInclusionRing ℓ)))

variable (X : Scheme.{u}) (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- The finite-field inclusion A to C_X, using the published scalar inclusion.
Source: paragraph (3), finite intermediate field E
(blueprint: lem-sfb-norm-algcl-cohomology-topology-comparison). -/
abbrev finiteScalarMap :=
  (upperStarFromPoint X).map (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)

/-- Pullback of c to X, including its ring-object structure.
Source: paragraph (3), c_X
(blueprint: lem-sfb-norm-algcl-cohomology-topology-comparison). -/
abbrev inclusionOnScheme := (upperStarFromPoint X).map (coefficientInclusion ℓ)

/-- The regular C_X-module restricted to A.
Source: paragraph (3), Res(C_X)
(blueprint: lem-sfb-norm-algcl-cohomology-topology-comparison). -/
abbrev finiteSubextensionModule :=
  (Mod.comap (finiteScalarMap ℓ X E)).obj
    (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))

/-- The regular B_X-module restricted to A along the composite inclusion.
Source: paragraph (3), Res(B_X)
(blueprint: lem-sfb-norm-algcl-cohomology-topology-comparison). -/
abbrev normContinuousModule :=
  (Mod.comap (finiteScalarMap ℓ X E ≫ inclusionOnScheme ℓ X)).obj
    (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) X))

/-- The actual A-linear coefficient inclusion, with its action inherited by restriction.
Source: paragraph (3), c_X viewed as a morphism of A-modules
(blueprint: lem-sfb-norm-algcl-cohomology-topology-comparison). -/
def coefficientModuleMap : finiteSubextensionModule ℓ X E ⟶ normContinuousModule ℓ X E :=
  Mod.Hom.mk' (inclusionOnScheme ℓ X) (by
    change (finiteScalarMap ℓ X E ▷ _ ≫ MonObj.mul) ≫ inclusionOnScheme ℓ X =
      _ ◁ inclusionOnScheme ℓ X ≫
        (finiteScalarMap ℓ X E ≫ inclusionOnScheme ℓ X) ▷ _ ≫ MonObj.mul
    rw [Category.assoc, IsMonHom.mul_hom, MonoidalCategory.tensorHom_def]
    simp only [comp_whiskerRight, Category.assoc]
    rw [← whisker_exchange_assoc, ← whisker_exchange_assoc])

/-- The canonical comparison m_V in D(A). Tensoring the degree-zero inclusion with V
computes restricted derived extension of scalars on either side, and on any flat-term
K-flat model P the chain map is z tensor v mapping to c_X(z) tensor v.
Source: paragraph (3), displayed m_V
(blueprint: lem-sfb-norm-algcl-cohomology-topology-comparison). -/
def comparison
    (V : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))) :=
  ((DerivedCategory.singleFunctor _ 0).map (coefficientModuleMap ℓ X E)) ▷ V

/-- Forget A-actions exactly, then take ordinary unbounded derived global sections.
Source: paragraph (3), R Gamma on the small pro-etale site
(blueprint: lem-sfb-norm-algcl-cohomology-topology-comparison). -/
def derivedGlobalSections :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X)) ⥤
        DerivedCategory Ab.{u + 1} :=
  letI := (constantSheafΓAdj (Scheme.ProEt.topology X) Ab.{u + 1}).isRightAdjoint
  letI : (Sheaf.Γ (Scheme.ProEt.topology X) Ab.{u + 1}).Additive :=
    Functor.additive_of_preserves_binary_products _
  (Mod.forget (condensedRingObj (Profinite.continuousMapRingObj E) X)).mapDerivedCategory ⋙
    (Sheaf.Γ (Scheme.ProEt.topology X) Ab.{u + 1}).rightDerivedFunctor

/-- The actual coefficient inclusion becomes invertible after ordinary derived global
sections, for every bounded constructible finite-field input with finite constant models.
Source: paragraph (3), agent coefficient-topology obligation; exact literature proof WANTED
(blueprint: lem-sfb-norm-algcl-cohomology-topology-comparison).

Proof plan:
1. Choose a separable closure and apply lem-sfb-geometric-condensed-finite-scalar-model:
   its bounded geometric model has finite-dimensional continuous E-representation cohomology,
   and its two projection isomorphisms intertwine this actual coefficient inclusion.
2. Apply lem-sfb-profinite-algcl-derived-invariants-comparison to each cohomology
   representation. Exactness and shift compatibility give the comparison on its shifts.
3. Use the standard derived t-structure and lem-sf-triangle-two-out-of-three along the
   finite truncation tower of the bounded geometric model. Begin with zero below the
   cohomological support; induction gives invertibility on the whole model. This requires
   neither a finite cohomological dimension nor an infinite Postnikov convergence claim.
4. Apply lem-sfb-condensed-galois-global-descent. Its naturality and the C-linear square
   of the geometric model identify R Gamma(m_V), up to the two descent and projection
   isomorphisms, with the comparison proved invertible in step 3. Cancel these isomorphisms.
No sheaf-level isomorphism, flatness of c_X, or completeness of the algebraic closure is used. -/
theorem isIso_derivedGlobalSections_comparison
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)
    (a : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType a] [QuasiCompact a] [IsSeparated a]
    (V : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X)))
    (hV : constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X V) :
    IsIso ((derivedGlobalSections ℓ X E).map (comparison ℓ X E V)) := by
  sorry

end AlgebraicGeometry.ProEtale.NormAlgclComparison

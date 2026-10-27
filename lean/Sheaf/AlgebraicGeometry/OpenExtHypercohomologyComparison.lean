/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q42
-/
module

public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import Sheaf.Topology.RingedSpaceHypercohomologyPresheaf
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import Sheaf.Algebra.Homology.KInjectiveHomComplex
import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIso
import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparison
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized
import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturality
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-! # Local Ext and internal-Hom hypercohomology

Source: Stacks Project, Cohomology, Tags 08DK and 08DL, and the Hom-complex
cocycle formula (blueprint: lem-trf-open-ext-hypercohomology-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

variable (X : RingedSpace.{u})
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]
  [∀ U : Opens X, HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X).over U))]

/-- The local shifted Hom group, using exact derived open restriction.
Source: Stacks, Tag 08DK (blueprint: lem-trf-open-ext-hypercohomology-comparison). -/
abbrev localDerivedExt (K L : DerivedCategory (SheafOfModules.{u} (moduleRings X)))
    (i : ℤ) (U : Opens X) :=
  ((SheafOfModules.overFunctor.{u} (moduleRings X) U).mapDerivedCategory.obj K ⟶
    ((SheafOfModules.overFunctor.{u} (moduleRings X) U).mapDerivedCategory.obj L)⟦i⟧)

/-- The existing unbounded hypercohomology presheaf applied to the existing RHom bifunctor.
Source: Stacks, Tag 08DK (blueprint: lem-trf-open-ext-hypercohomology-comparison). -/
abbrev internalHomHypercohomology (i : ℤ) :
    (DerivedCategory (SheafOfModules.{u} (moduleRings X)))ᵒᵖ ×
      DerivedCategory (SheafOfModules.{u} (moduleRings X)) ⥤
        (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  derivedInternalHom (Opens.grothendieckTopology X) X.sheaf ⋙
    RingedSpace.ringedSpaceHypercohomologyPresheaf X i

/-- Shifted local Hom restriction: undo the restriction/shift comparison, use the
recorded canonical restriction on the pair K,L[i], and restore the comparison on W.
Source: Stacks, Tags 08DK and 08DL
(blueprint: lem-trf-open-ext-hypercohomology-comparison). -/
def localDerivedExtRestriction
    {K L : DerivedCategory (SheafOfModules.{u} (moduleRings X))}
    (i : ℤ) {W U : Opens X} (j : W ⟶ U) (f : localDerivedExt X K L i U) :
    localDerivedExt X K L i W :=
  derivedOpenHomRestriction X j
      (f ≫ ((SheafOfModules.overFunctor.{u} (moduleRings X) U).mapDerivedCategory.commShiftIso
        i).inv.app L) ≫
    ((SheafOfModules.overFunctor.{u} (moduleRings X) W).mapDerivedCategory.commShiftIso
      i).hom.app L

/-- The canonical additive local Ext comparison, natural in both derived arguments and
in every open, including successive restrictions. No boundedness or freeness is assumed.

Source: Stacks, Tag 08DK, all shifts; Tag 08DL and the Hom-complex cocycle formula
(blueprint: lem-trf-open-ext-hypercohomology-comparison).

Proof:
1. Represent K,L by E,M. Resolve M functorially by a K-injective I, and E by a K-flat P.
The complexes C=Hom(E,I) and B=Hom(P,I) are quasi-isomorphic by rhom-well-defined;
B is K-injective by hom-kflat-into-kinjective. Crucially, sections of C to B are
quasi-isomorphisms on every open, by hom-complex-sections-quasi-iso.
2. Naturality of the right-derived evaluation unit gives a square for C to B. The top,
bottom and right arrows are invertible, hence so is the unit for C. One functorial
K-injective replacement of C computes these units on all opens and their restrictions.
3. The canonical section comparison sends a cocycle to its shifted chain map.
Restriction of I and every shift of I is K-injective. The K-injective localization
bijection thus identifies its homotopy class with a derived morphism. Compose this
additive bijection with the inverse cohomology of the unit from step 2.
4. Every component of the shifted chain map is the evaluated Hom-complex projection.
Restricting a cocycle restricts these components; the signs depend only on the degrees.
The same holds for boundaries. The composition comparisons in derivedOpenHomRestriction
therefore give exactly the displayed restriction square, including the shift isomorphisms.
5. Precomposition by t and postcomposition by s act on cochains by z to szt, hence on
shifted maps by t;f;s[i]. The canonical section comparison and derived-naturality lemma
prove the square on representatives. Naturality of both resolution units and inversion
of quasi-isomorphisms descend it through localization to arbitrary derived morphisms.
6. Restricting components twice equals direct restriction. The intermediate composition
isomorphisms cancel in the conjugation formula. Identity restriction is the identity.
Thus the additive comparisons form an isomorphism of abelian presheaves. -/
theorem openExt_hypercohomology_comparison (i : ℤ) :
    ∃ α : ∀ (K L : DerivedCategory (SheafOfModules.{u} (moduleRings X))) (U : Opens X),
      ((internalHomHypercohomology X i).obj (op K, L)).obj (op U) ≃+
        localDerivedExt X K L i U,
      (∀ (K L : DerivedCategory (SheafOfModules.{u} (moduleRings X)))
        (W U : Opens X) (j : W ⟶ U)
        (a : ((internalHomHypercohomology X i).obj (op K, L)).obj (op U)),
        α K L W (((internalHomHypercohomology X i).obj (op K, L)).map j.op a) =
          localDerivedExtRestriction X i j (α K L U a)) ∧
      (∀ (K' K L L' : DerivedCategory (SheafOfModules.{u} (moduleRings X)))
        (t : K' ⟶ K) (s : L ⟶ L') (U : Opens X)
        (a : ((internalHomHypercohomology X i).obj (op K, L)).obj (op U)),
        α K' L' U (((internalHomHypercohomology X i).map (t.op, s)).app (op U) a) =
          (SheafOfModules.overFunctor.{u} (moduleRings X) U).mapDerivedCategory.map t ≫
            α K L U a ≫ (shiftFunctor _ i).map
              ((SheafOfModules.overFunctor.{u} (moduleRings X) U).mapDerivedCategory.map s)) ∧
      (∀ (K L : DerivedCategory (SheafOfModules.{u} (moduleRings X)))
        (V W U : Opens X) (k : V ⟶ W) (j : W ⟶ U)
        (a : ((internalHomHypercohomology X i).obj (op K, L)).obj (op U)),
        localDerivedExtRestriction X i k
            (localDerivedExtRestriction X i j (α K L U a)) =
          localDerivedExtRestriction X i (k ≫ j) (α K L U a)) := by
  sorry

end AlgebraicGeometry

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q137
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.Topology.Bases
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Sites.Sheafification
import Sheaf.Algebra.Homology.KInjectiveRestrictLocalized
import WeilConjectures.Topology.RingedSpaceModuleEnoughInjectives
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Sheaf.Algebra.Homology.DerivedInternalHomSectionsModel
import Sheaf.CategoryTheory.Sites.UnboundedSectionsLocalization
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.AlgebraicGeometry.UnboundedDirectImageSectionPresheaf

/-!
# Negative local Ext vanishing on a basis and the derived Hom sheaf

Source: Stacks Project, cohomology.tex, Tag 0D66, part (2)
(blueprint: lem-trf-derived-basis-local-ext-sheaf).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

/-- Negative Ext vanishing on inverse images of basis opens extends to every open, and
local degree-zero derived Hom is an abelian sheaf. The sheaf is specified by additive
identifications with these exact Hom groups, commuting with the existing canonical
`derivedOpenHomRestriction`; it is not an arbitrary sheaf with unrelated fibres.
Restriction uses the exact termwise restriction functor on the slice site. This site
presents the open with its restricted structure sheaf. `f` is a morphism of ringed spaces;
no locality condition on its stalk maps is imposed.

Source: Stacks Project, cohomology.tex, Tag 0D66 (2)
(blueprint: lem-trf-derived-basis-local-ext-sheaf).

Proof:
1. Put A = RHom(K,L). Internal Hom commutes with restriction. The tensor-Hom adjunction
and the K-injective sections computation identify H^i(f⁻¹V,A) with
Hom(K|f⁻¹V,(L|f⁻¹V)[i]), naturally for inclusions of opens. A cocycle restricts the same
local maps, and restriction preserves K-injectivity, so these comparisons commute with
successive restrictions without any boundedness assumption.
2. Put B = Rf_*A. The unbounded direct-image section-presheaf comparison identifies
H^i(f⁻¹V,A) with H^i(V,B) and its sheafification with the underlying abelian sheaf of
H^i(B). For i < 0 this presheaf is zero on the basis. Any map to an abelian sheaf is zero:
its values restrict to zero on the cover by basis members contained in each open, hence
are zero by separatedness. The sheafification universal property, applied to its own
identity and zero maps, gives H^i(B) = 0 for all negative i.
3. B is therefore bounded below. Choose a K-injective representative J with injective
terms and J^n = 0 for n < 0. Derived evaluation at any open is computed by J(V), so
H^i(V,B) = 0 for i < 0. Moreover H^0(J(V)) is the kernel of J^0(V) to J^1(V), since
J^-1 = 0. Kernels of module sheaves are sectionwise, so this is H^0(B)(V).
4. All comparisons restrict the same sections and cocycles. Thus the underlying abelian
sheaf of H^0(B), with the resulting additive identifications e, has exactly the canonical
Hom restriction maps in the conclusion. Chaining the comparisons also proves vanishing
on every open. The empty-cover axiom covers the empty open; the basis need not be closed
under intersections. -/
theorem derived_basis_local_ext_sheaf
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    (B : Set (Opens Y))
    (hB : IsTopologicalBasis ((fun V : Opens Y ↦ (V : Set Y)) '' B))
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]
    [∀ U : Opens X, HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X).over U))]
    (K L : DerivedCategory (SheafOfModules.{u} (moduleRings X)))
    (hneg : ∀ V ∈ B, ∀ i : ℤ, i < 0 →
      Subsingleton
        ((SheafOfModules.overFunctor.{u} (moduleRings X)
            ((Opens.map f.hom.base).obj V)).mapDerivedCategory.obj K ⟶
          ((SheafOfModules.overFunctor.{u} (moduleRings X)
            ((Opens.map f.hom.base).obj V)).mapDerivedCategory.obj L)⟦i⟧)) :
    (∀ (V : Opens Y) (i : ℤ), i < 0 →
      Subsingleton
        ((SheafOfModules.overFunctor.{u} (moduleRings X)
            ((Opens.map f.hom.base).obj V)).mapDerivedCategory.obj K ⟶
          ((SheafOfModules.overFunctor.{u} (moduleRings X)
            ((Opens.map f.hom.base).obj V)).mapDerivedCategory.obj L)⟦i⟧)) ∧
    ∃ (H : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{w})
      (e : ∀ V : Opens Y, H.obj.obj (op V) ≃+
        ((SheafOfModules.overFunctor.{u} (moduleRings X)
            ((Opens.map f.hom.base).obj V)).mapDerivedCategory.obj K ⟶
          (SheafOfModules.overFunctor.{u} (moduleRings X)
            ((Opens.map f.hom.base).obj V)).mapDerivedCategory.obj L)),
      ∀ (U V : Opens Y) (i : U ⟶ V) (s : H.obj.obj (op V)),
        e U (H.obj.map i.op s) =
          derivedOpenHomRestriction X ((Opens.map f.hom.base).map i) (e V s) := by
  sorry

end AlgebraicGeometry

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.AlgebraicGeometry.GenericComponentData
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.CategoryTheory.LeftDerivedEquivalenceSquare
import Sheaf.CategoryTheory.ModuleTerminalScalarComparison

/-! # Derived scalar compatibility from ordinary equivalences

Source: HRS, proof following (4.4); Stacks Project, Tags 05RR and 0941.
-/

@[expose] public section

set_option autoImplicit false

universe u wR wS wV wCJ wCK
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.ProEt

/-- Normalized terminal evaluation supplies the ordinary discrete-ring square.
Source: HRS, proof following (4.4)
(blueprint: lem-zl-generic-component-derived-scalar-transport).

Proof: the restriction map along t is an invertible semilinear evaluation map.
The equation for e makes it linear for the indicated R-actions. This identifies
the scalar-restriction right adjoints, and hence their left adjoints, by uniqueness.
The independent constant-ring comparison is retained as the second clause. -/
theorem generic_component_ordinary_scalar_transport
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    (A : Sheaf J RingCat.{u + 1}) (B : Sheaf K RingCat.{u + 1})
    (φ : A ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj B)
    (c : C) (d : D) (t : F.obj c ≅ d)
    (e : A.obj.obj (op c) ≅ B.obj.obj (op d))
    (he : e.hom = φ.hom.app (op c) ≫ B.obj.map t.inv.op)
    (E : ringedSiteModules.{u + 1} A ≌ ringedSiteModules.{u + 1} B)
    (adj : Nonempty (E.functor ⊣ SheafOfModules.pushforward φ))
    (h : GenericComponentConstantScalarCompatibility A B c d e E) :
    GenericComponentOrdinaryScalarCompatibility A B c d e E := by
  refine ⟨?_, h⟩
  intro R _ a FS FV _ _ hFS hFV
  exact module_terminal_scalar_comparison F A B φ c d t e he E.functor adj.some
    R a FS FV hFS.some hFV.some

/-- The ordinary comparisons imply all the unbounded derived scalar comparisons.
Source: HRS, proof following (4.4); Stacks Project, Tags 05RR and 0941
(blueprint: lem-zl-generic-component-derived-scalar-transport).

Proof: the additive module equivalence is exact. Its termwise functor therefore
localizes at all quasi-isomorphisms to a derived equivalence, with the standard
Q-factorization. An ordinary scalar-extension square is a square of arbitrary
additive functors under exact equivalences. The uniqueness of universal right Kan
extensions gives its derived square. For ordinary ring modules the source
equivalence is the identity. For constant-ring sheaves use the supplied equivalence
ER. Exact constant realization commutes with ER; its derived comparison is obtained
by localizing that isomorphism and using functoriality of exact-functor localization.
Precompose the scalar-extension derived square with this comparison. No boundedness,
flatness or choice of resolutions is needed. -/
theorem generic_component_derived_scalar_transport
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (A : Sheaf J RingCat.{u + 1}) (B : Sheaf K RingCat.{u + 1})
    (c : C) (d : D) (e : A.obj.obj (op c) ≅ B.obj.obj (op d))
    (E : ringedSiteModules.{u + 1} A ≌ ringedSiteModules.{u + 1} B)
    [E.functor.Additive]
    (h : GenericComponentOrdinaryScalarCompatibility A B c d e E)
    [HasDerivedCategory.{wS} (ringedSiteModules.{u + 1} A)]
    [HasDerivedCategory.{wV} (ringedSiteModules.{u + 1} B)] :
    ∃ ED : DerivedCategory (ringedSiteModules.{u + 1} A) ≌
        DerivedCategory (ringedSiteModules.{u + 1} B),
      Nonempty (DerivedCategory.Q ⋙ ED.functor ≅
        E.functor.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) ∧
      GenericComponentScalarCompatibility.{u, wR, wS, wV, wCJ, wCK} A B c d e ED := by
  classical
  refine ⟨E.mapDerivedCategory, ⟨E.functor.mapDerivedCategoryFactors⟩, ?_, ?_⟩
  · intro R _ _ a FS FV _ _ hFS hFV LS LV εS εV hLS hLV
    let := hLS
    let := hLV
    obtain ⟨eF⟩ := h.1 R a FS FV hFS hFV
    let : (CategoryTheory.Equivalence.refl (C := ModuleCat.{u + 1} R)).functor.Additive :=
      show (𝟭 (ModuleCat.{u + 1} R)).Additive from inferInstance
    obtain ⟨eD⟩ := CategoryTheory.LeftDerivedEquivalenceSquare.comparison
      (CategoryTheory.Equivalence.refl (C := ModuleCat.{u + 1} R)) E FS FV LS LV εS εV
      (eF ≪≫ (Functor.leftUnitor FV).symm)
    exact ⟨eD ≪≫ Functor.isoWhiskerRight (Functor.mapDerivedCategoryIdIso _) LV ≪≫
      Functor.leftUnitor LV⟩
  · intro R _ _ _ _ aS aV ha FS FV _ _ hFS hFV LS LV εS εV hLS hLV
    let := hLS
    let := hLV
    obtain ⟨ER, hER, ⟨eConst⟩, hERscalar⟩ := h.2 R
    let := hER
    obtain ⟨eF⟩ := hERscalar aS aV ha FS FV hFS hFV
    obtain ⟨eD⟩ := CategoryTheory.LeftDerivedEquivalenceSquare.comparison
      ER E FS FV LS LV εS εV eF
    let eConstD : commutativeSiteDerivedConstantModuleFunctor J R ⋙
        ER.mapDerivedCategory.functor ≅ commutativeSiteDerivedConstantModuleFunctor K R :=
      (Functor.mapDerivedCategoryCompIso (commutativeSiteConstantModuleFunctor J R)
        ER.functor).symm ≪≫ Functor.mapDerivedCategoryNatIso eConst
    exact ⟨Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ eD ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eConstD LV⟩

end AlgebraicGeometry.Scheme.ProEt

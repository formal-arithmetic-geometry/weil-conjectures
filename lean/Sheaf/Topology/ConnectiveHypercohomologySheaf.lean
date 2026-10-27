module

public import Sheaf.Topology.RingedSpaceHypercohomologyPresheaf
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Topology.RingedSpaceModuleEnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses

/-! # Connective module-sheaf hypercohomology in nonpositive degrees

Source: Stacks Project, Cohomology, Tag 0D66, proof of (1)
(blueprint: lem-trf-connective-hypercohomology-sheaf).
-/

@[expose] public section

set_option autoImplicit false

universe u w wAb

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.RingedSpace

/-- On every ringed space, a connective derived module sheaf has vanishing negative
hypercohomology on all opens. Its zeroth hypercohomology presheaf is canonically the
underlying abelian sheaf of its zeroth cohomology sheaf. The family of presheaf
isomorphisms is natural in all derived morphisms between connective objects.
The final equation fixes the canonical comparison: on every map M[0] → E its
composite with the ordinary-to-derived unit is the map on zeroth cohomology.

Source: Stacks Project, Cohomology, Tag 0D66, proof of (1)
(blueprint: lem-trf-connective-hypercohomology-sheaf).

Proof:
1. Module sheaves on a ringed space are abelian with enough injectives by
   lem-sc-ringed-space-module-sheaves-enough-injectives. The hypothesis places E
   in D⁺. By lem-weil-pbc-dplus-injective-representative choose a single global
   injective complex I, zero below zero, with QI ≅ E. It is K-injective.
2. For every open V, including the empty open, evaluate this same I termwise.
   By def-sfb-right-derived-functor and prop-pur-kinjective-resolutions-exist this
   computes unbounded RΓ(V,E). The complex of sections is zero below zero, hence
   its negative cohomology vanishes. Evaluation need not preserve injectives.
3. Both H⁰(Γ(V,I)) and Γ(V,H⁰(I)) are the cycles in I⁰(V), since I⁻¹ = 0;
   kernels of module sheaves are sectionwise. Send each cycle to itself and then
   transport by H⁰(QI ≅ E). Restrictions send cycles to their restrictions, giving
   an isomorphism of abelian presheaves with the specified derived restrictions.
4. By lem-weil-pbc-kinjective-hom-derived any derived map between two such models
   is represented by a chain map, unique up to homotopy. Both comparisons send a
   cycle s to its image under that chain map. Homotopic maps agree on cycles:
   their difference is d⁻¹h⁰ + h¹d⁰, which is zero there. This proves naturality,
   independence of the model, and the displayed unit normalization for M[0] → E.
   The target is the underlying abelian sheaf of H⁰(E), so transport its sheaf
   axiom across the isomorphism. The empty-cover axiom gives zero at the empty
   open. No upper bound, quasi-compactness, or scheme structure is used. -/
theorem connective_hypercohomology_sheaf (X : RingedSpace.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{wAb} AddCommGrpCat.{u}] :
    (∀ (E : DerivedCategory (SheafOfModules.{u} (moduleRings X)))
      (_ : ∀ i : ℤ, i < 0 →
        IsZero ((DerivedCategory.homologyFunctor _ i).obj E))
      (V : Opens X) (i : ℤ), i < 0 →
        IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj
          ((openModuleDerivedSections X V).obj E))) ∧
    ∃ e : ∀ (E : DerivedCategory (SheafOfModules.{u} (moduleRings X)))
      (_ : ∀ i : ℤ, i < 0 →
        IsZero ((DerivedCategory.homologyFunctor _ i).obj E)),
      (ringedSpaceHypercohomologyPresheaf X 0).obj E ≅
        (moduleAbelianPresheaf X).obj ((DerivedCategory.homologyFunctor _ 0).obj E),
      (∀ (E E' : DerivedCategory (SheafOfModules.{u} (moduleRings X)))
        (hE : ∀ i : ℤ, i < 0 → IsZero ((DerivedCategory.homologyFunctor _ i).obj E))
        (hE' : ∀ i : ℤ, i < 0 → IsZero ((DerivedCategory.homologyFunctor _ i).obj E'))
        (f : E ⟶ E'),
        (ringedSpaceHypercohomologyPresheaf X 0).map f ≫ (e E' hE').hom =
          (e E hE).hom ≫
            (moduleAbelianPresheaf X).map ((DerivedCategory.homologyFunctor _ 0).map f)) ∧
      (∀ (E : DerivedCategory (SheafOfModules.{u} (moduleRings X)))
        (hE : ∀ i : ℤ, i < 0 → IsZero ((DerivedCategory.homologyFunctor _ i).obj E)),
        Presheaf.IsSheaf (Opens.grothendieckTopology X)
          ((ringedSpaceHypercohomologyPresheaf X 0).obj E) ∧
        IsZero (((ringedSpaceHypercohomologyPresheaf X 0).obj E).obj (op ⊥))) ∧
      (∀ (E : DerivedCategory (SheafOfModules.{u} (moduleRings X)))
        (hE : ∀ i : ℤ, i < 0 → IsZero ((DerivedCategory.homologyFunctor _ i).obj E))
        (M : SheafOfModules.{u} (moduleRings X))
        (f : (DerivedCategory.singleFunctor _ 0).obj M ⟶ E),
        hypercohomologyPresheafSingleUnit X M ≫
            (ringedSpaceHypercohomologyPresheaf X 0).map f ≫ (e E hE).hom =
          (moduleAbelianPresheaf X).map
            ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).inv.app M ≫
              (DerivedCategory.homologyFunctor _ 0).map f)) := by
  sorry

end AlgebraicGeometry.RingedSpace

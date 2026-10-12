/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone

/-!
# Derived change of rings on a ringed site

Source: literature/stacks-project/sites-cohomology.tex, Tags 06YT, 06YY, and
literature/stacks-project/derived.tex, Tag 06XN
(blueprint: lem-pur-derived-change-of-rings).

The change of rings `- ⊗_O O'` is the landed `SheafOfModules.changeOfRings φ` on objects
and `SheafOfModules.changeOfRingsHom φ` on morphisms (def-pur-sheaf-tensor-product); the
statement asserts an additive functor `E` with exactly these objects and maps, and uses
`E.mapHomologicalComplex` (termwise change of rings of complexes) and
`E.mapHomotopyCategory ⋙ DerivedCategory.Qh` (the functor `K(O) → D(O')`).
-/

@[expose] public section

universe w u

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

set_option hygiene false in
local notation "𝓡" R => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

/-- Derived change of rings along a morphism `φ : O ⟶ O'` of sheaves of commutative rings
on a site. There is an additive functor `E : Mod(O) ⥤ Mod(O')` whose objects and maps are
the change of rings `changeOfRings φ` / `changeOfRingsHom φ` (`- ⊗_O O'`), such that
(1) termwise change of rings `E.mapHomologicalComplex` sends every quasi-isomorphism between
K-flat complexes to a quasi-isomorphism, and (2) the functor
`K(O) → D(O')`, `G ↦ Q(G ⊗_O O')`, has an everywhere defined (pointwise) left derived
functor `Lφ^* : D(O) ⥤ D(O')` with counit `ε`, which is triangulated, and `ε` is an
isomorphism at every K-flat complex. Hence for a K-flat resolution `s : P → G` the canonical
map `Lφ^* G ≅ Lφ^* P → P ⊗_O O'` (inverse of `Lφ^*(s)` followed by `ε_P`) is an isomorphism,
and the comparison isomorphisms between two resolutions are composites of these, so
canonical and compatible with composition.
Source: Stacks Project, Tags 06YT, 06YY, and 06XN.
Proof: (1) For a quasi-isomorphism `α : P → Q` of K-flat complexes, its cone `C` is acyclic
and K-flat. Tensoring commutes with cones (lem-pc-tensor-mapping-cone-iso), so the cone of
`α ⊗ 1` is `Tot(C ⊗_O O')`; take a K-flat resolution `R → O'` (lem-pc-kflat-resolution):
by symmetry of `Tot` and K-flatness of `C`, `Tot(C ⊗ O') ≃ Tot(C ⊗ R)` is acyclic
(Tag 06YT), so `α ⊗ 1` is a quasi-isomorphism.
(2) The functor `K(O) → D(O')` is exact (termwise additive functors commute with shifts and
cones). The K-flat complexes form a resolving class by lem-pc-kflat-resolution and are sent
to isomorphisms on quasi-isomorphisms by (1); lem-pur-left-derived-from-kflat-class (Tags
06XN, 05SE) gives the everywhere defined triangulated left derived functor whose counit is an
isomorphism on K-flat complexes. (3) The canonical maps are composites of `ε_P` and inverses of
images of quasi-isomorphisms, hence isomorphisms and compatible with composition.
(blueprint: lem-pur-derived-change-of-rings) -/
theorem derivedChangeOfRings
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    {O O' : Sheaf J CommRingCat.{u}} (φ : O ⟶ O')
    [HasDerivedCategory.{w} (SheafOfModules.{u} (𝓡 O))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (𝓡 O'))] :
    ∃ (E : SheafOfModules.{u} (𝓡 O) ⥤ SheafOfModules.{u} (𝓡 O'))
      (h : ∀ M : SheafOfModules.{u} (𝓡 O), E.obj M = changeOfRings.{u, u, u} φ M)
      (_ : ∀ {M N : SheafOfModules.{u} (𝓡 O)} (a : M ⟶ N),
        E.map a = eqToHom (h M) ≫ changeOfRingsHom.{u, u, u} φ M a ≫ eqToHom (h N).symm)
      (_ : E.Additive),
      (∀ {P Q : CochainComplex (SheafOfModules.{u} (𝓡 O)) ℤ} (α : P ⟶ Q),
        P.IsKFlat → Q.IsKFlat → QuasiIso α →
          QuasiIso ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map α)) ∧
      (E.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
          (HomotopyCategory.quasiIso (SheafOfModules.{u} (𝓡 O)) (ComplexShape.up ℤ)) ∧
      ∃ (LF : DerivedCategory (SheafOfModules.{u} (𝓡 O)) ⥤
          DerivedCategory (SheafOfModules.{u} (𝓡 O')))
        (ε : DerivedCategory.Qh ⋙ LF ⟶
          E.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh),
        LF.IsLeftDerivedFunctor ε
            (HomotopyCategory.quasiIso (SheafOfModules.{u} (𝓡 O)) (ComplexShape.up ℤ)) ∧
          (∃ (_ : LF.CommShift ℤ), LF.IsTriangulated) ∧
          ∀ P : CochainComplex (SheafOfModules.{u} (𝓡 O)) ℤ, P.IsKFlat →
            IsIso (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) := by
  sorry

end SheafOfModules

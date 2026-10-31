/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass

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

## Main definitions

- `derivedChangeRing`: the underlying ring sheaf in independent site universes.

## Main statements

- `derivedChangeOfRingsGeneral`: the full derived-change-of-rings statement without
  identifying the object and morphism universes of the site.
-/

@[expose] public section

universe w u v

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- Forget commutativity without identifying the two universes of the site.
Source: Stacks Tag 06YY (blueprint: lem-pur-derived-change-of-rings). -/
noncomputable abbrev derivedChangeRing {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    (O : Sheaf J CommRingCat.{max u v}) :=
  (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj O

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
Proof:
1. Form the sectionwise extension-of-scalars functor from changeOfRingsPresheaf and
changeOfRingsHom_naturality (def-pur-sheaf-tensor-product), then compose with sheafification.
Identities and composition hold sectionwise. Both functors are additive by their
adjunctions to additive restriction or forgetful functors (Adjunction.left_adjoint_additive).
This gives E with exactly the specified objects and maps.
2. Apply lem-pur-change-of-rings-kflat-quasi-iso to E with these identifications to obtain
preservation of quasi-isomorphisms between K-flat complexes.
3. Let F be the induced homotopy functor followed by derived localization
(def-weil-abstract-derived-category); it commutes with shifts and is triangulated.
Use homotopy objects represented by K-flat complexes as the resolving class
(def-pc-kflat-complex). Resolve every representative by lem-pc-kflat-resolution and apply
quotient_map_mem_quasiIso_iff to its augmentation. For a quasi-isomorphism between objects
of this class, lift through the full homotopy quotient on chosen K-flat representatives.
Step 2 and localization make its F-image invertible. Apply
lem-pur-left-derived-from-kflat-class to obtain pointwise existence, the universal derived
pair, triangulatedness, and the counit isomorphism on every K-flat complex. The canonical
resolution comparisons are composites of these counit maps and inverses of images of
quasi-isomorphisms, hence are isomorphisms and compatible with a third resolution.
(blueprint: lem-pur-derived-change-of-rings) -/
theorem derivedChangeOfRingsGeneral
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    {O O' : Sheaf J CommRingCat.{max u v}} (φ : O ⟶ O')
    [HasDerivedCategory.{w} (SheafOfModules.{max u v} (derivedChangeRing J O))]
    [HasDerivedCategory.{w} (SheafOfModules.{max u v} (derivedChangeRing J O'))] :
    ∃ (E : SheafOfModules.{max u v} (derivedChangeRing J O) ⥤ SheafOfModules.{max u v}
      (derivedChangeRing J O'))
      (h : ∀ M : SheafOfModules.{max u v} (derivedChangeRing J O), E.obj M = changeOfRings.{v, u,
        max u v} φ M)
      (_ : ∀ {M N : SheafOfModules.{max u v} (derivedChangeRing J O)} (a : M ⟶ N),
        E.map a = eqToHom (h M) ≫ changeOfRingsHom.{v, u, max u v} φ M a ≫ eqToHom (h N).symm)
      (_ : E.Additive),
      (∀ {P Q : CochainComplex (SheafOfModules.{max u v} (derivedChangeRing J O)) ℤ} (α : P ⟶ Q),
        P.IsAcyclicTensorKFlat → Q.IsAcyclicTensorKFlat → QuasiIso α →
          QuasiIso ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map α)) ∧
      (E.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
          (HomotopyCategory.quasiIso (SheafOfModules.{max u v} (derivedChangeRing J O))
            (ComplexShape.up ℤ)) ∧
      ∃ (LF : DerivedCategory (SheafOfModules.{max u v} (derivedChangeRing J O)) ⥤
          DerivedCategory (SheafOfModules.{max u v} (derivedChangeRing J O')))
        (ε : DerivedCategory.Qh ⋙ LF ⟶
          E.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh),
        LF.IsLeftDerivedFunctor ε
            (HomotopyCategory.quasiIso (SheafOfModules.{max u v} (derivedChangeRing J O))
              (ComplexShape.up ℤ)) ∧
          (∃ (_ : LF.CommShift ℤ), LF.IsTriangulated) ∧
          ∀ P : CochainComplex (SheafOfModules.{max u v} (derivedChangeRing J O)) ℤ,
            P.IsAcyclicTensorKFlat →
            IsIso (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) := by
  -- At coefficient universe max u v, the two K-flat predicates agree definitionally.
  -- Relative essential smallness and sheafification are supplied by existing instances.
  exact derivedChangeOfRingsIndependentCoefficients φ

end SheafOfModules

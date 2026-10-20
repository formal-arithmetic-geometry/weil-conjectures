/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q28
-/
module

public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LocalSite
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Topology.Constructible

/-!
# Constructible etale modules over a discrete Noetherian ring

Source: Stacks Project, etale-cohomology.tex, Tag 03RW(3), and proetale.tex, Tag 09AL,
with the bounded restriction in the constructible comparison blueprint
(blueprint: def-pe-etale-constructible-module).

The ambient category is modules over the constant ring sheaf. Its existing restriction
of scalars identifies these with module-valued sheaves, where the recorded etale inverse
image applies. Constructibility is affine-local, with finitely generated constant values;
it imposes neither a global finite stratification nor finiteness of the underlying sets.
The two categories below retain all ambient morphisms. No completeness condition is used.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Affine-local constructibility in the module-valued encoding. On every affine open,
a finite constructible locally closed stratification admits etale trivializations with
finitely generated constant module values. The schemes and immersions of the strata are
those of the recorded `Stratification`; constructibility is in the affine open.
Source: Stacks Project, Tag 03RW(3)
(blueprint: def-pe-etale-constructible-module). -/
def Scheme.IsAffineLocallyConstructibleEtaleModuleSheaf
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [IsNoetherianRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) : Prop :=
  ∀ U : X.Opens, IsAffineOpen U →
    ∃ S : Scheme.Stratification U.toScheme,
      (∀ a : Fin S.n, Topology.IsConstructible (S.stratum a)) ∧
      ∀ a : Fin S.n,
        ∃ V : Scheme.Cover.{u} Scheme.etalePrecoverage (S.domain a),
          ∀ b : V.I₀, ∃ M : ModuleCat.{u + 1} Λ, Module.Finite Λ M ∧
            Nonempty
              ((((Etale.upperStar (ModuleCat.{u + 1} Λ) (S.immersion a ≫ U.ι)).obj F).over
                  (MorphismProperty.Over.mk ⊤ (V.f b) (V.map_prop b))) ≅
                (constantSheaf
                  ((S.domain a).smallEtaleTopology.over
                    (MorphismProperty.Over.mk ⊤ (V.f b) (V.map_prop b)))
                  (ModuleCat.{u + 1} Λ)).obj M)

namespace Etale

/-- Constructible modules over the constant ring sheaf, tested after the existing
constant-scalar restriction functor. Its inverse extends the scalar action by sheafification;
thus the local isomorphisms are module-sheaf isomorphisms, not just abelian-sheaf isomorphisms.
Source: Stacks Project, Tag 03RW(3)
(blueprint: def-pe-etale-constructible-module). -/
def constructibleNoetherianModules (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [IsNoetherianRing Λ] :
    ObjectProperty (ringedSiteModules.{u + 1}
      ((constantSheaf X.smallEtaleTopology RingCat.{u + 1}).obj (RingCat.of Λ))) :=
  fun F ↦ Scheme.IsAffineLocallyConstructibleEtaleModuleSheaf
    ((Scheme.etaleConstantModuleRestrictionFunctor X Λ).obj F)

/-- The full category of constructible etale modules: all linear ambient morphisms,
with inherited identities and composition. Source: Stacks Project, Tag 03RW(3)
(blueprint: def-pe-etale-constructible-module). -/
abbrev ConstructibleNoetherianModuleCategory (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [IsNoetherianRing Λ] :=
  (constructibleNoetherianModules X Λ).FullSubcategory

/-- Choose Mathlib's standard localization for the ambient category of all modules over
the constant ring sheaf. This is localization data, not an additional mathematical hypothesis.
Source: Stacks Project, Tag 09AL and Derived Categories, Tag 05RU
(blueprint: def-pe-etale-constructible-module). -/
noncomputable instance noetherianEtaleModulesHasDerivedCategory
    (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] :
    HasDerivedCategory.{u + 2} (ringedSiteModules.{u + 1}
      ((constantSheaf X.smallEtaleTopology RingCat.{u + 1}).obj (RingCat.of Λ))) :=
  HasDerivedCategory.standard _

/-- Bounded complexes in the derived category of all constant-ring module sheaves whose
cohomology sheaves are constructible in every integer degree. The cohomology vanishes
outside one finite interval, and no completeness condition is imposed.
Source: Stacks Project, Tag 09AL, with the blueprint's bounded restriction
(blueprint: def-pe-etale-constructible-module). -/
def boundedConstructibleNoetherianModules (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [IsNoetherianRing Λ] :
    ObjectProperty (DerivedCategory (ringedSiteModules.{u + 1}
      ((constantSheaf X.smallEtaleTopology RingCat.{u + 1}).obj (RingCat.of Λ)))) :=
  fun K ↦
    (∀ q : ℤ, constructibleNoetherianModules X Λ
      ((_root_.DerivedCategory.homologyFunctor _ q).obj K)) ∧
    ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, (q < a ∨ b < q) →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj K)

/-- `D^b_c(X_et, Λ)`, retaining every ambient derived morphism between the bounded objects
with constructible cohomology. Source: Stacks Project, Tag 09AL, bounded restriction
(blueprint: def-pe-etale-constructible-module). -/
abbrev BoundedConstructibleNoetherianModuleCategory (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [IsNoetherianRing Λ] :=
  (boundedConstructibleNoetherianModules X Λ).FullSubcategory

end Etale

end AlgebraicGeometry

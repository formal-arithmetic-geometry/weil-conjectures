module

public import Sheaf.AlgebraicGeometry.ProEtalePairFlasque
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.ProEtaleClosedEssentialImage
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.CategoryTheory.RingedSiteModules

/-!
# Exact sequence of supported sections for injective pro-etale complexes

Source: Weil conjectures blueprint, node `lem-pur-support-exact`;
Stacks Project, Tags 03EJ, 03EI, 09AH and 0114 (blueprint: lem-pur-support-exact).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

/-- Apply the actual closed supported inverse image and direct image term by term.
Source: Weil conjectures blueprint, node `lem-pur-support-exact`, displayed first term
(blueprint: lem-pur-support-exact). -/
noncomputable def supportedSectionsComplex
    (R : Type (u + 1)) [CommRing R] [Finite R] {Z U X : Scheme.{u}}
    (s : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion s] [IsOpenImmersion j]
    (hcompl : IsCompl (Set.range s.base) (Set.range j.base))
    (I : CochainComplex (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) ℤ) :
    CochainComplex (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) ℤ :=
  letI : PreservesFiniteLimits (finiteClosedUpperShriek R s j) :=
    (finiteSupportedSections_leftExact R s j hcompl).2
  (((s)_*[ModuleCat.{u + 1} R]).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (((finiteClosedUpperShriek R s j).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I)

/-- The canonical supported-section inclusion and open restriction unit are short exact
for a termwise injective complex and a quasi-compact open complement.
Source: Weil conjectures blueprint, node `lem-pur-support-exact`; Stacks Project,
Tags 03EJ, 03EI, 09AH and 0114 (blueprint: lem-pur-support-exact).
Proof:
1. Identify open inverse image with restriction by localization of the pro-etale site
   (`lem-weil-proetale-weakly-etale-localization` and `def-pur-localized-ringed-site`).
   The coefficient map is identity on constants, so the module unit on an object V is
   restriction to V times_X U (`def-weil-proetale-inverse-image`).
2. The inclusion V times_X U into V gives an injection on representable bases, hence a
   monomorphism of free module presheaves (`lem-weil-pbc-free-yoneda-presheaf-module`).
   Exact sheafification preserves this monomorphism
   (`lem-weil-pbc-ringed-site-module-sheafification-exact`).
3. The free-module Hom bijection and sheafification adjunction identify precomposition
   with this map with restriction of sections: evaluate on the identity basis element
   (`def-weil-presheaf-modules-sheafification`).
4. Injectivity of each I.X n extends every such section across that monomorphism
   (`def-sp-injective-resolutions`). Thus the open unit is sectionwise surjective and
   consequently epic in every degree.
5. Its kernel is the supported-section sheaf. For a quasi-compact complement its closed
   adjunction unit identifies this kernel with s_*s^!I.X n (`def-pur-flasque-support`).
   Naturality makes the kernel inclusions and open units chain maps, with zero composite.
6. The sequence is short exact in each degree (`def-weil-pbc-exact-sequence`); the abelian
   degreewise criterion gives short exactness of complexes
   (`lem-weil-pbc-cochain-complexes-degreewise-exact`). No boundedness or K-injectivity is
   used. The equations below specify the canonical maps, rather than arbitrary maps
   between the same three objects. -/
theorem shortExact_sectionsWithSupport
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {Z U X : Scheme.{u}} (s : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion s] [IsOpenImmersion j] [QuasiCompact j]
    (hcompl : IsCompl (Set.range s.base) (Set.range j.base))
    (I : CochainComplex (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} R)) ℤ)
    [∀ n, Injective (I.X n)] :
    ∃ (f : supportedSectionsComplex R s j hcompl I ⟶ I)
      (g : I ⟶ (((j)^*[ModuleCat.{u + 1} R] ⋙ (j)_*[ModuleCat.{u + 1} R]).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I),
      (∀ n, (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) s).unit.app
          ((finiteSupportedSections R j).obj (I.X n)) ≫ f.f n =
        (finiteSupportedSectionsι R j).app (I.X n)) ∧
      (∀ n, g.f n =
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) j).unit.app (I.X n)) ∧
      ∃ (w : f ≫ g = 0), (ShortComplex.mk f g w).ShortExact := by
  sorry

end AlgebraicGeometry.ProEtale

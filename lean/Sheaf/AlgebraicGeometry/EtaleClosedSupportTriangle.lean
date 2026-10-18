/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.KInjectiveTotalDerived
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import Sheaf.Algebra.Homology.KInjectiveRestrictLocalized
import Sheaf.CategoryTheory.Sites.SheafificationPlusTheorem
import Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage
import WeilConjectures.SixFunctors.OpenClosed.Stalk
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-!
# The ordinary derived closed-support triangle

Source: blueprint sec-smooth-purity/sk-prop-sf-existence,
lem-exc-closed-support-triangle, order 1804; Stacks Project, Tags 0A45 and 0152
(blueprint: lem-exc-closed-support-triangle).
-/

set_option autoImplicit false

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- For a complementary closed-open pair and a finite, possibly noncommutative ring,
the closed adjunction counit and open adjunction unit extend to a natural distinguished
triangle on the ordinary unbounded derived category. Module-valued etale sheaves encode
left modules over the sheafification of the constant ring presheaf: a locally represented
constant scalar acts locally, and the resulting sections glue uniquely. This is the same
encoding as the recorded closed-ambient adjoint, without constructibility conditions.

Source: blueprint lem-exc-closed-support-triangle, order 1804; Stacks Project,
Tags 0A45 (support triangle), 0152 (boundary), 079P (injective-term replacement),
070K (total derivation), 08FI (restriction of K-injectives), 04CA (closed direct image),
09XQ (sections with support) and 093X (restriction of injective sections)
(blueprint: lem-exc-closed-support-triangle).

Proof, following the nine steps of the node:
1. In the chosen small-site universe, module sheaves are Grothendieck abelian.
   Replace a representative of K functorially by a K-injective complex I with injective
   terms (lem-pur-kinjective-degreewise-existence).
2. Identify the open site with the localized site. The plus formula for sheafification
   identifies the coefficient sheaves on the open, including their ring operations.
   Thus open inverse image is exact restriction, its unit is restriction of sections,
   and j^*I is K-injective (lem-pur-kinjective-restrict-localized). Total derivation
   identifies j_*j^*I with Rj_*j^*K (lem-weil-pbc-kinjective-total-derived).
3. Transport scalar endomorphisms through the fully faithful closed direct image
   (lem-kun-04ca). Its image consists of sheaves supported on Z, and its inverse is i^*.
   Geometric stalks detect exactness, so i_* is exact and acts termwise on derived objects.
4. Put F(N) = ker(N → j_*j^*N). The sectionwise kernel is supported on Z, so
   F(N) ≅ i_*H(N), where H(N) = i^*F(N). Every map i_*M → N factors through this kernel.
   Full faithfulness gives i_* ⊣ H, with counit the kernel inclusion.
5. For each etale V, the free module sheaf on V×_T U embeds in the free module sheaf
   on V: the indexing map is injective and module sheafification is exact. Injectivity
   of I^q extends every section across that embedding, so I^q → j_*j^*I^q is epic.
6. Naturality restricts the differential to F(I^q), giving the short exact sequence
   of complexes 0 → i_*H(I) → I → j_*j^*I → 0, with the counit and unit as its maps.
7. Since i_* is exact, its right adjoint H preserves K-injectives. The termwise
   homotopy adjunction and the Hom bijection into K-injectives identify RH with Ri^!
   of lem-exc-closed-ambient, compatibly with the derived counit.
8. The same homotopy adjunction for exact j^* and j_* identifies the second map
   with the unit of mapDerivedUpperStarLowerStarAdjunction.
9. Apply lem-weil-pbc-complex-ses-triangle. Its cone quasi-isomorphism q and projection p
   give the boundary -p q⁻¹. Maps of the short exact sequences preserve that boundary.
   Additivity makes homotopic representative maps equal after localization; the Hom
   bijection into K-injectives supplies every derived morphism. Functorial replacement
   and its quasi-isomorphism comparisons therefore descend this boundary to a natural
   transformation on the whole derived category, independent of representatives.
   No boundedness or constructibility is imposed at any step. -/
theorem exists_etale_closedSupportTriangle
    (A : Type (u + 1)) [Ring A] [Finite A]
    {Z T U : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (j : U ⟶ T) [IsOpenImmersion j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    ∃ δ : D(upperStar (ModuleCat.{u + 1} A) j) ⋙
        R(lowerStar (ModuleCat.{u + 1} A) j) ⟶
        ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint ⋙
          R(lowerStar (ModuleCat.{u + 1} A) i)) ⋙
          shiftFunctor (_root_.DerivedCategory
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) (1 : ℤ),
      ∀ K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)),
        Triangle.mk
          ((Adjunction.ofIsLeftAdjoint
            (R(lowerStar (ModuleCat.{u + 1} A) i))).counit.app K)
          ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit.app K)
          (δ.app K) ∈ distTriang _ := by
  sorry

end AlgebraicGeometry.Etale

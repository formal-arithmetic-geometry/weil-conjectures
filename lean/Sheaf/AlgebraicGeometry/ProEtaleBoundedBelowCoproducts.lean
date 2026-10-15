/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleOperations
public import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Sheaf.CategoryTheory.RingedSiteGrothendieckAbelian
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.Plus
import Sheaf.AlgebraicGeometry.ProEtaleAffineAcyclicHypercover
import Sheaf.AlgebraicGeometry.ProEtaleHypercoverComputesBoundedComplex
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Sheaf.Paper.SiteSheafificationSectionsLocal
import Sheaf.CategoryTheory.DerivedModuleDirectSums
import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction

/-!
# Pro-etale direct image and uniformly bounded-below coproducts

Source: Stacks Project, Tag 09A3, relative rational-algebra module version
(blueprint: lem-weil-pbc-proetale-bounded-below-coproducts).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Ordinary derived direct image for a qcqs morphism commutes with every small,
uniformly bounded-below family over the inverse-image coefficient sheaf.
Source: Stacks Project, Tag 09A3, relative module version
(blueprint: lem-weil-pbc-proetale-bounded-below-coproducts).

Coproducts are expressed by their universal cocones: `s` and `t` are coproducts of
`K` and its direct images. The final morphism is their canonical comparison, obtained
by descending the images of the coprojections of `s` along the universal cocone `t`.
Thus existence of both coproducts is asserted, rather than assumed. In these derived
module categories they are represented by sheafified termwise direct sums. The rational
algebra structure on each section is unique, so every restriction is automatically linear.

Proof:
1. The module category is Grothendieck abelian (lem-pur-ringed-site-grothendieck-abelian)
and has enough injectives. By lem-weil-pbc-dplus-injective-representative choose injective
representatives E_i zero below N. Their sheafified termwise sum S represents the derived
coproduct: sums are filtered colimits of finite sums and are exact. Resolve S by an
injective J zero below N. K-injective comparison represents the derived isomorphism by
a quasi-isomorphism S → J (lem-weil-pbc-kinjective-hom-derived).
2. Test over affine pro-etale V factoring through an affine open A of the base. These
objects cover every site object. The inverse image of A is qcqs by
lem-weil-pbc-qcqs-over-affine. A finite affine cover, and finite affine covers of its
pairwise intersections, pull back over affine V to show that T ×_U V is qcqs.
3. Choose an affine weakly contractible hypercover of T ×_U V by
lem-weil-pbc-proetale-affine-acyclic-hypercover. The natural total-complex models of
lem-weil-pbc-proetale-hypercover-computes-bounded-complex compute derived sections of
E_i, S and J. For injective complexes these are their ordinary section complexes.
4. On each affine hypercover term W, sections commute with sums of module sheaves.
Indeed module sheafification has the underlying abelian sheafification, and then set
sheafification (lem-pc-sites-sheafification-underlying-sets). Sections are locally finite
support tuples by lem-weil-pbc-site-sheafification-sections-local. A finite affine
refinement of the cover of W bounds their supports by one finite set. Separation makes
all other components zero. Finite sums are finite products, so their sections are the
finite sums of sections. Component projections prove injectivity; the maps are natural.
5. In total degree r only 0 ≤ p ≤ r-N occurs. Exchange this finite diagonal sum with
the sum over i. The alternating restrictions and signed complex differential agree on
each summand, giving an isomorphism compatible with all inclusions. The derived section
comparison is therefore an isomorphism. After S → J this says that the sum of the
section complexes of E_i maps quasi-isomorphically to the section complex of J;
lem-pc-derived-module-direct-sums identifies the section-complex derived coproduct.
6. Form the presheaf complex P = ⨁ h_*E_i and its map to h_*J. It is a quasi-isomorphism
on the affine basis of step 2. Exact module sheafification
(lem-weil-pbc-ringed-site-module-sheafification-exact) commutes with cohomology.
Kernel and cokernel presheaves vanish on that basis, hence sheafify to zero by the
covering property and separation. Thus the sheafified map is a quasi-isomorphism.
7. Its source represents the coproduct of Rh_*K_i and its target represents Rh_* of
the coproduct. Its composites with coprojections are precisely Rh_* of the original
inclusions, so it is the canonical comparison below. It is invertible by
lem-weil-pbc-derived-plus-iso-on-cohomology; fullness of the bounded-below category in
the unbounded category (lem-weil-pbc-kinjective-hom-derived) gives the stated result. -/
theorem proEtaleRingDerivedDirectImage_boundedBelow_coproducts
    {T U : Scheme.{u}} (h : T ⟶ U) [QuasiCompact h] [QuasiSeparated h]
    (R : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
    [∀ V : U.ProEtᵒᵖ, Algebra ℚ (R.obj.obj V)]
    (I : Type (u + 1)) (N : ℤ)
    (K : I → DerivedCategory
      (proEtaleRingModules T ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R)))
    (hK : ∀ (i : I) (n : ℤ), n < N →
      IsZero ((DerivedCategory.homologyFunctor _ n).obj (K i))) :
    ∃ s : Cofan K, ∃ _ : IsColimit s,
      ∃ t : Cofan (fun i ↦ (proEtaleRingDerivedDirectImage h R
        ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R) (Iso.refl _)).obj (K i)),
      ∃ ht : IsColimit t,
        IsIso (ht.desc (Cofan.mk
          ((proEtaleRingDerivedDirectImage h R
            ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R) (Iso.refl _)).obj s.pt)
          (fun i ↦ (proEtaleRingDerivedDirectImage h R
            ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R)
              (Iso.refl _)).map (s.inj i)))) := by
  sorry

end AlgebraicGeometry.Scheme

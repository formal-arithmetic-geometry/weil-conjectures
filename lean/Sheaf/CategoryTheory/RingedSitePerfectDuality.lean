/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Sheaf.CategoryTheory.RingedSiteDualityMaps
public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.Algebra.Homology.HomComplex
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Homology.BoundedExactTermHomQuasiIso
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent
import Sheaf.CategoryTheory.LocalizedModuleExactIndependent
import Mathlib.CategoryTheory.Sites.LocalProperties
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems

/-! # Perfect duality on a small ringed site

Source: Stacks Project, sites-cohomology.tex, Tag 08JJ,
lemma-dual-perfect-complex (blueprint: lem-sfb-ringed-site-perfect-duality).
The canonical maps are explicit transposes of evaluation in a normalized K-flat
closed tensor-Hom presentation, rather than unspecified isomorphic morphisms.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

/-- Perfect-complex duality for the specified canonical maps.
The existential is a normalized presentation of the already recorded derived
tensor and Hom: its transposition, unit, associator and symmetry are fixed on
ordinary representatives. It is not a choice of an arbitrary bidual morphism or
an arbitrary isomorphism. The last clause says the actual canonical evaluation
natural transformation is invertible, in the tensor order of the node.
Source: Stacks Project, Tag 08JJ, lemma-dual-perfect-complex
(blueprint: lem-sfb-ringed-site-perfect-duality).

Proof:
1. Use lem-sfb-ringed-site-duality-maps for the normalized canonical maps and
   lem-weil-pbc-ringed-internal-hom-exact-restriction to restrict them. On covering
   slice sites choose the bounded finite-free-summand representatives E of hP.
2. Split each E^i into a finite free sheaf. Its dual is a finite free summand;
   the dual-basis formulas invert termwise biduality and tensor-Hom evaluation.
   Hom out of each term, and tensor with it or its dual, are exact retracts of
   finite direct sum, using lem-sc-finite-free-internal-hom-exact. Thus the terms
   and their duals are flat (def-pc-flat-sheaf-modules).
3. Apply lem-pc-bounded-exact-term-hom-quasi-iso to the K-injective augmentation
   of an arbitrary complex F. Ordinary Hom(E,F) computes derived Hom, naturally
   in F; boundedness of E makes each Hom product finite.
4. For F=O[0] obtain the dual complex D, with D^q=(E^(-q))^dual and differential
   (-1)^(q+1) times the dual differential. It is supported in [-b,-a] and its
   terms are finite free summands, so it is strictly perfect on this slice.
5. The two Hom comparisons identify the canonical bidual map with
   x ↦ (phi ↦ (-1)^i phi(x)). The double-dual differential is minus the double
   dual of d_E. These signs give a chain map, termwise invertible by step 2.
6. Choose a flat-term K-flat representative F of N by lem-pc-kflat-resolution.
   D is K-flat by lem-pc-bounded-above-flat-kflat-site; the comparison in
   lem-weil-pbc-site-derived-tensor-descent computes tensor by Tot(F tensor D).
7. Under step 3 and this comparison, canonical evaluation has summand map
   y tensor phi ↦ (x ↦ y phi(x)), with no sign. It is termwise invertible by
   step 2, and the tensor differential agrees with the Hom differential. The
   bounded dual makes each degree sum finite even when N is unbounded. The
   normalized Koszul symmetry gives precisely the order dual tensor N here.
8. Exact slice restriction commutes with cohomology. Represent any derived map
   by an actual map to a K-injective complex (lem-weil-pbc-kinjective-hom-derived).
   The sheaf-cover criterion lem-sfb-sheaf-cover-local-isomorphism makes its
   cohomology maps invertible globally if they are so on this covering family.
   Apply this to the canonical maps of steps 5 and 7.
9. Choose one global K-injective representative of the dual. Its restrictions
   remain K-injective by lem-pur-kinjective-restrict-localized. Lift the local
   isomorphisms from D to actual quasi-isomorphisms using
   lem-weil-pbc-kinjective-hom-derived; these are exactly the local perfectness
   condition. No global bound on P or its dual is imposed.
10. The comparison is natural by lem-sfb-ringed-site-duality-maps and symmetry.
    Since each component is invertible by step 8, its component inverses are
    natural too, proving IsIso of this specified natural transformation. -/
theorem ringedSitePerfectDuality
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r} ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))]
    (P : DerivedCategory (SheafOfModules.{max c v r} ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)))
    (hP : SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{c, v, r, w} R P) :
    ∃ M : RingedSiteDualityModel.{c, v, r, w} J R,
      SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{c, v, r, w} R
        ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj
          (op P, ringedSiteDualityUnit.{c, v, r, w} J R)) ∧
      IsIso (ringedSiteBidual M.closed M.symmetric
        (ringedSiteDualityUnit.{c, v, r, w} J R) P) ∧
      IsIso (ringedSiteDualEvaluationLeftNatTrans M.closed M.symmetric
        (ringedSiteDualityUnit.{c, v, r, w} J R) M.unitIso P) := by
  sorry

end CategoryTheory

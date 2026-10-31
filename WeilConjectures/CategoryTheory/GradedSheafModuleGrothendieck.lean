/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.GradedSheafModule
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
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
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Graded sheaf modules form a Grothendieck abelian category

Source: Stacks Project, sdga.tex, Tags 0FR0 and 0FRD, with the left-module convention
(blueprint: lem-sfb-graded-sheaf-module-grothendieck).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace CategoryTheory.SheafDg

/-- Graded left module sheaves over the underlying graded algebra of a sheaf dg algebra
form a Grothendieck abelian category. The existential supplies abelianness, rather than
assuming it; the second clause uses that same structure.

Source: Stacks Project, sdga.tex, lemma-gm-abelian (Tag 0FR0) and
lemma-gm-grothendieck-abelian (Tag 0FRD), translated to left modules
(blueprint: lem-sfb-graded-sheaf-module-grothendieck).

Proof:
1. On the small open site, ordinary module sheaves are abelian by
lem-pur-ringed-site-grothendieck-abelian and def-weil-sheaf-of-modules-category.
Take kernels and cokernels degreewise. The action restricts to the kernel.
Tensor preservation of colimits (lem-weil-pbc-independent-sheaf-tensor-colimits)
induces the quotient action on the cokernel. Unit and associativity are checked
through the epimorphic quotient maps. These give the graded universal properties.
Addition and biproducts are degreewise, and the coimage-image comparison is an
isomorphism degreewise whose inverse respects the action. Thus the category is
abelian, and exactness is detected in every degree.
2. For any small diagram take its colimit in every degree in ordinary module sheaves.
Tensor preservation of colimits induces the action on these colimits. The cocone maps
jointly determine the unit and associativity identities and the universal graded
factorization. This includes the empty diagram, and proves degreewise colimits.
3. A filtered diagram of short exact sequences is exact degreewise. Ordinary module
sheaves have exact filtered colimits by lem-pur-ringed-site-grothendieck-abelian.
The degreewise construction in step 2 and exactness detection in step 1 prove AB5.
4. For an open U and integer n, forget the differential of the signed shift A_U[-n].
Its degree-q term is A_U^(q-n), with action a.b=(-1)^(n|a|)ab.
Evaluation at 1 identifies its graded Hom into M|_U with sections of M^n on U:
the inverse sends b to (-1)^(n|b|)bm. The two signs in its action equation cancel,
and restriction compatibility and the unit give the inverse identities.
The graded open extension adjunction (lem-sfb-graded-open-extension-adjunction)
identifies Hom from its extension by zero with the same sections.
5. Take the coproduct of these extensions over all opens U and integers n, a set
in the size convention def-weil-size-convention. Distinct graded maps differ on
some section m of M^n(U). Step 4 gives a map from that summand detecting the
difference. Extend by zero on all other summands to obtain a map from the coproduct
detecting it. Hence its Hom functor is faithful, so this coproduct is a generator.
Steps 1--3 and this generator give def-sp-grothendieck-abelian. -/
theorem gradedLeftModule_grothendieckAbelian {X : TopCat.{u}}
    (S : TopCat.Sheaf CommRingCat.{w} X)
    [EssentiallySmall.{w} (TopologicalSpace.Opens X)] (A : Algebra S) :
    ∃ h : Abelian (GradedLeftModule (underlyingGradedAlgebra A)),
      @IsGrothendieckAbelian.{w} (GradedLeftModule (underlyingGradedAlgebra A)) _ h := by
  sorry

end CategoryTheory.SheafDg

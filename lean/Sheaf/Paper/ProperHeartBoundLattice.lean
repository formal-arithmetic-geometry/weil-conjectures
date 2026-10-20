/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q42
-/
module

public import Sheaf.Paper.ProperHeartBoundTorsion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.AlgebraicGeometry.ProEtaleProductsDerived
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Sheaf.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Sheaf.CategoryTheory.KInjectiveComputes
import Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
import WeilConjectures.CategoryTheory.Triangulated.MilnorSequence
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.Paper.IntegralModels

/-!
# The integral lattice bound for proper morphisms

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-proper-heart-bound,
`sk-lem-proper-heart-bound-lattice.md` and its proof
(blueprint: det-proper-heart-bound-lattice).

The coefficient ring is the pulled-back continuous condensed valuation ring, and the
extension by zero is the already recorded composite of open extension and closed direct image.
Cohomology is taken on the underlying abelian sheaf, after canonical pro-etale inverse image
along the projection from the fibre product. This is restriction to the slice site.
The integer fibre bound retains the empty-fibre case when the bound is negative.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- For an integral lisse finite free lattice on a locally closed finite-type stratum,
cohomology over an affine weakly contractible pro-etale base change vanishes above `2d+1`.
There is no finiteness or Noetherian assumption on that base change.
Source: blueprint main-20261015, sk-lem-proper-heart-bound-lattice, Completeness, Sections
and Milnor paragraphs; Stacks Tags 09BM, 09BP, 0D6K, 07KY and 07KW
(blueprint: det-proper-heart-bound-lattice).

Proof plan (the seven DAG steps):
1. Put K = a_! L. Clause (4) of sk-lem-integral-models puts K in the bounded constructible
   integral category and identifies its canonical derived reductions B_n with
   N_n = a_!(L/pi^n L) in degree zero. Clause (2) makes K derived complete, so it is the
   derived limit of B_n. Apply this only on the finite-type schemes X, S and its closure.
2. The projection r : X_V -> X is weakly etale by
   lem-weil-pbc-weakly-etale-composition-base-change and is an object of X_proet by
   def-weil-proetale-inverse-image. The slice identification of
   lem-weil-proetale-weakly-etale-localization gives restriction F. It is exact by
   lem-pur-site-restriction-module-adjunction-exact and preserves products by
   lem-weil-pbc-module-sheaves-limits-sectionwise. Keep the restricted integral ring.
3. By lem-sf-exact-functor-derived-triangulated, F acts on derived categories.
   By det-pe-products-derived, its sectionwise product comparison is the derived product
   comparison. Applying F to the Roos triangle of def-weil-derived-limit yields the Roos
   triangle for F(B_n): its nth component is pr_n minus f_n followed by pr_(n+1).
   Hence F(K) is the derived limit of F(B_n).
4. By lem-kun-site-rgamma-derived-limit, derived sections preserve this Roos triangle.
   Thus R Gamma(X_V,F(K)) is the derived limit of C_n = R Gamma(X_V,F(B_n)). Reindex
   the positive powers by n+1 when applying the sequential derived-limit statement.
5. If d < 0, every nonempty geometric fibre has dimension at least zero by
   def-kun-topological-krull-dimension. An algebraic closure of the residue field of any
   point of X supplies a point in a geometric fibre, a contradiction. Therefore X and X_V
   are empty and all cohomology vanishes. Otherwise d is nonnegative.
6. By lem-sfb-proetale-object-inverse-image-restriction, r inverse image on underlying
   abelian sheaves is slice restriction. Module sheaves are Grothendieck by
   prop-pur-kinjective-resolutions-exist and have enough injectives by
   lem-sp-grothendieck-enough-injectives. The comparison lem-sp-kinjective-computes and
   lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison identify cohomology with
   that of the underlying abelian sheaf, as in def-sfb-finite-derived-global-sections.
   Each B_n is individually isomorphic to N_n, so H^r(C_n) is the torsion cohomology group
   of det-proper-heart-bound-torsion. No compatibility of these individual isos is needed.
7. Apply lem-pc-derived-limit-milnor-sequence. For q > 2d+1, both q and q-1 exceed 2d.
   The torsion bound kills both outer towers in the Milnor short exact sequence.
   The limit and first derived limit of the zero tower are zero, so its middle group
   H^q(X_V,a_!L) is zero. The borderline q = 2d+1 is not asserted. -/
theorem properHeartBoundLattice
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (k : Type u) [Field k] (hchar : ringChar k ≠ 0) (hell : ringChar k ≠ ℓ)
    {X Y S Sbar : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [S.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))] [LocallyOfFiniteType (S ↘ Spec (.of k))]
    [QuasiCompact (S ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] (d : ℤ)
    (hd : ∀ y : Y, topologicalKrullDim
      (pullback p (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤
      if d < 0 then ⊥ else (d.toNat : WithBot ℕ∞))
    (V : Y.ProEt) [IsAffine V.left]
    (hV : (Scheme.ProEt.topology Y).IsWeaklyContractible.{u + 1} V)
    (j : S ⟶ Sbar) [IsOpenImmersion j] (i : Sbar ⟶ X) [IsClosedImmersion i]
    [(j ≫ i).IsOver (Spec (.of k))]
    (L : pulledBackModuleObjects (DerivedNakayama.integerRing ℓ E) S)
    (hL : IsLisseCoefficientModule (DerivedNakayama.integerRing ℓ E) L)
    (q : ℤ) (hq : 2 * d + 1 < q) :
    IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} q).obj
      ((rightDerivedGlobalSections Ab.{u + 1} (pullback p V.hom)).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((Scheme.proEtaleSheafInverseImage (pullback.fst p V.hom) Ab.{u + 1}).obj
            (((torsionLocallyClosedExtension ℓ E j i).obj L).X))))) := by
  sorry

end AlgebraicGeometry.ProEtale

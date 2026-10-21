module
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Topology.NoetherianSpace
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.Paper.ProEtaleConstructibleSheaf
public import Sheaf.SixFunctors.IntrinsicDerivedTensor
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleInverseImageStalk
import Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
import Sheaf.AlgebraicGeometry.ProEtaleStalkConservative
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.CategoryTheory.SiteMorphismComposition
import Sheaf.Paper.LocalizeRingedSiteMorphismGeneral
import Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.SfCommonStageWeilCohomology
import WeilConjectures.AlgebraicGeometry.EtaleStratificationLocalGluingCore
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor

/-!
# Finite-cover locality of bounded constructibility and a fixed Tor interval

Source: literature/stacks-project/etale-cohomology.tex, Tag 095F,
label `lemma-constructible-local` (blueprint: lem-sf-finite-cover-ctf-locality).
-/

@[expose] public section
set_option autoImplicit false
universe t

open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Finite-cover locality of bounded constructibility and a fixed Tor interval.
Source: Stacks Project, `etale-cohomology.tex`, Tag 095F, label
`lemma-constructible-local`; the finite-cover intrinsic pro-etale formulation and its
uniform Tor interval are the blueprint node
`lem-sf-finite-cover-ctf-locality` (blueprint: lem-sf-finite-cover-ctf-locality).
Proof steps (from Tag 095F and the cited pro-etale comparison nodes):
1. Descending-chain Noetherianity makes every open quasi-compact, so the diagonal is
quasi-compact and the affine basis gives a finite affine refinement of the cover.
Intersect each local finite constructible stratification with that refinement.
2. Localization identifies the pro-etale site over an open with the open's site;
restriction is exact and the derived tensor pullback comparison identifies each local
cohomology and tensor restriction with the corresponding global restriction.
3. Apply the finite affine stratification-local-gluing lemma to obtain one finite
locally-closed constructible stratification of X; reduction of each induced stratum
preserves the partition and local constancy with finite stalks.
4. Pullback along each stratum factorization preserves local constancy and finite stalks,
by base change of trivializing pro-etale covers, preservation of constant module sheaves,
and the inverse-image stalk formula.
5. For arbitrary degree-zero F, the local Tor hypotheses make the cohomology of the
global tensor vanish after restriction to every cover member; covering-family detection
of zero sheaves gives global vanishing in every degree outside [a,b].
6. Taking F to be the tensor unit identifies the tensor with K, giving finite support of
cohomology degrees; together with step 3 this is bounded constructibility and the same
Tor interval. The empty scheme and empty cover use the empty stratification and zero
sheaf. These steps use the statement dependencies `def-pc-scheme`,
`def-weil-open-immersion`, `def-weil-pbc-proetale-site`, `def-weil-derived-tensor`,
`def-weil-derived-cohomology-sheaves`, `def-weil-constructible-subset`, and
`def-weil-proetale-locally-constant-sheaf`.
-/
theorem finiteCoverCTFLocality
    (X : Scheme.{t})
    (hX : TopologicalSpace.NoetherianSpace X)
    (A : Type t) [CommRing A] [Finite A]
    (r : ℕ) (U : Fin r → Scheme.{t})
    (j : ∀ i : Fin r, U i ⟶ X)
    (hj : ∀ i : Fin r, IsOpenImmersion (j i))
    (hcover : ∀ x : X, ∃ i : Fin r, ∃ y : U i, (j i).base y = x)
    (K : proEtaleDerivedCategory X A)
    (a b : ℤ) (hab : a ≤ b)
    (hlocal : ∀ i : Fin r, Set.Finite {t : ℤ |
      ¬ IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules (U i) (proEtaleConstantRing (U i) A)) t).obj
          ((proEtaleConstantRingDerivedPullback A (j i)).obj K))})
    (hconstructible : ∀ (i : Fin r) (t : ℤ),
      IsConstructibleProEtaleModuleSheaf (U i) A
        ((DerivedCategory.homologyFunctor
          (proEtaleRingModules (U i) (proEtaleConstantRing (U i) A)) t).obj
            ((proEtaleConstantRingDerivedPullback A (j i)).obj K)))
    (htor : ∀ (i : Fin r)
      (F : proEtaleRingModules (U i) (proEtaleConstantRing (U i) A))
      (t : ℤ), t < a ∨ b < t →
      IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules (U i) (proEtaleConstantRing (U i) A)) t).obj
          (proEtaleDerivedTensor (U i) A
            ((proEtaleConstantRingDerivedPullback A (j i)).obj K)
            ((DerivedCategory.singleFunctor
              (proEtaleRingModules (U i) (proEtaleConstantRing (U i) A)) 0).obj F)))) :
    Set.Finite {t : ℤ |
      ¬ IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X A)) t).obj K)} ∧
    (∀ t : ℤ,
      IsConstructibleProEtaleModuleSheaf X A
        ((DerivedCategory.homologyFunctor
          (proEtaleRingModules X (proEtaleConstantRing X A)) t).obj K)) ∧
    (∀ (F : proEtaleRingModules X (proEtaleConstantRing X A)) (t : ℤ),
      t < a ∨ b < t →
      IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X A)) t).obj
          (proEtaleDerivedTensor X A K
            ((DerivedCategory.singleFunctor
              (proEtaleRingModules X (proEtaleConstantRing X A)) 0).obj F)))) := by
  sorry

end AlgebraicGeometry.Scheme

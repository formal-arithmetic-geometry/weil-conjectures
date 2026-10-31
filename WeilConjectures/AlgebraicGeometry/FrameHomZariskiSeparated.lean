/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FrameProductOnSupport
public import WeilConjectures.AlgebraicGeometry.SupportedCupFunctoriality
import WeilConjectures.AlgebraicGeometry.RelativeSupportBottomDescent
import WeilConjectures.AlgebraicGeometry.SupportedHomPullback
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedTensorPullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.IntTensorFamilyIso
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.Algebra.Homology.ShortComplex.Exact

/-! # Zariski separation in the bottom supported Hom degree -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.PurityFiniteSetting

/-- Bottom-degree supported Hom classes of a relative smooth pair are separated
for Zariski restriction. The classes are arbitrary, rather than classes supplied
by any tuple or orientation.
Source: the bottom-descent equality test in frame independence
(blueprint: lem-pur-frame-hom-zariski-separated).
Proof:
1. The characteristic m of the finite coefficient ring is positive and divides
   P.diagonalExponent, since that exponent annihilates the ring. Its image on U is
   a unit because the diagonal exponent is a unit. The exponent-change clause of
   etaleFiniteTwistPullback gives the normalized isomorphism from the diagonal
   twist to relativeSupportModuleCoefficient P U c. Its root-power formula fixes
   the map uniquely; the same formula gives compatibility with restriction.
2. Apply the inverse of chiP from supportedHom_pullback to each Hom class, after
   the coefficient isomorphism and the canonical single/shift identifications.
   Invert relativeSupportProComparison, whose definition includes the
   module-to-abelian comparison relativeSupportForgetDerived. This
   gives two elements of supportCohomology (pullback.snd i e) (2*c)
   (relativeSupportCoefficient P U c). All maps used are isomorphisms.
3. Choose W_x from hlocal for each x. The inclusions W_x into U cover U because
   x belongs to W_x. Their terminal arrows therefore generate a covering sieve
   of the small etale site, including when U is empty.
4. The compatibility clauses of supportedHom_pullback identify restriction of
   the supported classes with inverse image of the Hom representatives. Closed
   exchange agrees with functorialCupExchange by its epic-restriction
   normalization. The twist comparison agrees on roots and positive pure tensors.
   The kernel-normalized derived evaluation and global-support comparisons then
   identify these maps with relativeSupportGlobalRestriction. Thus hlocal makes
   the two supported-cohomology classes equal on every member of this cover.
5. Apply the last clause of relative_support_bottom_descent, with r=c and the
   supplied finite-stalk hypothesis. It identifies the two global classes.
   Cancel the isomorphisms in step 2 to obtain the displayed Hom equality.
   The same proof covers empty support and c=0. -/
theorem frameHom_zariski_separated (P : PurityFiniteSetting.{u}) {B V Z : Scheme.{u}}
    (b : B ⟶ Spec (.of P.field.k)) (v : V ⟶ B)
    [SmoothOfRelativeDimension P.level v] (i : Z ⟶ V) [IsClosedImmersion i]
    [Smooth (i ≫ v)] (c : ℕ)
    (hcodim : ∀ z : Z, ringKrullDim (V.presheaf.stalk (i z)) =
      ringKrullDim (Z.presheaf.stalk z) + (c : WithBot ℕ∞))
    (hfinite : ∀ z : Z, ringKrullDim (V.presheaf.stalk (i z)) ≠ ⊤)
    (U : Scheme.{u}) (e : U ⟶ V) [Etale e] (f : Fin c → Γ(U, ⊤))
    (tf : U.zeroLocusSubscheme (Set.range f) ⟶ Z)
    (hf : IsPullback tf (U.zeroLocusSubschemeι (Set.range f)) i e)
    (α β : cupSupportedHom P (pullback.snd i e)
      ((cupSingle P U).obj (P.frameTwist U c)) (2 * (c : ℤ)))
    (hlocal : ∀ x : U, ∃ W : U.Opens, x ∈ W ∧
      ∀ sq : ChosenCartesianSquare
        (pullback.fst (pullback.snd i e) W.ι)
        (pullback.snd (pullback.snd i e) W.ι) (pullback.snd i e) W.ι,
      P.functorialCupPullback true _ _ W.ι _ sq (e ≫ v ≫ b) (2 * (c : ℤ)) c α =
      P.functorialCupPullback true _ _ W.ι _ sq (e ≫ v ≫ b) (2 * (c : ℤ)) c β) :
    α = β := by
  sorry

end WeilConjectures.PurityFiniteSetting

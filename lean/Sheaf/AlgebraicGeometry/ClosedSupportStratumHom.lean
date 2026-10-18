/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleFiniteLocallyProjective
public import Sheaf.AlgebraicGeometry.AdmissibleCondensedCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.CategoryTheory.Monoidal.Closed.Preadditive
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Homology.HomComplex
public import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses

import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
import Sheaf.Algebra.Homology.KInjectiveHomComplex
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# Global derived Hom out of a stratum extension

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-sf-localization,
sk-lem-formal-closed-support-stratum-hom.md
(blueprint: det-lem-formal-closed-support-stratum-hom).

The global Hom functor is derived into abelian groups, rather than internal Hom.
All coefficient modules and derived categories are the existing module-object categories.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Global RHom from a module in degree zero, computed by Hom into a K-injective
representative. This is the global-sections Hom complex of the source statement:
its degree n is Hom(M,I^n), and its differential is postcomposition with d_I.
Source: blueprint stratum Hom lemma, definition of global RHom
(blueprint: det-lem-formal-closed-support-stratum-hom). -/
noncomputable def stratumGlobalRHom (X : Scheme.{u}) (M : supportModules Λ X) :
    DerivedCategory (supportModules Λ X) ⥤ DerivedCategory Ab.{u + 1} :=
  (preadditiveCoyoneda.obj (op M)).rightDerivedFunctor

/-- RΓ is the unbounded right derived functor of Hom from the regular coefficient module.
Source: blueprint stratum Hom lemma, definition of hypercohomology
(blueprint: det-lem-formal-closed-support-stratum-hom). -/
noncomputable def stratumRGamma (X : Scheme.{u}) :
    DerivedCategory (supportModules Λ X) ⥤ DerivedCategory Ab.{u + 1} :=
  stratumGlobalRHom Λ X (Mod.regular (condensedRingObj Λ X))

/-- The coefficient-linear internal Hom dual of L. The existing closed module tensor
represents sheaf Hom; its unit is the regular coefficient module.
Source: blueprint stratum Hom lemma, L-dual definition
(blueprint: det-lem-formal-closed-support-stratum-hom). -/
noncomputable def stratumDual (S : Scheme.{u}) (L : supportModules Λ S) : supportModules Λ S :=
  (ihom L).obj (𝟙_ (supportModules Λ S))

/-- Termwise tensor with the dual of a finite locally projective module is exact.
Source: blueprint stratum Hom lemma, tensor convention and proof step 3
(blueprint: det-lem-formal-closed-support-stratum-hom).
Proof: on each splitting cover L is a retract of a finite free module. Dualizing the
splitting makes its dual a retract of the dual finite free module, again finite free.
Tensor is then a retract of a finite direct sum of identity functors, hence exact.
Kernels and cokernels detect exactness locally on a covering, so this descends. -/
theorem stratumDualTensor_preservesFiniteLimits
    (S : Scheme.{u}) (L : supportModules Λ S) (hL : IsFiniteLocallyProjective Λ S L) :
    PreservesFiniteLimits (tensorLeft (stratumDual Λ S L)) := by
  sorry

/-- The ordinary tensor with L-dual applied termwise and descended to the unbounded
 derived category using its exactness; no K-flat replacement enters this construction.
Source: blueprint stratum Hom lemma, termwise tensor convention
(blueprint: det-lem-formal-closed-support-stratum-hom). -/
noncomputable def stratumDualTensor
    (S : Scheme.{u}) (L : supportModules Λ S) (hL : IsFiniteLocallyProjective Λ S L) :
    DerivedCategory (supportModules Λ S) ⥤ DerivedCategory (supportModules Λ S) :=
  letI := stratumDualTensor_preservesFiniteLimits Λ S L hL
  (tensorLeft (stratumDual Λ S L)).mapDerivedCategory

/-- Termwise tensor with L-dual agrees with the existing derived relative tensor.
Source: blueprint stratum Hom lemma, proof steps 3--4
(blueprint: det-lem-formal-closed-support-stratum-hom).
Proof: the finite-free splitting makes tensor with L-dual exact, so tensoring any
acyclic complex with its degree-zero complex is acyclic. It is therefore K-flat.
The K-flat model defining derived tensor consequently computes it on every complex,
and the localization universal property gives the natural isomorphism. -/
theorem stratumDualTensor_derived
    (S : Scheme.{u}) (L : supportModules Λ S) (hL : IsFiniteLocallyProjective Λ S L) :
    Nonempty (stratumDualTensor Λ S L hL ≅
      (derivedTensor Λ S).obj
        ((DerivedCategory.singleFunctor (supportModules Λ S) 0).obj (stratumDual Λ S L))) := by
  sorry

/-- All three global derived Hom isomorphisms, natural on the whole unbounded category,
and their shifted-Hom consequence for every integer.
Source: blueprint stratum Hom lemma and its proof
(blueprint: det-lem-formal-closed-support-stratum-hom).
Proof: (1) apply the closed-support adjunction with A=u!L; its global Hom comparison
is componentwise the adjunction on K-injective representatives. (2) Exact u! is left
adjoint to exact u*, so u* preserves K-injectives. Termwise adjunction gives an
isomorphism of global Hom complexes, commuting with differentials by naturality.
(3) The evaluation L-dual tensor M -> sheafHom(L,M) is an isomorphism for a finite
free L; on a finite-free splitting it is block diagonal, so the L block is invertible.
These local inverses glue. Both L and its dual are flat by the same splitting.
For a K-injective I representing u* R-Gamma_Z K, sheafHom(L,I) is K-injective by
K-flatness of L[0]. Its ordinary global sections compute R-Gamma and are the global
Hom complex defining RHom(L,I). Evaluation in each degree therefore gives the last
isomorphism, and flatness identifies its termwise tensor with derived tensor.
(4) Adjunction and evaluation commute with maps of K-injective representatives.
Homotopy equivalences between such representatives give independence and naturality
on D(X). Degree-q cocycles in the global Hom complex are maps from a!L to K[q],
and boundaries are null-homotopic maps. K-injective comparison identifies their
quotient with derived morphisms. Taking H^q gives the final natural isomorphism,
also for negative q; no boundedness or constructibility condition is used. -/
theorem closedSupport_stratum_globalHom
    {S Z V X : Scheme.{u}} (i : Z ⟶ X) (j : V ⟶ X) (uS : S ⟶ Z)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j] [IsOpenImmersion uS]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (_hΛ : IsAdmissibleCoefficient Λ)
    (L : supportModules Λ S) (hL : IsFiniteLocallyProjective Λ S L) :
    Nonempty (stratumGlobalRHom Λ X
        ((lowerStar Λ i).obj ((openImmersionLowerShriek Λ uS).obj L)) ≅
      (closedSupport Λ i j).rightDerivedFunctor ⋙
        stratumGlobalRHom Λ Z ((openImmersionLowerShriek Λ uS).obj L)) ∧
    Nonempty ((closedSupport Λ i j).rightDerivedFunctor ⋙
        stratumGlobalRHom Λ Z ((openImmersionLowerShriek Λ uS).obj L) ≅
      (closedSupport Λ i j).rightDerivedFunctor ⋙ (upperStar Λ uS).mapDerivedCategory ⋙
        stratumGlobalRHom Λ S L) ∧
    Nonempty ((closedSupport Λ i j).rightDerivedFunctor ⋙
        (upperStar Λ uS).mapDerivedCategory ⋙ stratumGlobalRHom Λ S L ≅
      (closedSupport Λ i j).rightDerivedFunctor ⋙ (upperStar Λ uS).mapDerivedCategory ⋙
        stratumDualTensor Λ S L hL ⋙ stratumRGamma Λ S) ∧
    ∀ q : ℤ, Nonempty
      (shiftFunctor (DerivedCategory (supportModules Λ X)) q ⋙
        preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor (supportModules Λ X) 0).obj
          ((lowerStar Λ i).obj ((openImmersionLowerShriek Λ uS).obj L)))) ≅
      (closedSupport Λ i j).rightDerivedFunctor ⋙ (upperStar Λ uS).mapDerivedCategory ⋙
        stratumDualTensor Λ S L hL ⋙ stratumRGamma Λ S ⋙
          DerivedCategory.homologyFunctor Ab.{u + 1} q) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing

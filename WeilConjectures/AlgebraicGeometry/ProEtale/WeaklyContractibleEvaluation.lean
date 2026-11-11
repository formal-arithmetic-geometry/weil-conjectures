/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.SectionsConservative
public import WeilConjectures.AlgebraicGeometry.ProEtaleSectionsLimitsColimits
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.GaloisAcyclic.WContractible

/-!
# Evaluation on weakly contractible objects of the pro-étale site

Let `W` be a weakly contractible object of `X_proét`. This file records three consequences of
the exactness of the evaluation functor `F ↦ F(W)` (blueprint
`corollary-evaluation-weakly-contractible-objects`):

* `AlgebraicGeometry.ProEtale.rightDerivedSectionsFunctorObjIso`: for every unbounded complex
  `K` of pro-étale sheaves of `Λ`-modules, `RΓ(W, K) ≅ K(W)`, the right side computed term by
  term;
* `AlgebraicGeometry.Scheme.ProEt.preservesLimitsOfSize_evaluation`: if `W` is moreover affine,
  evaluation at `W` of module sheaves over a sheaf of rings preserves all limits;
* `AlgebraicGeometry.Scheme.ProEt.shortComplex_exact_iff_forall_isWeaklyContractible` and
  `AlgebraicGeometry.Scheme.ProEt.acyclic_iff_forall_isWeaklyContractible`: exactness of short
  complexes and acyclicity of unbounded complexes of module sheaves can be tested on affine
  weakly contractible objects.
-/

@[expose] public section

universe t u r v wJ uJ

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Λ : Type (u + 1)) [Ring Λ]

/-- For a weakly contractible object `W` of `X_proét` and every (unbounded) complex `K` of
pro-étale sheaves of `Λ`-modules, the derived sections `RΓ(W, K)` are computed by applying the
sections over `W` term by term: `RΓ(W, K) ≅ K(W)`. Indeed evaluation at `W` is exact, so its
total right derived functor is the functor it induces on derived categories.
(blueprint: `corollary-evaluation-weakly-contractible-objects--3`) -/
noncomputable def rightDerivedSectionsFunctorObjIso {X : Scheme.{u}} {W : X.ProEt}
    (hW : (ProEt.topology X).IsWeaklyContractible.{u + 1} W)
    (K : CochainComplex (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) ℤ) :
    (sectionsFunctor (ModuleCat.{u + 1} Λ) W).rightDerivedFunctor.obj
        (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj (((sectionsFunctor (ModuleCat.{u + 1} Λ) W).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) :=
  have := preservesHomology_sectionsFunctor_of_isWeaklyContractible Λ hW
  have := (sectionsFunctor (ModuleCat.{u + 1} Λ) W).preservesFiniteLimits_of_preservesHomology
  have := (sectionsFunctor (ModuleCat.{u + 1} Λ) W).preservesFiniteColimits_of_preservesHomology
  (sectionsFunctor (ModuleCat.{u + 1} Λ) W).rightDerivedFunctorIsoMapDerivedCategory.app _ ≪≫
    (sectionsFunctor (ModuleCat.{u + 1} Λ) W).mapDerivedCategoryFactors.app K

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Scheme.ProEt

/-- For an affine weakly contractible object `W` of `X_proét`, evaluation `M ↦ M(W)` from
sheaves of `R`-modules to `R(W)`-modules preserves all limits, whatever the size of the
indexing category.
(blueprint: `corollary-evaluation-weakly-contractible-objects--4`) -/
theorem preservesLimitsOfSize_evaluation {X : Scheme.{u}}
    (R : Sheaf (ProEt.topology X) RingCat.{r}) (W : X.ProEt) [IsAffine W.left]
    (hW : (ProEt.topology X).IsWeaklyContractible.{max (u + 1) r v} W) :
    PreservesLimitsOfSize.{wJ, uJ} ((SheafOfModules.evaluation R (op W)) :
      SheafOfModules.{max (u + 1) r v} R ⥤ ModuleCat.{max (u + 1) r v} (R.obj.obj (op W))) :=
  (peSectionsLimitsColimits.{u, r, v, wJ, uJ} R W hW).1

/-- A sequence `A ⟶ B ⟶ C` of sheaves of `R`-modules on `X_proét` with zero composite is exact
if and only if it is exact after evaluation on every affine weakly contractible object `W`.
Together with `AlgebraicGeometry.Scheme.ProEt.acyclic_iff_forall_isWeaklyContractible`, this is
blueprint `corollary-evaluation-weakly-contractible-objects--6`. -/
theorem shortComplex_exact_iff_forall_isWeaklyContractible (X : Scheme.{t})
    (R : Sheaf (topology X) RingCat.{u}) (A B C : ringedSiteModules.{max u (t + 1)} R)
    (f : A ⟶ B) (g : B ⟶ C) (h : f ≫ g = 0) :
    (ShortComplex.mk f g h).Exact ↔
      ∀ (W : X.ProEt), IsAffine W.left →
        (topology X).IsWeaklyContractible.{max u (t + 1)} W →
          ((ShortComplex.mk f g h).map
            (SheafOfModules.evaluation.{max u (t + 1)} R (op W))).Exact :=
  (sections_conservative X R).1 A B C f g h

/-- An unbounded complex `K` of sheaves of `R`-modules on `X_proét` is acyclic if and only if
the complex of sections `K(W)` is acyclic for every affine weakly contractible object `W`.
Together with `AlgebraicGeometry.Scheme.ProEt.shortComplex_exact_iff_forall_isWeaklyContractible`,
this is blueprint `corollary-evaluation-weakly-contractible-objects--6`. -/
theorem acyclic_iff_forall_isWeaklyContractible (X : Scheme.{t})
    (R : Sheaf (topology X) RingCat.{u})
    (K : CochainComplex (ringedSiteModules.{max u (t + 1)} R) ℤ) :
    K.Acyclic ↔
      ∀ (W : X.ProEt), IsAffine W.left →
        (topology X).IsWeaklyContractible.{max u (t + 1)} W →
          HomologicalComplex.Acyclic
            ((SheafOfModules.evaluation.{max u (t + 1)} R (op W)).mapHomologicalComplex
              (ComplexShape.up ℤ) |>.obj K) :=
  (sections_conservative X R).2.1 K

end AlgebraicGeometry.Scheme.ProEt

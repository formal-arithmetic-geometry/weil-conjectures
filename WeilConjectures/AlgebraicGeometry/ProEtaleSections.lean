/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.SectionsConservative
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.AlgebraicGeometry.WContractibleAffineCover
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.RingTheory.ProEtale.WContractible
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import WeilConjectures.RingTheory.IndPrincipalZariski
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.AlgebraicGeometry.ProEtaleSectionsLimitsColimits
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
public import WeilConjectures.AlgebraicGeometry.ProEtaleQcqsSiteLimits
public import WeilConjectures.AlgebraicGeometry.ProEtaleQcqsSubsite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Sites.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractibleBasis
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtale.Projective
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Conservative affine weakly contractible sections

Source: literature/blueprint/latest/blueprint/sec-proetale-coefficients/
sk-cor-pe-sections/_section.md (node `sk-cor-pe-sections`).

The theorem packages the conservative evaluation criterion, preservation of all
module limits and colimits, and the affine weakly contractible basis together
with the coherent qcqs pro-etale subsite.
-/

@[expose] public section

set_option autoImplicit false

universe t u r v wJ uJ

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

set_option linter.checkUnivs false

/--
Evaluation on affine weakly contractible pro-etale objects detects exactness,
acyclicity, isomorphisms and quasi-isomorphisms, and preserves all limits and
colimits of module sheaves.  The affine weakly contractible basis and the
coherent qcqs subsite provide the covering and site assertions in the
statement.

Proof (the four proof steps recorded for `sk-cor-pe-sections`).
1. The affine weakly contractible basis gives a covering of every object by
   affine spectra of w-contractible rings; its projectivity clause splits every
   epimorphism onto the represented sheaf.  The weak-contractibility
   definition therefore gives the exact sections used below.
2. For a short complex, the conservative sections criterion says that
   exactness is equivalent to exactness after evaluation on every affine
   weakly contractible object.  Applying it to the three-term pieces of a
   complex detects acyclicity degree by degree; applying it to the kernel and
   cokernel short complexes detects isomorphisms and quasi-isomorphisms.
3. Evaluation preserves limits sectionwise.  For a direct sum, a section on an
   affine site-quasi-compact object is locally a finite sum, and a finite
   refinement makes one finite set of summands suffice.  Thus evaluation
   preserves arbitrary direct sums; every colimit is a coequalizer of a map
   between direct sums, so exact evaluation preserves all colimits (including
   the empty diagram and filtered colimits).
4. Site quasi-compactness means that every covering presieve has a finite
   refinement.  Affine objects have this property: by the finite affine
   refinement clause of the pro-etale site, finitely many members of a covering
   of an affine object already form a covering, a finite subfamily.  Quasi-compact,
   quasi-separated objects with finite covers form the coherent qcqs subsite:
   fibre products stay in the subsite by weakly etale stability and the
   qcqs-morphism permanence theorem.  An affine weakly contractible object is
   coherent and projective, and these objects cover every site object.  These
   are precisely the remaining clauses below.

(blueprint: sk-cor-pe-sections)
-/
theorem conservative_affine_weaklyContractible_sections
    (X : Scheme.{t}) (R : Sheaf (topology X) RingCat.{u}) :
    (∀ (A B C : ringedSiteModules.{max u (t + 1)} R) (f : A ⟶ B)
        (g : B ⟶ C) (h : f ≫ g = 0),
      (ShortComplex.mk f g h).Exact ↔
        ∀ (W : X.ProEt), IsAffine W.left →
          (topology X).IsWeaklyContractible.{max u (t + 1)} W →
            ((ShortComplex.mk f g h).map
              (SheafOfModules.evaluation.{max u (t + 1)} R (op W))).Exact) ∧
    (∀ (K : CochainComplex (ringedSiteModules.{max u (t + 1)} R) ℤ),
      K.Acyclic ↔
        ∀ (W : X.ProEt), IsAffine W.left →
          (topology X).IsWeaklyContractible.{max u (t + 1)} W →
            HomologicalComplex.Acyclic
              ((SheafOfModules.evaluation.{max u (t + 1)} R (op W)).mapHomologicalComplex
                (ComplexShape.up ℤ) |>.obj K)) ∧
    (∀ (A B : ringedSiteModules.{max u (t + 1)} R) (f : A ⟶ B),
      IsIso f ↔
        ∀ (W : X.ProEt), IsAffine W.left →
          (topology X).IsWeaklyContractible.{max u (t + 1)} W →
            Function.Bijective
              ((SheafOfModules.evaluation.{max u (t + 1)} R (op W)).map f).hom) ∧
    (∀ (K L : CochainComplex (ringedSiteModules.{max u (t + 1)} R) ℤ)
        (f : K ⟶ L),
      QuasiIso f ↔
        ∀ (W : X.ProEt), IsAffine W.left →
          (topology X).IsWeaklyContractible.{max u (t + 1)} W →
            QuasiIso
              (((SheafOfModules.evaluation.{max u (t + 1)} R (op W)).mapHomologicalComplex
                (ComplexShape.up ℤ)).map f)) ∧
    (∀ (W : X.ProEt) [IsAffine W.left]
        (hW : (topology X).IsWeaklyContractible.{max (t + 1) u v} W),
      PreservesLimitsOfSize.{wJ, uJ}
          ((SheafOfModules.evaluation R (op W)) :
            SheafOfModules.{max (t + 1) u v} R ⥤
              ModuleCat.{max (t + 1) u v} (R.obj.obj (op W))) ∧
        PreservesColimitsOfSize.{wJ, uJ}
          ((SheafOfModules.evaluation R (op W)) :
            SheafOfModules.{max (t + 1) u v} R ⥤
              ModuleCat.{max (t + 1) u v} (R.obj.obj (op W)))) ∧
    (∀ U : X.ProEt, ∃ (I : Type t) (W : I → X.ProEt)
      (f : ∀ i : I, W i ⟶ U),
      Presieve.ofArrows W f ∈ precoverage X U ∧
        ∀ i : I, IsAffine (W i).left ∧
          (topology X).IsWeaklyContractible.{t + 1} (W i)) ∧
    (∀ (W : X.ProEt), IsAffine W.left →
      (topology X).IsWeaklyContractible.{t + 1} W →
      (∀ (F : Sheaf (topology X) (Type (t + 1)))
          (φ : F ⟶ (topology X).uliftYoneda.{t + 1}.obj W) [Epi φ],
        ∃ s : (topology X).uliftYoneda.{t + 1}.obj W ⟶ F,
          s ≫ φ = 𝟙 _) ∧
      Projective ((topology X).uliftYoneda.{t + 1}.obj W)) ∧
    (∀ (W : X.ProEt), IsAffine W.left →
      (∀ (S : Presieve W), S ∈ precoverage X W →
        ∃ S' : Presieve W, S' ≤ S ∧ S' ∈ precoverage X W ∧
          S' ∈ Precoverage.finite (X.ProEt) W) ∧
      CompactSpace W.left ∧
        (∀ (V : X.ProEt), CompactSpace V.left →
          ∀ (f : V ⟶ W), CompactSpace (Limits.pullback f f).left)) ∧
    (∀ (T : Qcqs X) (S : Presieve T),
      S ∈ qcqsPrecoverage X T → S ∈ Precoverage.finite (Qcqs X) T) ∧
    ∃ h : HasPullbacks (Qcqs X),
      ∃ J : @Pretopology (Qcqs X) inferInstance h,
        J.toPrecoverage = qcqsPrecoverage X ∧
        PreservesLimitsOfShape WalkingCospan (qcqsInclusion X) ∧
        PreservesLimitsOfShape WalkingCospan
          (qcqsInclusion X ⋙ ProEt.forget X ⋙ Over.forget X) ∧
        (∀ (T : Qcqs X) (S : Presieve T),
          S ∈ qcqsPrecoverage X T →
            S.map (qcqsInclusion X) ∈ precoverage X ((qcqsInclusion X).obj T)) ∧
        (∀ T : Qcqs X, HasFiniteLimits (Over T) ∧
          PreservesFiniteLimits
            (Over.post (X := T) (qcqsInclusion X ⋙ ProEt.forget X) ⋙
              Over.iteratedSliceForward ((qcqsInclusion X ⋙ ProEt.forget X).obj T))) ∧
        (CompactSpace X → QuasiSeparatedSpace X →
          HasFiniteLimits (Qcqs X) ∧
            PreservesFiniteLimits (qcqsInclusion X ⋙ ProEt.forget X)) ∧
        (∀ (T : Qcqs X) (S R : Presieve T),
          S ∈ qcqsPrecoverage X T →
            R ∈ Precoverage.finite (Qcqs X) T → S ⊔ R ∈ qcqsPrecoverage X T)
:= by
  sorry

end AlgebraicGeometry.Scheme.ProEt

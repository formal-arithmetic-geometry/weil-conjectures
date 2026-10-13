/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.RingTheory.Finiteness.Projective
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Sheaf.Topology.RingedSpaceModuleCohomology

import Sheaf.AlgebraicGeometry.LeraySpectralSequence
import Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange
import Sheaf.AlgebraicGeometry.PerfectAffineBoundedProjective
import Sheaf.AlgebraicGeometry.ModulePushforwardInjectiveAcyclic
import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech

/-! # Finite projective complex models for cohomology over an affine base

Source: Stacks Project, Tags 0B91(2), 08EB and 01F2.
(blueprint: lem-sc-valuation-proper-coherent-higher-direct-images-perfectness).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Proper flat finite-presentation morphisms with finite locally free coefficients admit a
bounded finite projective complex model for every cohomology module over the affine base.
No coherence or valuation hypothesis on the base ring is required for this model.
Source: Stacks Project, perfect.tex, Tags 0B91(2) and 08EB; cohomology.tex, Tag 01F2.
(blueprint: lem-sc-valuation-proper-coherent-higher-direct-images-perfectness)

Proof: Finite local freeness implies finite presentation and quasi-coherence. Since f is
flat, every local free summand is flat over the base, so the coefficient module is relatively
flat. Apply perfect_derivedDirectImage_baseChange to obtain perfectness of Rf_*F. On the
affine base Spec A, perfect_iff_affine_bounded_projective (Tag 08EB) gives a bounded
complex P of finite projective A-modules whose associated-sheaf complex represents Rf_*F.
Perfect objects have quasi-coherent homology: this is local, and on each strictly perfect
neighbourhood it follows from exactness of the affine associated-sheaf functor. That same
exactness identifies the homology sheaves of the global model with the associated sheaves
of H^q(P). Their positive cohomology on Spec A vanishes by affine acyclicity.
For scalar compatibility, form Leray in modules over Gamma(Spec A), before forgetting to
abelian groups. Direct images of injectives are acyclic for module-valued sections by
module_pushforward_injective_acyclic. On an injective resolution I of F the composite
section complex is Gamma(X,I), with its Gamma(Spec A)-action restricted along f.appTop;
this sectionwise equality commutes with the differentials. Resolution comparison therefore
identifies the abutment with the prescribed scalar restriction of moduleCohomology.
The vanishing columns p > 0 make the edge map an isomorphism in that module category.
Its target is Gamma(Spec A, H^q(P)~), canonically H^q(P) after restricting scalars along
GammaSpecIso.inv. Thus the composite is an A-linear isomorphism, not merely an additive one.
For an empty X or rank-zero coefficient use the zero complex; the
same proof also covers q above the complex bounds, when both modules vanish. The model is
used only in propositions, and no definition selects an arbitrary witness. -/
theorem exists_finiteProjectiveComplex_model_moduleCohomology
    {A : Type u} [CommRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (d : ℕ) (F : X.Modules) [F.IsFiniteLocallyFreeOfRank d] (q : ℕ) :
    ∃ P : CochainComplex (ModuleCat.{u} A) ℤ,
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)) ∧
      (∀ n : ℤ, Module.Finite A (P.X n) ∧ Module.Projective A (P.X n)) ∧
      Nonempty (((ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F)) ≅ P.homology (q : ℤ)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules

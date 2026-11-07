/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Submission.WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Submission.WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSpecializationAffineCoordinates
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSpecializationCounit
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSpecializationUnitComparison

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Sections on a closed specialization neighbourhood in the pro-etale site

Source: Stacks Project, `proetale.tex`, Tag 09AC, `lemma-compute-i-star`
(blueprint: lem-weil-pbc-proetale-specialization-restriction-sections).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The adjunction unit on sections of a weakly contractible affine specialization
neighbourhood is a natural isomorphism of abelian groups. Whiskering the unit with
sections at `V` retains its naturality in the abelian sheaf. Its target at `F` is
`(i⁻¹ F)((proEtaleBaseChange i).obj V)`, i.e. sections on `V ×[X] Z`.

Source: Stacks Project, Tag 09AC, `lemma-compute-i-star`
(blueprint: lem-weil-pbc-proetale-specialization-restriction-sections).

Proof plan:
1. Use weakly-etale localization to replace `X` by the affine scheme `V`, preserving
restriction and the unit. Write `B = V`, `T = B ×[X] Z`, and `k : T ⟶ B`.
2. Use the affine closed-site functors `v ⊣ u` of Tags 09BK/09BL and their counit
`p : v(T) ⟶ B`. The image of `p` contains `T`. Ind-etale maps are flat, so their
images are stable under generalization (flat going-down). The specialization
hypothesis makes `p` surjective. As an affine weakly-etale morphism it is a cover.
3. Local surjectivity for the representable epimorphism of this cover and weak
contractibility of `B` give a section `s` of `p`. After applying `u`, the counit
is an isomorphism by full faithfulness of `v`. Thus `p ≫ s` and the identity have
the same image under `u`; the adjunction bijection makes them equal. Hence `p`
is an isomorphism.
4. A finite affine ind-etale cover of `T` lifts by `v` to a cover of `B`: its image
contains `T` and is stable under generalization. Weak contractibility supplies a
section over `B`; base change and the canonical `u(v(T)) ≅ T` give a section of
the original cover.
5. Refine local lifts of a section along a set-sheaf epimorphism to a finite
ind-etale cover of `T`. Finite-coproduct evaluation and the section from step 4
produce a global lift. This proves weak contractibility of `T`; the dense-subsite
sheaf equivalence gives the same conclusion on the affine ind-etale basis.
6. Apply affine closed inverse-image evaluation to obtain `(k⁻¹ F)(T) ≅ F(v(T))`.
Under `v ⊣ u`, the inverse-image unit is precisely restriction along the counit
`p`, followed by sheafification/evaluation. It is an isomorphism by step 3.
7. Transport back through localization. All maps preserve addition. Naturality of
restriction and sheafification identifies the result with the original unit,
naturally in `F`, rather than merely an abstract isomorphism of section groups. -/
theorem isIso_proEtaleUnit_sections_of_specialization
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (V : X.ProEt) [IsAffine V.left]
    (hweak : ∀ (P Q : Sheaf (ProEt.topology X) (Type (u + 1))) (φ : P ⟶ Q),
      Epi φ → Function.Surjective (φ.hom.app (op V)))
    (hspec : ∀ x : V.left, ∃ z : ↥(pullback V.hom i),
      Specializes x ((pullback.fst V.hom i) z)) :
    IsIso (Functor.whiskerRight (proEtaleSheafAdjunction i AddCommGrpCat.{u + 1}).unit
      ((sheafSections (ProEt.topology X) AddCommGrpCat.{u + 1}).obj (op V))) := by
  let A := Γ(V.left, ⊤)
  let I := RingHom.ker (pullback.fst V.hom i).appTop.hom
  let B := AffineProEt.ofEtale (𝟙 (Spec A))
  obtain ⟨hB, hspecB⟩ := specialization_affine_coordinates i V hweak hspec
  obtain ⟨_, _, _, _, _, ⟨adj⟩, _, _⟩ :=
    AffineProEt.affine_closed_site_functor_properties A I
  have hcounit : IsIso (adj.counit.app B) :=
    AffineProEt.isIso_closedSiteCounit_of_specialization A I adj B hB hspecB
  exact isIso_proEtaleUnit_sections_of_closedSiteCounit i V hB adj hcounit

end AlgebraicGeometry.Scheme

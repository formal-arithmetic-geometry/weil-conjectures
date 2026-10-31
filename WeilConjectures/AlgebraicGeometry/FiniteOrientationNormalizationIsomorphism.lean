/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.FiniteRingSectionDeformation
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurityMaps
public import WeilConjectures.AlgebraicGeometry.DualizingCartesianApexIsomorphism
public import WeilConjectures.AlgebraicGeometry.VectorBundleIntegrationCharts
public import WeilConjectures.AlgebraicGeometry.VectorPurityNormalization

/-! # Source-isomorphism invariance of finite orientation normalization

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/`
`sk-prop-sp-purity-bc/sk-prop-sp-purity-bc-factors.proof.md`, proof (1)
(blueprint: lem-pur-finite-orientation-normalization-isomorphism).

The theorem states that the diagonal, normalized Rees specialization, and
normal-bundle integration equation is transported along an isomorphism of
sources over a fixed base.  The proof is the six-step argument from the
blueprint: transport the Rees deformation and vector-bundle factors, compare
the exceptional maps by their counit mate, paste the factors, and apply the
inverse source isomorphism for the converse.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry Scheme WeilConjectures
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

/-- The counit-preserving exceptional comparison on the dualizing objects for a source
isomorphism.  It is the component at the coefficient unit of the comparison in
`dualizing_cartesian_apex_isomorphism`, using the canonical pullback square of `r` and
`𝟙 S`.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/`
`sk-prop-sp-purity-bc/sk-prop-sp-purity-bc-factors.proof.md`, proof (1)
(blueprint: lem-pur-finite-orientation-normalization-isomorphism).
-/
noncomputable def sourceDualizingIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {T U S : Scheme.{u}} (r : T ⟶ S) (e : U ≅ T)
    [IsNoetherian T] [IsNoetherian U] [IsNoetherian S]
    [IsSeparated r] [QuasiCompact r] [HasCompactification r]
    [IsSeparated (e.hom ≫ r)] [QuasiCompact (e.hom ≫ r)]
    [HasCompactification (e.hom ≫ r)] :
    (ordinaryFinitePullback A e.hom).obj (dualizingComplex A r) ≅
      dualizingComplex A (e.hom ≫ r) := by
  let i : T ≅ pullback r (𝟙 S) :=
    (pullbackConeOfRightIsoIsLimit r (𝟙 S)).conePointUniqueUpToIso
      (limit.isLimit (cospan r (𝟙 S)))
  let q : ChosenCartesianSquare (𝟙 T) r r (𝟙 S) := by
    refine ⟨⟨by simp⟩, i, ?_, ?_⟩
    · convert IsLimit.conePointUniqueUpToIso_hom_comp
        (pullbackConeOfRightIsoIsLimit r (𝟙 S))
        (limit.isLimit (cospan r (𝟙 S))) WalkingCospan.left using 1 <;> simp [i]
    · convert IsLimit.conePointUniqueUpToIso_hom_comp
        (pullbackConeOfRightIsoIsLimit r (𝟙 S))
        (limit.isLimit (cospan r (𝟙 S))) WalkingCospan.right using 1 <;> simp [i]
  let q_e : IsPullback (e.hom ≫ 𝟙 T) (e.hom ≫ r) r (𝟙 S) := by
    apply IsPullback.of_iso_pullback (P := U)
      (CommSq.mk (by simp)) (e ≪≫ q.isoPullback)
    · simp [q, i]
    · simp [q, i]
  letI : IsIso (cartesianApexExceptionalComparison A e r) :=
    (dualizing_cartesian_apex_isomorphism A q e q_e).1
  exact (asIso (cartesianApexExceptionalComparison A e r)).app
    (𝟙_ (DerivedCategoryModule A S))

/-- The canonical map on orientation isomorphisms induced by a source isomorphism.
It is `B_e⁻¹ ; e^*(−) ; c_{e,d}`, with the counit-preserving comparison
`sourceDualizingIso` and the fixed roots-and-pure-tensor coefficient transport.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/`
`sk-prop-sp-purity-bc/sk-prop-sp-purity-bc-factors.proof.md`, proof (1)
(blueprint: lem-pur-finite-orientation-normalization-isomorphism).
-/
noncomputable def sourceOrientationMap
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {T U S : Scheme.{u}} (r : T ⟶ S) (h : U ⟶ S) (e : U ≅ T)
    (he : h = e.hom ≫ r)
    [IsNoetherian T] [IsNoetherian U] [IsNoetherian S]
    [IsSeparated r] [QuasiCompact r] [HasCompactification r]
    [HasCompactification h]
    [IsSeparated (e.hom ≫ r)] [QuasiCompact (e.hom ≫ r)]
    [HasCompactification (e.hom ≫ r)] (d : ℕ)
    (hT : IsUnit (N : Γ(T, ⊤))) :
    (dualizingComplex A r ≅ line A N hA T d) →
      (dualizingComplex A h ≅ line A N hA U d) := by
  subst h
  exact fun α =>
    (sourceDualizingIso A r e).symm ≪≫
      (ordinaryFinitePullback A e.hom).mapIso α ≪≫
      vectorIntegrationBaseCoefficientPullback A N hA
        (PurityFiniteSetting.purityTwistTransport A N hN hA) e.hom hT d

/-- Source-isomorphism invariance of the finite diagonal normalization predicate.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/`
`sk-prop-sp-purity-bc/sk-prop-sp-purity-bc-factors.proof.md`, proof (1)
(blueprint: lem-pur-finite-orientation-normalization-isomorphism).

The proof follows the source clause by clause.  First the map
`e ×_S e` identifies the two diagonal Rees deformations and their section
pairs.  The finite integrated-specialization and bundle-section-adjoint
base-change equations transport the two corresponding factors.  The
counit-preserving comparison of exceptional maps transports the diagonal
factor.  Pasting these equalities transports `OrientationNormalized`; the
same construction for `e.symm` gives the inverse and the canonical unit and
composition identifications cancel the two transports.  The first conjunct is
the bijection between the two normalized solution sets; the second conjunct
states that its inverse is `sourceOrientationMap` for `e.symm` (with
`r = e.symm.hom ≫ h` derived from `he`).  The identity source
isomorphism, dimension zero, empty schemes, and the zero coefficient ring are
included by the same equations.
-/
theorem finite_orientation_normalization_isomorphism
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {T U S : Scheme.{u}}
    [IsNoetherian T] [IsNoetherian U] [IsNoetherian S]
    (r : T ⟶ S) (h : U ⟶ S) (e : U ≅ T)
    (he : h = e.hom ≫ r)
    [IsSeparated r] [QuasiCompact r] [HasCompactification r]
    [IsSeparated h] [QuasiCompact h] [HasCompactification h]
    (d : ℕ)
    [SmoothOfRelativeDimension d r]
    [SmoothOfRelativeDimension d h]
    (G_r : FiniteRingSectionDeformation.Geometry d
      (pullback.fst r r) (pullback.diagonal r))
    (G_h : FiniteRingSectionDeformation.Geometry d
      (pullback.fst h h) (pullback.diagonal h))
    (hT : IsUnit (N : Γ(T, ⊤)))
    (hU : IsUnit (N : Γ(U, ⊤))) :
    Set.BijOn (sourceOrientationMap A N hN hA r h e he d hT)
      {α | OrientationNormalized A N hN hA r d G_r hT α}
      {α | OrientationNormalized A N hN hA h d G_h hU α} ∧
    Set.InvOn
      (sourceOrientationMap A N hN hA h r e.symm
        (by rw [he, Iso.symm_hom, Iso.inv_hom_id_assoc]) d hU)
      (sourceOrientationMap A N hN hA r h e he d hT)
      {α | OrientationNormalized A N hN hA r d G_r hT α}
      {α | OrientationNormalized A N hN hA h d G_h hU α} := by
  sorry

end AlgebraicGeometry.Etale.FiniteSmoothPurity

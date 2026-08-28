/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties

/-!
# The diagonal of a morphism locally of finite presentation

We prove the cancellation property of morphisms locally of finite presentation: if `f ≫ g` is
locally of finite presentation and `g` is locally of finite type, then so is `f`
(`AlgebraicGeometry.locallyOfFinitePresentation_of_comp`, Stacks Tag 02FV).

Applying this to `Δ ≫ pullback.fst f f = 𝟙 X` shows that the diagonal of a morphism locally of
finite presentation is again locally of finite presentation
(`AlgebraicGeometry.locallyOfFinitePresentation_diagonal`). Since a diagonal is a monomorphism,
it is automatically quasi-separated, so it is of finite presentation as soon as it is
quasi-compact, that is, as soon as `f` is quasi-separated.

# Finite-type ideal sheaves and closed immersions of finite presentation

We also record the two directions of the correspondence between finite-type ideal sheaves and
closed immersions locally of finite presentation:
`AlgebraicGeometry.Scheme.IdealSheafData.FiniteType.locallyOfFinitePresentation_subschemeι`
and `AlgebraicGeometry.Scheme.Hom.finiteType_ker`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- **Cancellation for morphisms locally of finite presentation**: if `f ≫ g` is locally of
finite presentation and `g` is locally of finite type, then `f` is locally of finite
presentation. -/
@[stacks 02FV]
theorem locallyOfFinitePresentation_of_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFinitePresentation (f ≫ g)] [LocallyOfFiniteType g] :
    LocallyOfFinitePresentation f :=
  HasRingHomProperty.of_comp' (P' := @LocallyOfFiniteType)
    (fun _ _ hf hfg ↦ hfg.of_comp_finiteType _ hf) ‹_› ‹_›

section Diagonal

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The diagonal of a morphism locally of finite presentation is locally of finite
presentation. -/
instance locallyOfFinitePresentation_diagonal [LocallyOfFinitePresentation f] :
    LocallyOfFinitePresentation (pullback.diagonal f) := by
  have : LocallyOfFinitePresentation (pullback.diagonal f ≫ pullback.fst f f) := by
    rw [pullback.diagonal_fst]; infer_instance
  exact locallyOfFinitePresentation_of_comp _ (pullback.fst f f)

/-- **The diagonal of a morphism of finite presentation is of finite presentation.**

Mathlib has no bundled class for "of finite presentation"; a morphism is of finite presentation
if it is locally of finite presentation, quasi-compact and quasi-separated. Note that `f` itself
need not be quasi-compact for this. -/
theorem Scheme.Hom.diagonal_finitePresentation [LocallyOfFinitePresentation f]
    [QuasiSeparated f] :
    LocallyOfFinitePresentation (pullback.diagonal f) ∧ QuasiCompact (pullback.diagonal f) ∧
      QuasiSeparated (pullback.diagonal f) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

end Diagonal

section IdealSheaf

variable {X Y : Scheme.{u}}

/-- The closed subscheme cut out by a finite-type ideal sheaf is locally of finite
presentation over the ambient scheme. -/
lemma Scheme.IdealSheafData.FiniteType.locallyOfFinitePresentation_subschemeι
    {I : X.IdealSheafData} (hI : I.FiniteType) :
    LocallyOfFinitePresentation I.subschemeι := by
  refine IsZariskiLocalAtSource.of_openCover I.subschemeCover.openCover fun U : X.affineOpens ↦ ?_
  change LocallyOfFinitePresentation (I.subschemeCover.f U ≫ I.subschemeι)
  rw [(I.isPullback_subschemeCover_map U).w]
  have : LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U)))) := by
    rw [LocallyOfFinitePresentation.SpecMap_iff]
    exact RingHom.FinitePresentation.of_surjective _ Ideal.Quotient.mk_surjective
      (by simpa only [CommRingCat.hom_ofHom, Ideal.mk_ker] using hI U)
  infer_instance

/-- The ideal sheaf cut out by a closed immersion locally of finite presentation is of
finite type. -/
lemma Scheme.Hom.finiteType_ker (f : X ⟶ Y) [IsClosedImmersion f]
    [LocallyOfFinitePresentation f] : f.ker.FiniteType := by
  intro U
  rw [Scheme.Hom.ker_apply]
  have hU : IsAffineOpen (f ⁻¹ᵁ U.1) := U.2.preimage f
  have hfp : (f.app U.1).hom.FinitePresentation := by
    rw [f.app_eq_appLE]
    exact f.finitePresentation_appLE U.2 hU le_rfl
  letI := (f.app U.1).hom.toAlgebra
  haveI : Algebra.FinitePresentation Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) := hfp
  haveI : Algebra.FinitePresentation Γ(Y, U.1) Γ(Y, U.1) := Algebra.FinitePresentation.self _
  exact Algebra.FinitePresentation.ker_fG_of_surjective
    (Algebra.ofId Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1)) (f.app_surjective U.1 U.2)

end IdealSheaf

end AlgebraicGeometry

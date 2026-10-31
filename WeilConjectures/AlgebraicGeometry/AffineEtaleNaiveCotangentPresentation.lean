/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpaceNaiveCotangentComplex
public import WeilConjectures.AlgebraicGeometry.AbelianSpacePoincareData
public import WeilConjectures.RingTheory.NaiveCotangentComparison
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.RingTheory.PresentationsHomotopyEquivalent
import WeilConjectures.AlgebraicGeometry.DerivedEtaleZariskiEquivalence
import WeilConjectures.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence

/-! # Polynomial presentations of the affine small étale naive cotangent complex

Source: Stacks Project, Tags 0D0X, 0D0I and 00S1; associated étale modules, Tag 03DX
(blueprint: lem-sfb-affine-etale-naive-cotangent-presentation).

The right-hand complex uses the existing conormal differential and two-term ring
complex. Associated étale sheaves are tilde followed by the canonical left adjoint
to the existing Zariski restriction on the identity chart of the represented scheme.
This adjunction fixes the functor up to unique isomorphism; no module data are chosen
from an uncharacterized existence assertion. Its target is the same small affine
ringed model as the intrinsic naive cotangent complex.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Zariski restriction for a represented scheme has its canonical tensor left adjoint.
Source: Stacks, Tags 03DX, 03FH and 039Z
(blueprint: lem-sfb-affine-etale-naive-cotangent-presentation).
Proof: on the ordinary small étale site this is extension by the structure sheaf
along epsilon. The identity chart identifies the existing restriction with epsilon
pushforward. Conjugate that adjunction by the affine-basis restriction equivalence;
the resulting left adjoint has the original section and module universes. -/
theorem representedSchemeModule_isRightAdjoint {S : Scheme.{u}} (T : Over S) :
    (Poincare.schemeModule T).IsRightAdjoint := by
  sorry

/-- The canonical extension to the small affine model, adjoint to actual Zariski restriction.
Source: Stacks, Tags 03DX, 03FH and 039Z
(blueprint: lem-sfb-affine-etale-naive-cotangent-presentation). -/
def representedSchemeModuleExtension {S : Scheme.{u}} (T : Over S) :
    T.left.Modules ⥤ (schemeSpace T).SmallModules :=
  @Functor.leftAdjoint _ _ _ _ (Poincare.schemeModule T)
    (representedSchemeModule_isRightAdjoint T)

/-- Tilde followed by canonical étale tensor extension, expressed on the existing basis.
For a B-module M this is the module sheaf M~_et, not merely its abelian sheaf.
Source: Stacks, Tags 01HV, 03DU and 03DX
(blueprint: lem-sfb-affine-etale-naive-cotangent-presentation). -/
def representedAffineEtaleAssociated {S : Scheme.{u}} (B : CommRingCat.{u})
    (b : Spec B ⟶ S) : ModuleCat.{u} B ⥤ (schemeSpace (Over.mk b)).SmallModules :=
  tilde.functor B ⋙ representedSchemeModuleExtension (Over.mk b)

/-- The associated étale module functor is additive.
Source: Stacks, Tags 01HV and 03DX
(blueprint: lem-sfb-affine-etale-naive-cotangent-presentation).
Proof: tilde is a left adjoint. Tensor extension is the left adjoint just defined.
Both preserve finite coproducts, hence biproducts in these abelian categories, so
both are additive and their composite is additive. -/
@[instance] theorem representedAffineEtaleAssociated_additive {S : Scheme.{u}}
    (B : CommRingCat.{u}) (b : Spec B ⟶ S) :
    (representedAffineEtaleAssociated B b).Additive := by
  sorry

/-- The given polynomial surjection, packaged in the existing ring-complex interface.
Source: Stacks, Algebra, Tags 00S0 and 00S1
(blueprint: lem-sfb-affine-etale-naive-cotangent-presentation). -/
def affineCotangentPolynomialPresentation
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    {T : Type u} (α : MvPolynomial T R →ₐ[R] B) (hα : Function.Surjective α) :
    Algebra.CotangentResolution.Naive.Presentation
      (Arrow.mk (CommRingCat.ofHom (algebraMap R B))) where
  ring := CommRingCat.of (MvPolynomial T R)
  base := CommRingCat.ofHom (algebraMap R (MvPolynomial T R))
  augmentation := CommRingCat.ofHom α.toRingHom
  triangle := CommRingCat.hom_ext α.comp_algebraMap
  surjective := hα

/-- Apply the associated étale module functor termwise to the existing ring complex.
Source: Stacks, Tags 00S1, 0D0I and 03DX
(blueprint: lem-sfb-affine-etale-naive-cotangent-presentation). -/
def affineCotangentEtaleComplex
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    {T : Type u} (α : MvPolynomial T R →ₐ[R] B) (hα : Function.Surjective α)
    {S : Scheme.{u}} (b : Spec (CommRingCat.of B) ⟶ S) :
    CochainComplex (schemeSpace (Over.mk b)).SmallModules ℤ :=
  letI := representedAffineEtaleAssociated_additive (CommRingCat.of B) b
  ((representedAffineEtaleAssociated (CommRingCat.of B) b).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj
      (Algebra.CotangentResolution.Naive.complex
        (affineCotangentPolynomialPresentation α hα))

/-- The affine polynomial-presentation comparison in the unbounded derived module category.
No finiteness, Noetherian, flatness or regular-sequence hypothesis is imposed.
Source: Stacks, Tags 0D0X, 0D0I and 00S1
(blueprint: lem-sfb-affine-etale-naive-cotangent-presentation).

Proof:
1. Apply lem-weil-pbc-nl-presentations-homotopy-equivalent to the specified
   presentation and the canonical presentation R[x_b | b in B] → B. Apply the
   additive functor M ↦ M~_et termwise. It preserves the chain maps and both
   chain-homotopy identities, hence gives an isomorphism in the derived category.
   Tilde and the module extension are the functors of
   lem-weil-pbc-affine-tilde-gamma-adjunction and
   lem-trf-scheme-zariski-etale-quasi-coherent-equivalence, transported through
   the existing affine-basis equivalence. The degree -1 term is I/I², the degree
   zero term is B tensor_P Omega[P/R], and the differential is [h] ↦ 1 tensor dh
   by Mathlib's conormal differential; Leibniz gives its well-defined B-linearity.
2. lem-sfb-zariski-naive-cotangent-affine-comparison gives the canonical affine
   Zariski quasi-isomorphism. Exactness of epsilon tensor pullback from
   lem-sfb-derived-etale-zariski-equivalence preserves it. Naturality of the
   associated-sheaf comparison identifies the single differential as well as
   both terms, yielding the canonical-presentation étale complex.
3. lem-sfb-scheme-naive-cotangent-etale-comparison identifies that pullback with
   the intrinsic naive cotangent of the represented spaces over S. Compose the
   inverses of these comparisons to obtain the displayed isomorphism. All
   complexes remain in degrees -1,0; no flatness of the conormal module is used. -/
theorem affine_etale_naive_cotangent_presentation
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    {T : Type u} (α : MvPolynomial T R →ₐ[R] B) (hα : Function.Surjective α)
    {S : Scheme.{u}} (v : Spec (CommRingCat.of R) ⟶ S)
    [HasDerivedCategory.{w}
      (schemeSpace (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ v))).SmallModules] :
    Nonempty
      (naiveCotangent
          (groupSchemeMap
            (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap R B))) rfl :
              Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ v) ⟶ Over.mk v)) ≅
        DerivedCategory.Q.obj (affineCotangentEtaleComplex α hα
          (Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ v))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace

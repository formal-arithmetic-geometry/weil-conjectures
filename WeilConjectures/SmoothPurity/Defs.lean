/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition
public import WeilConjectures.SmoothPurity.OrientationCanonical
public import WeilConjectures.SmoothPurity.TateTwistBoundedConstructible
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationModels
public import WeilConjectures.AlgebraicGeometry.ExplicitSmoothComparison.ComparisonBrownExplicit
public import WeilConjectures.AlgebraicGeometry.PurityIntegralTower.CondensedTateIntegralTower
public import WeilConjectures.AlgebraicGeometry.PurityIntegralTower.FinitePuritySourceUnitReduction
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSmoothTraceUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.PoincareTateBoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.RepresentingTraceClassification
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Trace.TraceNonuniqueness
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.TateTwist.ProEtale
public import WeilConjectures.WeilObject.Sheaf.StalkUnit

/-!

# Smooth purity for `ℚ̄_ℓ`-coefficients on the pro-étale site

Let `ℓ` be a prime and `k` a field of characteristic `p > 0` with `p ≠ ℓ`. As in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, all schemes are
objects `X : Over (Spec (.of k))`, separated and of finite type over `Spec k`, and all morphisms
are morphisms `f : X ⟶ Y` of `Over (Spec (.of k))`; in particular `ℓ` is invertible on every
scheme considered. In the documentation, `X` also stands for the underlying scheme `X.left`.

Let `f : X ⟶ Y` be a morphism whose underlying morphism of schemes `f.left` is smooth of pure
relative dimension `d`. *Smooth purity* (SGA 4, Exposé XVIII, Théorème 3.2.5, and Bhatt–Scholze,
*The pro-étale topology for schemes*, Section 6.8, for `ℚ̄_ℓ`-coefficients) identifies the
exceptional inverse image of the constant coefficient object with a shifted Tate twist:
```
pur_f : Rf^! ℚ̄_ℓ,Y ≅ ℚ̄_ℓ,X(d)[2d]
```
in the derived category `D(Mod_{ℚ̄_ℓ,X})` of module objects over `ℚ̄_ℓ,X = p_X^* ℚ̲̄_ℓ`, the
pullback of the condensed ring `ℚ̲̄_ℓ` (`Profinite.padicAlgClRingObj ℓ`). Here `Rf^!` is
`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleUpperShriek` on the bounded
constructible derived categories `Dᵇc(-)⟦ℚ̲̄_ℓ⟧` (the right adjoint of `Rf_!`, built from the
compactification of `f` chosen by Nagata's theorem), `ℚ̄_ℓ,Y` is the tensor unit of the
monoidal category `Dᵇc(Y)⟦ℚ̲̄_ℓ⟧`
(`AlgebraicGeometry.ProEtale.CondensedRing.isMonoidal_boundedConstructible`), whose underlying
complex is the tensor unit of `D(Mod_{ℚ̄_ℓ,Y})`, and `ℚ̄_ℓ,X(d)` is the Tate twist of
`WeilConjectures.TateTwist.ProEtale`. The isomorphism is stated after the inclusion
`Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ D(Mod_{ℚ̄_ℓ,X})`, which is fully faithful, so that the constructibility of the Tate
twists need not be recorded.

## The orientation and the sorried properties

The orientation `γ_f : ℚ̄_ℓ,X(d)[2d] ⟶ Rf^! ℚ̄_ℓ,Y`
(`AlgebraicGeometry.ProEtale.CondensedRing.smoothOrientation`, blueprint `sk-thm-purity-transport`,
used in `def-pur-smooth-trace`) is a `@[no_expose]` definition. It is the canonical orientation
(`AlgebraicGeometry.ProEtale.CondensedRing.IsCanonicalSmoothOrientation`): the extension of
scalars to `ℚ̄_ℓ` of the integral morphism `ℤ_ℓ,X(d)[2d] ⟶ Rf^! ℤ_ℓ,Y` lifting the finite
orientations `Rf^! Λ_Y ≅ Λ_X(d)[2d]`, `Λ = ℤ ⧸ ℓⁿ`, of the diagonal argument
(`AlgebraicGeometry.Etale.dualizingComplexTwistShiftIso`), when an isomorphism with this property
is known to exist. The lift always exists mathematically (SGA 4, Exposé XVIII: the finite
orientations are compatible under change of coefficients, blueprint
`det-sp-purity-coefficient-change`) and is unique, but its existence is not formalized; when it is
not available, `γ_f` is a non-canonical isomorphism
(`AlgebraicGeometry.ProEtale.CondensedRing.nonempty_iso_tateTwist_upperShriekUnit`). In all cases
`γ_f` is an isomorphism (`AlgebraicGeometry.ProEtale.CondensedRing.isIso_smoothOrientation`). The
trace map `Tr_f : Rf_! ℚ̄_ℓ,X(d)[2d] ⟶ ℚ̄_ℓ,Y` of SGA 4, Exposé XVIII
(`AlgebraicGeometry.ProEtale.CondensedRing.smoothTrace`) is the blueprint composite of `Rf_! γ_f`
and the counit of `Rf_! ⊣ Rf^!`. The purity isomorphism
`AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso` is *defined* from it, as the inverse
of its adjoint `ℚ̄_ℓ,X(d)[2d] ⟶ Rf^! ℚ̄_ℓ,Y` for `Rf_! ⊣ Rf^!`
(`AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityMap`, equal to `γ_f`). The following
properties of the trace are `sorry`ed:

- `AlgebraicGeometry.ProEtale.CondensedRing.isIso_smoothPurityMap`: smooth purity proper, the
  adjoint of the trace is an isomorphism;
- `AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso_zero_of_isOpenImmersion`: in
  relative dimension zero, for an open immersion `j`, the purity isomorphism is the canonical
  identification `Rj^! ℚ̄_ℓ ≅ j^* ℚ̄_ℓ ≅ ℚ̄_ℓ`
  (`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleUpperShriekUnitIso_padicAlgCl`);
- `AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso_comp_openImmersion`: compatibility
  with composition with an open immersion `j` on the target, through the composition
  isomorphism `R(f ≫ j)^! ≅ Rj^! ⋙ Rf^!`.

These normalizations pin the trace down far more than an arbitrary isomorphism
`Rf^! ℚ̄_ℓ ≅ ℚ̄_ℓ(d)[2d]`, but not completely: the compatibility with general composition and
with base change, and the identification of the trace of a smooth curve with the classical
trace on `H²_c`, need the comparison isomorphisms of Tate twists along pullbacks and tensor
products, which are not available yet.

-/

@[expose] public section

set_option Elab.async false

universe u

open scoped CategoryTheory.Obj

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Purity

-- Keep abstract categorical calculations from expanding the sheaf-module models.
attribute [local irreducible] DerivedCategory.monoidalClosed Mod.monoidalClosed
  Mod.monoidalCategory Mod.monoidalCategoryStruct upperStarFromPoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory

attribute [local irreducible] Scheme.PurityIntegralTower.ReconstructionResult
  boundedConstructibleLowerShriek boundedConstructibleUpperShriek
  boundedConstructibleUpperShriekAdjunction

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f.left]

omit [SmoothOfRelativeDimension d f.left] in
/-- Blueprint `def-pur-smooth-trace` (`γ_{f,Λ_Y}`, `sk-prop-sp-orientation`): the **orientation**
`ℚ̄_ℓ,X(d)[2d] ⟶ Rf^! ℚ̄_ℓ,Y` of a morphism `f` smooth of pure relative dimension `d`, the purity
isomorphism normalized by integration on the affine line (the canonical orientation of
`𝔸¹_Y ⟶ Y`). Take the explicit smooth adjunction counit constructed from the finite
orientations, integral tower and scalar extension. Identify its source with the published
Tate complex and take its adjunct under the bounded constructible adjunction. -/
@[no_expose]
noncomputable def smoothOrientation :
    boundedConstructibleTateTwist ℓ X d (2 * d) ⟶
      (boundedConstructibleUpperShriek ℓ f).obj
        (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) :=
  by
    classical
    exact if h : SmoothOfRelativeDimension d f.left then
      letI := h
      (boundedConstructibleUpperShriekAdjunction ℓ f).homEquiv _ _
        ⟨(boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ
            (compactificationOverField f)).hom.app _ ≫
          NormalizedUnitTrace.closureTrace ℓ f d⟩
    else 0

set_option linter.overlappingInstances false in
/-- The orientation of a morphism smooth of pure relative dimension `d` is an isomorphism: both
the canonical and the non-canonical orientations are (`isIso_smoothOrientationOfSmooth`). -/
instance isIso_smoothOrientation [SmoothOfRelativeDimension d f.left] :
    IsIso (smoothOrientation ℓ f d) := by
  rw [smoothOrientation, dif_pos ‹_›]
  infer_instance

/-- Blueprint `def-pur-smooth-trace` (`sk-def-sp-trace`): the **trace map**
`Tr_f : Rf_! ℚ̄_ℓ,X(d)[2d] ⟶ ℚ̄_ℓ,Y` of a morphism `f` smooth of pure relative dimension `d`
(SGA 4, Exposé XVIII, Théorème 2.9): the composite
`Rf_! ℚ̄_ℓ,X(d)[2d] ⟶ Rf_! Rf^! ℚ̄_ℓ,Y ⟶ ℚ̄_ℓ,Y` of `Rf_!` of the orientation `γ_f`
(`smoothOrientation`) and the counit `Tr_f` of `Rf_! ⊣ Rf^!`. -/
@[no_expose]
noncomputable def smoothTrace :
    (boundedConstructibleLowerShriek ℓ f).obj
      (boundedConstructibleTateTwist ℓ X d (2 * d)) ⟶
      𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :=
  (boundedConstructibleLowerShriek ℓ f).map (smoothOrientation ℓ f d) ≫
    (boundedConstructibleUpperShriekAdjunction ℓ f).counit.app _

omit [SmoothOfRelativeDimension d f.left] in
/-- The smooth trace is the counit transpose of the orientation: `Tr^sm_f = Tr_f ∘ Rf_!(γ_f)`.
Source: def-pur-smooth-trace. -/
theorem smoothTrace_eq :
    smoothTrace ℓ f d =
      (boundedConstructibleLowerShriek ℓ f).map (smoothOrientation ℓ f d) ≫
        (boundedConstructibleUpperShriekAdjunction ℓ f).counit.app _ := by
  unfold smoothTrace
  rfl

/-- The smooth trace recovers the specified explicit counit used to construct
its orientation. This is the adjunction inverse law, with the bounded-to-ambient
compact-support comparison retained. -/
private theorem smoothTrace_eq_normalizedCounit :
    (smoothTrace ℓ f d).hom =
      (boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ
        (compactificationOverField f)).hom.app (boundedConstructibleTateTwist ℓ X d (2 * d)) ≫
        NormalizedUnitTrace.closureTrace ℓ f d := by
  let t : (boundedConstructibleLowerShriek ℓ f).obj
      (boundedConstructibleTateTwist ℓ X d (2 * d)) ⟶ 𝟙_ _ :=
    ⟨(boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ
        (compactificationOverField f)).hom.app _ ≫
      NormalizedUnitTrace.closureTrace ℓ f d⟩
  have ho : smoothOrientation ℓ f d =
      (boundedConstructibleUpperShriekAdjunction ℓ f).homEquiv _ _ t := by
    dsimp only [smoothOrientation]
    rw [dif_pos (inferInstance : SmoothOfRelativeDimension d f.left)]
  have h := ((boundedConstructibleUpperShriekAdjunction ℓ f).homEquiv _ _).symm_apply_apply t
  rw [(boundedConstructibleUpperShriekAdjunction ℓ f).homEquiv_counit] at h
  rw [smoothTrace_eq, ho]
  exact congrArg (fun q ↦ q.hom) h

/-- The **purity map** `ℚ̄_ℓ,X(d)[2d] ⟶ Rf^! ℚ̄_ℓ,Y`: the adjoint of the trace `Tr_f` for
`Rf_! ⊣ Rf^!`. -/
noncomputable def smoothPurityMap :
    boundedConstructibleTateTwist ℓ X d (2 * d) ⟶
      (boundedConstructibleUpperShriek ℓ f).obj
        (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) :=
  (boundedConstructibleUpperShriekAdjunction ℓ f).homEquiv _ _ (smoothTrace ℓ f d)

omit [SmoothOfRelativeDimension d f.left] in
/-- The purity map is the orientation: the adjunct of `Tr_f ∘ Rf_!(γ_f)` is `γ_f`.
Source: def-pur-smooth-trace (the purity map is recovered from the smooth trace). -/
theorem smoothPurityMap_eq_smoothOrientation :
    smoothPurityMap ℓ f d = smoothOrientation ℓ f d := by
  change (boundedConstructibleUpperShriekAdjunction ℓ f).homEquiv _ _ (smoothTrace ℓ f d) = _
  rw [smoothTrace_eq]
  rw [← (boundedConstructibleUpperShriekAdjunction ℓ f).homEquiv_counit _ _
    (smoothOrientation ℓ f d)]
  exact ((boundedConstructibleUpperShriekAdjunction ℓ f).homEquiv _ _).apply_symm_apply _

/-- Taking the adjunct of the explicit counit composite recovers its input morphism.
Source: `lem-route-is-iso-smooth-purity-map`, Step 4. Apply the adjunction Hom equivalence
and its inverse law; this does not assume that the input is invertible. -/
private theorem smoothPurityMap_eq_of_trace_formula
    (a : boundedConstructibleTateTwist ℓ X d (2 * d) ⟶
      (boundedConstructibleUpperShriek ℓ f).obj
        (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)))
    (htrace : smoothTrace ℓ f d =
      (boundedConstructibleLowerShriek ℓ f).map a ≫
        (boundedConstructibleUpperShriekAdjunction
          ℓ f).counit.app (𝟙_ _)) :
    smoothPurityMap ℓ f d = a := by
  change (boundedConstructibleUpperShriekAdjunction ℓ f).homEquiv _ _
    (smoothTrace ℓ f d) = a
  rw [htrace, ← (boundedConstructibleUpperShriekAdjunction
    ℓ f).homEquiv_counit _ _ a]
  exact ((boundedConstructibleUpperShriekAdjunction ℓ f).homEquiv _ _).apply_symm_apply _

/-- Lift the specified ambient Tate realization through the full constructible inclusion,
then compose it with the reconstructed exceptional comparison. Its counit transpose
has exactly that adjunct, and its inverse is the ambient reconstruction formula.
Source: `lem-route-is-iso-smooth-purity-map`, Steps 3--5, and
`def-pur-condensed-smooth-purity-iso`. The reconstruction and trace formula are supplied
explicitly; no isomorphism or trace is selected by a mere existence theorem. -/
private theorem smoothPurityMap_of_reconstructed_trace
    {M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (a : M.obj ≅ (shiftFunctor _ (2 * d : ℤ)).obj (tateTwistDerived X.left ℓ d))
    (c : M ≅ (boundedConstructibleUpperShriek
      ℓ f).obj (𝟙_ _))
    (htrace : smoothTrace ℓ f d =
      (boundedConstructibleLowerShriek ℓ f).map
          (((ObjectProperty.ι _).preimageIso
            (X := M) (Y := boundedConstructibleTateTwist ℓ X d (2 * d)) a).inv ≫ c.hom) ≫
        (boundedConstructibleUpperShriekAdjunction
          ℓ f).counit.app (𝟙_ _)) :
    ∃ e : boundedConstructibleTateTwist ℓ X d (2 * d) ≅
        (boundedConstructibleUpperShriek ℓ f).obj
          (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)),
      smoothPurityMap ℓ f d = e.hom ∧
        (ObjectProperty.ι _).mapIso e.symm = (ObjectProperty.ι _).mapIso c.symm ≪≫ a := by
  let A : M ≅ boundedConstructibleTateTwist ℓ X d (2 * d) :=
    (ObjectProperty.ι _).preimageIso a
  let e := A.symm ≪≫ c
  have he : smoothPurityMap ℓ f d = e.hom :=
    smoothPurityMap_eq_of_trace_formula ℓ f d e.hom htrace
  have hinv : (ObjectProperty.ι _).mapIso e.symm =
      (ObjectProperty.ι _).mapIso c.symm ≪≫ a := by
    apply Iso.ext
    simp only [e, Iso.symm_hom, Iso.symm_inv, Iso.trans_inv, Functor.mapIso_hom,
      Iso.trans_hom, Functor.map_comp, A, Functor.preimageIso_hom, Functor.map_preimage]
  exact ⟨e, he, hinv⟩

-- The smoothness hypothesis is a binder of the instance: an `instance` drops unused
-- instance-implicit section variables, even under `include`. The elaborated signature has it
-- once; the linter also counts the section variable in scope.

set_option linter.overlappingInstances false in
/-- Blueprint `sk-thm-sp-qbar`: **smooth purity** (SGA 4, Exposé XVIII, Théorème 3.2.5): the
adjoint of the trace, `ℚ̄_ℓ,X(d)[2d] ⟶ Rf^! ℚ̄_ℓ,Y`, is an isomorphism, for `f` smooth of
relative dimension `d`. -/
instance isIso_smoothPurityMap [SmoothOfRelativeDimension d f.left] :
    IsIso (smoothPurityMap ℓ f d) :=
  sorry

/-- **Smooth purity**: for a morphism `f : X ⟶ Y` of separated `k`-schemes of finite type
which is smooth of pure relative dimension `d`, the exceptional inverse image of the constant
coefficient object is the shifted Tate twist, `Rf^! ℚ̄_ℓ,Y ≅ ℚ̄_ℓ,X(d)[2d]`. It is the inverse of
the adjoint of the trace (`smoothPurityMap`), after the inclusion
`Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ D(Mod_{ℚ̄_ℓ,X})`. -/
noncomputable def smoothPurityIso :
    ((boundedConstructibleUpperShriek ℓ f).obj
      (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧))).obj ≅
      (shiftFunctor _ (2 * d : ℤ)).obj (tateTwistDerived X.left ℓ d) :=
  (ObjectProperty.ι _).mapIso (asIso (smoothPurityMap ℓ f d)).symm

omit [SmoothOfRelativeDimension d f.left] in
/-- Blueprint `sk-thm-purity-transport`, étale case: **normalization of purity in relative
dimension zero**: for an open immersion `j`, the purity isomorphism `Rj^! ℚ̄_ℓ ≅ ℚ̄_ℓ(0)[0]` is
the canonical identification `Rj^! ℚ̄_ℓ ≅ j^* ℚ̄_ℓ ≅ ℚ̄_ℓ`
(`boundedConstructibleUpperShriekUnitIso_padicAlgCl`); equivalently, the trace of `j` is the
counit `Rj_! Rj^! ℚ̄_ℓ ⟶ ℚ̄_ℓ` read through it. -/
theorem smoothPurityIso_zero_of_isOpenImmersion (j : X ⟶ Y) [IsOpenImmersion j.left] :
    smoothPurityIso ℓ j 0 =
      (ObjectProperty.ι _).mapIso (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j) ≪≫
        (tateTwistDerivedZeroIso ℓ X.left).symm ≪≫
        ((shiftFunctorZero' _ (2 * ((0 : ℕ) : ℤ)) (by simp)).app _).symm :=
  sorry

/-- Blueprint `sk-prop-sp-composition`, case of an open immersion: **compatibility of purity
with composition with an open immersion**: for `f` smooth of pure relative dimension `d` and an
open immersion `j` on its target, the purity isomorphism of `f ≫ j` is that of `f` precomposed with
`R(f ≫ j)^! ℚ̄_ℓ ≅ Rf^! Rj^! ℚ̄_ℓ ≅ Rf^! ℚ̄_ℓ`, the composition isomorphism of the exceptional
inverse images followed by purity for `j` (`boundedConstructibleUpperShriekUnitIso_padicAlgCl`). -/
theorem smoothPurityIso_comp_openImmersion {Z : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom]
    [QuasiCompact Z.hom] [IsSeparated Z.hom] (j : Y ⟶ Z) [IsOpenImmersion j.left]
    [SmoothOfRelativeDimension d (f ≫ j).left] :
    smoothPurityIso ℓ (f ≫ j) d =
      (ObjectProperty.ι _).mapIso
          ((boundedConstructibleUpperShriekComp_padicAlgCl ℓ f j).app _ ≪≫
            (boundedConstructibleUpperShriek ℓ f).mapIso
              (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j)) ≪≫
        smoothPurityIso ℓ f d :=
  sorry

end Purity

end AlgebraicGeometry.ProEtale.CondensedRing

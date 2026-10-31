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
/-- Blueprint `sk-thm-purity-transport` (`γ_{f,ℚ̄_ℓ}(ℚ̄_ℓ,Y)`, used in `def-pur-smooth-trace`): the
**orientation** `ℚ̄_ℓ,X(d)[2d] ⟶ Rf^! ℚ̄_ℓ,Y` of a morphism `f` smooth of pure relative dimension
`d`, the datum the smooth trace is built from. It is `smoothOrientationOfSmooth`: the canonical
orientation (`IsCanonicalSmoothOrientation`, the extension of scalars of the integral lift of the
finite orientations `Rf^! Λ_Y ≅ Λ_X(d)[2d]` of the diagonal argument) when an isomorphism with
this property is known to exist, and otherwise a non-canonical isomorphism
(`nonempty_iso_tateTwist_upperShriekUnit`). The canonical orientation always exists
mathematically (SGA 4, Exposé XVIII: the finite orientations are compatible under change of
coefficients, blueprint `det-sp-purity-coefficient-change`), but the existence of the compatible
lift is not formalised. It is an isomorphism (`isIso_smoothOrientation`).
The signature does not carry `[SmoothOfRelativeDimension d f.left]`: for `f` not smooth of pure
relative dimension `d` the value is `0`, and the datum is meaningful only for `f` smooth of pure
relative dimension `d`. -/
@[no_expose]
noncomputable def smoothOrientation :
    boundedConstructibleTateTwist ℓ X d (2 * d) ⟶
      (boundedConstructibleUpperShriek ℓ f).obj
        (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) := by
  classical
  exact if _ : SmoothOfRelativeDimension d f.left then
    haveI := neZero_natCast_of_ringChar_ne ℓ (k := k)
    smoothOrientationOfSmooth ℓ f d
  else 0

-- The smoothness hypothesis is a binder of the instance: an `instance` drops unused
-- instance-implicit section variables, even under `include`. The elaborated signature has it
-- once; the linter also counts the section variable in scope.
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
  exact (congrArg ((boundedConstructibleUpperShriekAdjunction ℓ f).homEquiv _ _)
    ((boundedConstructibleUpperShriekAdjunction ℓ f).homEquiv_counit _ _
      (smoothOrientation ℓ f d))).symm.trans
    (((boundedConstructibleUpperShriekAdjunction ℓ f).homEquiv _ _).apply_symm_apply _)

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

/-- The normalized inverse formula for an explicitly reconstructed trace.
Source: `def-pur-condensed-smooth-purity-iso` and the last step of
`lem-route-smooth-purity-iso-comp-open-immersion`. The preceding helper constructs the
comparison before the disputed purity instance; here equality of its hom with the
actual adjunct identifies its inverse with the already defined purity isomorphism. -/
private theorem smoothPurityIso_eq_of_reconstructed_trace
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
    smoothPurityIso ℓ f d = (ObjectProperty.ι _).mapIso c.symm ≪≫ a := by
  obtain ⟨e, he, hinv⟩ := smoothPurityMap_of_reconstructed_trace ℓ f d a c htrace
  have h : asIso (smoothPurityMap ℓ f d) = e := Iso.ext he
  unfold smoothPurityIso
  rw [h]
  exact hinv

/-- Invert a common-source comparison square in an arbitrary category.
Source: the final inversion step of the open-composition node. Cancel the
common-source isomorphism and use its supplied comparison equation. -/
private theorem smoothTrace_inverse_comparison_square
    {C : Type*} [Category C] {M A B : C}
    (cf : M ≅ A) (ch : M ≅ B) (r : B ≅ A)
    (h : ch.hom ≫ r.hom = cf.hom) : ch.inv = r.hom ≫ cf.inv := by
  apply (cancel_epi ch.hom).1
  rw [ch.hom_inv_id, ← Category.assoc, h, cf.hom_inv_id]

/-- Map the inverse common-source comparison without unfolding the functor.
Source: the same final inversion step, after the constructible inclusion.
First invert the abstract square, then use functoriality of mapped isomorphisms. -/
private theorem smoothTrace_map_inverse_comparison_square
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {M A B : C}
    (cf : M ≅ A) (ch : M ≅ B) (r : B ≅ A)
    (h : ch.hom ≫ r.hom = cf.hom) :
    F.mapIso ch.symm = F.mapIso r ≪≫ F.mapIso cf.symm := by
  have he : ch.symm = r ≪≫ cf.symm :=
    Iso.ext (smoothTrace_inverse_comparison_square cf ch r h)
  rw [he, Functor.mapIso_trans]

/-- Cancel a mapped inverse unit comparison in an abstract square.
Source: the map-square to isomorphism-square step of the composition node.
Compose with the mapped forward unit comparison and use functoriality. -/
private theorem smoothTrace_comp_eq_of_map_inv
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {U V : C}
    (e : U ≅ V) {M N : D} (a : M ⟶ N) (b : N ⟶ F.obj U) (c : M ⟶ F.obj V)
    (h : a ≫ b = c ≫ F.map e.inv) : a ≫ b ≫ F.map e.hom = c := by
  rw [← Category.assoc, h, Category.assoc, ← F.map_comp, e.inv_hom_id,
    F.map_id, Category.comp_id]

/-- Inverting a common-source comparison square gives the required open-composition
formula for purity. Source: `lem-route-smooth-purity-iso-comp-open-immersion`, Step 8.
Apply the reconstructed trace formula to each map, cancel the two comparison
isomorphisms in the supplied square, and map the resulting inverse equation through
the inclusion. The equality of reconstructed comparisons is a geometric input. -/
private theorem smoothPurityIso_comp_of_reconstructed_traces
    {Z : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    [IsSeparated Z.hom] (j : Y ⟶ Z)
    [SmoothOfRelativeDimension d (f ≫ j).left]
    {M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (a : M.obj ≅ (shiftFunctor _ (2 * d : ℤ)).obj (tateTwistDerived X.left ℓ d))
    (cf : M ≅ (boundedConstructibleUpperShriek
      ℓ f).obj (𝟙_ _))
    (ch : M ≅ (boundedConstructibleUpperShriek
      ℓ (f ≫ j)).obj (𝟙_ _))
    (r : (boundedConstructibleUpperShriek
        ℓ (f ≫ j)).obj (𝟙_ _) ≅
      (boundedConstructibleUpperShriek
        ℓ f).obj (𝟙_ _))
    (hf : smoothTrace ℓ f d =
      (boundedConstructibleLowerShriek ℓ f).map
          (((ObjectProperty.ι _).preimageIso
            (X := M) (Y := boundedConstructibleTateTwist ℓ X d (2 * d)) a).inv ≫ cf.hom) ≫
        (boundedConstructibleUpperShriekAdjunction
          ℓ f).counit.app (𝟙_ _))
    (hh : smoothTrace ℓ (f ≫ j) d =
      (boundedConstructibleLowerShriek ℓ (f ≫ j)).map
          (((ObjectProperty.ι _).preimageIso
            (X := M) (Y := boundedConstructibleTateTwist ℓ X d (2 * d)) a).inv ≫ ch.hom) ≫
        (boundedConstructibleUpperShriekAdjunction
          ℓ (f ≫ j)).counit.app (𝟙_ _))
    (hcomp : ch.hom ≫ r.hom = cf.hom) :
    smoothPurityIso ℓ (f ≫ j) d =
      (ObjectProperty.ι _).mapIso r ≪≫ smoothPurityIso ℓ f d := by
  let I := (boundedConstructible
    (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι
  have hh' := smoothPurityIso_eq_of_reconstructed_trace ℓ (f ≫ j) d a ch hh
  have hf' := smoothPurityIso_eq_of_reconstructed_trace ℓ f d a cf hf
  calc
    smoothPurityIso ℓ (f ≫ j) d = I.mapIso ch.symm ≪≫ a := hh'
    _ = (I.mapIso r ≪≫ I.mapIso cf.symm) ≪≫ a :=
      congrArg (fun e ↦ e ≪≫ a) (smoothTrace_map_inverse_comparison_square I cf ch r hcomp)
    _ = I.mapIso r ≪≫ (I.mapIso cf.symm ≪≫ a) := Iso.trans_assoc _ _ _
    _ = I.mapIso r ≪≫ smoothPurityIso ℓ f d :=
      congrArg (fun e ↦ I.mapIso r ≪≫ e) hf'.symm

omit [SmoothOfRelativeDimension d f.left] in
/-- Complete the zero-dimensional normalization from its explicit trace formula.
Source: `lem-route-smooth-purity-iso-zero-of-is-open-immersion`, Step 3. Use the
coefficient unit as the realized object, the inverse live open-unit comparison as
c, and the canonical inverse zero-twist/zero-shift comparison as a. The general
reconstructed inverse formula then gives exactly the stated normalization. -/
private theorem smoothPurityIso_zero_of_trace_formula
    (j : X ⟶ Y) [IsOpenImmersion j.left]
    (htrace : smoothTrace ℓ j 0 =
      (boundedConstructibleLowerShriek ℓ j).map
          (((ObjectProperty.ι _).preimageIso
            (X := 𝟙_ (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧))
            (Y := boundedConstructibleTateTwist ℓ X 0 (2 * 0))
            ((tateTwistDerivedZeroIso ℓ X.left).symm ≪≫
              ((shiftFunctorZero' _ (2 * ((0 : ℕ) : ℤ)) (by simp)).app _).symm)).inv ≫
            (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j).inv) ≫
        (boundedConstructibleUpperShriekAdjunction
          ℓ j).counit.app (𝟙_ _)) :
    smoothPurityIso ℓ j 0 =
      (ObjectProperty.ι _).mapIso (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j) ≪≫
        (tateTwistDerivedZeroIso ℓ X.left).symm ≪≫
        ((shiftFunctorZero' _ (2 * ((0 : ℕ) : ℤ)) (by simp)).app _).symm := by
  have h := smoothPurityIso_eq_of_reconstructed_trace ℓ j 0
    (M := 𝟙_ (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧))
    ((tateTwistDerivedZeroIso ℓ X.left).symm ≪≫
      ((shiftFunctorZero' _ (2 * ((0 : ℕ) : ℤ)) (by simp)).app _).symm)
    (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j).symm htrace
  simpa only [Iso.symm_symm_eq] using h

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

/-- Invert the actual purity-map square obtained from trace transitivity.
Source: `lem-route-smooth-purity-iso-comp-open-immersion`, Steps 7--8.
Use the canonical open-unit inverse as q in the preceding mate calculation,
compose with its inverse, and cancel the invertible actual purity map. Applying
the fully faithful inclusion gives the exact stated ambient composition formula.
Invertibility is supplied explicitly, rather than derived from the disputed
unconditional instance. The trace transitivity equation is the geometric input. -/
private theorem smoothPurityIso_comp_of_trace_transitivity
    {Z : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    [IsSeparated Z.hom] (j : Y ⟶ Z) [IsOpenImmersion j.left]
    [SmoothOfRelativeDimension d (f ≫ j).left]
    (hf : IsIso (smoothPurityMap ℓ f d)) (hh : IsIso (smoothPurityMap ℓ (f ≫ j) d))
    (htrace : (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f j).inv.app
          (boundedConstructibleTateTwist ℓ X d (2 * d)) ≫ smoothTrace ℓ (f ≫ j) d =
      (boundedConstructibleLowerShriek ℓ j).map
          (smoothTrace ℓ f d ≫ (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j).inv) ≫
        (boundedConstructibleUpperShriekAdjunction
          ℓ j).counit.app (𝟙_ _)) :
    smoothPurityIso ℓ (f ≫ j) d =
      (ObjectProperty.ι _).mapIso
          ((boundedConstructibleUpperShriekComp_padicAlgCl ℓ f j).app _ ≪≫
            (boundedConstructibleUpperShriek ℓ f).mapIso
              (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j)) ≪≫
        smoothPurityIso ℓ f d := by
  let := hf
  let := hh
  let G := boundedConstructibleUpperShriek ℓ f
  let r := (boundedConstructibleUpperShriekComp_padicAlgCl ℓ f j).app (𝟙_ _) ≪≫
    G.mapIso (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j)
  have hm := smoothPurityMap_comp_of_trace_transitivity ℓ f d j
    (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j).inv htrace
  have hs : smoothPurityMap ℓ (f ≫ j) d ≫ r.hom = smoothPurityMap ℓ f d := by
    exact smoothTrace_comp_eq_of_map_inv G _ _ _ _ hm
  exact smoothTrace_map_inverse_comparison_square (ObjectProperty.ι _)
    (asIso (smoothPurityMap ℓ f d)) (asIso (smoothPurityMap ℓ (f ≫ j) d)) r hs

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

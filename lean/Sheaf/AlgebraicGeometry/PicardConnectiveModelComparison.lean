/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.PicardOrdinaryModelCycles
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.PicardDerivedModelSections
import Sheaf.AlgebraicGeometry.ConnectiveSingleHom
import Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback
import Sheaf.AlgebraicGeometry.DerivedPullbackStructureSheaf

/-! # Derived test sections and ordinary connective cycles

Source: Stacks Project, Tags 06YJ and 0D5S.
(blueprint: lem-sc-picard-connective-model-comparison)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- For a fixed connective strictly perfect model, test sections are ordinary
cycles on every scheme mapping through its open domain. The comparison is natural
for the canonical composition maps. No affine, scalar-basis or residue hypothesis
is used.
Source: Stacks Project, Tags 06YJ and 0D5S; Tag 05RR, truncation calculus of fractions.
(blueprint: lem-sc-picard-connective-model-comparison)

Proof: Transport the localized complex along `Modules.overEquiv U`. Its terms are
retracts of finite free modules and are flat; it is bounded, hence K-flat. The open
restriction comparison `Modules.overFunctorEquiv` identifies its localization with
the derived restriction of E. The K-flat counit computes every further derived
pullback by termwise tensor pullback. Both source and target remain connective.
Apply `DerivedCategory.connective_single_hom_bijective` after identifying pullback
of the degree-zero structure sheaf with the single of its underived pullback.
A chain map from a single complex is determined by its degree-zero component;
its sole condition is the outgoing differential equation defining the subgroup.
These identifications are additive. On representatives, successive pullback is
conjugation by the underived composition comparison. The derived comparison is
induced from these same counits, as specified by `exists_derivedPullbackComposition`.
Naturality of counits and of localization therefore gives the displayed equality,
including the equality transports for both t and s. Fix the model isomorphism once
before making all these comparisons; this supplies a single simultaneous family. -/
theorem picard_connective_model_comparison
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    (W : Scheme.{v}) (E : schemeDerivedCategory W) (U : W.Opens)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K) (hneg : ∀ i : ℤ, i < 0 → IsZero (K.X i))
    (hE : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj E ≅
        DerivedCategory.Q.obj K)) :
    ∃ q : ∀ {T : Scheme.{v}} (t : T ⟶ W) (s : T ⟶ U.toScheme),
        s ≫ U.ι = t →
          picardDerivedModelSections E t ≃+ picardOrdinaryModelCycles W U K t s,
      ∀ {T T' : Scheme.{v}} (i : T' ⟶ T) (t : T ⟶ W) (t' : T' ⟶ W)
        (s : T ⟶ U.toScheme) (s' : T' ⟶ U.toScheme)
        (ht : i ≫ t = t') (hs : i ≫ s = s')
        (hf : s ≫ U.ι = t) (hf' : s' ≫ U.ι = t')
        (ξ : picardDerivedModelSections E t),
        (q t' s' hf' (picardDerivedModelRestriction E i t t' ht ξ)).val =
          picardOrdinaryModelRestriction W U K i t t' s s' ht hs
            (q t s hf ξ).val := by sorry

end AlgebraicGeometry.Scheme

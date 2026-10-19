/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q120
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.Blowup.AdmissibleBlowup
public import Sheaf.AlgebraicGeometry.ModuleStrictTransform
public import WeilConjectures.AlgebraicGeometry.FiniteTypeIdealModule
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.RingTheory.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportPullback
import Sheaf.AlgebraicGeometry.FinitePushforwardFiniteType
import Mathlib.RingTheory.FiniteStability
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.Algebra.Module.FinitePresentation
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.Unramified.Finite
import Sheaf.AlgebraicGeometry.AffineChartRelativeFlatCriterion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.DimensionBaseChange
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Sheaf.AlgebraicGeometry.ModuleFinitePresentationCokernel
import Sheaf.AlgebraicGeometry.GenericFreeBlowup
import Sheaf.AlgebraicGeometry.ModuleAdmissibleBlowupCalculus
import Sheaf.AlgebraicGeometry.ModuleStrictTransformAffinePushforward
import Sheaf.AlgebraicGeometry.ModuleStrictTransformUniversalExact
import Sheaf.AlgebraicGeometry.NagataBoundaryDivisorCartier
import Sheaf.AlgebraicGeometry.UnramifiedMorphism
import Sheaf.RingTheory.FreeSubtractionFlatness
import Sheaf.TraceFormula.ElementaryModuleDevissage
import Sheaf.TraceFormula.EtaleFlatteningDescent
import Sheaf.TraceFormula.FlatFiniteTypeDensePresentation

/-!
# Flattening a module by an admissible blowup

Source: Stacks Project, Tag 0815, `flat.tex`, Theorem `theorem-flatten-module`
(blueprint: lem-trf-flattening-module-by-admissible-blowup).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finite-type quasi-coherent module, finitely presented and flat over the preserved
quasi-compact open, becomes flat and finitely presented after an admissible base blowup.
The centre is retained in `B`, and the transform is the canonical module strict transform.
Source: Stacks Project, Tag 0815, Theorem `theorem-flatten-module`
(blueprint: lem-trf-flattening-module-by-admissible-blowup).

Proof:
1. First prove flatness by strong induction on a uniform bound for fibre-support dimension
   (`lem-fin-finite-type-fibre-dimension-bound`). For empty fibre supports the finite-type
   support criterion (`lem-weil-pbc-support-pullback-finite-type`) makes the module zero;
   the unit-ideal blowup suffices.
2. Use `lem-trf-etale-flattening-descent` to pass to finitely many affine neighbourhoods.
   Include empty-source diagrams over base charts to cover base points missed by the source.
3. Apply `lem-trf-elementary-module-devissage`: replace the module locally by a module on a
   closed subscheme finite over a smooth affine family with geometrically integral fibres.
   Its finite pushforward is finite type (`lem-pc-f3-finite-pushforward-finite-type`).
4. Preserve finite presentation over the open: the closed immersion and finite map are
   finitely presented by the affine finite-presentation and algebra-presentation lemmas.
   Descend the presentation across the quotient ring, then use finite algebra as finite
   module and `lem-pc-module-finite-presentation-transitive`. Use
   `lem-weil-pbc-quasi-coherent-finite-type-affine` to identify module and sheaf presentations.
5. Etale source pullback preserves base flatness by `lem-weil-pbc-etale-algebra-flat`.
   Etale base neighbourhoods are unramified, by the diagonal and Kahler-differential
   criteria (`lem-weil-pbc-formally-unramified-ring-iff-kahler-zero`), and
   `lem-sc-unramified-flat-of-base-flat` upgrades base flatness to the new base.
6. Affine pushforward preserves and reflects relative flatness by
   `lem-pc-affine-chart-relative-flat-criterion`. It commutes with strict transform by
   `lem-trf-strict-transform-affine-pushforward`, so it suffices to flatten the module
   on the smooth family.
7. Apply `lem-trf-generic-free-blowup` to obtain a finite locally free locus meeting every
   fibre. Base change preserves smoothness and geometric fibre dimension
   (`lem-pc-proper-base-change`, `lem-pc-dim-base-change`). The admissible-blowup calculus
   preserves finite type and the restriction over the open and composes successive blowups.
8. At a fibre generic point choose module sections giving a basis over its residue field.
   Their map from a finite free module is an isomorphism on a neighbourhood. The open-map
   theorem (`lem-weil-pbc-flat-finite-presentation-open`) permits shrinking the base so this
   neighbourhood meets every fibre.
9. By `lem-trf-free-subtraction-flatness` the free-module map is universally injective and
   its cokernel has the same relative flat locus. The cokernel remains finitely presented
   over the open by `lem-weil-pbc-module-finite-presentation-cokernel`.
10. Its fibre support is a proper closed subset of an integral fibre, so its dimension
    drops strictly; in dimension zero it is empty. Apply the induction hypothesis.
11. Use `lem-trf-strict-transform-universal-exact` for the transformed exact sequence.
    The calculus identifies the free term with the free pullback and retains the generic
    basis locus. The free-subtraction flatness criterion transfers flatness from the
    transformed cokernel to the transformed module.
12. Compose the preliminary and induction blowups by
    `lem-trf-module-admissible-blowup-calculus`, then descend along the finite etale covers
    using `lem-trf-etale-flattening-descent` and the affine-pushforward comparison.
13. Choose a finite-type ideal cutting out the boundary by
    `lemma-nagata-qc-open-complement-ideal-exists`, and apply
    `det-nagata-boundary-divisor-cartier` to make the preserved open schematically dense.
    Flatness makes the further strict transform the ordinary pullback, still flat and
    finite type. Local finite presentation of the ambient morphism survives base change
    (`lem-weil-pbc-finite-presentation-base-change-composition`). The preserved open is
    retrocompact on the qcqs base. Apply `lem-trf-flat-finite-type-dense-presentation`
    and compose the two blowups with the module strict-transform comparison. -/
theorem exists_flat_finitePresentation_moduleStrictTransform_admissibleBlowup
    {S X : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (f : X ⟶ S) [QuasiCompact f] [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (U : S.Opens) (hU : IsCompact (U : Set S))
    (hfp : ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj F).IsFinitePresentation)
    (hflat : ∀ x : X, f x ∈ U → Module.Flat (S.presheaf.stalk (f x))
      ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F))) :
    ∃ B : IsAdmissible S U,
      (∀ x : (Limits.pullback f B.I.blowupMap : Scheme.{u}),
        Module.Flat (B.I.blowup.presheaf.stalk ((pullback.snd f B.I.blowupMap) x))
          ((ModuleCat.restrictScalars ((pullback.snd f B.I.blowupMap).stalkMap x).hom).obj
            ((RingedSpace.moduleStalkFunctor
              (Limits.pullback f B.I.blowupMap).toRingedSpace x).obj
                (@Scheme.Modules.moduleStrictTransform X S f B.I
                  (B.I.isFiniteType_toModules_sheaf B.finiteType) F inferInstance)))) ∧
      (@Scheme.Modules.moduleStrictTransform X S f B.I
        (B.I.isFiniteType_toModules_sheaf B.finiteType) F inferInstance).IsFinitePresentation := by
  sorry

end AlgebraicGeometry

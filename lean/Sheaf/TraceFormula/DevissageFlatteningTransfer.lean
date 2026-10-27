/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q70
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.AlgebraicGeometry.TensorPullbackQuasiCoherent
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.Blowup.AdmissibleBlowup
public import WeilConjectures.AlgebraicGeometry.FiniteTypeIdealModule
public import Sheaf.AlgebraicGeometry.ModuleStrictTransform
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.AffineChartRelativeFlatCriterion
import WeilConjectures.AlgebraicGeometry.TensorPullbackFinitePresentation
import Sheaf.TraceFormula.ElementaryDevissageFinitePresentation
import Sheaf.TraceFormula.ElementaryModuleDevissage
import Sheaf.TraceFormula.EtaleLocalRingFlatness
import Sheaf.RingTheory.FiniteExtensionModuleFinitePresentation
import Sheaf.RingTheory.FinitelyPresentedOverSubring
import Sheaf.AlgebraicGeometry.RelativeFlatnessSourceCover
import Sheaf.AlgebraicGeometry.ModuleStrictTransformAffinePushforward
import Sheaf.AlgebraicGeometry.ModuleStrictTransformKernel
import WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChange
import WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine

/-! # Elementary devissage preserves module-flattening data

Source: Stacks Project, More on Flatness, Tag 0815, proof paragraph 2, and
Tags 057S and 057T (blueprint: lem-trf-devissage-flattening-transfer).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Elementary devissage preserves finite presentation and relative flatness over the
preserved open, and reflects relative flatness of the centre-dependent strict transforms.
The support dimension is computed in the subspace of nonzero stalks of the fibre module.
The pointed base neighbourhood has distinguished point `f₁ x₁`.
Admissible blowups are parameterized by their retained centres `B.I`; any specified
isomorphism with this blowup transports both transforms and their relative flatness.

Source: Stacks Project, More on Flatness, Tag 0815, proof paragraph 2;
Tags 057S, 057T, 05BA, 05B3, 05B4 and Divisors Tag 080G
(blueprint: lem-trf-devissage-flattening-transfer).

Proof (the nine steps of the DAG):
1. Local finite presentation implies local finite type by the affine-open criterion
   (lem-weil-pbc-lfp-affine-opens-finite-presentation). Apply
   lem-trf-elementary-module-devissage at x, retaining its pointed affine diagram.
   The affine base neighbourhood is quasi-compact over the quasi-separated base by
   lem-weil-pbc-qcqs-morphism-permanence; its inverse image of U is quasi-compact by
   lem-weil-pbc-quasi-compact-morphism-preimage-qc-open.
2. lem-trf-elementary-devissage-finite-presentation makes pi finitely presented.
   The closed immersion and the finite morphism are affine. Only the morphism clause
   of this lemma is used globally; its marked-point neighbourhood clauses are not.
3. Affine pushforward makes N = pi_*G quasi-coherent
   (lem-weil-pbc-affine-pushforward-base-change). On affine spectra Spec C over Spec B,
   a finite C-generating family of G, multiplied by a finite B-generating family of C,
   generates N over B. Use lem-weil-pbc-quasi-coherent-finite-type-affine.
4. Pullback preserves the presentation of F over U by
   lem-pc-tensor-pullback-finite-presentation. On every affine chart of X_1 over U_T,
   write the closed immersion as B -> C = B/J. Its module is finitely presented over B,
   hence over C by lem-trf-finitely-presented-over-subring. The affine criterion gives
   finite presentation of G everywhere over U_T.
5. On affine charts of Y over U_T the finite algebra B -> C is finitely presented
   by lem-weil-pbc-lfp-affine-opens-finite-presentation. Restriction of scalars preserves
   module finite presentation by lem-trf-finite-extension-module-finite-presentation.
   The affine module criterion therefore makes N finitely presented over U_T.
6. Etale source pullback preserves stalk flatness over the original base by
   lem-trf-relative-flatness-source-cover. Upgrade to the etale base local ring using
   lem-trf-etale-local-ring-flatness. The base-compatible closed-pushforward stalk
   identification (lem-weil-pbc-closed-pushforward-stalks) gives flatness of G over U_T.
7. The inverse images of affine base opens in the affine T-schemes Z and Y are affine
   (lem-weil-pbc-morphism-affine-schemes-affine, pqf-def-affine-morphism).
   Their G and N section modules have the same base action. Apply
   lem-pc-affine-chart-relative-flat-criterion on these charts to obtain flatness of N.
8. For each retained admissible centre, strict transform commutes with both affine
   pushforwards by lem-trf-strict-transform-affine-pushforward. The isomorphism i_*G
   with g^*F identifies the supported-section kernels and their quotients.
   lem-trf-strict-transform-sheaf-kernel gives quasi-coherence of the transforms.
9. After blowup, the base changes of Z, Y and X_1 remain affine over the new base by
   lem-weil-pbc-affine-morphism-permanence. Over every affine base chart the three
   section modules of G^b and its two direct images are the same base module.
   lem-pc-affine-chart-relative-flat-criterion therefore identifies relative flatness
   of the two displayed transforms. The affine base charts cover the entire blowup;
   neither flatness of the blowup nor singleton fibres after blowup are required. -/
theorem exists_devissage_flattening_transfer
    {S X : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (f : X ⟶ S) [QuasiCompact f] [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (U : S.Opens) (_hU : IsCompact (U : Set S))
    (_hfp : ((restrictFunctor (f ⁻¹ᵁ U).ι).obj F).IsFinitePresentation)
    (_hflat : ((restrictFunctor (f ⁻¹ᵁ U).ι).obj F).IsFlatOver (f ∣_ U))
    (x : X) (hx : ¬ Subsingleton
      (((tensorPullback (f.fiberι (f x))).obj F).presheaf.stalk (f.asFiber x))) :
    ∃ n : ℕ,
      topologicalKrullDimAt
        (⟨f.asFiber x, hx⟩ : {q : f.fiber (f x) |
          ¬ Subsingleton (((tensorPullback (f.fiberι (f x))).obj F).presheaf.stalk q)}) =
        (n : WithBot ℕ∞) ∧
      ∃ (X₁ T Z Y : Scheme.{u}) (g : X₁ ⟶ X) (e : T ⟶ S)
        (f₁ : X₁ ⟶ T) (i : Z ⟶ X₁) (π : Z ⟶ Y) (h : Y ⟶ T)
        (x₁ : X₁) (G : Z.Modules),
        IsAffine X₁ ∧ IsAffine T ∧ IsAffine Z ∧ IsAffine Y ∧
        Etale g ∧ Etale e ∧ QuasiCompact e ∧
        g x₁ = x ∧ e (f₁ x₁) = f x ∧ g ≫ f = f₁ ≫ e ∧ i ≫ f₁ = π ≫ h ∧
        IsClosedImmersion i ∧ LocallyOfFinitePresentation i ∧
        QuasiCompact i ∧ QuasiSeparated i ∧ IsFinite π ∧
        G.IsQuasicoherent ∧ G.IsFiniteType ∧
        Nonempty ((pushforward i).obj G ≅ (tensorPullback g).obj F) ∧
        SmoothOfRelativeDimension n h ∧ GeometricallyIntegral h ∧
        ∃ hN : ((pushforward π).obj G).IsQuasicoherent,
          ((pushforward π).obj G).IsFiniteType ∧
          ((restrictFunctor (h ⁻¹ᵁ (e ⁻¹ᵁ U)).ι).obj
            ((pushforward π).obj G)).IsFinitePresentation ∧
          ((restrictFunctor (h ⁻¹ᵁ (e ⁻¹ᵁ U)).ι).obj
            ((pushforward π).obj G)).IsFlatOver (h ∣_ (e ⁻¹ᵁ U)) ∧
          ∀ B : IsAdmissible T (e ⁻¹ᵁ U),
            ((@moduleStrictTransform Y T h B.I
              (B.I.isFiniteType_toModules_sheaf B.finiteType)
              ((pushforward π).obj G) hN).IsFlatOver (pullback.snd h B.I.blowupMap) ↔
            (@moduleStrictTransform X₁ T f₁ B.I
              (B.I.isFiniteType_toModules_sheaf B.finiteType)
              ((tensorPullback g).obj F) (isQuasicoherent_tensorPullback g F)).IsFlatOver
                (pullback.snd f₁ B.I.blowupMap)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules

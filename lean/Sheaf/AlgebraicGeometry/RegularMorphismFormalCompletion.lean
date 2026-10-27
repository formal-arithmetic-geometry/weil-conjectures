/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q47
-/
module

public import Sheaf.AlgebraicGeometry.AdicFormalGeometry
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.RingTheory.FiniteTypeGRing
import WeilConjectures.RingTheory.GRingCompletionRegular
import WeilConjectures.RingTheory.LocalizationRegular
import WeilConjectures.RingTheory.RegularComposition
import WeilConjectures.RingTheory.RegularLocalMaximal
import WeilConjectures.RingTheory.RegularPermanence
import WeilConjectures.RingTheory.RegularThroughLocalization

/-!
# Regular morphisms remain regular after formal completion

Source: Temkin, Functorial desingularization of quasi-excellent schemes in characteristic zero:
the non-embedded case, Corollary 2.4.5 and Lemma 2.4.6, printed pages 16--17
(blueprint: lem-per-regular-morphism-formal-completion).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- Completing an ideal-compatible regular morphism of Noetherian quasi-excellent schemes
over the rationals gives regular ring maps on every pair of formal affine opens.
Source: Temkin, Corollary 2.4.5 and Lemma 2.4.6, printed pages 16--17
(blueprint: lem-per-regular-morphism-formal-completion).

Proof plan:
1. On ordinary affine charts, flatness and geometric regularity of the scheme fibres give
   regular coordinate ring maps. The fibre-product affine-spectrum description identifies
   their fibres, and the quasi-excellent-formal-affines lemma gives quasi-excellence and
   Noetherianity of the completions and all their formal affine opens.
2. For a chart map A to B, the completion map from B to its J-adic completion D is regular
   by the G-ring completion theorem. Compose to obtain regularity of A to D. The fibre
   rings are localizations of quotients of the Noetherian ring D, hence Noetherian.
3. Ideal containment induces the canonical compatible quotient maps, hence the map from
   the I-adic completion C of A to D. The extended J makes D complete by the completion
   modulo ideal theorem. Apply completed-base-regularity to obtain regularity of C to D.
   These are the maps used by adicFormalCompletionMap, so they glue.
4. Refine both charts to principal formal opens. Replace a source element t by t times
   the image of the target element s; the formal open is unchanged and the ordinary
   localization map exists. Localization, G-ring completion, regular composition and
   regular-through-localization, followed by completed-base-regularity, prove regularity
   of the map of completed localizations. Quasi-excellence of the ordinary localizations
   follows from finite-type permanence for G-rings and the finite-type definition of J-2.
5. For arbitrary formal affine opens, use formal-affine-principal-refinement to choose
   common principal neighbourhoods inside the original chart pairs. Step 4 and regular
   composition give regular maps from the target coordinate ring to the smaller source
   chart rings, covering the source formal affine.
6. At each maximal ideal of the source chart ring F, principal refinement supplies a
   faithfully flat localization above it. Apply the prime/maximal local criterion to the
   regular map to this smaller chart; descend regularity faithfully flatly to the local
   map into F at the chosen maximal ideal. The same local criterion now proves that the
   whole coordinate ring map is regular. No finite-type hypothesis on f occurs. -/
theorem regularMorphism_formalCompletion
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (_qX : X ⟶ Spec (CommRingCat.of (ULift.{u} ℚ)))
    (f : Y ⟶ X) [Flat f]
    (_hX : ∀ U : X.affineOpens, IsQuasiExcellent Γ(X, U))
    (_hY : ∀ V : Y.affineOpens, IsQuasiExcellent Γ(Y, V))
    (_hf : ∀ (x : X) (K : Type u) [Field K] [Algebra (X.residueField x) K]
      [Module.Finite (X.residueField x) K],
      IsRegularScheme (pullback (f.fiberToSpecResidueField x)
        (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) K)))))
    (I : X.IdealSheafData) (J : Y.IdealSheafData)
    (_hI : RingedSpace.IsCoherent X.toRingedSpace I.toModules)
    (_hJ : RingedSpace.IsCoherent Y.toRingedSpace J.toModules)
    (hIJ : I.comap f ≤ J) :
    IsRegularOnAdicFormalAffines (adicFormalCompletionMap f I J hIJ) := by
  sorry

end AlgebraicGeometry

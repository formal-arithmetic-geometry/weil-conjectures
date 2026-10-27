/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Localization.LocalizationLocalization
import WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism

/-!
# Relative Weil extension across codimension at least two

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, 4.4 Theorem 1, printed pp.109--110,
specialized to an open subscheme of the spectrum of a Dedekind domain
(blueprint: lem-sfb-relative-weil-codimension-extension).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

set_option autoImplicit false

/-- A morphism from a fibrewise dense open containing all points of local dimension at most
one in a smooth scheme over an open Dedekind base extends to the whole scheme when its target
is a smooth separated group scheme. Source: BLR, Néron Models, 4.4 Theorem 1, pp.109--110
(blueprint: lem-sfb-relative-weil-codimension-extension).

Proof: cover the open base `T` by principal opens. Noetherianity of `D` gives a finite
subcover, and principal localization gives affine Noetherian charts
(def-weil-pbc-noetherian-ring, lem-weil-pbc-principal-localization-open-immersion,
def-weil-open-immersion, lem-weil-pbc-localization-noetherian). The stalk at a point of
`T` is the corresponding localization of `D`, by restriction to the open and the affine
stalk identification (def-weil-open-immersion,
lem-weil-pbc-spec-local-ring-canonical-morphism). Localizations of the integrally closed
domain `D` are integrally closed domains (lem-weil-pbc-localization-normal-domain).
Thus `T` is normal Noetherian. Apply lem-sfb-relative-group-weil-extension to `T`, `X`,
`G`, `V` and `u`; its smoothness, separatedness, fibrewise density and codimension
hypotheses are exactly those below. The extension it supplies has the stated restriction.
Neither quasi-compactness nor separatedness of `X`, nor commutativity of `G`, is used. -/
theorem exists_extension_of_fiberwise_dense_of_codimension_two
    (D : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D] [IsIntegrallyClosed D]
    (E : Type u) [Field E] [Algebra D E] [IsFractionRing D E]
    (hD : ringKrullDim D = 1) (T : (Spec (CommRingCat.of D)).Opens) [Nonempty T]
    (X G : Scheme.{u}) (f : X ⟶ T.toScheme) (g : G ⟶ T.toScheme)
    [Smooth f] [Smooth g] [IsSeparated g] [GrpObj (Over.mk g)]
    (V : X.Opens) (u : V.toScheme ⟶ G) (hu : u ≫ g = V.ι ≫ f)
    (hdense : ∀ t : T.toScheme, Dense ((f.fiberι t) ⁻¹' (V : Set X)))
    (hcodim : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1 → x ∈ V) :
    ∃ ubar : X ⟶ G, ubar ≫ g = f ∧ V.ι ≫ ubar = u := by
  sorry

end AlgebraicGeometry

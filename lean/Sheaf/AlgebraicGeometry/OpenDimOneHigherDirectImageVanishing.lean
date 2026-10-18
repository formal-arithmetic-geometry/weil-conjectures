/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Constructible
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Flat.Localization
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineVanishing
import Sheaf.AlgebraicGeometry.LocalSpectrumOpenClassification
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism

/-!
# Higher direct images of retrocompact opens in local dimension at most one

Source: Stacks Project, Varieties, Tag 09N8, lemma-affine
(blueprint: lem-a1-open-dimension-one-higher-image-vanishing).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- If every local ring of a scheme is Noetherian of dimension at most one, the positive
higher direct images of a quasi-coherent module along a retrocompact open inclusion vanish.

Source: Stacks Project, Varieties, Tag 09N8, lemma-affine
(blueprint: lem-a1-open-dimension-one-higher-image-vanishing).

Proof:
1. Test vanishing at each stalk x. The affine-open stalk localization theorem
(lem-weil-pbc-affine-open-stalk-localization), together with localization flatness
(lem-weil-pbc-localization-flat), makes Spec O_{X,x} -> X flat. Retrocompactness makes
U.ι quasi-compact; its diagonal is an isomorphism, so it is quasi-separated. Flat base
change (lem-pc-flat-base-change-cohom) reduces the stalk to the pulled-back open immersion
into Spec O_{X,x}.
2. Apply lem-a1-local-spectrum-open-classification to this Noetherian local ring of
dimension at most one. If its closed point belongs to the pulled-back open, the open is
the whole spectrum and its inclusion has vanishing positive higher direct images.
Otherwise the open has finite discrete underlying space and is affine.
3. In the latter case its morphism to the affine local spectrum is affine. The pullback
of F is quasi-coherent, so lem-pc-affine-morphism-hi gives vanishing in every positive
degree. Both cases give zero stalks, hence the original higher direct image is zero. -/
theorem isZero_higherDirectImage_open_of_stalk_dimension_le_one
    (X : Scheme.{u}) (hnoeth : ∀ x : X, IsNoetherianRing (X.presheaf.stalk x))
    (hdim : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1)
    (U : X.Opens) (hU : IsRetrocompact (U : Set X))
    (F : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
    (hF : F.IsQuasicoherent) (p : ℕ) (hp : 0 < p) :
    IsZero (((RingedSpace.moduleDirectImage U.ι.toLRSHom.toShHom).rightDerived p).obj F) := by
  sorry

end AlgebraicGeometry

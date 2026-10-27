/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.DensePoints
import WeilConjectures.AlgebraicGeometry.ConstantLocalDimensionComponents
import Sheaf.RingTheory.HenselianSmoothAlgebraLifting
import Sheaf.AlgebraicGeometry.NowhereDenseDimensionDrop

/-! # Strict-local sections meeting dense opens in extended fibres

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, 2.3 Proposition 5 and
5.3 Lemma 7 and the field-extension paragraph in the proof of Lemma 6;
EGA IV₃, 11.10.7 (blueprint: lem-sfb-strict-local-sections-meet-dense-fibre-opens).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A smooth surjective finite-type scheme over a nonzero Noetherian strictly henselian
local ring has a section; in every field extension of every fibre, some section meets
any prescribed dense open. `SplitEpi p` packages a section and its section equation.

Source: BLR, Néron Models, 2.3 Proposition 5, p.47; 5.3 Lemma 7, pp.126--127;
the field-extension paragraph of the proof of 5.3 Lemma 6, pp.125--126;
EGA IV₃, 11.10.7 (blueprint: lem-sfb-strict-local-sections-meet-dense-fibre-opens).

Proof:
1. At the closed point, the residue field is separably closed. The nonempty smooth
   closed fibre has a rational point by `lem-pc-dense-separable-points`. Use
   `lem-sfb-smooth-space-dimension-strata` to choose an affine neighbourhood U of
   that point in a constant-relative-dimension stratum, of dimension n. Open
   restriction is smooth (`lem-pc-open-immersion-smooth-composition`), hence its
   coordinate algebra is smooth (`lem-weil-pbc-smooth-ring-map-iff-smooth-affine`).
2. Lift every closed-fibre rational point of U across the maximal-ideal henselian
   pair by `lem-trf-henselian-smooth-algebra-lifting`. Their values are dense by
   `lem-pc-dense-separable-points`; composing a lifted section with U → Y proves
   existence. Smoothness and nonemptiness of the fibres use
   `lem-pc-proper-base-change` and `lem-weil-pbc-surjective-base-change`.
3. Each point s specializes to the closed point. By
   `lem-sfb-section-value-closure-dimension-specialization`, the closure C of the
   section values in U_s has dimension at least n. Every component of U_s has
   dimension n by the strata lemma, `lem-wf-affine-noetherian-components` and
   `lem-sbc-constant-local-dimension-components`, so U_s has dimension n.
4. By `lem-sc-hilbert-nowhere-dense-dimension-drop`, C has nonempty interior V.
   Section values lying in V are dense in V and factor through V by
   `lem-weil-pbc-morphism-factors-through-open-subscheme`. Their induced L-points
   are dense in V_L by `lem-sfb-rational-density-field-extension`.
5. The open V_L remains nonempty and open in Y_L, using
   `lem-weil-pbc-open-immersion-base-change`, `lem-pc-field-extension-surjective`
   and `lem-weil-pbc-surjective-base-change`. Thus the dense open O meets V_L,
   and density there supplies the required section. The projection equations for
   `sectionBaseChange` identify its induced L-point with the selected point. -/
theorem strictLocal_sections_meet_dense_fibre_opens
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    [IsStrictlyHenselianLocalRing A] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of A))
    [Smooth p] [Surjective p] [LocallyOfFiniteType p] [QuasiCompact p] :
    Nonempty (SplitEpi p) ∧
      ∀ (s : Spec (.of A)) (L : Type u) [Field L]
        [Algebra ((Spec (.of A)).residueField s) L]
        (O : (pullback p
          (Spec.map (CommRingCat.ofHom (algebraMap ((Spec (.of A)).residueField s) L)) ≫
            (Spec (.of A)).fromSpecResidueField s)).Opens),
        Dense O.carrier →
          ∃ a : SplitEpi p,
            sectionBaseChange p a.section_ a.id
              (Over.mk (Spec.map
                (CommRingCat.ofHom (algebraMap ((Spec (.of A)).residueField s) L)) ≫
                  (Spec (.of A)).fromSpecResidueField s)) (default : Spec (.of L)) ∈ O := by
  sorry

end AlgebraicGeometry

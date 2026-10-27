module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.Defs.Filter
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions

import WeilConjectures.AlgebraicGeometry.Morphisms.Slicing
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Compactness.Compact
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty

/-!
# Quasi-compact selection in a fibrewise dense smooth open

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, §2.5, Lemma 3,
printed pp.56--57 (blueprint: lem-sfb-smooth-fibre-dense-quasi-compact-selection).

The inverse image of an open under `p.fiberι s` is the underlying open of its
scheme-theoretic base change to `Spec κ(s)`. Compactness is topological
quasi-compactness and imposes no separation condition.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A fibrewise dense open of a smooth quasi-compact scheme contains a quasi-compact
open that is still dense in every fibre. Neither the base nor the original open is
assumed quasi-compact, and empty schemes and empty fibres are allowed.

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, §2.5, Lemma 3,
printed pp.56--57 (blueprint: lem-sfb-smooth-fibre-dense-quasi-compact-selection).

Proof (the node's smooth-slicing argument):
1. For empty X take the empty open. Otherwise use `sbc-lem-slicing` to cover X
   by etale images of affine D_i, with smooth maps D_i → T_i to affine schemes
   etale over S, having sections and geometrically connected nonempty fibres.
   Etale maps are open (`lem-weil-pbc-etale-morphism-open-map`), so compactness
   of X selects finitely many charts.
2. Put E_i = e_i⁻¹(U). For t in T_i, the fibre F_{i,t} is integral and nonempty
   by `lem-trf-smooth-connected-fibre-normal-integrality`. Etale base change
   (`lem-weil-pbc-etale-scheme-base-change`) and the open singleton components
   of an etale fibre (`lem-weil-pbc-etale-fibre-discrete-separable-points`)
   identify F_{i,t} with an open in (D_i)_s, s = a_i(t). Its map to X_s is open,
   so fibrewise density of U makes (E_i)_t dense and nonempty in F_{i,t}.
3. Cover E_i by affine opens using `lem-weil-pbc-affine-opens-basis`.
   Smoothness gives flatness and local finite presentation (`lem-pc-smooth-flat`),
   hence openness (`lem-weil-pbc-flat-lfp-open`). Their images cover T_i.
   Compactness of affine T_i (`lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact`)
   selects finitely many. Their union B_i meets every F_{i,t}, and its open
   fibre is dense because F_{i,t} is irreducible.
4. Take W to be the union of the images of all these finitely many affine opens.
   It is open and lies in U. Each image is compact by
   `lem-weil-pbc-continuous-image-quasi-compact`, so W is compact. The maps
   B_i → X factor through the open subscheme W (`def-weil-open-immersion`);
   their base changes therefore factor through W_s (`def-pc-base-change`).
5. The retained etale charts cover every X_s by
   `lem-weil-pbc-etale-covering-base-change`. A nonempty open H in X_s lifts to
   a nonempty open in one (D_i)_s. Choose a point and its image t in T_i.
   Intersecting with the open integral fibre F_{i,t} gives a nonempty open,
   which meets (B_i)_t by step 3. Its image lies in H ∩ W_s. Thus W_s is dense
   in X_s; this is automatic for an empty fibre. -/
theorem Smooth.exists_isCompact_open_fibrewise_dense
    {X S : Scheme.{u}} (p : X ⟶ S) [Smooth p] [CompactSpace X]
    (U : X.Opens) (hU : ∀ s : S, Dense ((p.fiberι s) ⁻¹' (U : Set X))) :
    ∃ W : X.Opens, W ≤ U ∧ IsCompact (W : Set X) ∧
      ∀ s : S, Dense ((p.fiberι s) ⁻¹' (W : Set X)) := by
  sorry

end AlgebraicGeometry

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q150
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.KrullDimension
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.Irreducible
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.ExistsAmpleOfDimLEOne
import Sheaf.AlgebraicGeometry.AmpleFiniteSetAffine
import Sheaf.AlgebraicGeometry.AmpleFinitePrincipalAffine
import WeilConjectures.Mathlib.Topology.KrullDimension

/-! # Two affine opens separating isolated singular points of a curve

Source: Stacks Project, Examples of Deformation Problems, Tag 0DZP,
`lemma-curve-isolated`, first paragraph of the proof.
(blueprint: lem-sfb-isolated-curve-two-affine-cover).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A separated finite-type scheme of dimension at most one over a field, smooth away from
finitely many closed points, admits a two-affine cover separating those points. The open
avoiding them and the intersection are smooth, and all three opens are of finite type.
Empty schemes and empty marked sets are permitted.

Source: Stacks Project, Tag 0DZP, `lemma-curve-isolated`, proof, first paragraph.
(blueprint: lem-sfb-isolated-curve-two-affine-cover).

Proof:
1. A field is Noetherian (`def-weil-pbc-noetherian-ring`), so its affine spectrum
   (`def-weil-affine-spectrum`) is locally Noetherian (`pqf-def-locnoeth`) and compact.
   Finite type makes X Noetherian (`lem-weil-pbc-finite-type-over-noetherian`).
2. There are finitely many irreducible components
   (`lem-weil-pbc-noetherian-finitely-many-components`), each with a unique generic point
   (`lem-sc-scheme-sober`). By `lem-sc-dim-one-ample-invertible`, X has an ample invertible
   module. Apply `lem-sc-ample-finite-set-affine` to P together with these generic points
   to obtain an affine open V containing them all.
3. Put F = X minus V. If F contained a strict chain A < B of irreducible closed subsets,
   `lem-sc-irreducible-components-cover` would put B inside a component C. Its generic
   point lies in V, so B < C, contradicting the dimension bound
   (`def-kun-topological-krull-dimension`). Thus F has dimension at most zero, and
   `lem-sc-dim0-finite` makes it a finite set of closed points.
4. The complement W of P is open, contains F, and is smooth over k by the local smoothness
   hypothesis. If F is empty, take U empty, affine as the spectrum of the zero ring
   (`def-weil-affine-spectrum`, `def-pc-scheme`). Otherwise apply
   `lem-sc-ample-finite-principal-affine` to F inside W. This yields an affine U containing
   F and avoiding P. In either case U and V cover X.
5. Since X is separated over the affine base Spec k, the intersection of its two affine
   opens is affine (`lem-weil-pbc-separated-affine-open-intersection`).
6. Each of U, V and their intersection is compact
   (`lem-weil-pbc-affine-scheme-qcqs`), hence quasi-compact over the one-point base. The
   structure map of X is quasi-separated (`lem-pc-separated-quasi-separated`), so
   `lemma-nagata-open-immersion-qc-over-separated-target` makes their inclusions into X
   quasi-compact. They are finite type (`lem-weil-pbc-qc-open-immersion-finite-type`),
   and composition with the structure map preserves finite type
   (`lem-sfb-finite-type-composition-base-change`).
7. Both U and its intersection with V are open in W. Their maps to Spec k are smooth by
   `lem-pc-open-immersion-smooth-composition`. These steps allow P and X to be empty.
-/
theorem exists_isolated_curve_two_affine_cover
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hdim : topologicalKrullDim X ≤ 1) (P : Set X) (hP : P.Finite)
    (hclosed : ∀ x ∈ P, IsClosed ({x} : Set X))
    (hsmooth : ∀ x ∉ P, ∃ W : X.Opens, x ∈ W ∧ Smooth (W.ι ≫ f)) :
    ∃ U V : X.Opens,
      IsAffineOpen U ∧ IsAffineOpen V ∧ U ⊔ V = ⊤ ∧
      P ⊆ (V : Set X) ∧ Disjoint (U : Set X) P ∧ IsAffineOpen (U ⊓ V) ∧
      LocallyOfFiniteType (U.ι ≫ f) ∧ QuasiCompact (U.ι ≫ f) ∧
      LocallyOfFiniteType (V.ι ≫ f) ∧ QuasiCompact (V.ι ≫ f) ∧
      LocallyOfFiniteType ((U ⊓ V).ι ≫ f) ∧ QuasiCompact ((U ⊓ V).ι ≫ f) ∧
      Smooth (U.ι ≫ f) ∧ Smooth ((U ⊓ V).ι ≫ f) := by
  sorry

end AlgebraicGeometry

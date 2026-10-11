/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Sheaf.AlgebraicGeometry.QuasiFiniteMorphism

/-!
# Quasi-finite morphisms and finite fibres

Source: Stacks Project, Morphisms of Schemes, Lemma 29.21.10, Tag 02NH
(blueprint: pqf-lem-qf-finitefibres).
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- A morphism is quasi-finite exactly when it is locally of finite type, of finite type,
quasi-compact, and has finite fibres. Finite type is the conjunction of locally of finite
type and quasi-compact; its redundant occurrence is retained from the blueprint.
Source: Stacks Project, Lemma 29.21.10, Tag 02NH (blueprint: pqf-lem-qf-finitefibres).

Proof: In the forward direction, `pqf-def-quasifinite` gives finite type and isolated
points of each fibre, and `def-weil-pbc-scheme-conventions` gives local finite type and
quasi-compactness. By `lem-pc-quasi-compact-base-change`, each fibre over a residue field
is quasi-compact. Its open singletons cover it, so a finite subcover makes it finite.
The homeomorphism in `def-pc-scheme-fibre` identifies it with the set-theoretic fibre.

Conversely, local finite type and quasi-compactness give finite type. Choose affine
neighbourhoods of a point and its image. By `lem-weil-pbc-lft-affine-pairs` their ring map
is of finite type. The fibre algebra is finitely generated over the residue field.
By `lem-weil-pbc-open-fibre-product` and `lem-weil-pbc-fibre-product-affine-spectra`, its
spectrum is an open part of the scheme fibre. The homeomorphism of `def-pc-scheme-fibre`
and finite fibres make this spectrum finite. By `lem-sc-lft-over-field-jacobson-space`,
closed points in each point closure are dense. They are a finite closed set, so exhaust
that closure; hence every point is closed. A finite space with all points closed is
discrete, so the chosen fibre point is isolated. Then
`lem-weil-pbc-isolated-fibre-point-quasi-finite-affine-pairs` gives quasi-finiteness at
the point. This holds at every point, giving local quasi-finiteness in the sense of
`pqf-def-quasifinite`. Finally `pqf-lem-qf-locqf-qc` gives quasi-finiteness. -/
theorem isQuasiFinite_iff_finiteFibres {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) :
    IsQuasiFinite f ↔
      AlgebraicGeometry.LocallyOfFiniteType f ∧
        (AlgebraicGeometry.LocallyOfFiniteType f ∧ AlgebraicGeometry.QuasiCompact f) ∧
        AlgebraicGeometry.QuasiCompact f ∧ HasFiniteFibres f := by
  sorry

end AlgebraicGeometry.Scheme.Hom

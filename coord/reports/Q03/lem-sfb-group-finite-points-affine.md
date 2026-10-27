## Worker report

States `AlgebraicGeometry.GrpObj.exists_isAffineOpen_fin_points` in
`Sheaf.AlgebraicGeometry.GroupFinitePointsAffine`. The only proof is the expected
`sorry`. No definitions, new nodes, dependency repairs, or statement corrections.

The source was read in `literature/stacks-project/groupoids.tex`,
Tag 0B7S, `lemma-points-in-affine`, including its proof. It agrees with the node.

Hypothesis and conclusion correspondence:

- Algebraically closed field k: `(k : Type u) [Field k] [IsAlgClosed k]`.
- Group scheme H over k: `(H : Over (Spec (.of k))) [GrpObj H]`.
  This is exactly the representation required by def-sc-group-scheme, not a
  commutative group object. Its structure morphism is `H.hom`.
- Locally of finite type: `[LocallyOfFiniteType H.hom]`. There is no
  `QuasiCompact H.hom` assumption and no finite-type strengthening.
- Integer n at least zero: `(n : ℕ)`; this parametrizes precisely the
  nonnegative integers, including zero.
- List of k-morphisms: `(h : Fin n → (Spec (.of k) ⟶ H.left))` together with
  `(hh : ∀ i : Fin n, h i ≫ H.hom = 𝟙 (Spec (.of k)))`.
  The equations are precisely the condition of being morphisms over k.
- An open subscheme U contained in H: `∃ U : H.left.Opens`, with the canonical
  open subscheme `U.toScheme` and inclusion `U.ι`.
- Affineness: `IsAffineOpen U`, Mathlib's affineness of that open subscheme.
- All marked morphisms factor: `∀ i : Fin n, ∃ hU : Spec (.of k) ⟶ U.toScheme,
  hU ≫ U.ι = h i`. Each factor is automatically over k: composing its equation
  with `H.hom` and using `hh i` gives
  `hU ≫ (U.ι ≫ H.hom) = 𝟙 (Spec (.of k))`.
- Repetitions are permitted because h need not be injective. No connected,
  smooth, reduced, separated or quasi-compact hypothesis has been added.

Statement dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (def-weil-field).
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, explicitly identified
  by def-weil-algebraic-closure's Mathlib match; a chosen AlgebraicClosure is
  unnecessary because the node assumes k itself algebraically closed.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, specialized
  to `Over (Spec (.of k))` as its node requires. Read the recorded interface
  and the convention docstring of
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
  `Mathlib.AlgebraicGeometry.Group.Affine` supplies the group-scheme context.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and schemes.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`
  and the canonical open-subscheme interface; `U.ι` is the open inclusion.
- `Mathlib.AlgebraicGeometry.AffineScheme`: `AlgebraicGeometry.IsAffineOpen`,
  literally affineness of the open subscheme, not a newly defined predicate.

The public imports expose these statement notions. The plain proof imports
record the existing proof plan:

- `Sheaf.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent`:
  `AlgebraicGeometry.locallyAlgebraicGroup_identityComponent`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Basic`:
  `AlgebraicGeometry.GrpObj.mulLeftIso`, `mulRightIso`, `mulRight`, `conjBy`,
  `translate`, and the accompanying left-translation interface.
- `WeilConjectures.AlgebraicGeometry.IsAffineOfFiniteClosedCover`:
  `AlgebraicGeometry.isAffine_of_finite_closed_cover`.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents` and irreducibility.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- The public imports also supply the remaining proof dependencies:
  `IsOpenImmersion.lift`, `lift_fac`, `lift_uniq` from OpenImmersion;
  `LocallyOfFiniteType.jacobsonSpace` from FiniteType;
  `residueFieldIsoBase` and `SpecMap_residueFieldIsoBase_inv` from
  `Mathlib.AlgebraicGeometry.AlgClosed.Basic`; and `Scheme`.

The theorem docstring transcribes all five proof steps: finite component
partition using the identity-component theorem; intersection of translated
opens in the irreducible component; a rational point from Jacobson density
and the closed residue field; translation back with the noncommutative order
preserved; and finite disjoint affine assembly with open factorization.

Edge cases checked mathematically before writing:

- n = 0: choose the empty open, affine as Spec of the zero ring; the factor
  condition is vacuous. No positivity assumption on n occurs.
- Repeated points: allowed by the family representation, no distinctness condition.
- Infinitely many components/non-quasi-compact H: only finitely many marked
  components are used; H itself is not assumed quasi-compact.
- Infinitesimal groups such as alpha_p and mu_p: no reducedness or smoothness
  is required, and the proof retains the open component's nilpotents.
- Abelian varieties: H need not be affine; the conclusion concerns only U.
- Noncommutative disconnected groups: neither a commutative group structure
  nor a connectedness assumption is present. The translation product order
  follows the source and node.
- Arbitrary characteristic and universe u are allowed. The field, schemes,
  rational source and open subscheme share the standard Scheme universe.
- An empty group scheme over a field supplies no group unit, so it is not
  silently excluded by a new hypothesis; the existing GrpObj structure already
  accounts for this.

Searches made through the prescribed msearch tool:

1. LeanFinder: `Every finite list of rational points of a group scheme locally
   of finite type over an algebraically closed field factors through a common
   affine open subscheme`. Eight hits concerned affine transition limits,
   finite morphisms, products of points of affine schemes and finite-type
   ring maps. None states this result.
2. Loogle: `"IsAffineOpen", "GrpObj"`. Zero hits.
3. Mathlib grep in AlgebraicGeometry:
   `finite.*[Pp]oint.*[Aa]ffine|[Aa]ffine.*finite.*[Pp]oint|[Gg]rpObj.*[Aa]ffineOpen`.
   Zero hits.
4. LeanSearch: `Finite rational points in a locally finite type group scheme
   over an algebraically closed field lie in one affine open`. Eight hits:
   affine covers/opens, finite morphisms and local finite type. None is a
   common affine-open assertion for a group scheme.
5. `rg` in `lean/WeilConjectures` and `lean/Sheaf` for affine/finite/point
   combinations and GrpObj/IsAffineOpen: found unrelated affine-line finite
   points, projective descent, finite generic points, and group
   quasi-projectivity. These have different hypotheses. The existing
   locally-separated group-space module cites this node in its proof but
   does not state it. Searching the item id in WeilConjectures found no match.
6. `rg` for `exists_isAffineOpen_fin_points`, `finitePoints_affineOpen`, and
   `group_finite_points_affine` in Mathlib, WeilConjectures, Sheaf and the
   upstream declaration-name index found no declaration-name conflict.

Validation: the delivered module compiled through scompile.py in both its
sandbox and library contexts with no errors or unexpected warnings.
No STATEMENT-DISPUTED flag or node fault remains.

## Second reading by Q03

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Worker report

The item is stated in `Sheaf.AlgebraicGeometry.RegularDimensionFunctionPullback` as
`AlgebraicGeometry.Scheme.regular_pullback_isGeometricDimensionFunction`.
The original item statement is unchanged. Its sole postponed proof is `sorry`;
the docstring contains all eight DAG proof steps and their supporting nodes.

Clause-by-clause rendering:

- Schemes P, X and the specified morphism r: `{P X : Scheme.{u}} (r : P ⟶ X)`.
- Both schemes Noetherian: `[IsNoetherian P] [IsNoetherian X]`.
- Excellence: `hP` and `hX` assert `IsExcellent Γ(_, U)` on every affine open,
  using the recorded excellent-ring definition. Excellence is local, so this
  is the usual excellent-scheme condition without introducing another predicate.
- Regularity: `[Flat r]` and `hregular`, testing `IsRegularScheme` on the pullback
  of `r.fiberToSpecResidueField x` along Spec of every finite field extension.
  `Module.Finite (X.residueField x) L` is precisely finiteness of that extension;
  the identity extension is included. No finite type or presentation binder occurs.
- The given integer-valued function and its dimension-function hypothesis:
  `(δX : X → ℤ) (hδX : IsGeometricDimensionFunction X δX)`.
- The local fibre ring at p is exactly
  `(r.fiber (r p)).presheaf.stalk (r.asFiber p)`. The canonical `asFiber`
  comes from Mathlib's fibre homeomorphism, not an arbitrary choice of a point.
- `∃ b : P → ℕ` with the displayed equality in `WithBot ℕ∞` identifies every b p
  with that actual Krull dimension. These nonzero Noetherian local rings have
  finite dimension, so such natural representatives exist and are unique.
  This conclusion merely makes the node's integer subtraction well typed;
  no finiteness assumption is added, and infinity is not silently sent to zero.
- The second conjunct is the exact proposed function
  `IsGeometricDimensionFunction P (fun p ↦ δX (r p) - (b p : ℤ))`.
- In the new definition, the target geometric point is `barX`, the source is
  `a` into `strictHenselizationScheme barX`, and immediacy is
  `topologicalKrullDim (closure {a (closedPoint Ωy)}) = 1`.
  The equation evaluates δ at the source image under the canonical structural
  map and at `barX (closedPoint Ωx)`, giving source = target + 1.
  ILO XIV 2.1.1 identifies geometric points of the strict localization with
  specialization morphisms, so this retains every immediate geometric specialization.

Dependency declarations read and used:

- `Sheaf.RingTheory.ExcellentRing`: `IsExcellent` (including its quasi-excellent
  and universally catenary constituents).
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`;
  `Flat.iff_flat_stalkMap` verifies the dependency's stalkwise description.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`,
  exactly `IsLocallyNoetherian X ∧ IsRegular X`.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`,
  `fiberToSpecResidueField`, `asFiber`, and the defining fibre homeomorphism.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.SpecToEquivOfField`;
  geometric points use algebraically closed fields and actual Spec morphisms.
- `Sheaf.AlgebraicGeometry.StrictHenselization`: `strictHenselizationScheme`,
  now an abbreviation of the published strict localization.
- `WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap`:
  `Scheme.strictHenselizationStructuralMap`, read with `scompile.py --source`.
  Its defining existence theorem characterizes the common structural composite.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.

Proof-only imports cover the recorded fibre stalk quotient and Mathlib flat
base change, flat torsion-freeness, and flat height formula. The other five
non-Mathlib proof nodes have no Lean record or closed upstream audit, so there
is no published proof module to import; their use is retained in the proof docstring.
No dependency module is replaced or copied.

Edge cases: P empty makes both quantified conclusions vacuous; X empty forces
P empty. The identity map has zero-dimensional field fibres and gives δX itself.
For maps to a field, the function is a constant minus fibre-local dimension,
with the negative sign required by the source. Zero-dimensional fibres subtract
zero. There is no global finite-dimensionality assumption: every relevant local
Noetherian ring is finite dimensional, even if dimensions are not uniformly bounded.
All universes are explicit and auto-implicit binding is disabled. Field tests live
in the scheme universe, which includes all finite residue extensions up to isomorphism.

Searches: `msearch.py` LeanSearch query "A dimension function on a scheme decreases
by one along every immediate geometric specialization" found only Krull dimension,
specialization and smoothness results; LeanFinder queries on regular pullback
and on dimension functions returned smooth relative dimension and generic
specialization lemmas, not a match. Loogle `"ringKrullDim", "Flat"` returned zero
hits. Mathlib grep `dimensionFunction|IsDimensionFunction|dimension.function`
returned zero hits. The same upstream grep and the exact item-id grep found no
upstream declaration. Project grep found only explanatory comments and the
downstream RegularSpecializationGeometry module; importing its theorem would
be circular. Searching DAG definition titles found no dimension-function node;
`tools/blueprint_refs.py search 'dimension function'` found zero blueprint nodes.
Exact outputs for the new notion are in its `mathlib_searches`.

Source checked directly: the local ILO PDF, extracted with pdftotext, XIV
Definitions 2.1.1--2.1.2 (p.209), Proposition 2.5.4 (pp.217--218), and XVII
Definition 2.1.1. They confirm the sign, geometric immediacy, and absence of a
finite-type restriction. No statement dispute or correction was necessary.

Validation: both delivered files compiled cleanly through `scompile.py Q29
lem-per-regular-dimension-function-pullback`, separately in dependency order.

## New nodes

`def-per-geometric-dimension-function` supplies the missing standalone predicate,
in `Sheaf.AlgebraicGeometry.GeometricDimensionFunction`. It is real predicate
data, with no sorry. Its source is ILO XVII Definition 2.1.1 and XIV
Definitions 2.1.1--2.1.2. It reuses geometric points, strict localization, its
canonical structural map, and Mathlib topological Krull dimension. The searches
above establish that no existing definition node or Lean declaration owns it;
potential-dualizing nodes mention it but do not define it independently.

## Second reading by Q29

I reopened the written signatures and the node and checked the scheme, morphism,
Noetherianity, excellence, flatness and finite-extension fibre regularity binders
one by one. I checked both conclusion conjuncts against b_r and δ_P, including
the integer coercions and the negative sign. The natural representative is in
the conclusion, not an extra hypothesis. I also checked the new predicate's
strict-local source point, canonical structural image, one-dimensional closure,
and source = target + 1 equation against the two ILO definitions. No mismatch
was found and no statement changed. This is the dispatched worker's own second
pass; the brief assigns the independent review to the maintainer and prohibits
starting another agent.

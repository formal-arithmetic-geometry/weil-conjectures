## Worker report

The module `Sheaf.AlgebraicGeometry.SeparatedLqfAffineFiniteSet` states
`AlgebraicGeometry.exists_isAffineOpen_of_finite_of_isLocallyQuasiFinite`.
Its only theorem has proof `sorry`; no definitions or proofs are added.
The source read is Stacks Project, `more-morphisms.tex`, Tag 07S0,
`lemma-separated-locally-quasi-finite-over-affine`, including its proof (lines 12662 ff.).
The node agrees with that source and needs no correction.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Schemes X and Y are `{X Y : Scheme.{u}}`, with the explicitly declared universe `u`.
  The morphism is `(f : X ⟶ Y)`.
- Y affine is `[IsAffine Y]`. Mathlib's class says the canonical map to the spectrum of
  global sections is an isomorphism, equivalently the node's affine scheme condition.
- f separated is `[IsSeparated f]`. The class field is precisely
  `IsClosedImmersion (pullback.diagonal f)`, the node's closed diagonal condition.
- f locally quasi-finite is `(hf : f.IsLocallyQuasiFinite)`, using the dependency's
  recorded Stacks predicate, not Mathlib's predicate lacking local finite type.
  Its definition is `∀ x : X, IsQuasiFiniteAtPoint f x`; the latter supplies affine
  neighbourhoods, finite type, and ring quasi-finiteness at the corresponding prime.
- Every finite subset is `(E : Set X) (hE : E.Finite)`; no closedness or distinctness
  assumption is made on the points.
- An open subscheme W is `W : X.Opens`, carrying the canonical restricted scheme
  structure; affineness is `IsAffineOpen W`, defined as affineness of that open scheme.
- Containing E is `E ⊆ W`, with W coerced to its underlying set.
- The conclusion is the existential `∃ W : X.Opens, IsAffineOpen W ∧ E ⊆ W`.
- No quasi-compactness, Noetherianity, finite-type assumption on X, nonemptiness,
  or extra assumption on E is present. `autoImplicit false` checks all binders.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and `AlgebraicGeometry.Scheme.Hom` (structure declarations and docstrings).
- `def-weil-affine-spectrum`: the same module, `AlgebraicGeometry.Spec` and
  `AlgebraicGeometry.Spec.map`; affineness uses `AlgebraicGeometry.IsAffine` and
  `IsAffineOpen` from `Mathlib.AlgebraicGeometry.AffineScheme` (lines 59 and 251).
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, whose
  separatedness notion is `AlgebraicGeometry.IsSeparated` in `Morphisms.Separated`
  (lines 42–46). Properness itself is not assumed.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, its projections, and universal lift, read at
  lines 85–130. Separatedness uses this fibre product through its diagonal.
- `pqf-def-quasifinite`: `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`,
  `AlgebraicGeometry.Scheme.Hom.IsLocallyQuasiFinite`, and the full definition and
  docstring of `IsQuasiFiniteAtPoint` on which it depends.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`. The conclusion uses the canonical open
  subscheme of an `X.Opens`, not an arbitrary map.

The module also imports every recorded proof dependency's available module. Mathlib
leaves are imported from ResidueField, AffineScheme, Morphisms.QuasiSeparated,
Morphisms.ClosedImmersion, Morphisms.FinitePresentation, Spectrum.Prime.Topology,
and Ideal.Operations. The project proof modules are
`WeilConjectures.AlgebraicGeometry.IsLocallyQuasiFiniteResLE`,
`WeilConjectures.AlgebraicGeometry.LocallyOfFiniteTypeOfIsLocallyQuasiFinite`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine` (both the relative definition
and Zariski main theorem input). Their recorded signatures and docstrings were read.
Proof-only imports are not public. The theorem docstring records all six steps of the
accepted DAG proof: empty case; finite affine union; restriction; quasi-affineness;
prime avoidance in an ambient spectrum; pullback of the principal affine open.

Edge cases checked mathematically:

- E empty: the empty open is affine (spectrum of the zero ring), even for nonempty X.
- X empty: its only finite subset and the chosen affine open are empty.
- Y empty: a morphism into Y forces X empty; no nonempty case is lost.
- Arbitrary nonclosed points, including a generic point and a closed point of a DVR,
  are allowed; the proof uses prime ideals without a maximality assumption.
- An infinite disjoint union of copies of an affine target mapping by the identity
  is allowed: X need not be quasi-compact, and only finitely many components are
  required for any fixed E.
- The doubled origin over the affine line is excluded by separatedness, as required;
  no unintended affine-neighbourhood theorem for nonseparated X is stated.
- There is no characteristic condition and no restriction to Noetherian rings.

Searches actually run before writing (through `msearch.py`, group Q36, this item):

- LeanFinder: `Every finite subset of a scheme separated locally quasi-finite over an
  affine scheme is contained in an affine open`. Eight hits: finite morphisms,
  quasi-finite definitions, quasi-affine basic covers, and compact-open finite affine
  unions; no exact theorem.
- Loogle: `"IsSeparated", "IsAffineOpen"`. Zero hits.
- Mathlib grep: `finite.*[aA]ffine|[aA]ffine.*finite|07S0`, directory AlgebraicGeometry.
  Twenty-five hits concern finite-type affine charts, quasi-compact covers and finite
  morphisms; none is the finite-set neighbourhood theorem.
- LeanSearch: `A finite subset of a scheme separated and locally quasi-finite over an
  affine scheme lies in an affine open`. Eight hits include `IsAffineOpen`,
  `Scheme.affineOpens`, finite morphisms, and finite affine unions; no exact theorem.
- Local `rg` in `lean/WeilConjectures` and `lean/Sheaf` for Tag 07S0, the source label,
  finite sets of points, affine neighbourhoods, and `exists_isAffineOpen` names.
  The upstream prime-avoidance helper `IsAffineOpen.exists_basicOpen_le_of_finite`
  requires an existing ambient affine open; it does not state this item.
  `exists_isAffineOpen_of_finite_projective` in
  `Sheaf.AlgebraicGeometry.ProjectiveFiniteAffineNeighbourhood` assumes an affine
  morphism into projective space and is not an exact match. Generic-point results
  in upstream Properties/Limits have different point restrictions.
- `grep -rn` of the item's id in `lean/WeilConjectures` returned no attachment.
- The proposed declaration name was searched in Mathlib, WeilConjectures, Sheaf,
  and `dag/lean_names_upstream.json`: no collision.

There are no disputed statements, new nodes, or dependency-interface faults.

Validation: `scompile.py Q36 lem-sfb-separated-lqf-affine-finite-set` compiled the
module in both sandbox and library contexts, at 1.4 and 1.5 seconds, with no errors
or disallowed warnings. The node's `lean.statement` is extracted verbatim from the
module's signature. The node is otherwise unchanged.

## Second reading by Q36

No second worker was started, following the dispatcher's explicit instruction.
The maintainer's independent review is the delivery's second reading.

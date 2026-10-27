## Worker report

The module `Sheaf.AlgebraicGeometry.ComponentwiseFiniteSetAffineNeighbourhood` states
`AlgebraicGeometry.exists_isAffineOpen_of_componentwise_finite_set`, with its proof
left as `sorry`. No definitions, helper theorems, or additional nodes are introduced.
The source read is Stacks `literature/stacks-project/varieties.tex`, Tag 09NM,
label `lemma-finite-set-codim-1-points-in-affine-per-component`, statement and full
proof (lines 9083–9136), and the following Tag 09NN reduction sentence.

Clause-by-clause correspondence:

- An arbitrary scheme is `(X : Scheme.{u})`, with explicitly bound universe `u`.
- Finitely many irreducible components is
  `(hcomponents : (irreducibleComponents X).Finite)`. This avoids choosing an
  enumeration; it is equivalent to the finite list in the node, including the
  empty list. Mathlib components are maximal nonempty irreducible subsets and
  are closed (`isClosed_of_mem_irreducibleComponents`).
- A finite subset is `(T : Set X) (hT : T.Finite)`.
- Each reduced induced closed component is represented by a closed subset
  `C : TopologicalSpace.Closeds X` with `(C : Set X) ∈ irreducibleComponents X`,
  and the existing construction `(Scheme.IdealSheafData.vanishingIdeal C).subscheme`.
  Every component has exactly one such closed-subset representation, so this
  quantification neither loses components nor asks for other closed subsets.
- The per-component affine neighbourhood is the existential `U` in that
  subscheme's `Opens`, with `IsAffineOpen U`.
- Containment of `T ∩ C` is
  `(Scheme.IdealSheafData.vanishingIdeal C).subschemeι ⁻¹' T ⊆ (U : Set _)`.
  The inclusion is a closed embedding with image `C`, by the recorded
  `reduced_induced_closed_subscheme`; hence this preimage is precisely the
  part of `T` lying on `C`, as points of its reduced induced subscheme.
- The conclusion is `∃ V : X.Opens, IsAffineOpen V ∧ T ⊆ (V : Set X)`.
- There are no separatedness, Noetherianity, reducedness, dimension,
  quasi-compactness, nonemptiness, or base-field hypotheses.

Statement dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Spec` (and `Spec.map`); the standard scheme and affine
  spectrum interfaces, available through the public imports.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents` (line 107), and
  closedness of its members (line 111).
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`:
  `AlgebraicGeometry.Scheme.IdealSheafData.reduced_induced_closed_subscheme`.
  Its full signature and proof docstring were read. Its real construction uses
  Mathlib `Scheme.IdealSheafData.vanishingIdeal` and `subscheme`/`subschemeι`,
  whose source and docstrings were also read. The public Mathlib subscheme
  import exposes the construction needed in this statement; no copy is made.
- `Mathlib.AlgebraicGeometry.AffineScheme`: `IsAffineOpen` is affineness of
  the restricted open scheme, exactly the node's affine-open requirement.

Recorded proof dependencies are imported privately where already stated:
`WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism`,
`WeilConjectures.AlgebraicGeometry.ThickeningAffineScheme`,
`WeilConjectures.AlgebraicGeometry.IsAffineOfFiniteClosedCover`, and
`Mathlib.RingTheory.Ideal.Operations` (`Ideal.subset_union_prime`). Closed
immersions and the affine basic-open/residue-field dictionary are already
available from the statement imports. Their recorded signatures were read.
`lem-trf-quotient-lift-finite-prime-avoidance` currently has no Lean record,
no Mathlib match, and no closed upstream audit: its proof-only import is
therefore omitted. It is not needed to type the present statement. The
theorem docstring retains all six proof steps, including that dependency,
the symmetric-shrinking typo correction, and the reduced-structure uniqueness
argument at the overlap.

Edge cases checked before writing: for empty `X`, its set of components and
`T` are empty, the component hypothesis is vacuous, and the empty open is
affine. For empty `T` in any `X`, the empty affine open works both locally
and globally. Zero components force `X` empty because every point belongs
to a component. One component gives exactly the affine-open assumption on
its reduction; the thickening lemma accounts for nilpotents in `X`.
Components meeting in points of `T` impose both local containment requirements;
using the inclusion's preimage preserves these points. Finite components do
not imply quasi-compactness, and none is assumed. The universe is arbitrary.
No statement correction or disputed statement was needed.

Searches actually run with `msearch.py NN
lem-trf-componentwise-finite-set-affine-neighbourhood`:

- `leanfinder`: "A finite subset of a scheme has an affine open neighbourhood
  if it does on each of finitely many reduced irreducible components".
  Eight hits: affine covers, affine-open bases, compact-open finite unions.
  None assembles one affine neighbourhood from component neighbourhoods.
- `loogle`: `AlgebraicGeometry.IsAffineOpen, irreducibleComponents`.
  Successful query, zero hits.
- `grep`: `(irreducible|component).*(affine|Affine)|(affine|Affine).*(irreducible|component)`
  in `AlgebraicGeometry`. Twelve hits: geometrically reduced schemes,
  Noetherian affine charts, affine cover components, and finite morphisms;
  no exact statement.
- `leansearch`: "A finite set of points has a common affine open neighbourhood
  if it has one in every reduced irreducible component of a scheme with
  finitely many irreducible components". Eight hits: one-point affine bases,
  affine covers and reduction to a one-point affine neighbourhood; no match.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` by the node id and
  component/affine and finite-set/neighbourhood vocabulary, and `grep -rn`
  of the exact node id in `lean/WeilConjectures`: no exact statement.
  Nearby upstream `Mathlib/AlgebraicGeometry/Properties` and `Limits`
  results concern generic points (and quasi-separated hypotheses), not
  arbitrary finite subsets with this componentwise hypothesis.
- `rg` of the intended declaration name in Mathlib, both project roots and
  `dag/lean_names_upstream.json`: no collision.

Validation: `scompile.py NN lem-trf-componentwise-finite-set-affine-neighbourhood`
compiled the delivered module in both sandbox and library modes, in 2.0 s
and 1.5 s respectively, with no diagnostics. All binders and the universe
are explicit. The item node copy changes only `lean`; its recorded signature
is extracted verbatim from the module.

## Second reading by NN

I reread the node, the Stacks statement and the completed signature. This
is the assigned worker's second pass; the maintainer performs the independent
review under the dispatcher brief. The four inputs match the node: arbitrary
`X`, finite components, finite `T`, and affine opens on each reduced induced
component containing the preimage of `T`. In particular, quantifying over
closed subsets with the component membership guard does not assert affine
neighbourhoods on every closed subset. The conclusion is one affine open of
the original `X`, rather than only its reduction or a union of affine opens.
The empty cases remain admitted; no typeclass assumption introduces an extra
geometric restriction. No mismatch was found and no statement was changed.

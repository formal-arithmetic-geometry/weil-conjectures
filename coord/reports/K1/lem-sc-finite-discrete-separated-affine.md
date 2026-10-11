## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteDiscreteSeparatedAffine` states
`AlgebraicGeometry.isAffine_of_finite_discrete_of_separated`, with exactly one
`sorry` and no proved declarations or new definitions. The node is unchanged
outside its `lean` record.

Hypothesis and conclusion correspondence:

- A scheme Y: `(Y : Scheme.{u})`, with an explicitly declared arbitrary universe `u`.
- Quasi-compact: `[CompactSpace Y]`, referring to the underlying topological space,
  with no Hausdorff requirement.
- Structure morphism to Spec Z separated: `[IsSeparated (terminal.from Y)]`.
  Mathlib constructs the terminal scheme from the spectrum of the initial
  commutative ring (the universe lift of Z) in `Mathlib.AlgebraicGeometry.Limits`.
  Thus its unique structure morphism is the specified morphism to Spec Z,
  up to the canonical terminal-object isomorphism. Separatedness is invariant
  under this isomorphism; no arbitrary base scheme or morphism is introduced.
- Underlying space finite: `[Finite Y]`; no enumeration or nonemptiness is assumed.
- Underlying space discrete: `[DiscreteTopology Y]`; this concerns the actual
  topology of the scheme, not a topology supplied independently.
- Y affine: `IsAffine Y`, Mathlib's canonical map to the spectrum of global
  sections being an isomorphism, equivalently isomorphism to a ring spectrum.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme` (structure/docstrings at lines 35–78).
- `def-weil-pbc-quasi-compact-scheme`: `CompactSpace`,
  `Mathlib.Topology.Defs.Filter` (lines 279–284), no separation condition.
- `def-weil-proper-morphism`: only its separatedness clause is needed.
  The node's recorded `IsProper` extends the very `IsSeparated` used here;
  its searches identify `AlgebraicGeometry.IsSeparated`,
  `Mathlib.AlgebraicGeometry.Morphisms.Separated` (lines 42–47), defined by
  closed immersion of the diagonal. We use that existing constituent notion,
  not properness, which would add finite-type and universally-closed conditions.
  Both the `IsProper` signature/docstring and `IsSeparated` signature/docstring
  were read; no dependency replacement or private definition is needed.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec`,
  `Mathlib.AlgebraicGeometry.Scheme` (lines 469–495); the conclusion uses
  `AlgebraicGeometry.IsAffine` from `Mathlib.AlgebraicGeometry.AffineScheme`
  (lines 58–61) and its canonical `Scheme.isoSpec` (lines 67–69).

Proof route: the node's sole proof step applies
`lem-weil-pbc-finite-discrete-scheme-affine`, represented by the existing instance
`AlgebraicGeometry.instIsAffineOfFiniteOfDiscreteTopologyCarrierCarrierCommRingCat`
(`Mathlib.AlgebraicGeometry.Limits`, line 700). Its full signature and source body
were read. It only needs finite/discrete, so it implies the present statement.
It does not have the exact present signature, since it omits quasi-compactness
and separatedness; consequently this delivery states the node's specialization
instead of recording the stronger result as the node's exact statement.

Source check: the local `literature/stacks-project/properties.tex` is absent on
this machine, so [Stacks Tag 0CKV](https://stacks.math.columbia.edu/tag/0CKV)
was opened directly. Lemma 28.10.6 states affineness for quasi-compact separated
zero-dimensional schemes; finite discrete spaces satisfy that special case.
There is no statement correction or disputed statement.

Edge cases checked: the empty scheme is allowed (`Finite` does not imply
nonempty) and is affine, the spectrum of the zero ring. A singleton spectrum
is allowed without reducedness or Noetherianity, and any finite disjoint union
of such schemes is allowed. No field or characteristic restrictions, finite-type
assumptions, dimension binder, or connectedness assumptions have been added.
The universe-polymorphic terminal scheme uses the lifted integer ring, so no
scheme universe is excluded.

Searches for existing statements and names:

- `msearch.py ... leanfinder "A quasi-compact separated scheme with finite discrete
  underlying topological space is affine"`: eight hits; the stronger finite/discrete
  affineness instance above and generic compactness/affineness results, no exact
  specialization with all four hypotheses.
- `msearch.py ... loogle "AlgebraicGeometry.IsAffine, Finite, DiscreteTopology"`:
  one hit, the same stronger instance.
- `msearch.py ... grep
  "finite.*discrete.*affine|isAffine.*finite|affine.*discrete|DiscreteTopology"
  AlgebraicGeometry`: 25 hits, including `Limits.lean:700`; other hits concern
  affine limit covers, finite morphisms, Artinian schemes, and related results.
- `rg` for finite/discrete affineness patterns in `WeilConjectures`, `lean/Sheaf`,
  and `dag/lean_names_upstream.json`: finite-over-field consequences and comments;
  no exact theorem matching this node.
- `grep -rn "lem-sc-finite-discrete-separated-affine" WeilConjectures`: no hits.
- `rg` for `isAffine_of_finite_discrete_of_separated|FiniteDiscreteSeparatedAffine`
  in Mathlib, WeilConjectures, lean/Sheaf, and the upstream name table: no hits.

The server single-file compile and `deliver2.py --no-push` are the validation
steps. The second reading is reserved for the independent reader.

## Second reading by K1

I reread the node statement, its dependency signatures, the source place, and the Lean file.
The correspondence is as follows:

- The object ``scheme Y`` is rendered by ``(Y : Scheme.{u})`` in
  ``AlgebraicGeometry``; the explicit universe ``u`` leaves all scheme universes open.
  This is the same Mathlib scheme object recorded by ``def-pc-scheme``.
- The hypothesis ``Y is quasi-compact`` is rendered by ``[CompactSpace Y]``.
  ``CompactSpace`` is the compactness of the carrier topology, equivalent to the
  dependency node's quasi-compact underlying-space condition; no Hausdorff or
  Noetherian assumption is added.
- The hypothesis that the structure morphism to ``Spec Z`` is separated is rendered
  by ``[IsSeparated (terminal.from Y)]``.  ``terminal.from Y`` is the canonical
  morphism from ``Y`` to the terminal scheme (the spectrum of the initial ring,
  i.e. the ``Spec Z`` base used by this development), so this is the specified
  structure morphism and introduces no arbitrary base or morphism.
- ``|Y|`` finite is ``[Finite Y]`` and ``|Y|`` discrete is
  ``[DiscreteTopology Y]``.  These are instances on the actual scheme carrier;
  neither is strengthened by an enumeration or nonemptiness requirement.
- The conclusion ``Y is affine`` is exactly ``IsAffine Y``, the Mathlib affine
  scheme predicate from ``def-weil-affine-spectrum``.

The quantifier and instance order in the Lean signature is therefore the node's
object followed by its four hypotheses and its affine conclusion.  The source,
Stacks Tag 0CKV, states that a separated zero-dimensional scheme has affine
quasi-compact opens and hence is affine when quasi-compact; finite discrete spaces
supply the zero-dimensional special case represented by this node.  The proof
field's sole step is represented by the finite/discrete ``IsAffine`` instance
(``lem-weil-pbc-finite-discrete-scheme-affine``), with the retained quasi-compact
and separated assumptions unused by that stronger result.

Edge cases were checked: ``Finite`` permits the empty carrier, so the empty scheme
is included; finite discrete disjoint unions and one-point schemes are included;
no connectedness, reducedness, Noetherianity, finite-type, characteristic, or field
hypothesis is present; and the explicit universe ``u`` excludes no case.  The
zero-ring/empty-spectrum case is covered by the same affine predicate.

I repeated the existing-notion searches with ``msearch.py`` (LeanFinder and
Loogle queries for finite/discrete affineness), ``rg`` over Mathlib,
``WeilConjectures``, ``lean/Sheaf``, and ``dag/lean_names_upstream.json``.  The
only matching result is the existing Mathlib instance
``AlgebraicGeometry.instIsAffineOfFiniteOfDiscreteTopologyCarrierCarrierCommRingCat``;
there is no declaration with this node's exact specialization.  Thus no duplicate
definition or dependency module is needed.

No mismatch was found between the node and the Lean signature, and no statement
correction was required.  The only file was compiled with ``scompile.py`` and
compiled cleanly; the theorem proof remains the required single ``sorry``.

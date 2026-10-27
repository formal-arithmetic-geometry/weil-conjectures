## Worker report

The module `Sheaf.AlgebraicGeometry.FlatSpaceFibreDimensionLowerSemicontinuous`
defines `AlgebraicGeometry.AlgebraicSpace.affineEtaleFibreDimension` and states
`AlgebraicGeometry.AlgebraicSpace.affineEtaleFibreDimension_finite_isOpen_of_flat`.
The theorem has the sole postponed proof. The definition contains only an actual
indexed supremum, without choices or postponed data.

Source read: Stacks `spaces-more-morphisms.tex`, Tag 0D4P,
`lemma-dimension-fibres-flat` (scheme-target reduction, lines 7203–7224), and
`more-morphisms.tex`, Tag 0D4H, `lemma-dimension-fibres-flat` (lines 8491–8512).
The tags index identifies 0D4N as `lemma-base-change-dimension-fibres`.
The current blueprint's `sk-thm-sf-ctf-stability-direct-images.proof.md`, (3), was
read; the accepted DAG's auxiliary dimension route is retained. No statement
correction, new node, or dependency-interface replacement is needed.

Clause-by-clause correspondence:

- The scheme target is `T : Over S`, with underlying scheme `T.left`.
  `X : AlgebraicSpace S` and `f : X.obj.obj ⟶ yoneda.obj T` are precisely a
  map from an algebraic space to that scheme. `S : Scheme.{u}` is any ambient
  base, in the existing algebraic-space universe convention. This adds no
  geometric restriction: an arbitrary family over T can use S = T.
- The fibre is the actual presheaf pullback of f along the Yoneda image of
  `T.left.fromSpecResidueField t`. The latter is an `Over S` morphism from
  `Over.mk (T.left.fromSpecResidueField t ≫ T.hom)` to T; its source is literally
  `Spec (T.left.residueField t)`. Thus the construction uses the canonical
  residue-field map, without a geometric point or arbitrary field extension.
- The supremum binds every `U : Over S`, `IsAffine U.left`, map `a` from its
  Yoneda presheaf to this fibre, and `IsEtale a`. Its terms are the recorded
  `topologicalKrullDim U.left`. `IsEtale` includes representability. Any scheme
  mapping to the fibre inherits an S-structure, so no chart is excluded.
  `WithBot ℕ∞` is exactly {-∞,0,1,...,∞}. Every chart of an empty fibre is empty
  and contributes bottom; an empty indexing family also has supremum bottom.
- `hflat : MapToSchemeIsLocally (@Flat) X T f` uses the existing scheme Flat
  predicate on every representable étale source chart. This is the established
  scheme-target form of the chartwise test. Compatible étale target charts give
  the equivalent source-and-target form by scheme base change and étale locality.
- `hlfp` uses the same recorded test with `@LocallyOfFinitePresentation`.
- `hqc : MapIsQuasiCompact f` is the existing definition-node interface:
  every affine scheme test has a pullback with compact underlying point space.
  For algebraic spaces this is equivalent to admitting a quasi-compact scheme
  atlas, as in the node. Finite affine open covers give the equivalent condition
  for every quasi-compact scheme test.
- `hqs : MapIsQuasiCompact (pullback.diagonal f)` applies exactly this predicate
  to the canonical relative diagonal, precisely the node's quasi-separatedness.
  These are the same two finiteness predicates used by `IsProperCurveFamily`
  in the already cited definition node; no theorem-node definition is used.
- The first conclusion is `∀ t, dimension = ⊥ ∨ ∃ n : ℕ, dimension = n`:
  every value lies in {-∞,0,1,...}, and +∞ is excluded.
- The second conclusion quantifies `a : ℤ` and `-1 ≤ a`. For the values in the
  first conclusion, `((a+1).toNat : WithBot ℕ∞) ≤ dimension` means exactly
  `dimension > a`. A bottom value never satisfies it. At a=-1 the bound is 0;
  at every a≥0 the bound is a+1. Thus the open set has exactly the node's strict
  superlevel set, including its negative threshold.
- There are no properness, nonemptiness, equidimensionality, Noetherian, field,
  or characteristic assumptions.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`
  (structure and morphism definitions, and spectrum definitions at 470–479).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsRepresentableWith`,
  `IsEtale`, `IsAlgebraicSpace`. Their full signatures and docstrings were read.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`, `Scheme.fromSpecResidueField` (45–46, 123ff, 237–239).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`,
  `etale_fibreProduct_isScheme`. The full module was read. It justifies using
  the actual presheaf fibre product, with the same chart representation tests.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim` (39–40), literally
  `Order.krullDim (IrreducibleCloseds T)` in `WithBot ℕ∞`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat` (42–46), and
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation` (45–48).
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `MapToSchemeIsLocally` and
  `MapIsQuasiCompact`, whose full definitions and docstrings were read again
  during repair. The former is the every-chart scheme test; the latter tests
  compactness of points of affine-test pullbacks. `IsProperCurveFamily` uses
  `MapIsQuasiCompact (pullback.diagonal f)` for quasi-separatedness. Added only
  its existing owning node `def-sfb-proper-curve-moduli` to stmt_deps. It has
  no path back to this item (statement and proof edges checked previously).

All currently stated proof-dependency modules are imported (Mathlib leaves by
their indicated source modules). Three proof dependencies currently have neither
Lean record nor Mathlib match: the finite affine atlas refinement, the algebraic
space atlas dimension comparison, and the locally algebraic component-dimension
lemma (three distinct nodes); their future imports are for maintenance to add.
They are not needed to type this statement. The proof docstring follows all six
accepted proof steps, including the empty cases and the finite affine ring argument.

Edge cases read against the statement: empty target (pointwise and openness
assertions vacuous); empty source (all values bottom and all superlevel sets
empty); identity (dimension zero, locus full at a=-1 and empty at a≥0);
open immersion (a=-1 locus is its open image); affine n-space (constant finite
n); disjoint union of a plane and a point (maximum dimension two, no purity
assumed). No characteristic or nonzero-ring restriction occurs. Spec of the zero
ring is permitted as an empty affine chart.

Searches actually run via msearch.py (2026-10-24):

- LeanFinder: `For a flat finitely presented morphism of algebraic spaces fibre
  dimension is lower semicontinuous`: eight hits, including
  `UniversallyOpen.of_flat`, scheme Flat, and smooth relative dimension; none
  states this algebraic-space Krull-dimension theorem.
- Loogle: `"LowerSemicontinuous", "AlgebraicGeometry"`: zero hits.
- grep (Mathlib): `lowerSemicontinuous.*dim|dim.*lowerSemicontinuous|dimensionFib|fiberDim`:
  zero hits.
- LeanSearch: `flat morphism finite presentation algebraic space fibre dimension
  lower semicontinuous`: eight hits for scheme Flat fields/constructors and
  locally constant module rank; no matching statement.
- rg of the same dimension/semicontinuity pattern in project Sheaf and upstream
  WeilConjectures found finite-locally-free vector-space fibre rank, not Krull
  dimension. Direct grep for the node id in WeilConjectures found none.
- Broader project searches for `fibreDimension|fiberDimension`, chartwise flatness,
  local finite presentation and quasi-compactness found and reused the recorded
  APIs listed above. `localFibreDimension` in AlgebraicSpaceLocalFibreDimensionOpen
  is a pointwise local dimension on the source, not the fibre dimension on the
  target, and is therefore not copied or substituted.

Validation: scompile.py compiled both its sandbox form and the final library module
successfully; the final delivery is also compiled by the dry-run wrapper.

## Second reading by Q08

This is the dispatch worker's self-check; independent mathematical review belongs
to the maintainer. Reopened the JSON statement and read the module from the fibre
supremum through the full theorem signature. The structural map is still arbitrary,
the residue-field map is canonical, and the supremum ranges over affine étale
charts of the fibre itself. Both global finiteness conditions are present, flatness
and lfp retain the recorded every-chart tests, and the output includes bottom and
excludes infinity. Checked a=-1 separately: the Nat lower bound becomes zero,
which accepts exactly the non-bottom finite values. No equidimensionality or
properness restriction slipped in. The sole added owning node `def-sfb-proper-curve-moduli` supplies both the
chart tests and `MapIsQuasiCompact`; no private copies or new notions were introduced.
On repair, checked both `hqc` and `hqs` against that definition module and its
`IsProperCurveFamily` signature: they now use `MapIsQuasiCompact f` and
`MapIsQuasiCompact (pullback.diagonal f)` verbatim. Removed the theorem node
and its direct import as requested. The helper defines exactly the function already stipulated by
this item and is listed in lean.declarations. Final import reading added explicit
public imports of the recorded scheme, flatness and finite-presentation modules.
No mathematical mismatch or disputed statement was found.

## Returned delivery repair

Return H2/H4 on immutable head `6e5fc9bc3d46`: repaired every requested part.
Changed hqc to `MapIsQuasiCompact f` and hqs to
`MapIsQuasiCompact (pullback.diagonal f)`, reusing the interface owned by
`def-sfb-proper-curve-moduli`. Removed
`lem-trf-space-qc-separated-etale-local` from stmt_deps and removed its import.
Updated the theorem docstring, verbatim lean.statement, lean.note, hypothesis
correspondence, dependency list, and second reading above. No new definition
node is needed. The node copy was regenerated from current main, retaining only
the repaired lean record and the single authorized definition-node addition.
All mathematical clauses accepted by the reviewer are retained.

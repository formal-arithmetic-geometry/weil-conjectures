## Worker report

Restores the statement of lem-per-punctured-local-closed-points in
Sheaf.RingTheory.PuncturedLocalClosedPoints. The old module is absent; the node's
lean_removed record confirms that its declaration was deleted, not moved elsewhere.
There is one theorem, with proof `sorry`, and no new definition or node correction.

Clause-by-clause rendering:

- A nonzero commutative local ring is `(A : Type u) [CommRing A] [IsLocalRing A]`.
  Mathlib's IsLocalRing extends Nontrivial and means a unique maximal ideal;
  no redundant nonzero assumption is needed.
- Noetherian is `[IsNoetherianRing A]`, exactly finite generation of every ideal.
- X = Spec A is `AlgebraicGeometry.Spec (CommRingCat.of A)`, using the recorded
  affine-spectrum dependency. Its underlying space is definitionally PrimeSpectrum A.
- The maximal ideal m is `IsLocalRing.closedPoint A`, whose asIdeal is maximalIdeal A.
- U with its subspace topology is the subtype
  `{x : AlgebraicGeometry.Spec (CommRingCat.of A) | x ≠ IsLocalRing.closedPoint A}`.
- W is an arbitrary `Set` of that subtype; `(hW : W.Nonempty)` supplies nonemptiness.
- `(hWlc : IsLocallyClosed W)` is exactly an intersection of an open and a closed
  subset of U: Mathlib/Topology/Defs/Basic.lean defines it by
  `∃ (U Z : Set X), IsOpen U ∧ IsClosed Z ∧ s = U ∩ Z`.
- `∃ w ∈ W, IsClosed ({w} : Set {x : ... | x ≠ ...})` supplies the requested point
  and asserts that its singleton is closed in U, with the same subtype topology.

Recorded statement dependencies read and used:

- def-weil-pbc-noetherian-ring: Mathlib.RingTheory.Noetherian.Defs,
  IsNoetherianRing and isNoetherianRing_iff; the adjacent
  isNoetherianRing_iff_ideal_fg identifies finite generation of every ideal.
- def-weil-affine-spectrum: Mathlib.AlgebraicGeometry.Scheme, AlgebraicGeometry.Spec
  (and its recorded functorial Spec.map signature read, although no map is needed here).

The stated proof dependencies are imported: spectrum topology (singleton closures,
zero loci and quotient embeddings), LocalRing.Quotient (quotient local structure),
Topology.NoetherianSpace, Topology.Separation.Basic, and Topology.KrullDimension.
The proof dependency lem-per-noetherian-local-domain-open-infinite has no Lean record
or Mathlib match at the time of reading, so has no module to import. It is not a
statement prerequisite. The theorem docstring reproduces all six DAG proof steps,
including the final use of that node; no replacement theorem or assumption was added.

Source checked directly: literature/stacks-project/properties.tex,
lemma-complement-closed-point-Jacobson (1), including its direct proof;
morphisms.tex, lemma-ubiquity-Jacobson-schemes (4); topology.tex,
definition-space-jacobson and the immediately following equivalence.
No mathematical discrepancy or STATEMENT-DISPUTED condition was found.

Edge cases checked: for a field, or a zero-dimensional local Artinian ring, U is empty
and no nonempty W exists, so the statement is vacuous. For a DVR, the generic point
is closed in U even though it is not closed in X; the singleton's explicit ambient
subtype retains this distinction. No domain, reducedness, dimension, characteristic,
or completeness hypothesis is imposed. Universe u is arbitrary; W is a subset, not
an auxiliary space with a size restriction. The zero ring is excluded by IsLocalRing.

Searches made via /home/ubuntu/weil-launcher-all/batch2/msearch.py:

- leanfinder: "Every nonempty locally closed subset of the punctured spectrum of a
  Noetherian local ring contains a point closed in the punctured spectrum".
  Eight hits: nonempty_inter_closedPoints, jacobsonSpace_iff_locallyClosed,
  PrimeSpectrum.exist_mem_one_of_mem_maximal_ideal,
  PrimeSpectrum.exists_isClosed_singleton_of_isJacobsonRing,
  IsLocalRing.specializes_closedPoint, PrimeSpectrum.quasiSober,
  IsLocalRing.isClosed_singleton_closedPoint, IsLocalRing.closed_point_mem_iff.
  None states the item: the closest results require JacobsonSpace on the puncture
  or IsJacobsonRing on the original ring, which are not available hypotheses.
- loogle: "IsLocalRing.closedPoint, IsLocallyClosed, IsNoetherianRing": zero hits.
- grep, RingTheory: "(punctured|isLocallyClosed.*[Ll]ocal|[Ll]ocal.*isLocallyClosed)":
  zero hits.
- rg in lean/WeilConjectures and lean/Sheaf, including the node id and exact old
  declaration name: no occurrence of this item/declaration. Broader punctured
  searches found other topics (completion, affine lines, spectral neighborhoods),
  with no matching assertion. dag/lean_names_upstream.json has no matching name.

## Second reading by Q134

A separate self-check pass read the completed module alongside the unchanged node;
this is not a claim of an independent agent review (the dispatch brief forbids agents).
The independent maintainer review remains the delivery review.
Checked every binder and conclusion: CommRing, IsNoetherianRing, IsLocalRing,
Spec (.of A), removal of exactly closedPoint A, arbitrary subset W, Nonempty,
IsLocallyClosed, existential membership, singleton closed in the puncture. No added
hypothesis or missing clause was found. Checked the topology and IsLocalRing definitions
directly in Mathlib. The docstring follows the six proof steps, including the unstated
final proof dependency. Only the node's lean field is changed. No correction was needed.

Validation: scompile.py compiled the sandbox probe and actual library module cleanly
(2.2 and 2.3 seconds); no errors or non-sorry warnings. The completed Lean file has
no line over 100 characters, and a JSON comparison confirms that lean is the only
changed node field. All variables and the universe are explicitly bound.

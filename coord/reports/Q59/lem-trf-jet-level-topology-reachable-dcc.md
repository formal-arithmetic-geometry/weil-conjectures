## Worker report

The delivery states `lem-trf-jet-level-topology-reachable-dcc` in
`Sheaf.AlgebraicGeometry.JetLevelTopologyReachableDcc`, with four named theorems,
each with `sorry` and a source/proof docstring. It also supplies the missing unrestricted
pair/reachability interface in `Sheaf.AlgebraicGeometry.JetLevelBlowupHistory`.
There are no proved theorems or data holes. The item's statement, proof, proof dependencies,
and source are unchanged. Its statement dependencies gain the new definition node and the
already landed initial-diagram, regular-coefficient, stalk-ideal and polynomial-ring definitions
which the statement actually uses.

Hypothesis and clause comparison:

* The schemes are `S.X` and `S.Z`, with inclusion `S.i` and rational structure map `S.p`.
  All four theorems bind `S : JetLevelPair.{u}` and explicitly require `IsReduced S.X`,
  `IsImmersion S.i`, `Smooth S.p`, `LocallyOfFiniteType (S.i ≫ S.p)` and
  `QuasiCompact (S.i ≫ S.p)`. These say reduced, locally closed in a smooth rational
  ambient, and finite type over the rationals. There is no separatedness, connectedness,
  equidimensionality, closed-point, or globally closed-embedding hypothesis.
  `ULift.{u} ℚ` merely places the same rational field in the scheme universe, so the
  statement covers `Scheme.{u}` for every explicitly declared universe `u`.
* The extended numerical function is the recorded `HilbertSamuel.function`, with ground
  field explicitly specified. Its existing definitions use stalk quotient length, inclusive
  summation iterated by residue-field transcendence degree, and the node's first-difference
  comparisons `HilbertSamuel.lt` and `HilbertSamuel.le`. No new numerical invariant is defined.
* `jet_level_finite_lengths` asserts that the `Module.length` of the quotient of each actual
  stalk by `maximalIdeal ^ (q + 1)` is not infinity, for every point and every natural degree.
* `jet_level_presentations` quantifies over every commutative `A : Type u` with its rational
  algebra structure and every open immersion `j : Spec A ⟶ S.X` compatible with the rational
  structure map (`hj`). Thus it includes every affine chart; it does not assume A finite type
  or assume a presentation. `DiagonalJets.principalParts` is exactly the diagonal quotient
  with its left-factor module structure. Existential `r`, `v`, `M` and `π`, with
  `Function.Surjective π` and `LinearMap.range M.toLin' = LinearMap.ker π`, give
  `A^r → A^v → P^q → 0`.
* For each integer `1 ≤ c ≤ v`, the displayed equality of sets identifies the upper locus
  of the actual value at `j x` with vanishing of every `(v-c+1)`-minor. Rows and columns
  are injective maps from `Fin (v - c.toNat + 1)`; determinant membership in `x.asIdeal`
  is exactly vanishing in the residue field. Allowing all injections describes the same
  minors as ordered row/column subsets. If too few columns exist the universal condition
  is vacuous, as required. The next two conjuncts give the all-points convention for
  `c ≤ 0` and the empty-set convention for `v < c`.
* `jet_level_topology` gives, for every `a`, an open `U` containing a, `IsAffineOpen U`,
  a finite set `F : Finset (ℕ → ℕ)`, and a natural `q₀`. Its image condition is
  `∀ x ∈ U, function ... x ∈ F`. Its unequal-pair condition gives an actual differing
  index `n ≤ q₀` with equality at every earlier index. The set containing U-members
  satisfying all coordinate inequalities through `q₀` is explicitly `IsOpen`; it contains
  a because a belongs to U and every coordinate is at most itself. The following universal
  clause says that every point of precisely that set has value lexicographically at most
  the value at a. The final conjunct is `IsClosed {x | le v (function ... x)}` for EVERY
  threshold sequence v.
* `jet_level_reachable_diagrams_dcc` binds a finite family `U : Fin m → S.Z.Opens`,
  its coordinate counts `e`, and actual maps `c` to the spectra of the e-variable rational
  polynomial rings. `haff`, `het`, `hbase`, `hcover`, and `hbound` respectively say affine
  charts, etale coordinates, rational compatibility, covering a neighbourhood of the image
  of X, and `e t ≤ d`. This is the node's fixed finite smooth ambient chart cover; neither
  the entire ambient nor X is required to lie in one chart.
* For EVERY `T` reachable by finite smooth-center blowups, `Smooth T.p ∧ IsReduced T.X`
  is a conclusion. The definition of reachability assumes neither of these conclusions.
  For every point x of T.X the theorem provides `a ≤ d`, an affine ambient open V, a point
  y mapping to `T.i x`, actual etale rational coordinates, and a Taylor homomorphism τ
  characterized by `HilbertCoefficient.isTaylorMap`. The ideal whose initial diagram is
  counted is exactly `taylorIdeal (stalkIdeal (T.i.ker.comap V.ι) y) τ`, the Taylor expansion
  of the transform's actual equations near the point. This is not an arbitrary formal
  ideal or an arbitrary map. For an immersion its kernel agrees with its closed equations
  near every image point, even when the immersion is not globally closed. Its count is
  asserted equal to the entire extended function, not only to one truncation.
* The last conjunct quantifies over every sequence of values, each individually witnessed
  by a reachable pair and a point; it forbids strict lexicographic descent at every index.
  No fixed history, equal history lengths, or consecutive-stage drop assumption is present.
  `Relation.ReflTransGen` includes zero blowups. Values from different finite histories,
  or a subsequence separated by arbitrary plateaus, are all included.

Dependency declarations used:

* `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup` and `blowupMap`.
* `WeilConjectures.Compactification.StrictTransform`: the scheme-theoretic
  `strictTransform`, `strictTransformMap`, and `Scheme.IdealSheafData.strictTransform`.
  The construction is the image of the open locus in the fibre product, not a topological
  closure or a chosen map.
* `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`.
* `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `.Etale`, `.ClosedImmersion`, `.Immersion`,
  `.FiniteType`, `.QuasiCompact`: `Smooth`, `Etale`, `IsClosedImmersion`, `IsImmersion`,
  `LocallyOfFiniteType` and `QuasiCompact`.
* `Sheaf.RingTheory.DiagonalJets`: `DiagonalJets.principalParts` (the other recorded
  declarations `fibreDimension` and `affineEvaluation` were also read).
* `Sheaf.AlgebraicGeometry.HilbertSamuelInvariant`: `function`, `localFunction`,
  `summation`, `lt`, `le`; all definitions and docstrings were read.
* `Sheaf.RingTheory.FormalInitialDiagram`: `initialDiagram`, `hilbertCount`.
* `Sheaf.AlgebraicGeometry.RegularHilbertCoefficientDatum`: `isTaylorMap`, `taylorIdeal`.
* `Sheaf.AlgebraicGeometry.MarkedIdealOrder`: `stalkIdeal`.
* `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`, with `MvPolynomial.C` for
  rational structural compatibility.
* `Sheaf.AlgebraicGeometry.JetLevelBlowupHistory`: the new `JetLevelPair`,
  `JetLevelBlowup` and `JetLevelReachable`.

The main module retains plain imports of the stated proof-dependency modules: the jet diagram
control, coordinate-subspace charts, smooth-center geometry, strict-transform base change,
finite-length support, field-minor, affine-space smoothness, finite-presentation, finite-type
Noetherian, and tensor right-exactness modules. `lem-trf-smooth-pair-blowup-local-models`
has no recorded module, so its not-yet-existing module is not imported; its role in proof
steps 3, 5 and 6 is explicitly retained in the docstrings. No downstream local-presentations
or reachable-level theorem is imported, so this delivery does not close the parent dependency
cycle.

Edge cases checked from the definitions and statements: empty X (including m=0 charts),
q=0, d=0, r=0 and v=0 presentations, c=0 and negative c, c=v, c=v+1, minor order larger
than the number of columns, zero blowups, empty centers, whole-component centers, nonclosed
points of a smooth rational line (whose summation exponent differs from that at closed
points), and histories of unequal lengths and plateaus. No case requires a nonempty scheme
or nonempty center. F may be a singleton, when q₀=0 suffices. No statement fault or
STATEMENT-DISPUTED flag was found.

Searches actually run:

* msearch leanfinder: "Hilbert Samuel jet module fibre dimensions local finiteness upper
  semicontinuity reachable smooth blowup histories descending chain condition" returned
  support-dimension, prime-chain, free-locus and adic-completion facts, not this package.
* msearch loogle: `"HilbertSamuel"` returned zero hits.
* msearch grep: `HilbertSamuel|principalParts|TaylorDiagram|BlowupHistory` returned zero
  Mathlib hits. Additional raw-history queries, with actual returned output, are recorded
  verbatim in the new node's `mathlib_searches`.
* `rg` in the read-only `lean/WeilConjectures` and `lean/Sheaf`, by HilbertSamuel,
  principalParts, Taylor diagrams, reachable levels, blowup histories and prospective names,
  found and reused the definitions above. The upstream principal-parts hits concern
  adelic residues and are a different notion. Grepping the item id upstream found none.
* Read `HilbertSamuelPresentation.lean`, `HilbertSamuelReachableLevels.lean`,
  `EmbeddedResolutionHistory.lean`, and `LabeledEmbeddedResolution.lean` to check whether
  their history notions suffice. Their limitations are described below. The existing parent
  reachable-level theorem also omits this node's jet presentation/minor/topology/diagram
  clauses and cannot serve as an existing match (and is downstream).
* Searched the DAG for histories and locally closed pairs, and ran `blueprint_refs.py search`
  for "blowup history" (zero matches) and "locally closed" (63 general matches, none defining
  this reachability relation). `blueprint_refs.py ancestor` reports
  `lem-trf-local-term-locality`. Prospective declaration names had no project/upstream match.

Read ILO PDF printed pp.93--94 locally, including 2.3.11 and 2.3.13, and the current blueprint
ancestor's contracting-correspondence material under `literature/blueprint/latest/`.
The historical embedded-resolution support is not substituted for that active blueprint route.

Validation: both delivered files compiled separately in dependency order through `scompile.py`
against the live server library, with no errors or non-sorry warnings. The new history module
has no theorem proof at all. All universes and variables are explicitly bound (`autoImplicit false`).

## New nodes

`def-trf-jet-level-blowup-history` defines raw rational pairs, their locally
Hilbert--Samuel-constant smooth-center steps, and finite reachability. It is needed because
the node's quantifier includes LOCALLY closed embeddings and its smoothness/reducedness
assertions must remain conclusions. `HilbertSamuel.Embedded` requires a globally closed
embedding and already assumes ambient smoothness; `BlowupTransition` is restricted to
those objects. `EmbeddedResolutionHistory` has an `EmbeddedResolutionPair` initial object,
which additionally requires a globally closed embedding and a separated finite-type smooth
ambient. Those records therefore exclude initial cases covered by this item. They also
encode retained labels/boundaries or full chronological comparisons which this numerical
reachability notion does not need. None is redefined or changed here. The new pair has only
X, Z, p and i as data, and the new relation uses the existing canonical blowup and strict
transform, with isomorphisms commuting with their maps. Its transitive reflexive closure
is Mathlib's existing relation construction. The source is the same ILO/BMT finite-history
setting as the item; searches above and the verbatim new-node search records found no existing
interface with this scope. All new-node fields, source and blueprint ancestry are supplied.

## Second reading by Q59

A separate pass reopened the two Lean modules and their two node records and compared each
hypothesis and clause as listed above. This dispatcher-started session was explicitly forbidden
to start other agents, so this is a second reading by the same worker; the maintainer's independent
review remains separate. The pass found that merely existentially quantifying a formal ideal
would forget its tie to the transform. The final statement instead records an actual affine
etale chart and Taylor map and uses the kernel ideal of the actual transformed inclusion.
The pass also checked that smoothness and reducedness occur only as hypotheses on the initial
pair and as conclusions on reached pairs; neither is built into the raw state/reachability.
It checked the integer endpoints, the existential matrix and surjection, the first-difference
prefix bound, the openness of the exact coordinate intersection, and the arbitrary-sequence
DCC quantifier. The auxiliary state adds no geometric hypotheses and copies no numerical or
blowup construction. The final new-node statement and all three declared definitions agree.
The item record lists all four theorem declarations; both record signatures are extracted
verbatim from the delivered files. No statement correction or dependency repair was needed.

## Worker report

The module `Sheaf.RingTheory.PartitionRestrictionIndZariski` states
`WContractification.PartitionRestriction.partition_restriction_ind_zariski`.
There is one theorem, whose proof is `sorry`; every helper has real data.
No statement, proof, dependency list, review, or other pre-existing node field changes.

Source read: Stacks `proetale.tex`, lemma-construct-profinite (097D), and
`literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-thm-pe-wc-cover/det-pe-wc-cover-second-stage.proof.md`, Preliminaries and Step 1.
The dependency module and full signatures were read before writing. No missing
notion, unusable dependency, or mathematical node fault was found.

Hypothesis and clause correspondence:

- The commutative ring R is `{R : Type u} [CommRing R]`.
- The spaces P and S have `TopologicalSpace`, `CompactSpace`, `T2Space`, and
  `TotallyDisconnectedSpace` instances. No nonempty-space hypothesis is imposed.
  A single arbitrary ambient universe u contains the input sets and their set-sized
  partition and neighbourhood indices, exactly as the recorded dependency interface.
- The continuous maps from Spec R to P and from S to P are respectively
  `g : C(PrimeSpectrum R, P)` and `f : C(S, P)`. `PrimeSpectrum R` is the
  underlying topological space of the recorded `AlgebraicGeometry.Spec (.of R)`.
- `Index S` is `(DiscreteQuotient S)ᵒᵖ`. A discrete quotient encodes its partition
  by the fibres of its surjective `proj`; compactness makes its quotient finite
  (Mathlib's `Finite` instance). Every fibre is nonempty and clopen; distinct
  fibres are disjoint and they cover S. Conversely, a finite partition by nonempty
  clopens determines exactly one such setoid. Thus no labelled duplicates or empty
  parts are introduced. Mathlib's `finsetClopens`, `comp_finsetClopens`, and
  `finsetClopens_inj` give the corresponding finite-set encoding. The opposite
  category has arrows from coarse to fine: a morphism h gives the parent map
  `DiscreteQuotient.ofLE h.unop.le` from the finer quotient to the coarser one.
  Its underlying relation is the refinement partial order specified by the node.
- `part Q a` is the fibre `Q.unop.proj ⁻¹' {a}`. The first conjunct says exactly
  `IsClosed (f '' part Q a)` for every part, without assuming f is open.
- `Nonempty (Index S)` and `IsFiltered (Index S)` express nonemptiness and
  directedness of this small thin poset. Smallness and its partial-order structure
  come from the actual setoid index, not extra hypotheses. In a poset the
  object-pair condition of `IsFiltered` is exactly directedness; parallel-arrow
  equalization is automatic.
- `stage g f Q` is the categorical product of the algebras
  `ClopenRestriction.algebra g (f '' part Q a)`, namely the node's E_Q.
  These are precisely the dependency's chosen clopen-neighbourhood colimits R_Z;
  no replacement restriction algebra is defined.
- `NeighborhoodIndex f Q` is the product, over parts a, of the dependency's
  reverse-inclusion `ClopenRestriction.Index (f '' part Q a)`. Its nonemptiness
  and filteredness are the next quantified conjuncts. Again it is a set-sized
  product of thin posets, so filteredness states the required directedness.
- `neighborhoodDiagram g f Q` is Mathlib `pointwiseProduct` of the actual
  dependency diagrams. Its object at U is the product of
  `RestrictClopen (ClopenRestriction.preimage g (U a).unop.val)`. Read directly
  from the upstream definition, this is `Localization.Away` at the unique
  pulled-back clopen idempotent. Thus the principal factors are exactly R[1/e_U],
  and the maps are the already constructed canonical localization maps.
- `comparison g f Q` is the existing
  `colimitPointwiseProductToProductColimit` on those diagrams. `IsIso` states
  that this actual canonical R-algebra map is an isomorphism. The following
  quantified equation states coordinate compatibility verbatim: the coprojection
  followed by comparison and projection equals projection followed by the
  coordinate colimit coprojection. This supplies the normalization, rather than
  merely claiming an abstract isomorphism between the two rings.
- `Algebra.IsIndPrincipalZariski R (stage g f Q)` is precisely the stated
  finite-principal-product version of ind-Zariski for each E_Q, including empty
  products. It is the existing predicate exposed by the recorded ind-etale node.
- The final existential supplies `D : Index S ⥤ CommAlgCat R`, with
  `hD : ∀ Q, D.obj Q = stage g f Q`. These are literal object equalities to
  the chosen products. For every refinement h and every target coordinate a',
  the displayed equation fixes `D.map h` to projection onto the containing part
  followed by `refinementRestriction g f h a'`. The latter is the dependency's
  inclusion-induced `ClopenRestriction.restriction`; its subset proof uses
  `DiscreteQuotient.ofLE_proj`. Product uniqueness fixes the map completely,
  while the functor fields state identity and composition. No arbitrary map or
  choice of an abstract isomorphism replaces a canonical construction. The theorem
  asserts that these specific maps form a functor; it does not extract a data
  definition by choice from an undetermined existence theorem.
- The last conjunct `Algebra.IsIndPrincipalZariski R (colimit D : CommAlgCat R)`
  is the specified final filtered-colimit assertion. Its algebra structure is
  the one on the actual categorical colimit in commutative R-algebras.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, whose underlying
  space is `PrimeSpectrum R`; publicly exposed by the restriction dependency.
- `Sheaf.RingTheory.ClopenRestrictionCanonicalLocalization`:
  `WContractification.ClopenRestriction.Index`, `preimage`, `idempotent`,
  `diagram`, `algebra`, `restriction`, `canonical_localization`, and
  `restriction_naturality`. The first six are used directly or through the actual
  diagram; the two theorems are the proof route.
- `Mathlib.GroupTheory.MonoidLocalization.Away`: `Localization.Away`, used by
  upstream `WContractification.RestrictClopen`, not redefined.
- `Mathlib.RingTheory.Spectrum.Prime.Topology`:
  `PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen` and
  `PrimeSpectrum.isIdempotentElemEquivClopens`, exposed by the restriction module
  and used by its actual `idempotent`/`preimage` construction.
- `Sheaf.RingTheory.IndEtaleUniverseTransport`: the recorded dependency module,
  publicly importing `Sheaf.RingTheory.IndPrincipalZariski` and hence
  `Algebra.IsIndPrincipalZariski`, the exact ind-Zariski clause needed here.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `colimit`, `colimit.ι`, and the
  colimit universal property, through the restriction module.
- `Mathlib.Topology.DiscreteQuotient`: `DiscreteQuotient`, its compact-space
  `Finite` instance, `proj`, `proj_surjective`, `isClopen_preimage`, `ofLE`,
  `ofLE_proj`, and the refinement order.
- `Mathlib.CategoryTheory.Limits.FilteredColimitCommutesProduct`:
  `pointwiseProduct`, `colimitPointwiseProductToProductColimit`.
- Proof-only imports: `Sheaf.RingTheory.IndEtaleStability` for
  `RingHom.indEtale_principalZariski_stability`;
  `Mathlib.Algebra.Category.Ring.FilteredColimits` for the forgetful preservation
  instance; `Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic` for
  `Concrete.isColimit_exists_rep` and `Concrete.isColimit_rep_eq_iff_exists`;
  `Mathlib.CategoryTheory.Limits.Constructions.Over.Connected` for the
  underlying-ring colimit transport. The commutative-algebra colimit-existence
  node is Mathlib's already available `HasColimits (CommAlgCat R)` instance.

Edge cases checked before and after writing:

- S empty: its unique setoid quotient has no points. The only partition has no
  parts. Its neighbourhood tuple type has exactly the empty function, products
  are terminal commutative R-algebras (the zero ring), and comparison is the
  one-object-colimit identification. No typeclass requires `Nonempty S`.
- P empty: f forces S empty and g forces Spec R empty; none of these cases are
  excluded. The same empty-product presentation works.
- R the zero ring: all its localization algebras and their products are zero.
- A constant f or overlapping images of disjoint source parts do not require
  distinct target images or f open/injective/surjective. Parent inclusion still
  induces precisely the required canonical restriction.
- The one-part partition gives exactly the closed restriction to f(S).
- Arbitrary refinement and two successive refinements: `ofLE_proj` and
  `ofLE_ofLE` identify their parent maps, and dependency restriction composition
  gives the diagram laws. Empty-coordinate assertions remain vacuous as required.

Searches made:

- `msearch.py ... leanfinder "Finite clopen partitions with canonical closed
  restriction algebras form a filtered diagram of ind Zariski algebras"`:
  8 hits, including `exists_clopen_partition_of_clopen_cover` and spectral
  clopen results; none states this canonical ring diagram and its comparison.
- `msearch.py ... loogle
  "CategoryTheory.Limits.colimitPointwiseProductToProductColimit"`: 7 hits;
  found the exact general canonical comparison and its coordinate identity,
  reused in the file. No complete match for the present node.
- `msearch.py ... leansearch "Finite products of filtered colimits of
  commutative algebras commute with filtered colimits"`: 8 hits, including the
  canonical comparison and its coordinate identity, reused as above.
- `msearch.py ... grep "ClopenPartition|IndZariski|partitionRestriction"`:
  0 Mathlib hits. Direct rg in Mathlib found `DiscreteQuotient`, avoiding a new
  definition of partitions, and its existing pointwise-product comparison API.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `ClopenPartition|clopenPartition|PartitionRestriction|partitionRestriction|
  partition_restriction|lem-pe-partition-restriction-ind-zariski`: only unrelated
  clopen partitions and an fppf helper, no match. In particular upstream
  `WContractification.PullbackProfinite` uses a different single restriction
  of locally constant functions, not this explicit coherent partition diagram.
- `rg` over `dag/nodes/sec-proetale-coefficients` for discrete quotients and
  finite clopen partitions found related geometric/incidence nodes, none carrying
  this ring diagram. No new independent notion is introduced in this delivery.
- The recorded dependency sources, full theorem signatures, and docstrings were
  read, not inferred from declaration names. The archived compact-object example
  is now withdrawn; its node points to the identical upstream declaration.

Validation: prescribed `scompile.py NZ lem-pe-partition-restriction-ind-zariski`
compiled the final module cleanly both as sandbox and library module (7.4 s and
8.0 s). The initial probe found a Prop-valued helper linter and an ambiguous
colimit coercion; the final file constructs the restriction map directly and
annotates the colimit as `CommAlgCat R`. No diagnostic commands remain. All
variables/universes are explicitly bound with `autoImplicit false`; all lines
are at most 100 characters.

## Second reading by NZ

The dispatcher forbids starting another agent and assigns the maintainer the
independent delivery review. This section records this worker's second reading,
not an independent-agent review. I reopened the full node and the final Lean
file and checked all hypotheses and clauses in the correspondence above.
The partition encoding covers exactly the nonempty clopen parts, including no
parts for an empty space. The literal object equalities and the coordinate
restriction equation prevent an unspecified diagram. The actual canonical
comparison and its normalization prevent an unspecified isomorphism. All
principal-localization and colimit structures reuse the dependency declarations.
No extra nonemptiness, openness, or surjectivity hypothesis was introduced, and
no clause was dropped. The compiler corrections do not alter the mathematical
statement. No statement correction, dependency repair, or new node is needed.

## Worker report

This is a stage-2 statement delivery. `ResolutionInvariantCalculus.lean` states
`AlgebraicGeometry.exists_resolution_invariant_calculus`, with `sorry` as the whole
proof. The only postponed theorem is this item. The two supporting definition modules
contain actual scheme diagrams, ideals, maps, isomorphisms, predicates and an inductively
generated class; they contain no `sorry`, choice of an unspecified object, or new axiom.
The original node statement, proof and proof dependencies are unchanged. Its statement
dependencies gain the two new definition nodes described below.

The previous worker's stale-dispatch conclusion concerned NZ's stage-1 split, not a
stage-2 Lean statement. I read the merged split and its independent review. It has no
Lean record. The retained NY sandbox was empty. Thus this delivery uses that reviewed
split rather than splitting it again.

I read the source ILO VIII 2.3.1, 2.3.4, 2.3.11--2.3.13, printed pp. 91--94, from the
local PDF, and the primary BMT HTML, https://arxiv.org/html/0905.3580, Theorem 6.1,
its Addendum and sections 6.1--6.3. The source distinguishes singular-locus resolution
from exceptional-divisor cleanup, warns about nonconstant relative dimension, and retains
local-embedding independence. The node's already reviewed dimension normalization is
used without modifying its statement. No new statement fault or STATEMENT-DISPUTED flag
was found.

Clause-by-clause correspondence:

* The initial data are exactly the already published `EmbeddedResolutionPair`: `X`,
  `P`, `base : P ⟶ Spec (.of (ULift ℚ))`, `inclusion`, `closed`, `reduced`, `smooth`,
  `separated`, `finiteType` and `quasiCompact`. The rational lift puts the base in the
  universe of the schemes. There is no integrality, connectedness, equidimensionality,
  quasiprojectivity or fixed dimension requirement. All finite disjoint unions are
  included by the same quantification over pairs.
* A raw `EmbeddedResolutionHistory A n` has ambient and intrinsic diagrams indexed
  contravariantly by `Fin (n + 1)`, their closed inclusions, and initial identifications
  with A. `center`, `centerToIntrinsic`, `centerClosed` and `centerInclusion` retain
  every ideal center, including its embedding in the strict transform. `ambientBlowup`
  and `ambientBlowupMap` identify each transition with the actual ordinary blowup;
  `strictTransform`, `strictTransformMap` and `strictTransformToSource` identify the
  actual scheme-theoretic strict transform and both its structural projections.
  Finite index order retains the chronological exceptional data. No smoothness or
  reducedness of the later stages is assumed in this raw-history type.
* The domain of admissible histories is `EmbeddedResolutionHistory.Admissible value`.
  Its `empty` constructor admits every length-zero history; `step` extends one only
  through `IsMaximumStep value E`; `pullback` permits exactly the smooth ambient
  history comparisons, deleting empty-center stages. These inductive constructors
  are the least class specified by the node, not an assumption that a resolution
  assignment has already been constructed. Arbitrary ambient blowup sequences are
  not declared admissible. The value family is harmlessly extended to raw histories;
  all its properties are required only on its own admissible histories.
* The existential binders `V`, `order : LinearOrder V` and `bottom : OrderBot V`
  give one common totally ordered value set and its least element. This is the
  equivalent pointed-set encoding of the node's V union bottom; the complement of
  the least element recovers its V. `ResolutionInvariantCalculus.value` is one family
  `∀ {A} {n} H, H.X → V`, simultaneous across all embedded inputs and their histories.
  It is not a choice of separate unrelated orders for different inputs. Smooth-value
  equality includes affine-space products, so these are the normalized synchronization
  values, not raw Hilbert--Samuel functions or a dimension-dependent first entry.
* Clause (1), finite image, is `finiteImage`. Pointwise detection of the regular local
  ring is `regularPoint`, using `IsRegularLocalRing (H.X.presheaf.stalk x)`. If H.X is
  nonregular, `maximumExists` gives an actual next history K and an `Extension H K` at
  its positive full maximum. `IsMaximumStep` contains `IsGreatest (Set.range (value H)) m`,
  `⊥ < m`, reducedness of the center scheme, and exact equality of its range in H.X
  with `{x | value H x = m}`. With the closed immersion this pins down the reduced
  induced center scheme, not just a set or an arbitrary map.
* Clause (1), geometry and coherence, is `maximumGeometry`: nonempty center,
  `IsRegularScheme`, empty interior of its range in H.X (the precise nowhere-dense
  convention in this node), and the exact finite-type-with-finite-type-kernels
  coherence condition on the ambient ideal and `E.centerMap.ker` on H.X.
  `nextGeometry` gives smoothness, separatedness, local finite type plus
  quasi-compactness of the next rational ambient scheme and `IsReduced K.X`.
  These are conclusions, not fields assumed of raw histories. `strictProgress`
  compares the actual two maxima and asserts strict decrease when the new maximum
  is positive. The `Admissible.step` constructor makes this the allowed next history.
* Clause (2), construction after smooth ambient pullback, is `pullbackExists`. It
  constructs a finite history with its `SmoothPullback` comparison. That comparison
  is cartesian over both initial schemes at every stage, and its `index` is a
  monotone surjection of stage sets. In its `centers` field a collapsed transition
  has unit pulled-back ambient ideal; a retained transition has nonempty center and
  its actual extended ideal. Thus precisely the empty stages, including all stages
  in an open missing the centers, are deleted. Pullback diagrams and center ideals
  are compared as schemes and ideals, not merely as topological sets. Open ambient
  restriction is the case of an open immersion; every open of a closed subscheme
  is obtained by ambient open restriction.
* Clause (2), local values and reduced ideals, is `smoothValues` at every point via
  `SmoothPullback.finalMap`, with no relative-dimension assumption. `smoothIdeals`
  says that every reduced maximum-stratum ideal J extends to the reduced ideal of
  the inverse-image stratum. This is expressed by `IsResolutionStratumIdeal`, which
  specifies reducedness of the closed subscheme and equality of its support with
  the value-equality locus. Its empty-case implication is explicitly J.comap = top.
  This clause includes the bottom maximum on a regular input; positivity was removed
  from an earlier draft of this comparison during self-review.
* Clause (3) uses `IntrinsicComparison`: a natural isomorphism of the entire
  strict-transform diagrams over an initial isomorphism, preserving all the ordered
  earlier intrinsic center ideals. No ambient isomorphism is demanded.
  `intrinsicValues` identifies the functions at the actual corresponding points.
  Consequently their images and their maxima agree in the one common value set.
  `intrinsicIdeals` identifies the reduced maximum-stratum ideals by actual comap,
  including the regular bottom maximum. These are equalities under the specified
  maps; composing them with `smoothValues`/`smoothIdeals` gives the same equalities
  after restriction or pullback. There is no additional choice of comparison which
  could violate that compatibility. The recorded ordered earlier ideals can also
  be pulled back along the diagrams to the final stage. An intrinsic identity
  blowup therefore does not erase its exceptional information. Empty stages under
  smooth pullback are collapsed according to the ambient ideal, not according to
  whether the intrinsic morphism happens to be an isomorphism.
* Clause (4) is `termination`: there cannot exist histories `H n` of each finite
  length n, compatible one-step extensions E n, all with `IsMaximumStep value (E n)`.
  Its length-zero term is an empty history and induction makes every prefix admissible.
  This is exactly exclusion of an infinite maximum-center process from each initial
  pair; no well-foundedness hypothesis on the arbitrary value order is added.

Dependency declarations read and reused:

* `Sheaf.AlgebraicGeometry.LabeledEmbeddedResolution`: `EmbeddedResolutionPair` and
  `EmbeddedResolutionSmoothMap`; the owning existing DAG node is
  `def-trf-labeled-embedded-resolution`, cited by the new history definition. A
  completed `LabeledEmbeddedResolutionTower` assumes a final regular scheme and
  cannot replace a finite intermediate history; it was not copied.
* `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Properties`: `IsReduced`;
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`;
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsSeparated`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
* `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup`, `blowupMap`;
  `WeilConjectures.Compactification.StrictTransform`: `strictTransform`,
  `strictTransformMap`, `strictTransformToSource` and the ideal-sheaf specialization.
  The latter is the scheme-theoretic image of the open complement in the fiber
  product, not a replacement by topological closure.
* `Sheaf.AlgebraicGeometry.IsRegularScheme`: `IsRegularScheme`, exactly
  `IsLocallyNoetherian ∧ IsRegular`; the local ring test is the existing
  `IsRegularLocalRing`.
* `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`:
  `Scheme.IdealSheafData.toModules`, the actual ideal module. Coherence uses the
  exact audited `Scheme.Modules.IsFiniteTypeWithFiniteTypeKernels` from
  `WeilConjectures.AlgebraicGeometry.Cohomology.FiniteFibre`. I read its full
  signature and docstring in the published framework. The pqf-def-coherent record's
  `IsQuasiCoherentFiniteType` alone does not expose the coherence kernel condition;
  its closed slopmaster2 audit already supplies this exact class, as used in the
  reviewed labeled-tower interface. This delivery uses that existing class, without
  redefining coherence or altering the dependency node.

The theorem imports every recorded proof-dependency module available now, privately:
ReducedInducedClosedSubscheme, the upstream etale reduced theorem, SmoothGeometricallyNormal,
FlatUnderRegular, finite-type-algebra Noetherianity, finite presentation over Noetherian
rings, regular-perfect-field smoothness, proper/smooth base change, etale base change
and smooth composition. The four new stage-1 lower inputs (Hilbert--Samuel smooth
profile, local presentations, numerical marked-ideal engine and smooth-center blowup
geometry) have no recorded Lean declaration yet, so no fictional import was added for
them. The entire seven-step DAG proof, with its dependency ids, is in the theorem
docstring for the later proof worker.

Edge cases checked before and during statement writing: n = 0 has no center index and
an initial pair up to the specified isomorphisms; empty and regular X have no positive
maximum and admit no maximum extension. Empty images remain finite and no greatest
value is demanded of the empty image. A smooth pullback missing every center has m = 0:
the monotone stage map is constant and all ambient center ideals pull back to top;
no impossible endpoint-preserving injection is used. A retained intrinsic identity
blowup keeps its earlier ideal. Different-dimensional components and smooth maps with
varying relative dimension are admitted by the existing pair and smooth-map types.
Both closed and generic points are in the same unqualified pointwise quantifier.
The common value type lives in Type (u + 1), enough for the family of u-small schemes;
there is no test-object quantifier in an independently smaller universe. No unbound
universe or implicit variable is used (`autoImplicit false` in every module).

Searches: msearch LeanFinder queries about simultaneous embedded resolution invariant
and about finite smooth-cartesian histories returned only ordinary smoothness, standard
smooth algebras, regular sequences and spectrum dimension lemmas. msearch LeanSearch
queries about finite embedded histories and local invariant calculus returned finite
scheme morphisms, finite simplicial pullbacks and smooth manifold embeddings. Loogle
`HilbertSamuel, ResolutionInvariant, EmbeddedResolution` returned unknown HilbertSamuel;
Loogle `"blowup"` returned no hits. Mathlib grep for
`EmbeddedResolutionHistory|ResolutionInvariantCalculus|IsResolutionStratumIdeal` returned
zero hits. The same identifiers and `AdmissibleHistory` had no hits in upstream
WeilConjectures, the side Sheaf library or the DAG before writing. Blueprint-reference
searches `admissible history`, `resolution invariant` and `embedded history` returned
zero blueprint definitions. Broader source searches found the reused labeled embedded
resolution interface and only unrelated Popescu desingularization and eventual
Hilbert--Samuel growth. Exact outputs of the three required search kinds, plus source
and DAG searches, are retained in each new node's mathlib_searches.

Validation: all three modules are compiled separately in dependency order through
scompile.py. The initial namespace and finite-index coercion errors were repaired in
the sandbox. No tests or global library build were run. The delivery dry run and final
push are performed through deliver2.py; their results are recorded below.

## New nodes

`def-trf-admissible-embedded-history` owns EmbeddedResolutionHistory.lean and its
finite diagram, extension, smooth/deletion comparison, intrinsic comparison and
admissibility definitions. Source: ILO VIII 2.3.1, 2.3.4, 2.3.11--2.3.13 and BMT 6.3.
The existing labeled-tower definition supplies the initial pairs but imposes a final
resolution, so it cannot describe the finite histories needed here. Searches above
found no replacement. The main record is the raw-history structure, and every helper
is listed in lean.declarations with its source/blueprint docstring.

`def-trf-resolution-invariant-calculus-data` owns ResolutionInvariantCalculusData.lean.
It defines the data and conditions of the four clauses and the reduced stratum-ideal
predicate, without asserting existence. Source: ILO VIII 2.3.11--2.3.13; BMT Theorem
6.1, Addendum, sections 6.1--6.3. It is an interface to the specified local functions,
not a second definition of blowup, strict transform, regularity or coherence. Searches
above found no existing finite-history invariant interface. The item asserts existence
of these data with exactly its four clauses; the new definition itself has no theorem.

Final validation: deliver2.py --no-push printed OK for commit c5466b4eb6: all three
files compile individually and server preflight passes. No non-sorry warnings remain.
The item has exactly one sorry; both new definition modules have none. The final
wrapper invocation delivers this same packet with this validation note included.

## Second reading by NY

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

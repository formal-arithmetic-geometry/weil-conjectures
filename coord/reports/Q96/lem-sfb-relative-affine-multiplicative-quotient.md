## Worker report

The delivery states `AlgebraicGeometry.relative_affine_multiplicative_quotient` in
`Sheaf.AlgebraicGeometry.RelativeAffineMultiplicativeQuotient`. Its sole postponed
proof is `by sorry`. It reuses the landed real-data predicate
`AlgebraicGeometry.IsRelativeMultiplicativeType` in
`Sheaf.AlgebraicGeometry.RelativeMultiplicativeType` (Q140). The repaired
packet supplies only the quotient theorem module and its node record.
No existing node statement, proof plan, or proof dependency is changed. The item
only gains its Lean record and the two landed definition dependencies described below.

Clause-by-clause correspondence:

- The arbitrary base S is `{S : Scheme.{u}}`. `N H : Grp (Over S)` have actual
  multiplication, unit, inverse and group diagrams; `i : N ⟶ H` is an actual
  homomorphism. These are Mathlib group objects, rather than abstract groups of
  geometric points or an unspecified action.
- Smoothness of H over S is `[Smooth H.X.hom]`; relative affineness is
  `[IsAffineHom H.X.hom]`, which permits a nonaffine base S. Finite presentation
  is the three binders `LocallyOfFinitePresentation`, `QuasiCompact` and
  `QuasiSeparated` on that structural morphism, exactly the convention of
  def-weil-pbc-scheme-conventions. `[GeometricallyConnected H.X.hom]` means
  connected, nonempty geometric fibres. Mathlib tests all field-valued fibres;
  this is equivalent to the algebraically closed fibre condition and includes
  the nonempty requirement of `ConnectedSpace`.
- The closed subgroup inclusion is `[IsClosedImmersion i.hom.hom.left]`.
  Closed immersions are monomorphisms; hence the already bundled homomorphism
  gives a subgroup on all test schemes. `hnormal` asks that the range of
  `IsMonHom.monoidHom i.hom.hom T` be normal for every `T : Over S`, not just
  for field-valued points. This is the relative normal-subgroup condition.
  The upstream `IsNormalSubgroupScheme` is specifically over a field, so it
  is inapplicable here; its normal-range condition is expressed directly with
  Mathlib's existing normal-subgroup predicate, without copying a definition.
- `hN : IsRelativeMultiplicativeType N` is precisely an fppf-local form of
  D(M) for finitely generated additive abelian M. In the landed definition, `I`,
  `R : I → CommRingCat.{u}`, `f` give affine covering charts;
  `Presieve.ofArrows ... f ∈
  Scheme.fppfPrecoverage S` is the jointly surjective flat locally finitely
  presented covering condition. The clause `∀ i : I, ∃ (M : Type u) (_ : AddCommGroup M)
  (_ : AddGroup.FG M), ...` allows a different finitely generated group on every chart.
  The final `Nonempty (... ≅ ringDiagonalizableGroup ... )` is an isomorphism
  of GROUP schemes on each chart, with the actual pullback operations. It is
  not merely a scheme isomorphism. The existing ringDiagonalizableGroup uses
  the group-algebra Hopf structure, so e_m has coproduct e_m tensor e_m.
  Such a group is automatically of finite presentation by fppf descent,
  as Conrad explicitly notes after Definition B.1.1; no additional arbitrary
  data or smoothness hypothesis is substituted for this property.
- The existential `J : Grp (Over S)` and `q : H ⟶ J` give the representing
  group and its homomorphism. Their structural smoothness, affineness, finite
  presentation and connected geometric fibres are the first six conjuncts.
- Faithful flatness of q is `Flat q.hom.hom.left ∧ Surjective
  q.hom.hom.left`. Its finite presentation is again the LFP, QC, QS triple.
- `IsFppfGroupQuotient i q` is the EXISTING definition registered by
  def-sfb-fppf-group-quotient-presentation. Its first conjunct is the
  scheme-theoretic kernel square, `IsPullback i (toUnit N) q η[J]`, in
  `Over S`; the forgetful functor creates these pullbacks, giving exactly
  N = H times_J S on underlying schemes.
- The same predicate supplies an isomorphism `H.X ⊗ N.X ≅ pullback q q`
  with first projection `fst H.X N.X` and second projection
  `lift (fst H.X N.X) (snd H.X N.X ≫ i.hom.hom) ≫ μ[H.X]`. Thus it is
  exactly (h,n) ↦ (h,h i(n)), rather than an arbitrary isomorphism.
- The predicate also requires that h_J be an fppf sheaf, and a map from the
  coequalizer of these two action/projection maps of representable presheaves
  to h_J, whose composite with the coequalizer projection is h_q. For every
  fppf sheaf Z, precomposition with this map is bijective on morphisms into
  Z. Since the pointwise coequalizer is H(T)/N(T), this is exactly its
  sheafification with the specified quotient map. The predicate further
  records fppf local surjectivity, already implied by the stated faithfully
  flat finitely presented q; it adds no geometric restriction.
- The final `∀ (S' : Scheme.{u}) (f : S' ⟶ S)` repeats every conclusion
  for `(Over.pullback f).mapGrp.obj J` and the ACTUAL pullbacks of i and q.
  In particular `IsFppfGroupQuotient` is asserted again for those pullbacks,
  retaining the kernel, torsor projection formulas, group operations and
  sheafification identification. There is no flatness assumption on f.
  The two sheafification universal properties determine the usual unique
  quotient comparison commuting with q. The theorem has no reductivity
  assumption on H and no smoothness assumption on N.

Dependency declarations read and used:

- def-pc-scheme: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- def-sfb-ring-diagonalizable-group:
  `Sheaf.AlgebraicGeometry.RingDiagonalizableGroup`,
  `AlgebraicGeometry.ringDiagonalizableGroup`; read its full definition and
  docstring, including the underlying Hopf-spectrum construction.
- def-pc-fppf-site: `Mathlib.AlgebraicGeometry.Sites.Fpqc`,
  `Scheme.fppfPrecoverage` and `Scheme.fppfTopology`; its slice topology
  `Scheme.fppfTopology.over S` is used by IsFppfGroupQuotient.
- def-sbc-smooth-morphisms: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.Smooth` (the affine-local ring-map notion, equivalent
  to the node's infinitesimal formulation).
- def-weil-pbc-scheme-conventions: convention-only record, no declaration to
  import; finite presentation is LFP plus QC plus QS, relative affineness
  is IsAffineHom, and faithful flatness is flatness plus surjectivity.
- def-weil-connected-scheme: `Mathlib.Topology.Connected.Basic`,
  `ConnectedSpace` (extends PreconnectedSpace with Nonempty); used through
  `Mathlib.AlgebraicGeometry.Geometrically.Connected`,
  `AlgebraicGeometry.GeometricallyConnected` and its field-fibre condition.
- def-weil-closed-immersion:
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion` (closed embedding plus stalk
  surjectivity); the underlying morphism of i uses it directly.
- Added landed definition dependency def-sfb-fppf-group-quotient-presentation:
  `Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry`,
  `AlgebraicGeometry.IsFppfGroupQuotient`. Read its entire signature, body
  and source docstring. It is already relative over arbitrary schemes;
  the field restriction of its original theorem consumer is not imposed.
- Landed def-sfb-relative-multiplicative-type (Q140):
  `Sheaf.AlgebraicGeometry.RelativeMultiplicativeType`,
  `AlgebraicGeometry.IsRelativeMultiplicativeType`, the predicate described above.

All seven recorded project proof-dependency modules are imported as plain
imports, together with the matching Mathlib modules for affine permanence,
closed-immersion permanence, pullback spectra, fppf covers, subcanonicity,
Yoneda, qcqs permanence and smooth ring-map base change. The coaction-grading
and strong-grading-torsor-algebra proof nodes have no recorded declarations
at the time of writing and hence no module to import. Their mathematical
steps remain in the theorem docstring. Every theorem proof remains sorry.

Edge cases checked before writing:

- Empty S: the definition permits I empty; every group scheme over the
  empty scheme is empty, and geometric-fibre conditions are vacuous. No
  Nonempty assumption on S or on the covering index has been inserted.
- Trivial N = D(0): the quotient is H and q is the identity; both kernel
  and torsor formulas specialize correctly. Rank-zero diagonalizable
  groups are included by AddGroup.FG, which has no positivity condition.
- H = N of multiplicative type when H is smooth connected: the quotient
  is the trivial S-group. The structural map H → S supplies the fppf
  quotient, and the kernel square has the claimed orientation.
- N = mu_p inside G_m in characteristic p: this non-smooth N is allowed;
  q is the p-th power map. Nothing requires smoothness or reducedness of N.
- Nonreduced and nonaffine base schemes are allowed: charts are affine,
  but neither S nor H's total space is required to be globally affine.
  Only the structural morphisms are affine.
- Disconnected S permits varying M_i; no constant rank or constant
  character-group hypothesis is introduced.
- Arbitrary base change includes f = identity, the empty base, nonflat
  maps, and nilpotent closed immersions. The same maps i and q are pulled
  back. All object, test-scheme, character and covering universes are
  explicitly u; no independent smaller test universe makes normality or
  the quotient property vacuous. autoImplicit and relaxedAutoImplicit
  are explicitly false.

Original searches before the Q140 landing (actual queries and digests are in searches.jsonl):

- LeanFinder: "Quotient of smooth affine group scheme by normal
  multiplicative type subgroup is affine fppf torsor". Eight unrelated
  affine-space, Galois-category and abstract-group quotient results;
  no theorem matching this relative assertion.
- Loogle: "AlgebraicGeometry.IsNormalSubgroupScheme, Grp,
  AlgebraicGeometry.Scheme.fppfTopology". No result; unknown first name.
- Mathlib grep via msearch.py:
  "multiplicative.?type|IsFppfGroupQuotient|NormalSubgroupScheme" in
  AlgebraicGeometry: no hits.
- LeanSearch: "group scheme over arbitrary scheme locally diagonalizable
  multiplicative type fppf" and "group scheme fppf locally diagonalizable
  over arbitrary base scheme multiplicative type". Eight unrelated
  type-tag and morphism-property results for each; no relative predicate.
- LeanFinder: "group scheme over scheme fppf locally isomorphic to
  diagonalizable group of finitely generated abelian group". Eight
  unrelated affine-space, finite-scheme, profinite-group and Galois-category
  results; no relative predicate.
- Loogle: "AddGroup.FG". Exact finite-generation class and standard lemmas
  found in Mathlib.GroupTheory.Finiteness; reused.
- rg on lean/WeilConjectures and lean/Sheaf for
  IsRelativeMultiplicativeType, relative_multiplicative,
  IsFppfGroupQuotient, multiplicative-type and diagonalizable names.
  Found the recorded ringDiagonalizableGroup, field-only multiplicative
  type, relative tori, and the already defined relative quotient predicate.
  No existing theorem stated this quotient assertion, and no relative
  multiplicative-type predicate existed at the original search time. The repair
  now reuses the Q140 predicate, read from current main and server source. Searching the item id upstream
  also gave no hit. A scan of definition-node statements confirmed these
  notions and the already landed quotient-presentation definition node.
- `python3 tools/blueprint_refs.py search 'multiplicative type'` returned
  zero blueprint nodes. The ancestor command reports null, inherited
  from this item's blueprint.from.node; the new node preserves that null
  and prepends the item to its via list, as other nodes in this route do.

Sources read: the node and all statement dependencies with their full
records, the recorded Lean declarations and their docstrings, Conrad's PDF
at Definition B.1.1 (printed p.280) and the quotient discussion in Lemma
3.3.2 (printed p.98). The fppf-local definition agrees exactly with B.1.1;
refining the charts by affine opens changes no condition. Conrad's quotient
discussion treats the central case; the accepted node's eight-step
strong-grading/descent proof covers its stated normal-subgroup generality.
There is no statement correction and no STATEMENT-DISPUTED finding.

## Landed definitions reused

`def-sfb-relative-multiplicative-type` is now a landed Q140 definition node.
Its recorded module and declaration have the same names used by the theorem's
existing public import and hN binder. Its definition uses bundled commutative
rings and chartwise existential finitely generated character groups. This is the
same fppf-local notion as the removed Q96 definition: bundling the rings and
moving the character witnesses under each chart changes no hypothesis.
The Q96 copies of the definition node and module are removed from this packet;
neither landed file is modified. There are no new nodes or dependency modules.

`def-sfb-fppf-group-quotient-presentation` is also already landed (Q95) and is
reused without copying or modifying its node or module.

## Second reading by Q96

A separate second reading of the source node, final module, landed definition
node and the full existing IsFppfGroupQuotient definition was performed by
this worker. No additional agent was started, as required by the dispatcher.
The read checked the following independently of the first drafting pass:

- H's smoothness, relative affineness, finite presentation and connected
  geometric fibres match the six binders, without restricting S to a field.
- i is a closed subgroup homomorphism; normality is tested on every
  S-scheme, including nilpotent tests. The first compile identified the
  missing MonObj scope for the existing group structure on hom-sets;
  opening that existing scope fixes elaboration without changing normality.
- hN's splitting isomorphisms are in Grp (Over (Spec R_i)), not in schemes
  alone; finitely generated groups and chartwise variation are retained.
  Empty covers, D(0) and characteristic-p mu_p remain admissible.
- J is an actual group scheme and q is a bundled homomorphism. All six
  structural properties, faithful flatness and finite presentation of q
  appear in the conclusion.
- The existing predicate has the exact kernel-square orientation, the two
  requested torsor projections, the coset presheaf and its actual
  sheafification universal map; the map agrees with h_q.
- Every resulting property is repeated for the literal base-changed group
  and maps for every f. No flatness, centrality, reductivity or smoothness
  of N was added.
- The source statement and its proof plan remain unchanged. The item adds the
  two landed definition dependencies to stmt_deps. Its Lean signature still
  matches the theorem file verbatim. The landed multiplicative-type definition
  supplies the same arbitrary-base fppf splitting notion, with varying finitely
  generated characters, empty covers and no smoothness condition on N.

No semantic mismatch was found. The return concerns the duplicated definition
packet rather than the theorem's hypotheses or conclusions.

## Returned delivery repair

Return on immutable head 53ef756cc85f: L reported that the new node
`def-sfb-relative-multiplicative-type` already exists on sheaf-dag, created by
another delivery. Repaired by deleting the sandbox copies of that node and its
module from the delivery. Read Q140's landed node, its full definition and its
server source through `scompile.py --source`. The theorem already imports the
same module and uses the same declaration; its signature needs no change.
Both added stmt_deps now refer to existing landed nodes. Compared the retained
item node with current main: all fields except lean and the two added stmt_deps
are identical. The repair is removal of the conflicting files and reuse of the
landed definition, rather than an unchanged re-push. Only the theorem module,
item node record and this report are submitted. The wrapper rebases this packet
onto current sheaf-dag. Required compile and dry-run results follow.

Repair validation: `scompile.py Q96 lem-sfb-relative-affine-multiplicative-quotient
lean/Sheaf/AlgebraicGeometry/RelativeAffineMultiplicativeQuotient.lean` returned
exit code 0 against the landed Q140 dependency, with no errors or unexpected
warnings. Both the sandbox-module and library-module checks passed. The wrapper
reported 28.4 s and 999.2 s respectively, including server scheduling; no timeout
setting was changed.

The repaired packet's required dry run returned `OK (dry run): commit c8ee59b306c
passes the preflight and compiles; nothing pushed`. Its staged set contains only
this report, the item's node and the quotient theorem module; neither the landed
multiplicative-type node nor its module is included.

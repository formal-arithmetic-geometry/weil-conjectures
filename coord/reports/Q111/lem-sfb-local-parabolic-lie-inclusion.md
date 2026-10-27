## Worker report

The main module is `Sheaf.AlgebraicGeometry.GroupScheme.LocalParabolicLieInclusion`.
Its one postponed theorem is
`AlgebraicGeometry.LocalParabolic.local_parabolic_lie_inclusion`; all definitions
have actual data. The item statement is unchanged. Two missing notions are
supplied as new definition nodes, and existing terminology nodes are added to
stmt_deps. No dependency record is replaced.

Clause correspondence:

- A nonzero commutative Noetherian local ring is `A : Type u`, `[CommRing A]`,
  `[IsNoetherianRing A]`, `[IsLocalRing A]`. The last class extends `Nontrivial A`;
  no additional nontriviality hypothesis is needed. The closed residue field is
  exactly `IsLocalRing.ResidueField A`, with quotient map `residue A`.
- The base is `Spec (.of A)`. `G P Q T : Grp (Over ...)` are actual group schemes,
  with the group operations and their diagrams from Mathlib's `GrpObj`.
- Smooth, affine and finitely presented G are `[Smooth G.X.hom]`,
  `[IsAffineHom G.X.hom]`, `[LocallyOfFinitePresentation G.X.hom]`.
  An affine morphism is quasi-compact and separated, so local finite presentation
  is finite presentation here, with no extra assumption or lost case.
- Connected reductive geometric fibres are `hred`, quantifying over every
  algebraically closed field and ring map `A →+* F`. It uses the existing
  `ReductiveTorusCentralizer.IsReductive`, including geometric connectedness and
  the exclusion of smooth connected normal unipotent subgroups. Its existing
  unipotence predicate is faithful smooth matrix unipotence, not just a condition
  on rational points.
- Smooth closed subgroup embeddings are `iP`, `iQ`, their `IsClosedImmersion`
  instances and `[Smooth P.X.hom]`, `[Smooth Q.X.hom]`. Since the arrows are in
  `Grp`, they respect the group law. No reducedness hypothesis is added.
- Parabolic geometric fibres are `hP`, `hQ`: the new `HasParabolicFibres` requires
  smooth connected fibres and a Borel embedding factoring through the subgroup.
  The existing Borel definition supplies maximal smooth connected solvability
  in the scheme-theoretic derived-series sense.
- The common torus is `iT`, its closed immersion instance, and `jP`, `jQ` with
  `hjP`, `hjQ`. Its split rank is arbitrary `r : ℕ` with group-scheme isomorphism
  `eT : T ≅ RingGroupSchemes.splitTorus A r`. `hmax` says the base-changed
  inclusion is a maximal torus at every geometric point.
- `lieImage` is the range of the existing differential of the closed-fibre
  inclusion. The differential sends a dual-number tangent point to its composite
  with the embedding, so these are precisely the stated tangent subspaces.
- First conjunct: `lieImage iQ ≤ lieImage iP → ∃ j : Q ⟶ P, j ≫ iP = iQ`.
  This expresses closed-subgroup containment by factorization of the embeddings.
  The factorization itself is necessarily a closed immersion because the two
  embeddings are closed immersions.
- Second conjunct: equal tangent ranges imply `∃ e : P ≅ Q, e.hom ≫ iQ = iP`.
  This is equality as embedded closed subgroup schemes; literal equality of
  separately chosen group-scheme representatives would be inappropriate.
- The final conjunct assumes `HasBorelFibres` for both subgroups. Their nonzero
  character supports are `{χ | χ.hom.hom ≠ 1 ∧ weightImage ... χ ≠ ⊥}`.
  Equality of these supports implies the same embedded subgroup isomorphism.
- `weightImage` is the intersection of the ambient full-character weight space
  with the subgroup tangent range. Containing T makes the range stable under
  conjugation, so this is exactly its tangent weight summand inside Lie(G_k).
- The trivial character is `0`, the categorical zero morphism (its underlying character is constant one). Both
  corresponding `weightImage` spaces equal `lieImage iT`.
- For each nontrivial character, if either subgroup weight summand occurs, it
  equals `UniversalConjugationWeight.weight` in the ambient tangent space, and
  that space has `Module.finrank (ResidueField A) ... = 1`. Both P and Q clauses
  are included separately.

Definitions used and inspected:

- Mathlib.CategoryTheory.Monoidal.Grp: `GrpObj`, bundled `Grp`, `Grp.homMk`.
- Mathlib.AlgebraicGeometry.Scheme: `Spec`, `Spec.map`.
- Mathlib.RingTheory.Noetherian.Defs: `IsNoetherianRing`.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: `AlgebraicGeometry.Smooth`.
- Mathlib.AlgebraicGeometry.Morphisms.Affine: `IsAffineHom`.
- Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation:
  `LocallyOfFinitePresentation`.
- WeilConjectures.AlgebraicGeometry.GroupScheme.Defs:
  `IsClosedSubgroupScheme`; the group-scheme convention is explicitly documented
  there and works over this general affine base through `Over`.
- WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring:
  `GrpObj.tangentPoint`, `points.map`, `tangentGroup`.
- WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Differential:
  `GrpObj.differential`, its full signature and dual-number docstring.
- Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology:
  `ReductiveTorusCentralizer.IsReductive`, `IsMaximalTorus`.
- Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusOverRing:
  `RingGroupSchemes.splitTorus`.
- Sheaf.AlgebraicGeometry.GroupScheme.Borel: `IsBorelGroupScheme`.
- Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces:
  `RankOneRoots.Character`, `multiplicativeValue`.
- The existing character tangent predicate
  `TorusCharacterTangent.weightSpace` was inspected but is not a usable replacement
  for the new space: it tests only k-rational points and agrees with full character
  spaces only under the documented density assumptions. We reuse its existing
  characters, coordinate evaluation and tangent points, not its restricted test.

Available proof dependencies are imported without `public`:
`Mathlib.RingTheory.FiniteType` (finite-type algebras over Noetherian rings),
`Mathlib.RingTheory.LocalRing.Module` (Nakayama), and
`Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections`.
The remaining proof dependencies have no recorded declaration/module at delivery
preparation and are not imported speculatively. Their six-step mathematical proof
is included in the theorem docstring; none is needed to state this item.

Edge cases: rank zero (empty root support), P=Q, P=G, Q=G, arbitrary positive
characteristic including small primes, nonreduced Noetherian local bases, finite
residue fields and non-henselian local rings. Zero rings are excluded by the
node and by IsLocalRing. All geometric fields and algebra test objects use the
base universe u, never a smaller independent universe. Universal weight tests
include nonreduced algebras and use actual characters rather than differentials.
For a torus, the zero weight space is the full torus tangent space and the
nonzero clauses are vacuous, as required.

Searches were made with msearch.py (raw results in searches.jsonl):

- leanfinder: "Parabolic subgroup schemes containing a common split maximal torus
  over a local ring are ordered by their closed fibre tangent Lie algebras":
  8 hits, only abstract Lie and root-system lemmas, no group-scheme comparison.
- loogle: `"Parabolic", "Lie"`: 0 hits.
- grep in Mathlib/AlgebraicGeometry: `parabolic|Parabolic|Borel`: 0 hits;
  `weightSpace|conjugationWeight`: 0 hits.
- leansearch: "Character weight spaces of the conjugation action of a split torus
  on the tangent Lie algebra of a group scheme": 8 abstract Lie-weight hits.
- leanfinder: "Geometric fibres of a subgroup scheme are parabolic when they are
  smooth connected and contain a Borel subgroup": 8 unrelated hits.
- leansearch: "A parabolic subgroup scheme is smooth with connected geometric
  fibres containing a Borel subgroup": 8 smooth-morphism hits, no parabolic notion.
- rg in project WeilConjectures and Sheaf: no occurrence of the item's id;
  inspected Borel, reductive, split-torus, rank-one character and tangent modules.
- rg in DAG definition nodes and `tools/blueprint_refs.py search` for
  "parabolic subgroup" and "character weight": no node giving the missing
  relative parabolic predicate or full algebra-valued character space.

Primary source read: Conrad's PDF at
https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf, Corollary 5.2.7(2),
printed p.155. It gives neighbourhood containment and equality; every open
neighbourhood of the closed point of a local spectrum is the whole spectrum.
No statement correction or STATEMENT-DISPUTED issue was found.

## New nodes

`def-sfb-geometric-parabolic-subgroup` defines canonical scalar extension and
geometric Borel/parabolic fibres over a ring. It builds on the existing Borel
predicate and pullback, rather than restating Borel maximality. Source: Conrad,
Definition 5.2.1 and Corollary 5.2.7. Searches above found no relative predicate.

`def-sfb-universal-conjugation-weight` defines the explicit dual-number map
ε↦bε and the full character eigenspace using conjugation on all algebra-valued
points. Source: Conrad, Section 4.1 and the weight argument of Corollary 5.2.7.
Its data use Mathlib's DualNumber.lift universal property, not a choice from an
existence theorem. The existing rational-point eigenspace differs over finite
fields; thus it is not a duplicate of def-sfb-torus-character-tangent-weights.

## Second reading by Q111

The dispatcher explicitly prohibits starting other agents and assigns the
maintainer the independent delivery review. This section records the worker's
second pass, not an independent-agent review. I compared the node and the
three modules again: all hypotheses and the three conclusion groups are mapped
above, including the often missed zero weight and dimension-one assertions.
The initial attempt to write the trivial character as a numeral in the bundled
Hom failed elaboration; it was replaced by the categorical zero morphism `0`, with nontriviality
stated on the underlying character morphism. I checked that the new weight
construction scales the infinitesimal coordinate, not the base coefficient,
and tests all B-points. The equality uses an embedding-compatible isomorphism,
and both directional subgroup-containment claims have the required orientation.
No statement text was changed. The independent mathematical reading remains the
maintainer's prescribed review.

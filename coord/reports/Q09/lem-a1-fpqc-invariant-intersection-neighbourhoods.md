## Worker report

The module `Sheaf.AlgebraicGeometry.FpqcInvariantIntersectionNeighbourhoods` states
`CategoryTheory.Over.DescentDatum.exists_fpqc_invariant_intersection_neighbourhood`, with
proof `sorry`. Its only other declaration is the actual canonical construction
`CategoryTheory.Over.DescentDatum.descentRelationTarget`, obtained directly from the
recorded datum's universal transport. No theorem is proved, no definition contains
postponed data, and the item's natural statement and dependency lists are unchanged.

The earlier attempt left only dispatcher brief markers in the sandbox. The shared node
is split and independently reviewed by NM, but has no `lean` record. That is a stage-1
review, not a Lean statement or an existing-declaration match. This delivery supplies
the missing stage-2 work; it does not resubmit the split.

Hypothesis and clause correspondence (node and source read in full):

- Schemes X and S: `{X S : Scheme.{u}}`; both are affine: `[IsAffine X] [IsAffine S]`.
- The specified morphism p: `(p : X ⟶ S)`; flatness and surjectivity:
  `[Flat p] [Surjective p]`. Neither is replaced by local finite presentation or openness.
- A scheme V over X: `{V : Over X}`, with underlying scheme `V.left` and structure
  morphism `V.hom`. Quasi-separatedness of V is `[QuasiSeparatedSpace V.left]`, using
  the recorded Mathlib equivalence with quasi-separatedness of the terminal morphism.
  No quasi-compactness of V, separation of V, or affine structure on V is assumed.
- The given descent datum: `(D : Over.DescentDatum p V)`. This is the recorded transport
  encoding of exactly the isomorphism and cocycle in `def-pd-descent-datum`; the full
  upstream docstring and structure were read. Identity and cocycle are structure laws,
  not additional hypotheses.
- For every v: `(v : V.left)` is a theorem argument.
- The open subscheme W and the subset E: `∃ (W : V.left.Opens) (E : Set V.left)`.
  `Scheme.Opens` parametrizes open subschemes with their induced structure sheaves.
- The inclusions v in W contained in E: `v ∈ W ∧ (W : Set V.left) ⊆ E`.
- E is an intersection of a nonempty set-indexed family of quasi-compact opens:
  `∃ 𝒰 : Set V.left.Opens, 𝒰.Nonempty ∧
  (∀ U ∈ 𝒰, IsCompact (U : Set V.left)) ∧
  E = ⋂ U ∈ 𝒰, (U : Set V.left)`.
  A set of opens suffices for every set-indexed family by taking its range; repeated
  members have no effect. There is no finite, countable, or fixed small-index restriction.
- Put R = `Limits.pullback (V.hom ≫ p) p`, with s its first projection and q its second.
  `D.descentRelationTarget` is t, the universal transport of the point s from s ≫ V.hom
  to q, with the commuting equation provided by the chosen pullback. Thus the descent
  isomorphism φ has components (q,t). This is the actual canonical target, not an
  arbitrary morphism constrained by a separate hypothesis or a choice from `Nonempty`.
- The first equality is
  `Limits.pullback.fst (V.hom ≫ p) p ⁻¹ᵁ W = D.descentRelationTarget ⁻¹ᵁ W`.
  This equality is in `R.Opens`, so it is an equality of the induced open subschemes.
  Since t = pr_V ∘ φ, the right side is φ⁻¹(X ×_S W); the left side is W ×_S X.
  Applying the isomorphism φ recovers exactly φ(W ×_S X) = X ×_S W.
- The second equality is
  `(Limits.pullback.fst (V.hom ≫ p) p) ⁻¹' E = D.descentRelationTarget ⁻¹' E`.
  This is equality of subsets of |R|, equivalent by the same isomorphism to
  φ(E ×_S X) = X ×_S E. E is not asserted open or given a scheme structure.

Dependency declarations used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and
  `Scheme.Hom`, with `Scheme.Opens` for the induced open subschemes.
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
  `AlgebraicGeometry.Flat`; its docstring and `Flat.iff_flat_stalkMap` identify the
  recorded affine-local class with the node's stalkwise notion.
- `def-weil-surjective-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`,
  `AlgebraicGeometry.Surjective`, whose field is surjectivity on underlying points.
- `def-weil-quasi-separated-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`,
  `AlgebraicGeometry.QuasiSeparated`, using `quasiSeparatedSpace_iff_quasiSeparated`.
- `def-pd-descent-datum`:
  `WeilConjectures.CategoryTheory.Comma.Over.DescentDatum`,
  `CategoryTheory.Over.DescentDatum` and its `transport` projection. The universal
  transport constructs the target in this module; no duplicate descent datum is defined.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `.fst`, `.snd`, and `.condition`; scheme pullbacks
  are supplied by `Mathlib.AlgebraicGeometry.Pullbacks`.

Statement dependency modules are public imports. Already stated proof inputs are imported
without `public`: affine morphisms and permanence, closed immersions and closed subschemes,
flat generalization lifting, scheme spectrality, the recorded
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
(`exists_specializes_of_mem_closure_range`),
`Sheaf.AlgebraicGeometry.DescentOrbitSaturated` (`descent_orbit_saturated`), and
`Sheaf.Topology.SpectralGeneralizations`
(`Topology.generalizations_isCompact_sInter_isCompactOpen`). The affine-open basis,
compact preimages, and open-immersion interface are provided by these imports and the
public statement dependencies. The declaration docstring carries every step of the
node's eight-step natural-language proof and its cited inputs. No import cycle is added.

Sources checked: local `literature/stacks-project/groupoids.tex`,
`lemma-constructing-invariant-opens` (03LO), `lemma-first-observation` (0APA),
`lemma-second-observation` (0APB), and `lemma-cartesian-equivalent-descent-datum` (0APF);
`literature/stacks-project/more-groupoids.tex`, `lemma-ind-quasi-affine` (0APK),
the paragraph translating the construction to properties (a) and (b).

Edge cases checked before writing:

- Empty V: the quantification over v is vacuous; no `Nonempty V` is added.
- Empty S (hence empty X under p): again no unwanted nonemptiness is required.
- Identity p: transport_self makes invariance automatic, and an affine open around v
  can be used for W and E, with a singleton family. No obstruction is introduced.
- V not quasi-compact: neither E nor W is required to be all of V. In particular the
  statement does not force a compact-space instance on V or require W quasi-compact.
- The family of opens is explicitly nonempty, as in the source. Empty or repeated
  members are otherwise permitted, and no set-universe case is excluded by encoding
  the family as its range in the set of all opens.
- The equalities concern inverse images on the actual scheme fibre product, including
  all its points; they are not tests restricted to rational or geometric points.

Searches made with the authorized tools, 2026-10-18:

- `msearch.py ... leanfinder`: "For a faithfully flat morphism of affine schemes, a
  descent datum on a quasi separated scheme has invariant open neighbourhoods inside
  invariant intersections of quasi compact opens". Eight hits: affine-transition
  covers, local-at-target descent lemmas, descent of universally open/open-immersion
  properties, flat and surjective descent, and qcqs powers. None constructs W and E.
- `msearch.py ... leansearch`: "A scheme with descent data along a flat affine cover
  has invariant open neighbourhoods contained in invariant intersections of quasi
  compact open subsets". Eight hits: `Scheme.Cover.gluedCover`, affine covers and
  generic descent of isomorphisms/open immersions/local properties. No exact match.
- `msearch.py ... loogle`: `"invariant", "IsOpen"`. Twelve hits, all measure-theoretic
  or topological monoid-action facts; no scheme-descent neighbourhood theorem.
- `msearch.py ... grep`, AlgebraicGeometry:
  `invariant.*[Oo]pen|[Oo]pen.*invariant|groupoid.*[Qq]uasi`. Zero hits.
- `rg -n -i 'invariant.*open|open.*invariant|descentRelationTarget|descent.*target|groupoid.*quasi'`
  in the source `WeilConjectures/`, shared `lean/Sheaf/`, and
  `dag/lean_names_upstream.json`. Existing hits concern affine/open descent, finite
  descent, and uses of this very missing lemma. No statement of this node or canonical
  relation target helper is present. The index mentions invariant affine neighbourhoods
  for `thm-pd-effective-descent`; these concern finite descent and do not state this
  general quasi-separated assertion.
- `grep -rn 'lem-a1-fpqc-invariant-intersection-neighbourhoods'` in the upstream source:
  no hits. Additional `rg` searches for `exists_isInvariant`, universal pullback
  transports, and relation targets found no reusable helper. The existing orbit
  saturation module uses an abstract pullback presentation with t specified by the
  same universal transport, confirming the encoding used here.

No `STATEMENT-DISPUTED` finding or node correction is needed. No new nodes or dependency
modules are needed: the target helper is part of expressing this node's existing datum,
explicitly allowed by the canonical-helper rule, and has actual data.

## Second reading by Q09

Independent maintainer reading, 2026-10-18, of immutable delivery
`ecc0ed71615e8656646e9149a31bc52b88ed0b90`. This replaces the author's self-check;
the reviewer did not author or previously second-read this delivery.

I read the item, all six snapshot statement dependencies, the delivered module and
its docstrings, and the source paragraphs together. The hypothesis/clause audit is:

- `{X S : Scheme.{u}} [IsAffine X] [IsAffine S]` retains both affine schemes;
  `(p : X ⟶ S) [Flat p] [Surjective p]` retains the specified flat surjection.
- `{V : Over X}` supplies exactly the structure map; `[QuasiSeparatedSpace V.left]`
  is absolute quasi-separatedness. No compactness, separation, finite presentation,
  ind-quasi-affineness, or openness of p is assumed.
- `(D : Over.DescentDatum p V)` uses the recorded transport datum. I read its
  naturality, identity and cocycle fields at upstream DescentDatum.lean:60-90.
  These encode the descent isomorphism without strengthening its hypotheses.
- `(v : V.left)` is arbitrary. The existential `W : V.left.Opens`, `E : Set V.left`
  and `v ∈ W ∧ (W : Set V.left) ⊆ E` give exactly the requested neighbourhood
  and containment. Opens carry their induced open subscheme structures.
- The existential set of opens `𝒰`, its `Nonempty`, compactness of every member,
  and `E = ⋂ U ∈ 𝒰, (U : Set V.left)` give every intersection clause. Taking the
  range of any indexed family loses neither the intersection nor nonemptiness,
  so no index-universe restriction is introduced.
- With s the first pullback projection and q the second, the helper transports
  the universal point s from s ≫ V.hom to q. Thus t is exactly pr_V after φ.
  Its data is explicit transport, with the pullback equation discharged by
  associativity; there is no arbitrary map, choice of data, or postponed data.
- `s ⁻¹ᵁ W = t ⁻¹ᵁ W` is equality of opens of the actual fibre product, hence of
  induced open subschemes. Since φ is invertible, it is equivalent to the node's
  image equality. The last `⁻¹' E` equality is the corresponding equality of
  subsets, without asserting E open or giving E a scheme structure.

I opened the dependency declarations: Scheme and Scheme.Hom (Mathlib Scheme.lean:42,74),
IsAffine (AffineScheme.lean:59), Flat (Morphisms/Flat.lean:42) and its stalkwise
characterization (:106), Surjective (Morphisms/UnderlyingMap.lean:59), QuasiSeparated
(Morphisms/QuasiSeparated.lean:50) and its terminal-map equivalence (:133), pullback,
fst, snd and lift (CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean:95-130),
and HasPullbacks Scheme (AlgebraicGeometry/Pullbacks.lean:485). These implement the
six dependency notions exactly. No dependency repair or additional prerequisite is needed.

Sources read in the Q09 source clone: groupoids.tex:3570-3680, definitions of
invariance and lemmas constructing-invariant-opens (03LO), first-observation (0APA),
second-observation (0APB); groupoids.tex:4074, cartesian-equivalent-descent-datum
(0APF); more-groupoids.tex:3092 onward, ind-quasi-affine (0APK), specifically the
translation (a),(b). Also read schemes.tex definition-scheme and definition-separated,
morphisms.tex definition-flat and definition-surjective, and descent.tex:8101,
definition-descent-datum. The general groupoid lemmas require quasi-separatedness
and flat quasi-compact source/target maps, not ind-quasi-affineness.

The eight proof-docstring steps match the node: (1) the canonical relation and affine
flat projections; (2) singleton saturation and unions; (3) compact generalization-stable
saturation and finite affine bounding open; (4) the closed-subscheme image and its
specialization closure; (5) both directions of closure invariance and disjointness;
(6) saturation of the bounding open; (7) the spectral compact-open intersection;
(8) translation through φ. I opened descent_orbit_saturated in
Sheaf/AlgebraicGeometry/DescentOrbitSaturated.lean, the exact generalizations theorem
in Sheaf/Topology/SpectralGeneralizations.lean, and
exists_specializes_of_mem_closure_range in upstream Morphisms/QuasiCompact.lean:70.
They supply the cited interfaces without extra hypotheses. In particular, affine
intersections need only be compact, and closure-specialization requires no finite
presentation or constructibility. The elementary steps are unions and inverse-image
identities, and the final conversion by an isomorphism.

Edge cases checked: empty V and empty base (vacuous), p = identity (singleton affine
open family works), non-quasi-compact V, H = V (empty complement), repeated family
members, and arbitrary characteristic. The empty indexing family is correctly excluded
by the node and Lean alike. The universe u is arbitrary; the transport tests include
the universal pullback itself. Every variable/universe is bound.

Independent rg searches for invariant opens/neighbourhoods, saturation, and both new
names in Mathlib AlgebraicGeometry, upstream WeilConjectures and Q09 lean/Sheaf found
no duplicate. I inspected InvariantAffineNeighbourhoods.lean: its finite flat finitely
presented p and affine containment assumptions make it a different statement.
The worker report records LeanSearch, LeanFinder/Loogle and grep searches.

The module and both declarations have source/blueprint docstrings. Both new names
are recorded in lean.declarations. The sole theorem has proof `sorry`; the helper
has real data, and its `simpa` establishes only the construction's pullback equation.
There are no overlong lines, local instances/notations, or extra theorem proofs.
The node's lean.statement is byte-for-byte the theorem signature before `:= by`.
Only lean was added to the item record; no statement correction/citer audit is required.
The route-pivot dropped list has empty intersection with stmt_deps and proof_deps;
no repair note exists for this item. No dropped machinery or pro-etale substitute occurs.

Compiler evidence: the delivery report mentions an initial pullback-shadowing repair
but gives no final command/output. I reproduced the final immutable file with:

```
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q09 \
  lem-a1-fpqc-invariant-intersection-neighbourhoods \
  snapshot/lean/Sheaf/AlgebraicGeometry/FpqcInvariantIntersectionNeighbourhoods.lean
```

Exit 0, no errors or warnings. The prescribed wrapper reported a server-side private
overlay, compiling the sandbox in 5.2 s and the library-path file in 2.9 s, each
under the 60 s limit. No direct ssh, global build, or live Lean write was performed.

Finding H11: the original section explicitly said “Author self-check for direct delivery”;
it did not provide an independent second reading. Repaired by this complete replacement
report, preserving the Worker report and adding this actual independent reading and
compile evidence. No Lean or node changes are necessary. Verdict: FIX (report only).

## Worker report

The module `Sheaf.AlgebraicGeometry.IsSeparatedOfSurjectiveUniversallyClosed` states
`AlgebraicGeometry.isSeparated_of_surjective_universallyClosed` with a `sorry` proof.
No definitions, dependency modules, new nodes, or statement corrections are needed.

Hypothesis and conclusion correspondence:

- The base scheme S and schemes X, Y are `{S X Y : Scheme.{u}}`, with the universe
  explicitly bound by `universe u`. There is no finiteness or nonemptiness restriction.
- The structural morphisms p: X → S and q: Y → S are `(p : X ⟶ S)` and `(q : Y ⟶ S)`.
- The morphism f: X → Y is `(f : X ⟶ Y)`.
- The condition q ∘ f = p is `(h : f ≫ q = p)`; Lean composition is written left to right.
- Surjectivity of f is `[Surjective f]`, meaning surjectivity on underlying points.
- Universal closedness of f is `[UniversallyClosed f]`, meaning every base change
  is closed on underlying topological spaces.
- Separatedness of p is `[IsSeparated p]`, exactly that its diagonal into
  `pullback p p` is a closed immersion. The node's parenthetical description is the
  definition of this class, not an additional hypothesis or conclusion.
- The entire conclusion, separatedness of q, is `IsSeparated q`.

The single import `Mathlib.AlgebraicGeometry.Morphisms.Proper` is the recorded module
of def-weil-proper-morphism and transitively supplies every dependency declaration.
The recorded signatures and their docstrings were read in the pinned Mathlib source:

- def-pc-scheme: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom`; scheme objects and morphisms.
- def-weil-surjective-morphism: `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`,
  `AlgebraicGeometry.Surjective`; underlying map surjective.
- def-weil-proper-morphism: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsSeparated` (defined in Morphisms.Separated) and
  `AlgebraicGeometry.UniversallyClosed` (defined in Morphisms.UniversallyClosed).
  `IsProper` itself is not a hypothesis: the node requires only the two named properties.
- def-pc-fibre-product:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`; these occur inside
  the definition of separatedness, through `pullback.diagonal`, rather than as extra data.
- def-weil-closed-immersion: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`; the diagonal condition in `IsSeparated`.

Source checked: https://stacks.math.columbia.edu/tag/09MQ, Lemma 29.42.11(4) and its
last proof paragraph. The local literature/stacks-project/morphisms.tex is absent on
this machine, so the authoritative Stacks page was read directly. It has exactly
these assumptions. The docstring carries all five steps of the node's proof,
including the dependency names and the final diagonal argument.

Edge cases checked mathematically before writing:

- If X is empty, surjectivity forces Y empty; its diagonal is a closed immersion.
- If S is empty, the given structural morphisms force X and Y empty.
- If f is the identity, the commuting triangle identifies the structural maps,
  and the conclusion follows from the input separatedness.
- No reducedness, Noetherian, finite type, field, characteristic, or quasi-separated
  hypothesis is imposed. Universally closed is not replaced by proper.
- Arbitrary schemes in any common universe are allowed. No test-scheme universe
  or size-limited quantifier is introduced by this theorem.

Searches (2026-10-11):

- msearch.py leanfinder, query "If X is separated over S and X to Y is surjective and
  universally closed then Y is separated over S": eight hits, including
  `UniversallyClosed.of_comp_of_isSeparated`, `UniversallyClosed.of_comp_surjective`,
  and `IsSeparated.of_comp`. None concludes separatedness of the second map under
  the node's hypotheses.
- msearch.py loogle, query "AlgebraicGeometry.IsSeparated, AlgebraicGeometry.Surjective,
  AlgebraicGeometry.UniversallyClosed": zero hits.
- msearch.py grep, pattern
  `of_comp.*surjective|[Ss]eparated.*[Ss]urjective|[Ss]urjective.*[Ss]eparated`, directory
  AlgebraicGeometry/Morphisms: six hits, for universal closedness descent,
  surjectivity descent, and surjectivity on stalks; no exact statement.
- rg in WeilConjectures and lean/Sheaf, patterns for separatedness and surjective
  universally closed maps: found quasi-separatedness descent, universal closedness
  results and flat base-change descent; no exact statement. The latter is
  `Sheaf.AlgebraicGeometry.IsSeparatedOfFlatSurjectiveBaseChange`, concerning a
  different morphism and hypotheses.
- rg for the node id in WeilConjectures: no hits.
- rg for `isSeparated_of_surjective_universallyClosed|surjective_universallyClosed`
  in Mathlib, WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json: no hits;
  the chosen declaration name is unused.

No statement dispute or mathematical node fault was found. Server compilation and
maintainer preflight are checked by scompile.py and deliver2.py --no-push; the
independent second reading is reserved for the second reader.


## Second reading by T1

Independent reading of the node, module, dependency nodes and their actual declarations.
No mismatch found; no Lean or node changes. Only this second-reading report was appended.
There are no new definition nodes, dependency modules, or statement corrections to review.

Object, hypothesis and conclusion checklist (each passes):

- Base scheme S and schemes X and Y: `{S X Y : Scheme.{u}}`, with `universe u`.
  Mathlib `Scheme` extends a locally ringed space with local affine neighbourhoods;
  `Scheme.Hom` is a morphism of locally ringed spaces. These are the recorded
  def-pc-scheme declarations, not a specialization.
- Structure maps p and q: `(p : X ⟶ S) (q : Y ⟶ S)`.
- Morphism f over S: `(f : X ⟶ Y) (h : f ≫ q = p)`.
  Left-to-right categorical composition expresses exactly q composed with f equals p.
- Surjectivity: `[Surjective f]`. Read UnderlyingMap.lean:59: its only field is
  `Function.Surjective f`, on underlying points (def-weil-surjective-morphism).
- Universal closedness: `[UniversallyClosed f]`. Read UniversallyClosed.lean:43:
  `universally (topologically @IsClosedMap) f`, precisely closedness after all
  scheme base changes (def-weil-proper-morphism).
- Separatedness of p: `[IsSeparated p]`. Read Separated.lean:44: its field is
  `IsClosedImmersion (pullback.diagonal p)`. This includes exactly the parenthetical
  diagonal clause in the node; there is no additional hypothesis.
- Fibre product and closed immersion in that clause: the recorded `pullback`, `fst`
  and `snd` in HasPullback.lean:95,111,115 and `IsClosedImmersion` in
  ClosedImmersion.lean:45 were opened. The latter is a closed embedding with
  surjective stalk maps, agreeing with the node's closed-subscheme condition.
  These definitions are used transitively through `IsSeparated`, without copies.
- Sole conclusion: `IsSeparated q`, separatedness over the same S. No absolute
  separatedness, quasi-separatedness, finiteness, or properness substituted.

Source: local Stacks .tex is absent. Independently opened both the authoritative
https://stacks.math.columbia.edu/tag/09MQ and the upstream .tex at
https://raw.githubusercontent.com/stacks/stacks-project/master/morphisms.tex,
label `lemma-image-universally-closed-separated`, lines 9275ff, and its surrounding
proper-morphism section. Part (4) and the final proof paragraph agree with the node.
The section imposes no standing Noetherian, finite-type, or field assumption.
The five docstring steps reproduce the node's commuting-diagonals argument,
universally closed product map, closed composite, surjective image equality, and
closed-image diagonal argument, naming the corresponding proof dependencies.

Edge cases: empty X forces empty Y by surjectivity; empty S forces both empty.
The statement includes all these schemes without nonemptiness instances. An
identity f gives the expected tautological descent. Zero-ring spectra are included.
There is no index set, natural-number parameter, coefficient ring, or characteristic
restriction. A common arbitrary universe is the standard Scheme category encoding;
no independent smaller test-scheme universe is introduced. All variables and the
universe are explicitly bound. No extra typeclass beyond the three node hypotheses.

Independent searches, using different wording from the worker (2026-10-11):

- msearch.py leanfinder: `descent of a closed diagonal along a universally closed
  surjection`: eight hits, including `UniversallyClosed.of_comp_surjective`,
  `universallyClosed_iff`, and universally closed projections. None has the required
  separatedness conclusion.
- msearch.py loogle: `AlgebraicGeometry.IsSeparated,
  AlgebraicGeometry.UniversallyClosed`: five hits, including
  `UniversallyClosed.of_comp_of_isSeparated` and properness constructors. They give
  different conclusions or assume separatedness of q instead.
- msearch.py grep: `IsSeparated.*Surjective|Surjective.*IsSeparated`: no hits.
- Independent rg of pinned Mathlib Morphisms, source WeilConjectures and project
  lean/Sheaf for separatedness with closedness/surjectivity and tag 09MQ found
  quasi-separatedness descent, universal closedness descent, and
  `isSeparated_of_flat_surjective_baseChange`. Opened the relevant signatures:
  quasi-separatedness and flat base-change descent are different statements.
  No exact declaration found. rg of the item id and proposed declaration name
  in WeilConjectures and dag/lean_names_upstream.json had no matches.

H5/H6/H8/H9: one theorem with only `sorry`; no definitions, private notation,
local instances, or hidden binders. Source/blueprint docstrings and all five proof
steps are present. Namespace and module topic fit the convention, every line fits
100 characters, and the single Proper import supplies the recorded dependency API.
The node's lean.statement is verbatim the file signature up to `:=`.

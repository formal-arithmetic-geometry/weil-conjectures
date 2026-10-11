## Worker report

The module `lean/Sheaf/AlgebraicGeometry/PerfectGeneratorPullback.lean` states
`AlgebraicGeometry.perfect_generator_pullback`, with its sole proof `sorry`.
It defines no new notion and changes only the item's `lean` record.

Hypothesis and conclusion correspondence:

- Schemes X and X': `{X X' : Scheme.{u}}` uses the recorded Mathlib scheme category.
- Both schemes are quasi-compact: `[CompactSpace X] [CompactSpace X']`. Mathlib's
  CompactSpace means quasi-compactness, without a Hausdorff assumption.
- Both are quasi-separated: `[QuasiSeparatedSpace X] [QuasiSeparatedSpace X']`.
- The affine morphism is `(g : X' ⟶ X) [IsAffineHom g]`, not a hypothesis that X'
  itself is affine.
- M belongs to D_QCoh(X): `(M : schemeDerivedQCohCategory X)` includes the
  `schemeDerivedQCohProperty X M.obj` certificate in the full-subcategory object.
- M is perfect: `(hperfect : Scheme.IsPerfect X M.obj)` uses exactly the dependency's
  perfectness definition. The instances `HasDerivedCategory` on X, X', and all opens
  of X are the shared localization data required by the recorded declarations;
  no separate Abelian instance is chosen and no perfectness on opens of X' is assumed.
- M is a generator: `hgen` says for every `E : schemeDerivedQCohCategory X`,
  `IsZero E.obj ↔ ∀ n : ℤ, Subsingleton (M.obj⟦n⟧ ⟶ E.obj)`.
  This is the same formulation used by the recorded `exists_perfect_generator`.
  It is equivalent to `IsWeakTriangulatedGenerator` from def-pc-generators:
  contraposition turns failure of zero-detection into a nonzero shifted Hom group;
  shift equivalence moves the shift from the target to the source, changing n to -n.
  Preadditivity means Subsingleton Hom is precisely that every morphism is zero.
  We state that criterion directly, rather than introduce a duplicate generator
  definition or an additional hypothesis choosing triangulated structure on D_QCoh.
- Lg* is exactly `(derivedPullback g).obj M.obj`.
- The conclusion first certifies its membership in D_QCoh(X') via
  `schemeDerivedQCohProperty X' ((derivedPullback g).obj M.obj)`. This is implicit
  in the node's claim that the pullback is an object generating that category.
- The second conjunct is the generator criterion on precisely all
  `E : schemeDerivedQCohCategory X'`, with every integer shift and Hom from the
  same pulled-back object. There is no assertion that it generates all D(O_X').

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.DerivedCategory`: `AlgebraicGeometry.schemeDerivedCategory`,
  `schemeDerivedQCohProperty`, `schemeDerivedQCohCategory` (imported by DerivedPullback).
- `Sheaf.AlgebraicGeometry.PerfectComplex`: `AlgebraicGeometry.Scheme.IsPerfect`.
- `Sheaf.AlgebraicGeometry.DerivedPullback`: `AlgebraicGeometry.derivedPullback`.
- `Sheaf.CategoryTheory.WeakTriangulatedGenerator`:
  `CategoryTheory.IsWeakTriangulatedGenerator` is rendered by its equivalent
  shifted-Hom vanishing test, as in the recorded existence theorem; its source
  and complete signature were read. No new predicate is defined.
- `Sheaf.AlgebraicGeometry.PerfectGeneratorExists`:
  `AlgebraicGeometry.exists_perfect_generator` supplies the existing convention for
  the hypothesis on M. It need not be imported: this node assumes a given perfect
  generator, rather than constructing or selecting the existence theorem's witness.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `AlgebraicGeometry.IsAffineHom`.

Edge cases checked before writing: the empty scheme and the zero derived category
are included. The zero object is a generator only when every test object is zero;
therefore hgen is neither vacuous on a nonzero category nor stronger on the empty
scheme. An empty source with a nonempty target is allowed; its generator conclusion
is automatic. For g an identity, the statement recovers the hypothesis up to the
canonical derived-pullback identity isomorphism. No nonempty or surjectivity hypothesis
is imposed on g. Negative shifts and zero shifts are included. Schemes use a common
universe u and the shared derived-localization morphism universe w, with all variables
explicitly bound. No field, Noetherian condition, or characteristic is introduced.

Searches for an existing theorem (2026-10-11):

- msearch.py leanfinder: "affine pullback of a perfect generator generates the quasi
  coherent derived category" — eight hits concerning localization, representatives,
  and HasDerivedCategory, none stating the claim.
- msearch.py loogle: "AlgebraicGeometry.derivedPullback,
  CategoryTheory.IsWeakTriangulatedGenerator" — zero hits; unknown identifier
  AlgebraicGeometry.derivedPullback (these are project declarations).
- msearch.py grep: "generator.*pullback|pullback.*generator|IsAffineHom" in
  AlgebraicGeometry — affine morphism definitions and stability results, no generator
  theorem. Narrow repeat "generator.*pullback|pullback.*generator" — zero hits.
- rg in source WeilConjectures, project lean/Sheaf, and dag/lean_names_upstream.json:
  "generator.*pullback|pullback.*generator|lem-pc-perfect-generator-pullback" — only
  unrelated free-module generators and affine-coordinate generators. Direct node-id
  search in the source — no hits.
- rg "perfect_generator_pullback|IsWeakTriangulatedGenerator" in Mathlib, source,
  project and upstream name index — only the recorded project generator definition;
  the proposed theorem name is unused.

Source checked directly: https://stacks.math.columbia.edu/tag/0BQT, Remark 36.16.4,
which equates affine pushforward conservativity with the generator property of derived
pullback. The item's proof steps already cite this correct source. Node source fault:
`source.document` still names an unavailable `derived-categories-of-schemes.tex` and
`source.place` gives Tag 09IS instead of Tag 0BQT; its own reviewed note records this
mistake. The module cites the actual Tag 0BQT, as does the proof. No statement change
is needed and the source field is left untouched under the permitted-field rule.
There is no disputed mathematical statement.

Validation: scompile.py on the server compiled the module in 2.3 seconds, with no
errors or warnings. The delivery dry run is the final validation step; the independent
second reader will supply its own reading and deliver.

## Second reading by C1

I independently opened the item JSON and its complete module, all six statement
 dependency nodes and the recorded declaration modules. No statement correction,
new definition node, or dependency module is present in this delivery.

Object/hypothesis/conclusion list and correspondence (H3):

1. X and X' are schemes: `{X X' : Scheme.{u}}`. I read Mathlib's `Scheme`
   structure (a locally ringed space with local affine charts) and `Scheme.Hom`
   (locally ringed-space morphisms). These match def-pc-scheme. PASS.
2. Both are quasi-compact: `[CompactSpace X] [CompactSpace X']`; neither implies
   Hausdorffness. Both are quasi-separated: `[QuasiSeparatedSpace X]` and its X'
   counterpart, meaning compact intersections of quasi-compact opens. PASS.
3. g is an affine morphism X' to X: `(g : X' ⟶ X) [IsAffineHom g]`.
   I read `IsAffineHom.isAffine_preimage`: inverse images of affine opens are affine.
   This imposes neither affineness of X' nor surjectivity of g. PASS.
4. M belongs to D_QCoh(X): `(M : schemeDerivedQCohCategory X)`.
   I read `schemeDerivedCategory`, `schemeDerivedQCohProperty` and
   `schemeDerivedQCohCategory`: the ambient category is the localization of all
   O_X-module complexes, and the full subcategory requires quasi-coherent cohomology
   in every integer degree. This is not D(QCoh(X)) substituted for D_QCoh(X). PASS.
5. M is perfect: `(hperfect : Scheme.IsPerfect X M.obj)`.
   I read `Scheme.IsStrictlyPerfect` and `Scheme.IsPerfect`: locally on a point's
   open neighbourhood, the restriction is isomorphic to a bounded complex of
   direct summands of finite free modules. This is exactly the dependency node.
   The derived-category instances on all opens of X are required by this recorded
   definition. The shared instances on X and X' specify the two localizations;
   they add no geometric finiteness assumptions or separate Abelian structure. PASS.
6. M is a weak generator: `hgen` tests every E in D_QCoh(X) and every n in Z
   by `IsZero E.obj ↔ ∀ n, Subsingleton (M.obj⟦n⟧ ⟶ E.obj)`.
   I read `IsWeakTriangulatedGenerator`: every nonzero K admits a nonzero map
   M to K[n]. In a preadditive category every Hom contains zero, so being
   subsingleton means all its maps are zero. Shifting both endpoints gives
   Hom(M[n], E) equivalent to Hom(M, E[-n]); integer negation is bijective.
   Contraposition gives exactly the dependency's nonzero-object detection.
   Fullness makes ambient Hom and subcategory Hom identical; zero objects and
   shifts are inherited since quasi-coherent cohomology is stable under shifts.
   This direct criterion is also the recorded `exists_perfect_generator` criterion;
   it introduces no second definition and does not assume that theorem's additional
   localizing-subcategory conclusion. PASS.
7. Lg* is `(derivedPullback g).obj M.obj`. I read `exists_derivedPullback` and
   `derivedPullback`: the chosen functor is the left-derived tensor pullback, with
   its universal property and K-flat comparison, not restriction of scalars or
   Mathlib's differently defined module pullback. PASS.
8. The pullback is an object of D_QCoh(X'): the first conjunct is
   `schemeDerivedQCohProperty X' ((derivedPullback g).obj M.obj)`.
   This spells out the membership implicit in the node's conclusion. PASS.
9. It generates precisely D_QCoh(X'): the second conjunct tests all
   `E : schemeDerivedQCohCategory X'`, with `IsZero E.obj` equivalent to vanishing
   of Hom from every integer shift of the same pullback. Quantifier order and
   generator interpretation agree with item 6. It asserts no perfectness conclusion
   and no generation of all D(O_X'). PASS.

Source reading: the local Stacks checkout is absent on this machine. I fetched and
read the actual `perfect.tex` from the official Stacks GitHub repository, including
its Conventions and the complete `remark-pullback-generator`; I also read
https://stacks.math.columbia.edu/tag/0BQT. The remark assumes qcqs source and target,
uses the derived adjunction, and concludes generator preservation for affine maps
from pushforward conservativity. There is no hidden field, characteristic, separated,
Noetherian, or finite-dimensional hypothesis. The perfectness hypothesis retained
here is in the node, though the source remark works for any generator. The subsequent
section's Noetherian discussion is not a hypothesis of this remark.

Edge cases: empty schemes are allowed, including empty source with nonempty target;
a morphism to the empty target forces the source empty. In the zero derived category
all Hom types are subsingleton and every object is zero. For M = 0 the hypothesis
forces all test objects zero, so it cannot give false generation on a nonzero category.
All shifts n = 0, negative, and positive are covered by Z. No index family, nonempty
cover index, base field, or characteristic restriction occurs. u and w are explicitly
bound and match all recorded dependency signatures; any pair of schemes is read in
one common ambient scheme universe. No independent lower test-object universe or
unbound variable occurs.

Independent H4 searches (2026-10-11), recorded by msearch.py in searches.jsonl:

- LeanFinder: `derived inverse image affine morphism weak generator detects zero
  objects` returned eight affine-morphism/local-property hits, none this statement.
- LeanSearch: `An affine morphism pulls back a perfect generator of the derived
  category of quasicoherent sheaves to a generator` was unavailable (HTTP internal
  server error). This is not a negative mathematical verdict.
- Loogle: `"generator"` returned twelve Lean name-generator declarations, no match.
- rg, independently in Mathlib, upstream WeilConjectures, project lean/Sheaf and
  dag/lean_names_upstream.json, for generator near inverse image/pullback and for
  `perfect_generator_pullback|IsWeakTriangulatedGenerator`: no theorem match.
  Upstream hits concern free-module or affine-coordinate generators; the project
  generator predicate is the dependency opened above. No duplicate notion is added.

H5/H6/H8/H9: no definition is introduced, the only theorem proof is `sorry`, the
module and theorem docstrings name the correct source and blueprint ID, and the
proof docstring follows all three DAG proof steps with their named inputs. Imports
provide exactly derived pullback, perfectness and affine morphisms; no unused
additional import is introduced. All source lines meet the 100-character convention.
The node's lean.statement is verbatim the theorem signature, without its proof.

Mismatches and changes: no Lean mismatch found; no module or node field changed.
The existing source metadata fault (nonexistent derived-categories-of-schemes.tex,
Tag 09IS instead of perfect.tex, Tag 0BQT) is independently confirmed and reported
here, rather than changing a field outside this delivery's ownership. The node's
proof sources and the Lean already use 0BQT. I added only this independent reading.

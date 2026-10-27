## Worker report

The module `Sheaf.AlgebraicGeometry.DecentQuasiCompactMonomorphicPoints` states
`AlgebraicGeometry.AlgebraicSpace.exists_quasiCompact_monomorphic_field_representative`.
Its sole proof is `sorry`; it introduces no definitions. The item node changes only
in `lean`. Its statement, statement dependencies and accepted six-step proof are unchanged.
There is no statement dispute, source fault, new node or dependency-interface repair.

I read the whole item, each statement dependency and its recorded source declaration,
Stacks `decent-spaces.tex` 03JV (`lemma-UR-finite-above-x`), 03I8
(`definition-very-reasonable`), and the 03JU proof used by the accepted split. The
latest blueprint unit and its direct-images proof were also read. The node is the
global form of 03JV (6) implies (4), with the node's scheme-test definition of
quasi-compactness. The module docstring reproduces all six accepted proof steps.

Clause-by-clause rendering:

- An arbitrary base scheme is `{S : Scheme.{u}}`; `X : AlgebraicSpace S` is the
  existing full subcategory of fppf sheaves with representable diagonal and an
  étale surjective atlas. No separation or finiteness assumption is added.
- The field-point set `|X|` is `Point X.obj.obj`. Its existing atlas topology is
  imported, though the theorem only needs the underlying point set.
- A field-valued map includes `(K : Type u) [Field K]`, its structure map
  `b : Spec (CommRingCat.of K) ⟶ S`, and its natural transformation
  `c : yoneda.obj (Over.mk b) ⟶ X.obj.obj`. This quantifies over all such maps,
  with all possible structure maps to the original base.
- The entire hypothesis “every field-valued morphism is quasi-compact” is `hqc`.
  For every `U : Over S`, `IsAffine U.left` and every `t : yoneda.obj U ⟶ X.obj.obj`,
  it supplies `V`, the projection `p : V ⟶ U`, and the other projection `q`, with
  `IsPullback q (yoneda.map p) c t ∧ CompactSpace V.left`. `IsPullback` is an
  actual representing square of presheaves. Thus `V.left` is the scheme
  `U ×_X Spec K`; `CompactSpace` imposes no Hausdorff condition. Existence of
  one such quasi-compact representative is equivalent to quasi-compactness of
  the fibre product, since representing schemes are uniquely isomorphic.
- “For every x” is the binder `x : Point X.obj.obj`, with no nonemptiness premise.
- The conclusion's `∃ (F : Type u) (_ : Field F) (b : Spec (CommRingCat.of F) ⟶ S)
  (j : yoneda.obj (Over.mk b) ⟶ X.obj.obj)` supplies exactly the field and field map.
- “Representing x” is `schemePointMap j (IsLocalRing.closedPoint F) = x`. A field
  spectrum has exactly one point, so this is its point class.
- “Monomorphism” is the explicit cancellation condition for every
  `Y : AlgebraicSpace S` and every `a c : Y.obj.obj ⟶ yoneda.obj (Over.mk b)`:
  `a ≫ j = c ≫ j → a = c`. These are precisely morphisms from `Y` to the field
  spectrum over `S`, viewed as natural transformations. Testing only scheme
  sources is not substituted for the node's explicit algebraic-space tests.
- The final universal affine-test clause repeats the definition used in `hqc`,
  with `j` in place of `c`. It states quasi-compactness of this chosen map on
  every affine scheme test, including tests whose structure map is not étale.

Statement dependencies and declarations read/used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and `Scheme.Hom` (source lines 36–47 and 73–94).
- `def-trf-algebraic-space`: `Sheaf.AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicGeometry.AlgebraicSpace` and its scheme-test
  `IsRepresentableWith`, `IsRepresentable`, `IsEtale`, `IsSurjective`,
  `IsAlgebraicSpace`. Their full definitions and docstrings were read. These
  supply the actual presheaf/sheaf and morphism types; nothing is copied.
- `def-a1-space-point-topology`: `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`,
  `pointTopologicalSpace`, importing `Point`, `PointRepresentative`, and
  `schemePointMap` from `AlgebraicSpacePointClasses`. Both modules were read.
- `def-weil-field`: its Mathlib match is `Field` (no Lean record is needed);
  `Mathlib.Algebra.Field.Defs`, `Field` at line 180, with its docstring.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `Spec.map`, definitions/docstrings at lines 469–480.
- `lem-trf-space-fibre-products-etale-covers`:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`,
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, and
  `etale_fibreProduct_isScheme`; full signatures and proof docstrings were read.
  The displayed scheme-representing squares use Mathlib's `IsPullback`, as does
  the existing algebraic-space interface.
- `def-weil-pbc-quasi-compact-scheme`: `Mathlib.Topology.Defs.Filter`, `CompactSpace`,
  source lines 279–285. This is exactly topological quasi-compactness.

The recorded statement-dependency modules are public imports; available proof-only
modules are plain imports. These include `SpaceChangeBase`,
`AlgebraicSpaceAffineEtaleCover`, `AlgebraicSpacePointClasses`, Mathlib residue-field,
preimmersion and étale modules, and the recorded upstream
`WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints`.
`lem-sfb-monomorphism-into-field-coproduct` and
`lem-sfb-finite-point-self-relation-field-monomorphism` had no recorded Lean module
at inspection time; their proof steps remain in the docstring. They are proof
prerequisites, not objects missing from this theorem's statement.

Edge cases checked before writing: empty `X` makes the universal conclusion vacuous;
an empty affine scheme test has an empty quasi-compact pullback; a field has no
zero-ring case; both characteristic zero and positive characteristic, including
inseparable field maps, remain included; nonclosed points are permitted. An arbitrary
non-quasi-separated base is allowed, and the proof restores that same base. No
nonempty atlas, Noetherian, quasi-separated or locally finite type premise is imposed.
All fields, schemes and point representatives use the recorded algebraic-space size
convention `u`; the point quotient itself is in `Type (u + 1)`. `autoImplicit false`
ensures every variable and universe is explicitly bound.

Searches made (2026-10-24):

- `msearch.py` LeanSearch, query “A decent algebraic space has a quasi compact
  monomorphism from a field spectrum representing every point”: eight hits,
  including `Scheme.fromSpecResidueField`,
  `Scheme.instIsPreimmersionFromSpecResidueField`,
  `Scheme.instOverSpecResidueField`, and `compactSpace_iff_exists`. They concern
  schemes, not this theorem for algebraic spaces.
- `msearch.py` LeanFinder, query “Every point of an algebraic space whose field
  valued morphisms are quasi compact has a quasi compact monomorphic field
  representative”: eight scheme quasi-compactness hits, including `QuasiCompact`,
  `quasiCompact_of_compactSpace`, `compactSpace_iff_quasiCompact`, and
  `quasiCompact_over_affine_iff`. None states the item.
- `msearch.py` Loogle, query `"AlgebraicSpace", "Mono"`: zero hits.
- `msearch.py` grep, regex `AlgebraicSpace|residualSpace|[Dd]ecent` in Mathlib's
  `AlgebraicGeometry`: zero hits.
- Direct `rg` of `lean/WeilConjectures` with
  `AlgebraicSpace|residualSpace|[Dd]ecent`: zero hits. The requested
  `grep -rn` by item id in that source also returned no hits.
- Direct `rg` of `lean/Sheaf/AlgebraicGeometry` with
  `decent|monomorphic.*represent|field.*monomorphism|monomorphism.*field`
  found nearby consumers and other statements. I read
  `DecentSpaceFiniteFieldMap` and `DecentAlgebraicFieldImageClosed`: the first
  assumes `hdecent` and proves finiteness of a specified map; the second assumes
  monomorphic representatives and proves closedness. Neither supplies this item.
- I also read the existing quasi-compactness predicates in `ProperCurveModuli`
  (`MapIsQuasiCompact`, compactness of the point space of a presheaf pullback)
  and `SpaceQCSeparatedEtaleLocal` (`IsQuasiCompactPresheafMap`, a compact atlas).
  Neither is redefined; the node specifically gives the scheme-pullback affine
  test, expanded here without introducing a new named notion, as in the landed
  `DecentSpaceFiniteFieldMap` hypothesis.
- Exact proposed declaration name searched in Mathlib, `WeilConjectures`, `Sheaf`
  and `dag/lean_names_upstream.json`: no existing declaration.

Validation: `scompile.py NI lem-sfb-decent-quasicompact-monomorphic-points` compiled
this file both as a sandbox module (4.7 s) and under its library module name (6.0 s),
with exit code 0 and no errors or unexpected warnings. No global build or direct
repository Git operation was run. The JSON signature was extracted verbatim from
the module, and its layout is indent 1, UTF-8, with a final newline. All Lean lines
are at most 100 characters. The final dry run and delivery are performed through
`deliver2.py`.

Dry run: `deliver2.py NI lem-sfb-decent-quasicompact-monomorphic-points --no-push`
returned `OK (dry run): commit 9eceaf34bda passes the preflight and compiles;
nothing pushed`. The packet contains exactly the module, item-node copy and worker report.

## Second reading by NI

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

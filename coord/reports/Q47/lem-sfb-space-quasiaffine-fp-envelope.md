## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceQuasiAffineFpEnvelope` states
`AlgebraicGeometry.AlgebraicSpace.exists_closedImmersion_finitePresentation_of_quasiAffine`.
It is precisely Stacks Tag 0871, lemma-quasi-affine-closed-in-finite-presentation,
read in `literature/stacks-project/spaces-limits.tex`, lines 2790–2820.
The theorem has one postponed proof (`sorry`), and its docstring carries all five
steps of the accepted DAG proof. No definitions or auxiliary theorems are introduced.

Clause-by-clause correspondence:

- The arbitrary base scheme is `{S : Scheme.{u}}`; `A B : AlgebraicSpace S`
  are the given algebraic spaces, and `g : A ⟶ B` is their morphism.
  Universe `u` is explicit, including in the scheme tests through `Over S`.
- Local finite type is `hlft : MapIsLocally (@LocallyOfFiniteType) g`.
  The existing predicate tests every compatible pair of representable étale
  scheme charts, with exactly the scheme property in the recorded dependency.
- Quasi-affineness is `hqa : IsRepresentableWith
  (fun _ _ p ↦ IsQuasiAffineHom p.left) g.hom.hom`.
  This quantifies over every scheme test and supplies an actual representing
  scheme pullback. Over an affine test, `IsQuasiAffineHom` is equivalent to the
  source being a quasi-affine scheme. Mathlib's `Scheme.IsQuasiAffine` includes
  compactness and an immersion into its canonical affine spectrum; the same
  Mathlib file gives `IsOpenImmersion X.toSpecΓ`. Thus it means exactly a
  quasi-compact open subscheme of an affine scheme. Conversely such a scheme
  is quasi-affine, and its morphism to any affine scheme is quasi-affine.
  Requiring the relative scheme property on all scheme tests is equivalent to
  requiring this on affine scheme tests: restrict to affine opens of the test.
- The quasi-compact base hypothesis is `hqc : IsQuasiCompact B.obj`, using
  the definition owned by `def-sfb-stack-qcqs-morphism`. Its definition requires
  a quasi-compact scheme and a representable surjective étale atlas. No atlas
  predicate is redefined or expanded inline in the theorem signature.
- Absolute quasi-separatedness of `B` is `hqs : IsAbsolutelyQuasiSeparated B`.
  The recorded definition uses the affine-pair criterion of Stacks 0AHR,
  equivalent to quasi-compactness of the absolute diagonal. It does not assert
  only relative quasi-separatedness over the possibly non-quasi-separated `S`.
- The witnesses are `C : AlgebraicSpace S`, `e : A ⟶ C`, and `v : C ⟶ B`.
- Closed immersion is `IsRepresentableWith
  (fun _ _ p ↦ IsClosedImmersion p.left) e.hom.hom`, exactly the node's
  representability and closed-immersion property after every scheme test.
- Finite presentation of `v` is the conjunction
  `MapIsQuasiCompact v.hom.hom`,
  `MapIsQuasiSeparated v.hom.hom`, and
  `MapIsLocallyOfFinitePresentation v`. The first is the affine-scheme-test
  compact-point-space criterion; the second applies it to the canonical relative
  diagonal; the third uses compatible étale charts. These are the existing
  definitions, with their definition-node owners cited.
- The commuting factorization is `e ≫ v = g`, Lean's order for `v ∘ e = g`.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsRepresentableWith`, `IsEtale`, `IsSurjective`. Their actual definitions
  use representing scheme pullback squares, not an arbitrary abstract arrow.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace` and its two sibling theorems provide the
  recorded sheaf fibre-product and atlas framework.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`; `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `IsClosedImmersion`. Their full class signatures and docstrings were read.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `MapIsLocally`, `MapIsLocallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `IsAbsolutelyQuasiSeparated`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine`: `IsQuasiAffineHom`;
  its definition tests preimages of affine opens with Mathlib's
  `Scheme.IsQuasiAffine` (defined in `Mathlib.AlgebraicGeometry.QuasiAffine`).
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `MapIsQuasiCompact`
  (owner `def-sfb-proper-curve-moduli`).
- `Sheaf.AlgebraicGeometry.StackQcqsMorphism`: `IsQuasiCompact`,
  `MapIsQuasiSeparated` (owner `def-sfb-stack-qcqs-morphism`).
  Their full signatures, definitions and source docstrings were read for this repair.
- The size-convention dependency is metatheoretic; explicit universe `u`
  implements it without adding any smallness or universe-equality hypothesis.

The five already-landed definition owners for local morphism properties, absolute
quasi-separatedness, scheme quasi-affineness, morphism quasi-compactness, and
space quasi-compactness/relative quasi-separatedness are added to `stmt_deps`
under brief-stage2 §5's permission to add already-landed statement interfaces. They define precisely
notions already stated in the item's prose; the statement itself is unchanged.

The two already-stated proof dependencies are imported without `public`:
`AlgebraicSpaceQuasiCompactFppfLocal` and `SpaceEventualClosedImmersion`.
Their recorded declarations and full source signatures/docstrings were read.
The other seven proof dependencies currently have no Lean record and are not
imported: quasiaffine-affine-factorization, affine-locality, affine-fp-limit,
limit-open-cover-descent, qcqs-permanence, qc-open-finite-presentation, and
separated-fp-composition (all with the `lem-sfb-space-` prefix).
They remain in the DAG proof and proof docstring for stage 3.

Edge cases checked before writing: empty `A` and empty `B` are permitted, with
empty scheme atlas and an empty envelope. Identity and closed-immersion maps
are included. The base scheme `S` need not be quasi-compact or quasi-separated;
only `B` has those assumptions. No Noetherianity, separatedness, finite type of
`S`, field hypothesis, nonempty space, or properness is imposed. Finite
presentation includes the relative diagonal condition, while `hqs` is absolute.
Scheme tests stay in the same universe as the algebraic-space definition;
there is no independently smaller universe of tests and no restriction on an
indexing set (the final statement has none).

Searches for an existing statement:

- `msearch.py ... leanfinder`: “A quasi affine locally finite type morphism of
  algebraic spaces over a quasi compact quasi separated base factors as a closed
  immersion followed by a morphism of finite presentation”. Eight hits, all
  scheme morphism properties or scheme immersion factorizations; no space theorem.
- `msearch.py ... loogle`: `"IsQuasiAffineHom", "LocallyOfFinitePresentation"`.
  Zero hits.
- `msearch.py ... leansearch`: “quasi affine algebraic spaces admit closed
  immersion into finite presentation over quasi compact quasi separated base”.
  Eight hits on scheme quasi-affineness and its canonical open immersion;
  none is the algebraic-space envelope theorem.
- `msearch.py ... grep` in `AlgebraicGeometry`:
  `AlgebraicSpace|[Qq]uasi[Aa]ffine.*[Ff]inite[Pp]resentation|[Ff]inite[Pp]resentation.*[Qq]uasi[Aa]ffine`.
  Zero hits.
- `rg` in `lean/WeilConjectures` for `QuasiAffine|quasiAffine` found the
  upstream scheme quasi-affine API, whose source definition was read and reused.
  `grep -rn` for this exact node id there had no hits.
- `rg` in `lean/Sheaf` for local finite type, local finite presentation,
  quasi-compactness, quasi-affineness and absolute quasi-separatedness found
  the shared predicates listed above and scheme-descent results, no envelope.
- `rg` of `dag/nodes` for quasi-affineness identified
  `def-nagata-quasi-affine-morphism`; no new notion is necessary.
- The chosen full declaration name was searched in Mathlib, WeilConjectures
  and Sheaf with no existing declaration found.

The example `Sheaf/CategoryTheory/CompactObject.lean` is now withdrawn. Its
node records the upstream replacement, so the current live module conventions
were followed instead. No dependency repair, statement correction, or disputed
mathematical claim was necessary.

Validation uses `scompile.py Q47 lem-sfb-space-quasiaffine-fp-envelope <module>`
for both sandbox and library-name forms, followed by the prescribed dry run
and delivery. The repaired version compiled cleanly in both forms (8.7 s and 4.2 s),
with no errors or non-sorry warnings. All variables are explicit, and
`set_option autoImplicit false` is included. The final dry run and delivery
are performed with the authorized `deliver2.py` wrapper.

## Repair of returned delivery 13ac9e0fe94b

H2: Removed `lem-trf-space-qc-separated-etale-local` from `stmt_deps` and
removed the direct import `Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal`.
The statement needs shared definitions, not that theorem. Added the actual
definition owners `def-sfb-proper-curve-moduli` and
`def-sfb-stack-qcqs-morphism` and imported their modules publicly.

H4: Replaced the inline quasi-compact atlas existential by exactly
`hqc : IsQuasiCompact B.obj`. Replaced the finite-presentation clause by exactly
`MapIsQuasiCompact v.hom.hom ∧ MapIsQuasiSeparated v.hom.hom ∧
MapIsLocallyOfFinitePresentation v`. The node's `lean.statement` is extracted
verbatim from the repaired module. The mathematical statement and its proof
plan are unchanged. The module header and clause mapping above now describe
the repaired interface. No private copy of any predicate remains.

Compared the retained sandbox with current main: the original delivery's node
differed only in `lean` and `stmt_deps`. The repaired node is based on current
main and changes only those authorized fields. The delivery wrapper refreshes
the base and builds the new delivery on current main. The maintainer's review
is the independent second reading, as required by the dispatcher.

## Second reading by Q47

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

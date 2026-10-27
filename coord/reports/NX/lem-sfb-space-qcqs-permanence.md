## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceQcqsPermanence` states
`AlgebraicGeometry.AlgebraicSpace.qcqs_permanence` with one postponed theorem proof.
It renders exactly Stacks Tag 073B(1)-(2), read in
`literature/stacks-project/spaces-morphisms.tex`, label
`lemma-quasi-compact-quasi-separated-permanence`. It introduces no definitions.

Clause-by-clause correspondence:

- The arbitrary scheme base is `{S : Scheme.{u}}`; no separation or finiteness condition
  is imposed on S. The single explicit universe u is the existing algebraic-space
  universe, with schemes in `Type (u+1)`, sheaf values in `Type u`, and point classes in
  `Type (u+1)`. `set_option autoImplicit false` forbids unbound implicits.
- The two algebraic spaces over S are `{X Y : AlgebraicSpace S}` and the arbitrary
  morphism is `(f : X ⟶ Y)`, using the existing full subcategory of fppf sheaves.
- Quasi-compactness of the source point space is
  `(hX : CompactSpace (Point X.obj.obj))`. The topology is the existing
  `AlgebraicSpace.pointTopologicalSpace`, final for representable etale scheme maps.
  Mathlib CompactSpace imposes no Hausdorffness.
- Absolute quasi-separatedness of the target is
  `(hY : IsAbsolutelyQuasiSeparated Y)`. This existing definition quantifies over all
  pairs of affine S-schemes mapping to Y and requires their sheaf fibre product to
  have compact point space. Stacks Tag 0AHR(3), read in spaces-properties.tex,
  `lemma-characterize-quasi-separated`, says exactly that this is equivalent to
  quasi-compactness of the absolute diagonal over Spec Z. In particular, this is
  not the diagonal over S when S is arbitrary.
- The first conclusion `MapIsQuasiCompact f.hom.hom` quantifies over every affine
  `T : Over S` and every `yoneda.obj T ⟶ Y.obj.obj`, requiring
  `CompactSpace (Point (Limits.pullback f.hom.hom a))`. These are actual presheaf
  fibre products, equivalent to the sheaf fibre products of the dependency.
- The second conclusion is
  `IsAbsolutelyQuasiSeparated X → MapIsQuasiCompact (pullback.diagonal f.hom.hom)`.
  Its additional assumption is precisely absolute quasi-separatedness of X; its
  conclusion is precisely quasi-compactness of the relative diagonal. The first
  conjunct already supplies quasi-compactness of f under this extra assumption,
  so the pair gives both parts of 073B(2).

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map`. Scheme and spectrum are supplied transitively by the public
  algebraic-space modules; the theorem does not choose an extra scheme structure.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsAlgebraicSpace`,
  `IsRepresentable`, `IsEtale`, `IsSurjective`. The definitions use the big fppf
  site and natural transformations.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `AlgebraicSpace.pointTopologicalSpace`; its point classes are the already existing
  `Point` of AlgebraicSpacePointClasses.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`,
  `etale_fibreProduct_isScheme`. This statement dependency is publicly imported.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `MapIsQuasiCompact`, read in full;
  it is exactly the point-space affine-test definition used by the node.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `IsAbsolutelyQuasiSeparated`, read in full and checked against Stacks 0AHR.
- `def-weil-size-convention` is a metatheoretic convention, not a missing Lean object.

The last two definition owners, `def-sfb-proper-curve-moduli` and
`def-sfb-space-absolute-quasi-separated`, are already landed nodes and are added to
stmt_deps under the rule allowing dependencies on landed definitions. No new node,
dependency repair or statement correction is required. The second clause expands
relative quasi-separatedness as the already defined morphism predicate applied to
`pullback.diagonal`; it does not add a duplicate relative predicate.

The module imports the stated proof dependencies privately: `SpaceChangeBase`
(`exists_spaceChangeBase`), `AlgebraicSpaceFiniteAffineSubatlas`
(`compactSpace_points_of_scheme_atlas`), Mathlib `Pullbacks` (`pullbackSpecIso`),
and `Morphisms.QuasiSeparated` (the affine scheme quasi-separatedness instance).
The other shared proof dependency is already a public statement import.
`lem-sfb-qc-space-affine-etale-atlas` and `lem-sfb-space-qc-cancellation` currently
have no recorded Lean declaration and are not needed to type this statement, so
there is no module to import for them. The complete four-step proof plan, including
these two nodes, is in the theorem docstring. No proof is attempted.

Edge cases checked mathematically before drafting: X may be empty; all affine
pullbacks are then empty, hence compact, and the relative diagonal satisfies the
same criterion. Y may be empty (a map into it forces X empty). Non-quasi-compact Y
is allowed. No quasi-separatedness of S is assumed: the target predicate uses the
absolute affine-pair test. Neither f nor X is assumed representable by a scheme.
The first conclusion does not require X quasi-separated; that extra hypothesis is
inside the implication in the second conclusion. Identity and non-separated maps
are retained. Empty affine tests and zero rings are included by `IsAffine`.

Searches (2026-10-24):

- `msearch.py ... leanfinder`: "A morphism of algebraic spaces from a quasi compact
  source to a quasi separated target is quasi compact and if source is quasi
  separated the morphism is quasi separated". Eight hits, all scheme results,
  including `quasiCompact_of_compactSpace`, `QuasiCompact.of_comp` and
  `QuasiSeparated.of_quasiSeparatedSpace`. Reading Mathlib QuasiSeparated.lean
  confirms that these quantify over Scheme, not AlgebraicSpace.
- `msearch.py ... loogle '"AlgebraicSpace", "QuasiCompact"'`: zero hits.
- `msearch.py ... grep 'AlgebraicSpace|algebraic space'`: zero Mathlib hits.
- `rg -n` over `lean/WeilConjectures` for the item id and algebraic-space names:
  no existing algebraic-space theorem. No matching declaration in
  `dag/lean_names_upstream.json` for the proposed theorem name.
- `rg -n` over `lean/Sheaf` for morphism quasi-compactness, quasi-separatedness,
  `IsAbsolutelyQuasiSeparated`, and permanence names found the definitions above
  and the distinct stack permanence theorem, not this algebraic-space theorem.
  `MapIsQuasiSeparated` in StackQcqsMorphism is definitionally the diagonal
  expression used here; importing that stack infrastructure is unnecessary.
- DAG searches located both definition-owner nodes, so no duplicate definition or
  new node is added. The requested example CompactObject module is now withdrawn;
  its node records the upstream declaration instead. The delivered module follows
  current module-mode public-import conventions.

No STATEMENT-DISPUTED issue or mathematical node fault was found.

Validation: `scompile.py NX lem-sfb-space-qcqs-permanence` compiled the module
in both sandbox and library mode, with no errors or unexpected warnings (1.7 s each).
The prescribed `deliver2.py ... --no-push` returned OK: the delivery passes server
preflight and per-file compilation.

## Second reading by NX

The dispatcher explicitly prohibits starting another agent. This is the worker's
second pass, not a claim of an independent reviewer; the maintainer performs the
independent review on the delivery. Re-read the node, the signature, ProperCurveModuli
MapIsQuasiCompact and AlgebraicSpaceAbsoluteQuasiSeparated alongside Stacks 073B and
0AHR. All base, space and map binders agree. Source compactness and target absolute
quasi-separatedness are required for both clauses; source absolute quasi-separatedness
is required only for the diagonal conclusion. The relative diagonal uses the
presheaf map `f.hom.hom`, not the map of bundled sheaves with a mismatched topology.
The first conjunct remains available under the second clause's extra hypothesis.
The absolute criterion avoids imposing quasi-separatedness of S. No definition,
proof, universe restriction, or stronger hypothesis was introduced. No mismatch found.

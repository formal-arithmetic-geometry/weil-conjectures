## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceLimitSchematicStage` states
`AlgebraicGeometry.AlgebraicSpace.exists_scheme_stage_of_isLimit`, with its whole
proof `sorry`. There are no new definitions and no auxiliary postponed theorems.
Its source is Stacks Project, Limits of Algebraic Spaces, Tag 07SR
(`lemma-limit-is-scheme`) under Situation 084R (`situation-descent`), read in
`literature/stacks-project/spaces-limits.tex`. The declaration docstring carries
all three proof steps of the node, including the comparison of the supplied
algebraic-space limit with the limit of fppf sheaves.

Hypothesis and clause correspondence:

- The scheme S is `{S : Scheme.{u}}`. Algebraic spaces over it are the existing
  `AlgebraicSpace S`, the full subcategory of fppf sheaves with representable
  diagonal and a representable surjective etale scheme atlas. Their morphisms
  are the existing natural transformations through that full subcategory.
- The small nonempty directed index set is `{I : Type u} [Preorder I]
  [Nonempty I] [IsDirected I (· ≤ ·)]`. This uses the scheme universe, not an
  independently smaller indexing universe. A preorder is the existing Stacks
  directed-set convention; antisymmetry is unnecessary.
- The inverse system is `D : Iᵒᵖ ⥤ AlgebraicSpace S`.
- Every stage is quasi-compact on the point topology by
  `hqc : ∀ i : I, CompactSpace (Point (D.obj (op i)).obj.obj)`.
  `CompactSpace` means every open cover has a finite subcover, without any
  Hausdorff assumption. The point topology is the recorded final topology for
  representable etale scheme-source maps, not a private atlas topology.
- Absolute quasi-separatedness of every stage is
  `hqs : ∀ i : I, IsAbsolutelyQuasiSeparated (D.obj (op i))`.
  This reuses the landed definition of `def-sfb-space-absolute-quasi-separated`.
  Its definition quantifies over every two affine S-schemes mapping to the
  space and asserts compactness of their sheaf fibre product's point space.
  Stacks Tag 0AHR(3), equivalent to (1), identifies this with quasi-compactness
  of the absolute diagonal over Spec Z; I read both the definition of absolute
  separation and this equivalence in `spaces-properties.tex`. Thus no
  quasi-separatedness assumption on S has been added. The item's `stmt_deps`
  gains this existing landed definition node; its statement is unchanged.
- Affine transitions are `haff`, which applies the recorded
  `IsRepresentableWith (fun _ _ p ↦ IsAffineHom p.left)` to every `D.map f`.
  This means each scheme base change comes with a scheme representing the
  pullback and an affine scheme projection. It is exactly the item's
  all-scheme-test convention. Finite and integral morphisms are explanatory
  conventions in the node, not hypotheses on this diagram; the theorem imposes
  neither finiteness nor integrality on any transition.
- The supplied algebraic space Z and its compatible projections are the apex
  and legs of `c : Cone D`. `hc : IsLimit c` is its universal property in
  algebraic spaces over S. For every algebraic space W it gives existence and
  uniqueness of a morphism to `c.pt` for every compatible family to the stages,
  hence exactly the asserted bijection. No limit in presheaves, sheaves or
  schemes is substituted for this hypothesis.
- Z is represented by a scheme through
  `hscheme : ∃ U : Over S, Nonempty (yoneda.obj U ≅ c.pt.obj.obj)`.
  The isomorphism is one of presheaves on schemes over S, so this is precisely
  scheme representability of the given space, including its S-structure.
- The conclusion `∃ (i : I) (U : Over S), Nonempty
  (yoneda.obj U ≅ (D.obj (op i)).obj.obj)` asserts that some stage is represented
  by a scheme over S. It imposes no affineness or eventual-stage conclusion.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom` (locally ringed spaces locally affine and their
  morphisms), reached through the public algebraic-space import.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`
  and `AlgebraicGeometry.AlgebraicSpace.IsRepresentableWith`, with their full
  definitions and docstrings read. Representability uses actual scheme-valued
  pullback squares, not an arbitrary map.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `AlgebraicGeometry.AlgebraicSpace.pointTopologicalSpace`; its existing `Point`
  carrier comes from `AlgebraicSpacePointClasses`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyQuasiSeparated`, reused without
  duplication and recorded by adding its already landed definition node.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`:
  `AlgebraicGeometry.IsAffineHom`, reached through the finite-morphism module;
  its full preimage-of-affine-open signature was read.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`
  (and `Mathlib.AlgebraicGeometry.Morphisms.Integral`:
  `AlgebraicGeometry.IsIntegralHom`) were read for the node's explanatory
  conventions. The recorded finite module is imported as a statement dependency;
  no finite/integral hypothesis is asserted.
- `def-weil-size-convention` is a metatheoretic convention with no declaration;
  the theorem explicitly binds `universe u` and uses the established site and
  scheme encodings. No auto-bound variable or universe remains.
- The stated proof dependency `lem-a1-space-etale-open-image` is imported with
  plain `import`. Its `points_compactSpace_iff` signature and proof docstring
  were read and are cited in step 1. The other proof dependency,
  `lem-sfb-space-affine-limits-schematic-stages`, currently has neither `lean`
  nor `mathlib_match`; there is consequently no module to import. It is not an
  object needed to type the present statement. It remains named in the proof
  plan and in the unchanged `proof_deps`.

Edge cases checked before writing: I must be nonempty, since the conclusion
selects an index. A singleton or constant system yields the expected assertion.
The representing scheme may be empty; neither the hypothesis nor conclusion
requires points. Non-surjective affine transitions are allowed. S need not be
quasi-separated or quasi-compact, so absolute quasi-separatedness must not be
replaced by the relative diagonal over S. Scheme representability at the limit
is weaker than affineness, and the conclusion keeps that distinction. No field,
characteristic, separatedness, finite type, or finiteness assumption is added.

Searches made with the prescribed `msearch.py` wrapper:

- LeanFinder: “An inverse limit of quasi compact quasi separated algebraic
  spaces with affine transition maps which is represented by a scheme has a
  scheme stage”. Eight hits, led by
  `AlgebraicGeometry.Scheme.exists_isAffine_of_isLimit` and
  `AlgebraicGeometry.Scheme.exists_isQuasiAffine_of_isLimit`; these have scheme
  stages already and do not state the item.
- Loogle: `"AlgebraicSpace", "IsAffineHom"`: zero hits.
- Mathlib grep: `AlgebraicSpace|limit.*isScheme|scheme.*limit.*stage` under
  `AlgebraicGeometry`: zero hits.
- LeanSearch: “An inverse limit of algebraic spaces with affine transition maps
  which is a scheme is a scheme at some stage”. Eight hits concerning scheme
  limits, finite limits and affine schemes; no algebraic-space schematic-stage
  result. Full machine search logs are in sandbox `searches.jsonl`.
- Project `rg` for `AlgebraicSpace`, the item id and the proposed declaration
  under `lean/WeilConjectures`: no hits. Project searches under `lean/Sheaf`
  found the definitions reused above and docstring citations of the stronger
  limit node, but no theorem for this item. Searching
  `dag/lean_names_upstream.json` for the item id also found none.

Validation: `scompile.py N9 lem-sfb-affine-space-limit-schematic-stage` compiled
this file as both the sandbox and its library module, with no errors or warnings
(6.5 s and 4.8 s respectively). The dry run and delivery use `deliver2.py`.
There is no statement correction, dependency repair, new node, or disputed
statement.

## Second reading by N9

I reopened the node and the compiled module for a second clause-by-clause pass.
The binders retain the arbitrary base, small nonempty directed index, all-stage
point compactness and absolute quasi-separatedness, affine transitions, and the
supplied categorical limit. The two Yoneda-isomorphism existentials render
scheme representability on both sides without choosing an atlas or restricting
to affine schemes. In particular `IsLimit c` is in `AlgebraicSpace S`, while
`haff` is tested on schemes; these distinct categories match the two distinct
clauses of the node. The reused absolute quasi-separated predicate is the
landed affine-pair criterion, rather than quasi-separatedness over S. The added
statement-dependency id records that reuse; no definition is copied. The
proof docstring follows all three accepted DAG steps. No mismatch was found
and no statement or proof-plan field was changed. This is a worker self-check;
the dispatcher's requested independent maintainer review reads the delivery.

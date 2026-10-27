## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceProperCancellation` states
`AlgebraicGeometry.AlgebraicSpace.mapIsProper_of_comp_of_mapIsSeparated`, with its
single proof postponed by `sorry`. There are no definitions or auxiliary theorems.
Source read: `literature/stacks-project/spaces-morphisms.tex`, definition-proper and
lemma-universally-closed-permanence, Tag 04NX(2), including its graph-factorization proof.
The node's statement, proof and proof dependencies are unchanged. The only node changes
are `lean` and addition of the landed definition `def-sfb-space-morphism-properties`
to `stmt_deps` (the brief expressly permits adding landed notion nodes).

Hypotheses and clauses, matched against the node:

- A scheme S, with the stated size convention: `{S : Scheme.{u}}`, explicit `universe u`.
  The existing algebraic-space category uses schemes in universe u, presheaf values
  in Type u and point classes in Type (u+1); this is its recorded universe convention.
  `set_option autoImplicit false` excludes silently introduced variables.
- Algebraic spaces X, Y, Z over the same S: `{X Y Z : AlgebraicSpace S}`. This is the
  existing full subcategory of fppf sheaves with representable diagonal and a
  representable surjective etale scheme atlas; these are not replaced by schemes.
- Morphisms u and v: `(u : X ⟶ Y) (v : Y ⟶ Z)`. Composition is `u ≫ v`, i.e. v after u.
  No extra commutative triangle or chosen presentation is required.
- Sheaf fibre products: the imported `AlgebraicSpaceFibreProductsEtaleCovers` is the
  recorded dependency. The definitions below use `Limits.pullback` of the underlying
  sheaf or presheaf maps. Its `fibreProduct_isAlgebraicSpace` supplies the closure and
  universal property used by the proof, not a scheme-representability assumption.
- Separatedness: `MapIsSeparated` is `IsRepresentableWith` applied to the actual
  relative diagonal, with scheme property `IsClosedImmersion p.left`. This includes
  representability of the diagonal and exactly the closed-immersion scheme tests.
- Quasi-compactness: the `MapIsQuasiCompact` inside `MapIsFiniteType` quantifies over
  EVERY affine scheme T mapping to the target and requires
  `CompactSpace (Point (Limits.pullback f a))`. This is equivalent to the node's
  existence of a surjective etale atlas from a quasi-compact scheme for each such
  pullback. Indeed the pullback is an algebraic space by the recorded fibre-product
  lemma, and `AlgebraicSpace.points_compactSpace_iff` in
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage` (Tag 03E4) states exactly
  this equivalence: a compact point space iff there is U with `CompactSpace U.left`,
  `IsEtale a` and `IsSurjective a`. Its proof is the finite-affine-subatlas argument;
  the converse is continuity and surjectivity of the atlas point map. I read its
  full signature/docstring, and also the finite-subatlas and compact-atlas statements
  in `AlgebraicSpaceFiniteAffineSubatlas`. This comparison is not an extra hypothesis
  or a newly postponed theorem in this delivery. In particular this is NOT merely
  quasi-compactness of the point map by inverse images of compact open subsets: the
  affine scheme fibre product is tested, retaining the node's non-quasi-separated cases.
- Finite type: `MapIsFiniteType f` is the conjunction of that quasi-compactness and
  `MapIsLocally (@LocallyOfFiniteType) f`. The latter tests every compatible pair of
  representable etale scheme charts and the induced scheme morphism h. Thus it is
  exactly local finite type on the node's compatible etale charts, with the existing
  Mathlib scheme predicate, not finite presentation.
- Point topology: `pointTopologicalSpace` in the recorded point-topology module is
  final for all representable etale scheme-source maps. `mapPoint` applies the
  natural transformation to field-valued representatives and descends to the quotient.
- Universal closedness: `MapIsUniversallyClosed f` quantifies over every algebraic
  space Y' over S and every g : Y' ⟶ Y, requiring `IsClosedMap` of `mapPoint` of
  the sheaf-pullback second projection. It is not restricted to representable maps
  or to scheme base changes.
- Properness: `MapIsProper f` is `MapIsSeparated f ∧ MapIsFiniteType f ∧
  MapIsUniversallyClosed f`; its scheme notions are the recorded Mathlib ones.
- The composite is proper: `(hproper : MapIsProper (u ≫ v))`.
- The second factor is separated: `(hsep : MapIsSeparated v)`.
- Conclusion: `MapIsProper u`, with all three properties above and no extra clause.
- No scheme representability, Noetherian, finite-presentation or local
  quasi-finiteness assumption is introduced: there is no corresponding binder.

Dependencies read and used (their source declarations and docstrings were opened):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsAlgebraicSpace`, `IsRepresentableWith`, `IsRepresentable`, `IsEtale`, `IsSurjective`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper` and its scheme convention;
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`: `IsSeparated`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace` (no Hausdorff requirement).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, `etale_fibreProduct_isScheme`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `PointRepresentative.map`,
  `pointImage`, `pointTopologicalSpace`, built on the recorded `Point` quotient.
- The added landed `def-sfb-space-morphism-properties` owns
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally`,
  `MapIsSeparated`, `MapIsFiniteType`, `MapIsUniversallyClosed`, `MapIsProper`.
  It reuses `AlgebraicSpace.mapPoint` and `MapIsQuasiCompact` from the module
  `ProperCurveModuli`, whose full definitions
  were also read. There is no missing notion and no dependency interface repair.

All statement dependencies are available through the public imports, directly or
transitively. The proof dependencies with Lean modules are the fibre-product,
quasi-compact-scheme and point-topology dependencies already publicly reached. The
closed-subspace-proper, proper-base-change, stack-finite-type-calculus and
space-separated-fp-composition nodes have no Lean record in the read snapshot, so no
module import is available for them; their uses are fully retained in the proof docstring.
They are proof-only dependencies and are not required to state this theorem.

Edge cases checked before writing:

- X empty, Y empty, and S empty are admitted by the category and by the finite-subatlas
  comparison (the empty finite subatlas is permitted). No Nonempty binder is present.
- v = identity recovers the properness hypothesis; u = identity is also admitted.
- Scheme-representable spaces recover the scheme cancellation statement; schemes
  are not imposed on arbitrary X, Y or Z.
- A non-quasi-separated target remains permitted: affine-test fibre products, rather
  than the weaker topological point-map condition, determine quasi-compactness.
- Separatedness of v is necessary: a section selecting one origin in the doubled-origin
  line over the affine line has identity composite to the affine line, while its image
  is not closed, so that section is not proper. This is why hsep is retained.
- Properness does not imply finite presentation over arbitrary bases; no finite
  presentation, Noetherian or reducedness restriction was substituted.

Searches (2026-10-24; the msearch wrapper also recorded them in searches.jsonl):

- LeanFinder: `For morphisms of algebraic spaces if the composite is proper and the
  second map separated then the first map is proper`: 8 results, headed by
  `AlgebraicGeometry.IsProper.of_comp` and `.of_comp_of_isSeparated`, all for schemes.
- Loogle: `"IsProper", "IsSeparated"`: 2 scheme hits, the scheme postcomposition
  property instance and `IsProper.toIsSeparated`; neither states the space theorem.
- LeanSearch: `Properness cancels through a separated morphism of algebraic spaces`:
  8 scheme-only results, including the same scheme cancellation statements.
- msearch grep: `AlgebraicSpace|of_comp_of_isSeparated`, AlgebraicGeometry/Morphisms:
  3 hits in Mathlib's scheme Proper.lean. The signatures and definitions there were read.
- rg in `lean/WeilConjectures`, `lean/Sheaf`, `dag/lean_names_upstream.json` and Mathlib:
  `proper_of_comp|mapIsProper_of_comp` found no declaration with the chosen name.
  `lem-sfb-space-proper-cancellation` in WeilConjectures had no hit; Sheaf has proof
  docstring citations in common admissible blowups and Stein factorization, no theorem.
- Broader Sheaf searches for algebraic-space morphism properties found the already
  landed `AlgebraicSpaceMorphismProperties` and `ProperCurveModuli`, which are reused.
  Searches in the DAG confirmed the owner `def-sfb-space-morphism-properties`.

No STATEMENT-DISPUTED flag, statement correction, new node or dependency module.
Server compilation by the prescribed `scompile.py` passed in sandbox and library modes
(2.6 s and 1.6 s), with no errors or unexpected warnings.

## Second reading by Q37

This is a direct dispatcher delivery with no second worker; the maintainer supplies
independent review as specified in the assignment. I reread the node and completed file
myself, without claiming an independent second reading. The hypothesis/clause matching
above checks S, X/Y/Z, both arrows, composition direction, the two hypotheses, and every
component of the conclusion. The only potential interface discrepancy was atlas versus
point-space quasi-compactness; the existing exact equivalence `points_compactSpace_iff`
resolves it on algebraic-space affine base changes, including the empty case. No
statement change was needed. The Lean file has one explicit universe, auto-implicits
disabled, one theorem with `sorry`, and the full six-step DAG proof in its docstring.

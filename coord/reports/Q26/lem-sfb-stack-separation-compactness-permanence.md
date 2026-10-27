## Worker report

The delivery states the three clauses of lem-sfb-stack-separation-compactness-permanence
in Sheaf.AlgebraicGeometry.StackSeparationPermanence. All three theorem proofs are `sorry`.
The only new construction is the real Prop-valued definition
CategoryTheory.IsSeparatedAlgebraicModuliMap, carried by a new definition node and module.
No original statement, proof, or proof dependency is changed. The item's stmt_deps gains
that definition and the already landed def-sfb-dm-stack-morphism-properties, which owns
the canonical relative diagonal and the scheme-test predicate.

Clause-by-clause correspondence:

- “Work over a field k”: each theorem binds `(k : Type u) [Field k]`, and every endpoint
  is a `BasedCategory (Over (Spec (.of k)))`. The three endpoint categories have independent
  object and morphism universes, with every universe explicitly bound.
- “Algebraic stacks”: `hA`, `hB`, and respectively `hB'` or `hC` are the existing
  `IsAlgebraicModuliStack` predicate. No DM, finite type, Noetherian, separated base,
  characteristic, or representability hypothesis is imposed on the first two clauses.
- “Morphisms f and g”: `BasedFunctor A B`, `BasedFunctor B C`; `f.comp g` is g after f.
  These are functors over the actual common scheme base.
- “Separated means proper relative diagonal”: the new definition tests
  `moduliRelativeDiagonal f` against every scheme map to `moduliTwoFiberProduct f f`.
  `HasSpaceBaseChange` retains the equivalence with the actual 2-pullback and the
  comparison with its specified projection p. Each p has
  `MapToSchemeIsSeparated Z T p`, `MapIsQuasiCompact p`,
  `MapToSchemeIsLocally (@LocallyOfFiniteType) Z T p`, and
  `MapToSchemeIsUniversallyClosed Z T p`. These are precisely properness of a space
  over a scheme. The last existing predicate tests every further scheme base change;
  these tests also detect universal closedness after an arbitrary space base change
  by descent along an étale atlas, as in the owning node's convention.
- “Stable under arbitrary base change”: `separatedAlgebraicModuliMap_baseChange` allows
  arbitrary algebraic B' and arbitrary `b : BasedFunctor B' B`, and concludes separatedness
  of `moduliTwoFiberFst b f`. This projects B' x_B A to B', with no restriction on b.
- “Stable under composition”: `separatedAlgebraicModuliMap_comp` assumes separated f
  and g and concludes separated `(f.comp g)` for arbitrary algebraic A, B, C.
- “For representable maps”: only the equivalence theorem assumes
  `IsRepresentableByAlgebraicSpaces f`. This tests every scheme base change by actual
  algebraic-space presentations, without requiring f to be scheme-representable.
- “Agrees with closed-immersion diagonal predicate on algebraic-space tests”:
  `separatedAlgebraicModuliMap_iff_closedDiagonal` states the iff with
  `ModuliSchemeTest @IsClosedImmersion (moduliRelativeDiagonal f)`.
  A closed immersion of spaces is representable by schemes, so scheme tests give exactly
  the algebraic-space-test notion. The scheme representative and projection comparison
  are retained by `IsSchemeModuliBaseChange`, not replaced by an unrelated proper map.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme` and its morphisms.
- Mathlib.Algebra.Field.Defs: `Field` (via the scheme and moduli imports).
- Mathlib.AlgebraicGeometry.Morphisms.Proper: `AlgebraicGeometry.IsProper`;
  Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: `AlgebraicGeometry.IsClosedImmersion`.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: `AlgebraicGeometry.AlgebraicSpace` and
  `AlgebraicSpace.IsRepresentableWith`.
- Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids: `BasedCategory`/`BasedFunctor`
  interfaces, `moduliTwoFiberProduct`, `moduliTwoFiberFst`, `HasSpaceBaseChange`,
  `IsRepresentableByAlgebraicSpaces`, and `ModuliTwoIso`.
- Sheaf.AlgebraicGeometry.AlgebraicModuliStack: `CategoryTheory.IsAlgebraicModuliStack`.
- Sheaf.AlgebraicGeometry.DmStackMorphismProperties: `moduliRelativeDiagonal`,
  `ModuliSchemeTest`; despite the owning module's DM title these particular definitions
  impose no DM assumption and are usable for arbitrary based categories.
- Sheaf.AlgebraicGeometry.ProperCurveModuli: the four properness components named above.
  They apply to arbitrary space-to-scheme maps, with no curve, flatness, dimension or
  finite-presentation condition attached to those components.
- The proof-plan imports include Mathlib.AlgebraicGeometry.ZariskisMainTheorem
  (`IsClosedImmersion.iff_isProper_and_mono`), Mathlib's proper-morphism module for
  closed-immersion properness/composition, and the recorded
  Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers module. Other proof
  dependencies have no recorded Lean declaration at the time of reading, so no module
  is invented for those proof-only prerequisites.

Edge cases checked mathematically before writing:

- Empty stacks/scheme tests and empty base changes: no nonemptiness or chosen atlas
  is added beyond the original algebraic-stack predicate.
- Identity maps and identity base changes: the projection orientation is correct;
  the diagonal of the identity is an equivalence, and the properness tests apply.
- Representable morphisms of schemes: the final iff reduces to the usual closed
  diagonal characterization of scheme separatedness.
- The non-DM stack BE for a positive-dimensional proper elliptic curve E over k:
  the proper E diagonal gives separatedness. It is included in the first two clauses,
  and the last clause correctly requires representability of f. Properness is not
  required on every étale source chart (that would incorrectly exclude proper E).
- Diagonals not representable by schemes can have nonschematic space tests: the new
  definition requires only an algebraic-space Z, not a scheme representative. In the
  representable-f equivalence, the node's monomorphism argument justifies scheme tests.
- No small independent test universe is introduced: T is in `Over S`, schemes and
  fields use u, while the stack endpoint universes are independent.
- All characteristics are retained. There are no degree, genus, or dimension bounds.

Searches actually run:

- msearch.py leanfinder, “Separated morphisms of algebraic stacks have proper diagonal
  and are stable under base change and composition”: eight hits, all about schemes.
- msearch.py loogle, “IsSeparated, IsStableUnderBaseChange”: zero hits, unknown
  unqualified identifier IsSeparated; this was not treated as evidence of absence.
- msearch.py grep, “Moduli.*Separated|SpaceMapIsProper|moduliDiagonal|Stack.*Separated”:
  three unrelated Mathlib hits in descent/constructible topology.
- msearch.py leansearch, “A morphism of algebraic stacks is separated when its relative
  diagonal is proper”: eight scheme-only hits.
- msearch.py leanfinder, “Definition separated algebraic stack morphism proper relative
  diagonal algebraic space tests”: eight scheme-only hits.
- msearch.py grep, “IsSeparatedAlgebraicModuliMap|ModuliProperSpaceTest|moduliRelativeDiagonal”:
  zero Mathlib hits. These last three actual search records are in the new node.
- rg in lean/WeilConjectures and lean/Sheaf for SpaceMapIsProper, moduliDiagonal,
  ModuliSchemeTest, and separated algebraic moduli names: found the canonical relative
  diagonal and the existing properness components, but no arbitrary-stack separated
  morphism predicate or the permanence statements. An explicit item-id search in
  lean/WeilConjectures found no existing statement.
- rg in dag/nodes and dag/lean_names_upstream.json for the proposed definition name/id:
  no existing definition. Related stack-separation-composition is a DM-only theorem,
  and HasProperModuliDiagonal is a DM-specific absolute predicate, not this notion.
- tools/blueprint_refs.py search 'separated stack': zero blueprint matches.
  tools/blueprint_refs.py ancestor returned inherited `None`; the new node preserves
  the item's null ancestor and extends its existing via chain, without inventing one.

Sources read: local stacks-morphisms.tex, definition-separated (04YW),
lemma-base-change-separated (050F), lemma-composition-separated (050K), and
lemma-representable-separated-diagonal-closed (04YS). No statement dispute or
source-based correction is needed.

## New nodes

`def-sfb-stack-separated-morphism` supplies exactly the missing proper-relative-diagonal
predicate, in Sheaf.AlgebraicGeometry.SeparatedAlgebraicModuliMap. It reuses the existing
relative diagonal, 2-pullback presentation, and four properness components rather than
copying any of them. Source: Stacks 04YW and the properness definition for spaces.
The three logged semantic/Mathlib searches, DAG and blueprint searches and project
source searches above found no existing declaration/node of this general notion.
The existing DM absolute diagonal predicate would demand scheme representatives and
cannot render the arbitrary-algebraic-stack statement. Every datum of the new Prop is
written in full, with no sorry and no choice of atlas or presentation.

Validation: both delivered modules compiled cleanly with the prescribed scompile.py
wrapper on 2026-10-24. The definition contains no postponed proof; the three permanence
theorems are the only sorry declarations. Delivery preflight is checked separately.

## Second reading by Q26

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

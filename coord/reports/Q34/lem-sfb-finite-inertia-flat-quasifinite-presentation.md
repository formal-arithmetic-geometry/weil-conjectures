## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteInertiaFlatQuasifinitePresentation` states
`CategoryTheory.finite_inertia_flat_quasifinite_presentation`, with `sorry` as its only
postponed proof. It constructs the helper `CategoryTheory.moduliSelfRelationArrow` with
real data: the composite of the inverse first endpoint comparison, the actual comma
comparison, and the second endpoint comparison. This helper belongs to the self-relation
notion already in the item's statement; it introduces no independent notion.

Read the complete item and its six proof steps, all fourteen original statement dependency
nodes and their recorded declarations/docstrings, and the four added landed definition
nodes and their declarations. Sources read: Stacks `stacks-morphisms.tex`,
`lemma-etale-local-quasi-DM` (0DU3), first proof paragraph, and
`lemma-etale-local-quasi-DM-at-x` (0DU4), including its explicit reference back to that
paragraph; `spaces-morphisms.tex`, Tag 03XX through the recorded representability module;
`algebraic.tex`, Tag 04T4 through the recorded groupoid interfaces. The current blueprint
`latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`
`sk-thm-sf-ctf-stability-direct-images.proof.md` was read: this is a supporting local
moduli step, not its unit statement. No repair note exists for this item.

Clause-by-clause rendering:

- A field k: `(k : Type u) [Field k]`; structural base is `Spec (CommRingCat.of k)`.
  The explicit universes `u v w` allow schemes in u and an independently sized total
  category `BasedCategory.{v,w}`. No equality of these levels is assumed.
- An algebraic stack over k: F is a based category over `Over (Spec ...)`, with
  `hF : IsAlgebraicModuliStack F`. This includes fibred-groupoid descent, algebraic-space
  diagonal, and a smooth surjective scheme atlas, exactly the recorded definition.
- Inertia objects and conjugating arrows: `moduliInertia F`, with the canonical
  `moduliInertiaProjection F`; the landed construction retains vertical automorphisms.
- Finite inertia projection: `hfinite : IsRepresentableFiniteModuliMap
  (moduliInertiaProjection F)`. Its definition quantifies over every scheme test,
  supplies a finite scheme projection and an equivalence to the actual 2-base change
  identifying the first projection. No reducedness, etaleness or finite geometric-point
  approximation replaces finiteness.
- Every stack point x: `∀ x : ModuliPoints F`.
- Affine k-scheme U: `U : Over (Spec ...)` and `IsAffine U.left`.
- Chart p: the actual `BasedFunctor (discreteModuli (yoneda.obj U)) F`.
- Representable by spaces: `IsRepresentableByAlgebraicSpaces p`.
- Flat and locally finitely presented: `ModuliSpaceTest (fun X Y f ↦
  Flat f ∧ LocallyOfFinitePresentation f) p`; this tests the actual projection of
  each scheme 2-base change on every representable etale scheme chart. It imposes
  neither smoothness nor global surjectivity, and no additional quasi-finiteness clause
  on p beyond the node's explicit conclusion.
- A scheme point u mapping to x: `u : U.left`, `moduliSchemePointMap p u = x`, using
  the actual residue-field image map recorded by the topology dependency.
- The self 2-fibre product is a scheme: `R : Over (Spec ...)` with E from h_R to
  `moduliTwoFiberProduct p p`, `E.toFunctor.IsEquivalence`, and the specified vertical
  natural isomorphisms α and β to the scheme maps s and t. Thus both projections,
  not just the abstract category R, are identified.
- Groupoid laws: `IsGroupoidScheme s.left t.left e i c`, using the exact declaration
  of def-a1-groupoid-scheme with `c : pullback s.left t.left ⟶ R.left`.
- Canonical self-relation structure: the final universally quantified equation identifies
  composition under E, α, β with composition of the actual stack comparison arrows.
  Here a is the earlier arrow, b the later one, and q has first projection b and second
  projection a. The endpoint equalities h, hs, ht supply only the equality transports.
  They exist for any composable pair and its composite by the groupoid source/target
  fields and Yoneda. They do not restrict the assertion to a proper subset of pairs.
  Since E is fully faithful, this equation pins the composition uniquely; identity and
  inverse then agree with the unique canonical identity and inverse. This clause spells
  out 'canonical' rather than permitting an unrelated groupoid on the same scheme.
- Both projections separated: `IsSeparated s.left ∧ IsSeparated t.left`, whose Mathlib
  definition is the closed-immersion diagonal condition.
- Both flat: `Flat s.left ∧ Flat t.left`.
- Both locally finitely presented: `LocallyOfFinitePresentation s.left` and the same for t.
- Both locally quasi-finite: `Scheme.Hom.IsLocallyQuasiFinite s.left` and the same for t,
  using the recorded Stacks 01TD predicate including local finite type.

Dependency declarations used (module names omit only the common `Sheaf.AlgebraicGeometry.`
prefix in this list):

- Mathlib: `Field` in `Mathlib.Algebra.Field.Defs`; `Scheme` and `Scheme.Hom` in
  `Mathlib.AlgebraicGeometry.Scheme`; `IsAffine` in `AffineScheme`; `Flat`,
  `LocallyOfFinitePresentation`, `Etale`, `IsFinite`, `IsSeparated` in the respective
  `Mathlib.AlgebraicGeometry.Morphisms` modules. Proper is publicly imported for the
  recorded separated/proper dependency; the proof-only finite-proper and affine-source
  separated instances are available there.
- `AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`, `IsEtale` and scheme tests.
- `AlgebraicModuliStack`: `CategoryTheory.IsAlgebraicModuliStack`.
- `StablePointedModuliGroupoids`: `BasedCategory`/`BasedFunctor` from Mathlib,
  `discreteModuli`, `discreteModuliMap`, `ModuliTwoIso`, `moduliTwoFiberProduct`,
  `moduliTwoFiberFst`, `IsRepresentableByAlgebraicSpaces` and `HasSpaceBaseChange`.
- `GroupoidScheme`: `AlgebraicGeometry.IsGroupoidScheme`.
- `StackPointTopology` and its public `StackPointTopologyFlatLfpOpen` dependency:
  `CategoryTheory.moduliSchemePointMap`; `ModuliPoints` is publicly imported from
  `DmStackMorphismProperties`, also the owner of `ModuliSpaceTest`.
- `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`:
  `AlgebraicGeometry.Scheme.Hom.IsLocallyQuasiFinite`.
- Added landed stmt_deps, with no changes to those nodes: def-sfb-moduli-inertia
  (`ModuliInertia`: `moduliInertia`, `moduliInertiaProjection`),
  def-sfb-finite-stack-scheme-tests (`FiniteStackSchemeTests`:
  `IsRepresentableFiniteModuliMap`), def-sfb-dm-stack-morphism-properties
  (`DmStackMorphismProperties`: `ModuliPoints`, `ModuliSpaceTest`), and
  def-sfb-open-moduli-substack (`OpenModuliSubstack`: `moduliTwoFiberSnd`). These are
  existing notions with usable declarations, so no duplicate/new node is created.

Every proof dependency with a recorded module, and the Mathlib leaves, is imported.
The seven unstated proof dependencies have no module to import and are not needed to
elaborate this stage-2 statement: inertia-locally-quasifinite-diagonal,
separated-source-finite-inertia-target, quasidm-flat-locally-quasifinite-atlas,
stack-diagonal-space-source-representability, representable-pullback-over-space,
groupoid-diagonal-two-pullback-identities, stack-separation-compactness-permanence
(all ids have prefix `lem-sfb-`). Their proof steps remain verbatim in the node and are
included in the theorem docstring. No prerequisite notion remains missing.

Edge cases checked mathematically: the empty stack has no x, so the conclusion is
vacuous; for a scheme choose an affine open through x and its diagonal self relation;
Bμ_p in characteristic p is allowed (the chart need not be etale, and inertia can be
nonreduced); BG for a finite group scheme remains allowed, whereas BG_m fails finite
inertia. No characteristic, Noetherian, quasi-compactness of R or finite-type-over-k
hypothesis is imposed. In particular the statement does not force the whole stack to
be separated, or p to be globally surjective. Composition's identity and inverse cases
are included in the universal equation, with equality transports on arbitrary schemes
in the fixed scheme universe. No disputed statement or correction.

Searches actually run through msearch.py for Q34 and this item:

- leanfinder: 'An algebraic stack with finite inertia admits at every point an affine
  flat locally finitely presented chart whose self relation is a separated locally
  quasi finite scheme groupoid'. Eight hits, including ordinary scheme
  `LocallyOfFinitePresentation`, `UniversallyOpen.of_flat` and affine-limit data;
  no algebraic-stack presentation theorem.
- loogle: `"IsGroupoidScheme", "IsRepresentableByAlgebraicSpaces"`: zero hits.
- grep: `finite.inertia|FiniteInertia|quasi.DM` in AlgebraicGeometry: zero hits.
- leansearch: 'An algebraic stack with finite inertia has an affine flat locally
  finitely presented scheme chart through every point with separated locally quasi
  finite scheme self relation'. Eight hits, including scheme `LocallyQuasiFinite`,
  `Flat`, and `IsFinite` declarations; no theorem for stacks.
- Direct rg searches of read-only project `lean/Sheaf`, `lean/WeilConjectures`, and
  `dag/lean_names_upstream.json` for the item id and proposed declaration names found
  no existing theorem or helper with these names. Broader inertia, groupoid, point-map,
  flat/lfp and chart-test searches located the landed interfaces used above.
  Searching DAG inertia nodes identified def-sfb-moduli-inertia; all four added nodes
  already have lean records, so no new-node searches or new nodes are necessary.

Validation: scompile.py compiled both the sandbox probe and library module cleanly
under the normal 60-second limit. An initial public-visibility error on the second
projection was repaired by explicitly public-importing its owning module. The theorem
has `sorry`; the helper has a concrete composite with no postponed proof or choice.
No local compiler or global build was run. The module's docstring carries all six
proof steps with their dependency ids. All variables/universes are explicit and lines
are at most 100 characters. Final wrapper dry run and delivery follow.

## Second reading by Q34

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

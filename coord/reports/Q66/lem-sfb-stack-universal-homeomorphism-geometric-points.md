## Worker report

The module `Sheaf.AlgebraicGeometry.StackUniversalHomeomorphismGeometricPoints`
states `CategoryTheory.stack_universalHomeomorphism_geometricPoints`, with one
postponed proof and no new definitions. It retains the node's statement and proof.
Sources read: `literature/stacks-project/stacks-morphisms.tex`, labels
`definition-universal-homeomorphism` (0CI7), `lemma-universally-injective`
(0CPN), and `lemma-universally-injective-point` (0DTM), including their proofs.
The current blueprint anchor is the direct-image finiteness proof in
`literature/blueprint/latest/blueprint/sec-six-functors-basics/` under
`sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`;
this supporting node follows the Stacks sources specified by the accepted split.

Hypothesis and clause correspondence:

- The base scheme is `{S : Scheme.{u}}`. All five universe variables are explicit,
  and `set_option autoImplicit false` forbids silently introduced variables.
  Fields and schemes use `u`; stack objects and morphisms have the larger bounds
  `max (u + 1) w` and `max u v`. Stack tests have the bounds
  `max (u + 1) w w'` and `max u v v'`, so they cannot be forced into a universe
  smaller than the schemes or source stack. The size-convention node is
  metatheoretic and supplies no declaration to import.
- The stack over S is `A : BasedCategory ... (Over S)`. Its entire
  Deligne--Mumford hypothesis is `hA : IsDeligneMumfordModuliStack A`, using the
  recorded stack descent, representable diagonal and surjective etale atlas.
  No representability, separation or finite-type assumption is put on q.
- The target is `Y : AlgebraicSpace S`. Its discrete fibred category is
  `discreteModuli Y.obj.obj`, and the actual S-morphism q is a
  `BasedFunctor A (discreteModuli Y.obj.obj)`.
- The universal homeomorphism hypothesis is written out as `hq`: for every
  `Z` satisfying `IsAlgebraicModuliStack Z` and every map `g` to Y,
  `IsHomeomorph (moduliPointMap (moduliTwoFiberFst g q))`. The product order is
  Z times A over Y, so its first projection is precisely the base change of q.
  The algebraic-stack predicate uses smooth scheme-chart tests and a smooth
  surjective atlas, as in the node. The point map and topology are the existing
  field-object quotient map and topology detected by smooth scheme atlases.
- Every algebraically closed field is quantified by `(K : Type u) [Field K]
  [IsAlgClosed K]`, with the arbitrary base map `(a : Spec (.of K) ⟶ S)`.
  The first conjunct is `Function.Bijective` of
  `(moduliFiberMap q (Over.mk a)).mapSkeleton.obj`. Mathlib's skeleton has
  underlying type the quotient by isomorphism. The target fibre of a discrete
  presheaf groupoid has isomorphism classes canonically identified with its
  sections Y(K), by Yoneda. This is the same encoding already used in the
  recorded `IsCoarseModuliScheme`, rather than an arbitrary bijection or a claim
  that the fibre functor is fully faithful.
- The second conjunct quantifies every `Y1 : AlgebraicSpace S` and every
  `h : Y1 ⟶ Y`, then every K and a. Its map is the actual projection
  `moduliTwoFiberFst (discreteModuliMap h.hom.hom) q`, restricted to that fibre
  and mapped to skeletons. Thus the base change is the existing 2-fibre product
  and its conclusion is bijectivity on the required classes over the same K.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its category.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`, used
  within the imported `SpaceMapIsSmooth` and smooth-atlas predicates.
- `Mathlib.Algebra.Field.Defs`: `Field`; and
  `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`. The algebraic-closure
  dependency's `mathlib_match` explicitly names `IsAlgClosed` for this clause;
  no chosen algebraic closure of K is required.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.IsDeligneMumfordModuliStack`, `discreteModuli`,
  `discreteModuliMap`, `moduliFiberMap`, `moduliTwoFiberProduct`,
  `moduliTwoFiberFst`, and the supporting stack/atlas definitions.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`:
  `CategoryTheory.IsAlgebraicModuliStack`, whose full source was read together
  with `SpaceMapIsSmooth` and `IsSmoothModuliAtlas`.
- `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`:
  `CategoryTheory.ModuliFieldObject`, `ModuliFieldRelation`, `ModuliPoints`,
  `moduliFieldMap`, `moduliPointMap`.
- `Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen`:
  `CategoryTheory.moduliPointTopologicalSpace` and `moduliSchemePointMap`.
- `Mathlib.CategoryTheory.Skeletal`: `Skeleton` and `Functor.mapSkeleton`.
- Plain proof import `Sheaf.AlgebraicGeometry.StackUniversalInjectivityCriteria`:
  `CategoryTheory.stack_universalInjectivity_criteria`. Its full signature and
  proof docstring were read. The other proof-only node
  `lem-sfb-stack-universally-injective-point-lift` has no recorded declaration
  in the read repository, so there is no module to import for it; the complete
  natural-language proof still names this planned input. It is unnecessary
  to elaborate the statement itself.

Three already-landed definition nodes are appended to `stmt_deps`:
`def-sfb-algebraic-moduli-stack`, `def-sfb-dm-stack-morphism-properties` and
`def-sfb-stack-point-topological-space`. Their complete statements and Lean
records were read. They carry exactly the algebraic-stack predicate, point
quotient/map and topology already described inline in the assigned node. This
uses brief-stage2 section 5's permission to add landed definition nodes; their
files and Lean records are not changed. There are no new or repaired dependency
modules and no statement correction.

Edge cases checked before writing:

- An empty source can satisfy the hypothesis only against an empty target;
  empty fibres and empty algebraic-space base changes give empty-to-empty
  bijections. No Nonempty assumption appears.
- BG to an algebraically closed point, for a finite etale group G, has one
  geometric isomorphism class with possibly nontrivial automorphisms. Skeleton
  bijectivity preserves this example; equivalence of fibre categories would not.
- Purely inseparable universal homeomorphisms and nonreduced schemes remain
  allowed. Neither characteristic nor reducedness is restricted.
- A proper open subspace fails the universal-homeomorphism hypothesis when it
  omits target points; mere injectivity cannot yield the first surjectivity.
- Identity and arbitrary nonrepresentable q are included. The base-change map h
  can be identity, empty, nonsurjective, non-etale, or nonseparated.
- The K-binder is unchanged in both factors: the statement does not replace K
  by an extension in order to obtain lifts.

Searches actually run through `batch2/msearch.py` with this group and item:

- `leanfinder`: "A universal homeomorphism from a Deligne Mumford stack to an
  algebraic space induces a bijection on isomorphism classes of geometric
  points". Eight hits, all scheme isomorphism/homeomorphism facts or stalkwise
  isomorphism criteria; no stack theorem.
- `loogle`: `"UniversalHomeomorph", "point"`. Zero hits.
- `grep`: `UniversalHomeomorph|universalHomeomorph|IsAlgebraicModuliStack`.
  Zero Mathlib hits.
- `leansearch`: "A universal homeomorphism of algebraic stacks induces a
  bijection on geometric isomorphism classes when its target is an algebraic
  space". Eight hits concerning scheme homeomorphisms or scheme universal
  injectivity; no stack theorem.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf` and
  `dag/lean_names_upstream.json` for the node id and proposed declaration name:
  no pre-existing statement. Broader `UniversalHomeomorph` and topology searches
  found the scheme theory, the existing stack topology, and
  `FiniteFlatAffineGroupoidModuli`, whose geometric-class conclusion concerns
  its particular affine groupoid quotient rather than arbitrary q.
- `rg` of Mathlib's `CategoryTheory/Skeletal.lean` and the existing coarse-moduli
  definition found the canonical skeleton map, so no quotient notion was added.

Validation: the prescribed `scompile.py Q66
lem-sfb-stack-universal-homeomorphism-geometric-points <file>` compiled both
`Sheaf.Stage2.Sandbox0` and the library module successfully, with no errors or
unexpected warnings. The file contains only its one named theorem with `sorry`.
No disputed statement or source error was found.

## Second reading by Q66

This is a second local self-check, not a claim of an independent worker review:
the dispatcher explicitly prohibits starting other agents and supplies the
maintainer's independent review after delivery.

Re-read the node's complete statement against the final signature. S, A, Y, q
and hA preserve every object and stack hypothesis. The hq projection lands in
the test stack Z, as 0CI7 requires; it does not test only algebraic spaces or
only schemes. The conclusion takes the actual fibre map on isomorphism classes,
and both the direct case and every Y1/h case quantify all algebraically closed
fields and all structural maps to S. The discrete target justifies reading its
skeleton as Y(K), consistently with the existing coarse-moduli definition.
The universe maxima contain u and the stack bounds. No unique-automorphism,
finite-type, representability or separation hypothesis was introduced. Checked
the added dependency nodes against their source declarations and confirmed they
are reused, not redefined. No mismatch was found and no theorem was proved.

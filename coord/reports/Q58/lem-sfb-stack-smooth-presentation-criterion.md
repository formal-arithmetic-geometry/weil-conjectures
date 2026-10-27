## Worker report

The module Sheaf.AlgebraicGeometry.StackSmoothPresentationCriterion states all clauses of
lem-sfb-stack-smooth-presentation-criterion. Its three theorems have `sorry` proofs. The six
structures/predicates are concrete helpers for this node's own presentation notion, with no
postponed data or new independent mathematical notion. No statement correction was necessary.

Clause-by-clause correspondence:

- The scheme base is `{S : Scheme.{u}}`. Both stacks have separately bound morphism and
  object universes, `X : BasedCategory.{v₁, w₁} (Over S)` and
  `Y : BasedCategory.{v₂, w₂} (Over S)`. There is no universe equality imposed on them.
  Schemes, field tests and algebraic-space sheaf values use the established scheme universe u.
- The specified stack morphism is `f : BasedFunctor X Y`; algebraicity is precisely
  `hX : IsAlgebraicModuliStack X`, `hY : IsAlgebraicModuliStack Y`.
- `SmoothModuliPresentation f` retains algebraic spaces `U`, `V`, vertical based functors
  `a`, `b`, the space morphism `q`, and its specified `comm` isomorphism. This is a based
  natural isomorphism, hence a 2-isomorphism over Sch/S. The two vertical hypotheses are
  `ModuliSpaceTest (@Smooth) a` and `ModuliSpaceTest (@Smooth) b`. Each includes actual
  algebraic-space presentations of every scheme base change and smoothness of their
  specified projections on every etale scheme chart, so it includes representability.
- Ordinary smoothness of a space map is `AlgebraicSpace.MapIsLocally (@Smooth) q`, using
  the existing compatible etale scheme-chart test and the existing scheme `Smooth`.
- Condition A is `IsSmoothModuliMap f`: it quantifies over EVERY such diagram, requires
  `ModuliSpaceTest (@Smooth) (moduliTwoFiberLift D.a
  (discreteModuliMap D.q.hom.hom) D.comm)`, and concludes ordinary smoothness of `D.q`.
  The comparison is the dependency's actual canonical functor to X ×_Y V, determined by
  both projections and the specified square isomorphism. It is not an arbitrary map.
- Condition B is `HasSmoothModuliPresentation f`: it asserts existence of the same
  diagram, `IsSurjectiveModuliMap D.a`, and ordinary smoothness of `D.q`. The existing
  surjectivity definition quantifies over every field object and supplies a field extension,
  a source object and its actual comparison 2-isomorphism. It imposes no surjectivity on b
  and no smoothness of the comparison to X ×_Y V in B.
- The scheme version uses `SmoothSchemeModuliPresentation f`, with `U V : Over S`,
  `q : U ⟶ V`, and the Yoneda images of exactly these schemes and this morphism. The two
  predicates `IsSmoothOnSchemeModuliPresentations` and `HasSmoothSchemeModuliPresentation`
  reproduce A and B, with scheme `Smooth D.q.left` as conclusion/test. In particular,
  these are literal scheme diagrams, not arbitrary equivalent presentations with an added
  representability assumption.
- `stack_smooth_presentation_criterion` asserts A ↔ B, A ↔ A_scheme and A ↔ B_scheme.
  Thus all four conditions are equivalent; A is the smooth-chart definition named by
  `IsSmoothModuliMap`, with no choice of an atlas.
- `isSmoothModuliMap_iff_space_smooth` treats every actual space morphism `f : X ⟶ Y`
  through its `discreteModuliMap f.hom.hom` and asserts equivalence with ordinary space
  smoothness. It adds no atlas, stack, separation or finiteness hypothesis for the spaces.
- `isSmoothModuliMap_iff_representable_smooth` has exactly algebraicity and
  `hf : IsRepresentableByAlgebraicSpaces f`, and concludes equivalence with
  `ModuliSpaceTest (@Smooth) f`, the specified scheme-base-change projection being smooth.
  This covers EVERY scheme T → Y, not just an atlas or geometric-point tests.
- No Deligne--Mumford, quasi-compactness, separation, Noetherian or finite-type assumption
  occurs. Importing DmStackMorphismProperties uses its fully general `ModuliSpaceTest`;
  that definition has no DM hypothesis.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: `AlgebraicGeometry.Smooth`.
- Mathlib.Algebra.Field.Defs: `Field`, used by the imported surjectivity definition.
- Sheaf.AlgebraicGeometry.AlgebraicModuliStack: `CategoryTheory.IsAlgebraicModuliStack`
  (with its `SpaceMapIsSmooth`, `IsSmoothModuliAtlas` definitions inspected).
- Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids: `discreteModuli`,
  `discreteModuliMap`, `moduliTwoFiberProduct`, `HasSpaceBaseChange`,
  `IsRepresentableByAlgebraicSpaces`, `ModuliTwoIso`; the full signatures and docstrings
  were read, including the actual projection comparison in `HasSpaceBaseChange`.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsEtale` and its scheme-test definition.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties:
  `AlgebraicSpace.MapIsLocally`. Its already landed node
  def-sfb-space-morphism-properties was added to stmt_deps.
- Sheaf.AlgebraicGeometry.DmStackMorphismProperties: `CategoryTheory.ModuliSpaceTest`.
  Its already landed node def-sfb-dm-stack-morphism-properties was added to stmt_deps.
- Sheaf.AlgebraicGeometry.ModuliChartNormalization: `CategoryTheory.moduliTwoFiberLift`.
  Its already landed node def-sfb-moduli-chart-normalization was added to stmt_deps.
- Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus:
  `CategoryTheory.IsSurjectiveModuliMap`. Its already landed node
  def-sfb-surjective-moduli-map was added to stmt_deps. This definition node records
  the existing predicate in the same module; no theorem conclusion supplies its data.

These additions are the already-landed-node provision of brief-stage2 section 5. No
copied definition and no dependency record repair is involved. A graph traversal of
statement and proof dependencies found no path from any of these four nodes to this item.

All recorded, currently stated proof dependencies are imported: EnlargedEtaleRingedSite,
AlgebraicStackFibreProducts, SchemeEtaleSourceTargetProperties,
SpaceEtalePresentationPropertyCriterion and AlgebraicSpaceRepresentableEtaleSchemeTests,
in addition to the statement imports. The four proof prerequisites without usable Lean
records (representable-smooth calculus, representable pullback over a space, smooth-source
point locality and smooth-surjective fppf locality) are not needed to type the statement;
the proof docstrings cite them and their DAG proof edges remain unchanged.

Source read: literature/stacks-project/stacks-morphisms.tex, lemma-local-source-target
(Tag 06FM), including its comparison diagrams, and the section-smooth introductory
verification and definition-smooth (075U). The node is not the blueprint unit's own
statement. This criterion does not assert an unproved existence as definition data.

Edge cases checked before writing:

- Empty source: empty source diagrams are allowed; A's universal quantifier and B's
  field-extension surjectivity do not impose Nonempty. A smooth empty atlas is permitted.
- Empty target forces an empty source for an actual stack morphism, and is not excluded.
- Identity space maps use the identity square. The canonical comparison to X ×_Y Y is
  retained, so the algebraic-space clause tests the original morphism.
- A nonsmooth or positive-dimensional-stabilizer Artin stack is not excluded by a DM
  requirement. For BG → Spec k, a smooth atlas gives the expected smooth criterion.
- The target chart can miss components: B never requires it to be surjective. This was
  checked explicitly against Stacks 06FM and all four predicate definitions.
- A representable morphism is tested on arbitrary schemes and all etale charts of the
  actual base changes, not merely a selected presentation. All field characteristics and
  unrestricted geometric fibres remain allowed.

Searches (all for this item through the prescribed msearch wrapper):

- LeanFinder: “A morphism of algebraic stacks is smooth if and only if every compatible
  smooth presentation is smooth”: 8 hits, all scheme/ring smoothness, including
  AlgebraicGeometry.isSmooth_iff and IsSmooth. No stack-presentation criterion.
- Loogle: `"Smooth", "Stack"`: 0 hits.
- grep Mathlib/AlgebraicGeometry: `AlgebraicStack|smooth.*presentation`: 6 hits, all scheme
  smoothness or finite presentation. Full scheme Smooth signature read in local Mathlib.
- LeanSearch: “Smooth morphisms of algebraic stacks are independent of smooth
  presentations”: 8 hits, scheme/ring smoothness only.
- rg in lean/WeilConjectures and lean/Sheaf for smooth presentations, representable
  smoothness, algebraic stacks, and the proposed declaration names: found the existing
  chartwise stack calculus, algebraic-space chart property, and canonical comparison;
  no duplicate general criterion or any of the new declaration names. Searching for the
  node id in lean/WeilConjectures found no match. The recorded upstream names index
  likewise has none of these declarations.

Validation: scompile.py Q58 lem-sfb-stack-smooth-presentation-criterion on the delivered
module passed both sandbox and library checks (5.0 s and 3.7 s), without warnings.
No STATEMENT-DISPUTED fault was found.

## Second reading by Q58

This is the worker's second reading; the dispatcher's requested independent review is
performed by the maintainer. No additional agent was started.

Reopened the node and the complete delivered module after compilation. Matched S and the
two arbitrary algebraic stacks to their explicit binders; matched every diagram component
and the orientation of comm to a.comp f ≅ q.comp b; checked the canonical comparison has
first component a and second component q. Compared A and B separately: only A requires
its induced map smooth, only B requires a surjective, neither requires b surjective.
Matched the two scheme analogues using actual Over S objects and q.left; checked all
three equivalences together include all four tests. Finally matched the space comparison
and the representable comparison to the final two sentences of the node. The existing
ModuliSpaceTest both supplies representability and tests the actual smooth projection,
so no missing representability conjunct or extra DM hypothesis is hidden in a helper.
No mismatch found and no statement changed during the second reading.

## Returned delivery repair: H2

The return on immutable head 255da6da2529 identified that the plain predicate
`CategoryTheory.IsSurjectiveModuliMap` must be cited through its definition node.
Replaced `lem-sfb-stack-chartwise-smooth-etale-calculus` in `stmt_deps` with the
already landed `def-sfb-surjective-moduli-map` (Q87, `existing: true`). Read that
node and the declaration with its full signature and source docstring at
StackChartwiseSmoothEtaleCalculus.lean:69: it is exactly the field-extension-local
lifting predicate used in the two existential chart conditions. The public import
already provides this declaration, so the Lean module requires no modification.
The mathematical statement, proof plan and all other dependency edges are retained.
Compared the saved node with current main: only `lean` and the four added
statement dependencies differ. Delivery tooling rebuilds the repair on current main.
The second reading confirms that the replacement changes the owning DAG reference
and leaves every hypothesis, chart condition and comparison theorem intact.

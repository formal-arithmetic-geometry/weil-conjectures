## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteInertiaPointwiseGroupoidChart` states
`CategoryTheory.exists_finiteInertia_pointwise_groupoid_chart`. Its only theorem has
proof `sorry`; it introduces no new definition and changes no natural-language
statement. There is no repair note for this item. I read Stacks
`stacks-morphisms.tex`, label `lemma-etale-local-quasi-DM-at-x` (Tag 0DU4), its
preceding proof, and `lemma-diagonal-diagonal` (0CL0), especially (1) and (5).
The tags table confirms 0DU4. This is the source's finite-inertia specialization.

Hypotheses and clauses, in node order:

- The base field is `(k : Type u) [Field k]`; schemes over it are
  `Over (Spec (.of k))`. `u`, `v`, and `w` are explicitly declared. The arbitrary
  target's morphism and object universes remain independent. The quotient's
  `BasedCategory.{u + 1, u + 1}` fits the category of schemes and all fppf descent
  data in the next universe; this imposes no size condition on the target.
- `X : BasedCategory ...` and `hX : IsAlgebraicModuliStack X` express the algebraic
  stack hypothesis, including CFG, etale descent, space diagonal and smooth atlas.
  The source and the statement's opening convention supply this hypothesis.
- Inertia is the existing `moduliInertia X` with conjugating arrows, and the
  projection is `moduliInertiaProjection X`. Its finite-inertia hypothesis is
  `IsRepresentableFiniteModuliMap (moduliInertiaProjection X)`: every scheme test
  is a finite scheme, with the actual projection compared over the base.
- The specified point is `x : ModuliPoints X`, the recorded field-object quotient.
  Its existing topology is supplied by `StackPointTopology`. No topological
  condition is imposed on x.
- The existential `U R : Over (Spec (.of k))`, `s t : R ⟶ U`, and `e,i,c` give
  exactly the schemes and groupoid operations. `IsAffine U.left` and
  `IsAffine R.left` give both affineness clauses. `IsGroupoidScheme ...` is the
  dependency's recorded groupoid law predicate on these same operations.
- `s.left.IsFiniteLocallyFree` and `t.left.IsFiniteLocallyFree` use the recorded
  upstream classes: finite, flat and locally finitely presented, with no constant
  rank or positive-rank requirement.
- `V`, its atlas map `a`, and
  `Nonempty (SchemeGroupoidQuotientPresentation s t e i c V a)` say that V is
  `[U/R]`: an fppf stack with the original arrow bijections, composition and fppf
  local objects. This existing presentation interface retains the actual
  groupoid, not just its orbit sheaf. Its groupoid field uses the equivalent
  `Scheme.IsGroupoid` law predicate; there is no second construction here.
- `IsAlgebraicModuliStack V` makes explicit that the quotient is an algebraic
  stack, as in 0DU4. `h : BasedFunctor V X` is the requested stack morphism;
  `IsRepresentableByAlgebraicSpaces h` and `IsEtaleModuliMap h` give precisely its
  two properties, with etaleness on scheme charts of every space base change.
- `z : ModuliFieldObject V` represents the requested point v, and
  `moduliPointMap h (Quot.mk _ z) = x` says h(v)=x. It chooses a representative of
  v, so h(z) represents x over exactly the same field scheme; this is a permitted
  common-field choice in the node's final sentence.
- The last universal clause uses every `T : Over (V.p.obj z.val).left`, every
  pullback object `b` in the fibre over T, and every arrow `β : b.val ⟶ z.val`
  over its structural map. All such arrows are cartesian in a CFG. It asserts
  bijectivity of the actual `moduliFiberMap h ... |>.mapAut` at b. Every T has
  such a pullback, so this is not vacuous. V's fppf stack condition includes the
  CFG lifting condition. The automorphism maps commute with further pullback by
  h's functoriality and preserve group operations. Thus Yoneda identifies the
  stabilizer group schemes, including nilpotent structure, rather than merely
  their field-valued points. There is no demand that h preserve stabilizers at
  any other point.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`: `IsAlgebraicModuliStack`, with
  `IsSmoothModuliAtlas`, `SpaceMapIsSmooth`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, its representable,
  etale and surjective map predicates; imported transitively by the stack API.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`: `BasedCategory`-based
  CFG conventions, `IsFibredInGroupoids`, `discreteModuli`, `ModuliTwoIso`,
  `moduliTwoFiberProduct`, `HasSpaceBaseChange`,
  `IsRepresentableByAlgebraicSpaces`, `SpaceMapIsEtale`, `moduliFiberMap`.
- `Sheaf.AlgebraicGeometry.ModuliInertia`: `moduliInertia` and
  `moduliInertiaProjection` (objects, conjugating arrows and forgetful functor).
- `Sheaf.AlgebraicGeometry.FiniteStackSchemeTests`:
  `IsRepresentableFiniteModuliMap`.
- `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`: `ModuliFieldObject`,
  `ModuliPoints`, `moduliPointMap`. These underlying definitions work for all CFGs;
  no DM hypothesis is added. `ModuliChartNormalization` supplies
  `IsEtaleModuliMap`, without a normalization hypothesis.
- `Sheaf.AlgebraicGeometry.GroupoidScheme`: `IsGroupoidScheme`.
- `Sheaf.AlgebraicGeometry.SchemeGroupoidQuotientPresentation`:
  `SchemeGroupoidQuotientPresentation`, whose stack field is the existing
  `IsFppfModuliStack` from `Sheaf.CategoryTheory.SiteStackification`.
- `Sheaf.AlgebraicGeometry.StackPointTopology`: `stack_point_topology` and its
  imported actual point topology. The conclusion itself is set-theoretic.
- `Sheaf.CategoryTheory.GroupoidStackificationLocalDescription`:
  `Pseudofunctor.exists_groupoid_stackification_local_description`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfTopology` (its over-site).
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `Scheme.Hom.IsFiniteLocallyFree`, read at current lines 893–908.
- The scheme property dependencies use existing `Flat`,
  `LocallyOfFinitePresentation`, `Etale`, `IsProper`, `IsSeparated`,
  `UniversallyClosed`, `IsFinite`, and `IsIntegralHom`; their signatures and
  docstrings were read in the respective Mathlib morphism files. No new
  separatedness or properness hypothesis occurs in the conclusion.

The five owning definition nodes for inertia, finite tests, quotient presentations,
representable etale maps and field-object point maps were already landed. They are
appended to `stmt_deps`, as allowed for landed interfaces. No dependency node is
changed. The proof-only imports include the currently stated chartwise calculus,
flat-lfp openness and scheme permanence facts. The other proof nodes currently
have no Lean record, so no fictional module is imported. The docstring records all
five accepted proof steps, including the restricted self-relation comparison and
the full scheme stabilizer comparison.

Edge cases checked: the empty stack has no x, so its case is correctly vacuous;
a nonempty x forces the chart to contain a point without assuming the object
scheme nonempty separately. Rank zero over irrelevant components is allowed.
For the trivial stack the identity finite-flat relation and identity chart give
the expected result. In characteristic p, the example B(mu_p) requires a flat
finite presentation rather than a DM or finite-etale atlas; neither extra
hypothesis is present. The final stabilizer test includes dual-number and other
nonreduced T, so mu_p is not mistaken for the trivial group. No finite-type,
Noetherian, perfect-field or algebraic-closure assumption is added. Pullback
objects exist also over the empty test scheme.

Searches performed for this item:

- `msearch.py`, leanfinder: "An algebraic stack with finite inertia has a pointwise
  stabilizer preserving etale affine finite locally free groupoid chart".
  Eight hits on scheme Etale and its permanence instances; none is this theorem.
- `msearch.py`, leansearch: "Algebraic stacks with finite inertia admit pointed
  etale neighbourhoods presented by affine finite flat groupoids preserving
  stabilizer group schemes". Eight hits: scheme etale topologies, ring standard
  etale pairs, etale permanence, finite affine morphisms; no exact match.
- `msearch.py`, loogle: `"IsEtale", "Groupoid"`: zero hits.
- `msearch.py`, grep: `finite.inertia|pointwise.*stabilizer|quasi.DM`: two unrelated
  imports of pointwise stabilizers in combinatorics/group theory.
- `rg` over both project source roots for finite inertia, stabilizers and quotient
  presentations found the existing interfaces listed above, but no pointwise
  finite-inertia chart theorem. `rg` for the exact node id in `WeilConjectures`
  found no declaration. The proposed declaration name also has no existing hit.
  The example `CompactObject.lean` is withdrawn; its node records the upstream
  `WeilConjectures.CategoryTheory.CompactObject`, which I read for conventions.

Validation: `scompile.py` on the final module returned exit 0 for the sandbox and
library names, with no errors or warnings (13.8 s and 14.3 s). Earlier elaboration
attempts exposed an unannotated `Over.homMk` whose source/target inference invoked
its default proof tactic; an explicit type and `rfl` resolve that expression.
The timeout limit was never raised. Temporary probes are removed. All variables
and universes are explicit (`autoImplicit false`), all lines are at most 100
characters, and the node's recorded signature is extracted verbatim from the file.
No statement dispute, source correction, new node, or dependency repair is needed.

## Second reading by Q146

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

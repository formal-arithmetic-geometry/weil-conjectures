## Worker report

Item: lem-sfb-dm-effective-formal-stabilizer-chart. Group NO, stage 2.
Module: `Sheaf.AlgebraicGeometry.DMEffectiveFormalStabilizerChart`.
Main declaration: `CategoryTheory.exists_effectiveFormalStabilizerChart`.

The statement is `Nonempty (DMFormalChart.Chart F x)`. `Chart` is an explicit
bundle of the conclusion, not an assumption or an arbitrary formal presentation.
All helper definitions have real data. The main theorem is the only postponed
proof. The statement is unchanged. There are no new nodes or dependency repairs.

Clause-by-clause reading:

- Algebraically closed ground field: `{k : Type u} [Field k] [IsAlgClosed k]`.
- The stack over k: `F : BasedCategory.{v,w} (Over (Spec (.of k)))` with
  `IsDeligneMumfordModuliStack F`. This is the dependency's actual CFG/etale
  descent/representable-diagonal/surjective-etale-atlas convention. No property
  about tame inertia, smoothness or coarse moduli is assumed.
- Finite type: `HasFiniteTypeEtaleModuliAtlas F`. Finite diagonal:
  `HasFiniteModuliDiagonal F`. Both are exactly the recorded scheme tests.
- The rational object is the map `x : h_(Spec k) → F`. The dependency explicitly
  identifies maps from schemes with their objects, retaining all automorphisms.
  Its vertical automorphism group is `Aut x` in the category of based functors.
- An etale scheme atlas is `Chart.U`, `p` and `atlas`. The last field retains the
  actual projections of every algebraic-space base change and asserts etaleness
  and surjectivity, exactly as the recorded DM convention does. `u : Spec k → U`
  and `pointIso : p(u) ≅ x` give the point and its specified identification.
- `R`, `s`, `t`, `η` and `universal` represent `U ×_F U` with its two projections.
  `η` is the universal vertical isomorphism `p s ≅ p t`. For every test scheme,
  every isomorphism of two atlas objects is induced by exactly one map to `R`,
  with both projections specified. This is the functor-of-points universal
  property of the two-fibre product, rather than just an unrelated equivalence
  or a bijection of geometric points. `etale` and `finite` give its etale
  projections and its finite map to `U ×_k U`.
- The stabilizer is `H` with its group structure, `finiteStabilizer` and the
  multiplicative equivalence `stabilizer : H ≃* Aut x`. A small finite model is
  used so coproducts of schemes have the ground universe; the stack's object
  and morphism universes remain independent. No smallness hypothesis is added.
- The fibre at `(u,u)` is `D`, with cartesian square `fiber` and colimit cofan
  `reducedFiber : IsColimit (Cofan.mk D point)` of copies of `Spec k` indexed
  by `H`. Thus this is the finite reduced scheme fibre, not only its set of
  rational points. `d` is its map to `R`. `label` identifies the universal
  arrow at the h-labelled point with conjugation of `stabilizer h` by
  `pointIso`.
- Identity, inverse and composition are specified without an independent choice
  of operations: `universal` identifies every arrow sheaf with the actual
  isomorphism sheaf in `F`. Transporting identity, inverse and composition
  along this identification is unique, is natural on every test scheme, and
  obeys all groupoid laws because stack isomorphisms do. This is exactly the
  two-fibre-product groupoid stipulated by the node. Since `label` uses a
  **multiplicative** equivalence, its reductions are identity, inversion and
  composition in H. In particular there is no set bijection forgetting the
  composition law and no newly postulated groupoid law.
- `tower U I` is the recorded `AdicFormalCompletion.thickenings` over k, with
  `I^(n+1)` at index n. `towerι` is its canonical map to U. Thus the formal
  atlas is `tower U u.left.ker`, and the completed arrow system is
  `tower R d.left.ker`. The point and fibre ideals are the actual scheme
  morphism kernels, not ideals chosen with only the same support.
- A is literally `AdicCompletion (maximalIdeal (U.left.presheaf.stalk z))
  (U.left.presheaf.stalk z)`, where `z = u.left (IsLocalRing.closedPoint k)`.
  `completedAtlas U z` is `Spec A` over k; `completedAtlasMap` is explicitly
  `Spec.map (CommRingCat.ofHom (algebraMap _ A)) ≫ U.left.fromSpecStalk z`. `completedIdeal` is the extended
  maximal ideal on `Spec A`, defined using the actual completion algebra map
  and `ΓSpecIso`. `effectiveComparison` identifies its thickening system with
  the formal atlas, and `effectiveComparison_map` fixes this identification
  over U, using that canonical map. Consequently the formal object is the
  restriction of `moduliChartMap (completedAtlasMap U z) p`, the effective
  morphism `Spec A → U → F`; it is not an unrelated chosen formal object.
- For each h, the completion at the actual arrow point is
  `tower R (point h ≫ d).left.ker`. The natural isomorphisms `source h` and
  `target h`, with `source_map` and `target_map`, identify the completed source
  and target with the formal atlas. Naturality includes every reduction map;
  their ambient-map equations fix the isomorphisms as the original s and t.
- `piece h` and `piece_map` are the compatible maps from each point completion
  into the whole fibre completion. `pieces n` is the coproduct universal
  property at **every** thickening. Thus the assertion is a disjoint-union
  decomposition of systems, not a statement about disjoint ambient opens.
- The target formal completion uses the already recorded `ModuliCompletionAt`:
  all geometric objects are scalar extensions of x. In this Noetherian,
  finitely generated point-ideal situation it equals the locally nilpotent
  test convention in the node. Vanishing at every geometric point means that
  the finitely many local generators lie in the nilradical; a common power
  vanishes on a sufficiently small affine test. Conversely a nilpotent
  thickening does not change geometric points. This concerns the full
  residual gerbe; no special-fibre trivialization is fixed globally.
- `mapsIntoCompletion` sends every atlas thickening map into that completion.
  `objects` says every object in the completion lifts on an arbitrary etale
  covering sieve to some atlas thickening, with the actual object isomorphism.
  `arrows` factors **every** isomorphism between any two such lifts through a
  thickening of the fibre; `universal` identifies all these arrows faithfully
  and uniquely. These are precisely local essential surjectivity and the full
  isomorphism-sheaf identification for stackification. As F is a stack, descent
  then gives its completion as the stackification of the completed groupoid.
  This formulation includes descent data for nontrivial torsors, unlike a
  groupoid of globally chosen atlas lifts only.
- Every completed arrow supplies the pullback of the single universal `η` at
  every thickening. Its compatibility with reductions is naturality; its two
  objects are restrictions of the effective object by
  `effectiveComparison_map`, `source_map` and `target_map`. There is no
  independent arrow or comparison chosen on individual thickenings.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `BasedCategory`/`BasedFunctor` from its Mathlib imports,
  `IsDeligneMumfordModuliStack`, `HasSpaceBaseChange`, `SpaceMapIsEtale`,
  `SpaceMapIsSurjective`, `discreteModuli`, `discreteModuliMap`, and the
  two-fibre-product/vertical-two-isomorphism conventions. Read the declarations
  and docstrings in its generic interface, lines 360–541.
- `Sheaf.AlgebraicGeometry.FiniteStackSchemeTests`:
  `HasFiniteModuliDiagonal` and `HasFiniteTypeEtaleModuliAtlas`; read the whole
  module, including the projection-compatible scheme tests.
- Mathlib: `Field` (Algebra/Field/Defs), `IsAlgClosed` (FieldTheory/IsAlgClosed/Basic),
  `Scheme` and its morphisms/stalks, scheme `Etale`, and `AdicCompletion` with its
  canonical algebra structure (RingTheory/AdicCompletion/Basic and Algebra).
  The algebraically-closed clause uses `IsAlgClosed`, as the algebraic-closure
  node's `mathlib_match` specifies; it does not require a chosen algebraic closure.
- Added landed dependency `def-sfb-formal-moduli-quotient`:
  `Sheaf.AlgebraicGeometry.FormalModuliQuotient`, `moduliChartMap` and
  `ModuliCompletionAt`; read its whole module. Only the existing chart-map and
  residual-gerbe predicates are reused; no duplicate quotient definition.
- Added landed dependency `def-per-adic-formal-completion`:
  `Sheaf.AlgebraicGeometry.AdicFormalCompletion`, `AdicFormalCompletion` and
  `.thickenings`; read its construction. `tower` only changes its base category
  using `Over.map`, retaining those exact schemes and transitions.
- Mathlib `Mathlib.AlgebraicGeometry.Stalk`: `Scheme.fromSpecStalk`, composed
  explicitly with `Spec.map` of the canonical `AdicCompletion` algebra map in
  `completedAtlas` and `completedAtlasMap`. No completed-local-base-change
  theorem node is a statement dependency.

All currently stated proof dependencies are imported as plain proof imports,
including etale fibres, DM Isom-space unramifiedness, unramified finite algebras,
Noetherian permanence, completion quotients/locality, etale completion isomorphisms,
thickening invariance and the affine formally-etale lifting theorem. Statement
imports are public. There is no import cycle introduced by these dependencies.

Edge cases checked before and after writing:

- H trivial: the cofan has a single `Spec k`, with the same full object/arrow clauses.
- Wild finite stabilizers, e.g. B(Z/p) in characteristic p: no characteristic or
  invertibility condition is used, and the finite *etale* stabilizer is not forced
  to be linearly reductive.
- Empty test schemes: the universal relation has its unique empty map and arrow;
  no uniqueness of a global group label on an empty scheme is asserted. An empty
  stack has no rational x, so the theorem has no such instance, as intended.
- Index zero means the closed fibre, since `.thickenings` uses n+1; no zero-power
  neighbourhood is silently removed or substituted.
- Nonreduced tests and different atlas-thickening levels n,m are retained in
  `universal` and `arrows`. For the latter, the fibre ideal is generated by the two
  pulled-back point ideals; their bounded nilpotence gives a common finite N.
- Infinite/disconnected test schemes are allowed. The object-lifting stage n is
  local on an arbitrary covering sieve, so no uniform bound on all tests is assumed.
- Independent v,w for F are retained. Only a small **finite model** of the
  stabilizer is placed in Type u, with an explicit equivalence to the actual group.

Searches executed (2026-10-24):

1. `msearch.py ... leanfinder` query: “An etale atlas of a Deligne Mumford stack
   completed at a point presents its formal completion by its finite automorphism
   group”. Eight hits about `Scheme.Etale`, ordinary etale morphisms and standard
   etale presentations; no stack-completion statement.
2. `msearch.py ... loogle` query: `AdicCompletion, AlgebraicGeometry.Scheme`.
   Result: OK, zero hits.
3. `msearch.py ... grep` query:
   `DeligneMumford|residualGerbe|formalCompletion|stabilizerChart`.
   Result: OK, zero Mathlib hits.
4. `rg` in `lean/WeilConjectures` for the item id: no hit. Broader keyword searches
   in that directory found ordinary coherent-module completion systems, not this
   stack theorem. `rg` in `lean/Sheaf` found the two reused definition prerequisite
   modules listed above and the completed-local-base-change helper (expanded
   inline in this repair), plus algebraic-space/groupoid and stable-moduli modules;
   no existing declaration states the item. Exact declaration names were checked
   against the project search results before introducing them.
5. Source reading: local Stacks `stacks-geometry.tex` at
   `remark-groupoid-defo` (0DR3), and `etale.tex` at
   `lemma-characterize-etale-completions` (039M) and its residue-degree remark.
   0DR3 is the framed presentation motivating the route; the node explicitly gives
   the direct finite-diagonal etale specialization and its unframed descent proof.

No STATEMENT-DISPUTED issue or node correction was found. The helper structure
spells out the node's conclusion; it introduces no replacement for a dependency's
notion. The theorem docstring retains all ten proof steps and their cited inputs.

All declaration signatures and universes are explicit. The only `sorry` is the
main theorem. Repair validation is recorded below.

## Second reading by NO

The dispatcher forbids starting another agent; this is a second self-reading, with
independent maintainer review still required. I reopened the node, its source and
all fields of `Chart`. I checked the list above against the original hypotheses and
each clause. The scheme-theoretic fibre is a cartesian square plus a coproduct of
`Spec k`; point indexing is tied to the actual group by `label`. The completed maps
are natural isomorphisms fixed over the ambient atlas and relation. The decomposition
is a levelwise coproduct compatible in the index. The effective object is tied to
the explicit completion-map/fromSpecStalk composite, and all arrows arise from
the universal arrow. Local lifts
and all-arrow factorization describe stackification and preserve residual-gerbe
automorphisms. I checked empty tests, n=0, wild characteristic and arbitrary
stack universes explicitly. No mathematical mismatch was found. Compiler repairs
were limited to the over-category extensionality syntax, an explicit `ΓSpecIso`
ring parameter, and declaring s and t as separate structure fields; none changes
the statement. No independent second-reader review is claimed here.

## Repair of returned delivery e558f94391c4

The maintainer's H2/H12 finding was that a theorem node owned no definition of
`Scheme.completionBaseMap`, despite that helper being the only declaration used
from its module. I applied the expressly authorized inline-composite correction:
`completedAtlas` and `completedAtlasMap` now construct
`Spec.map (CommRingCat.ofHom (algebraMap stalk completion)) ≫ fromSpecStalk`
directly. This is definitionally the same canonical morphism. The import of
`Sheaf.AlgebraicGeometry.CompletedLocalBaseChange` is replaced by Mathlib's
`AlgebraicGeometry.Stalk`, and `lem-trf-completed-local-base-change` is removed
from `stmt_deps`. No new notion, node or postponed proof is introduced. The
`Chart` fields and main theorem signature are unchanged. The remaining
statement-dependency additions are both definition nodes. The main-branch node
was compared with the retained returned node; the delivery wrapper rebases the
repair onto the current live repository.

Repair validation: `scompile.py` compiled the repaired sandbox and named library
module cleanly on the server (15.7 s and 20.9 s), with no errors or warnings
beyond the permitted main-theorem `sorry`. `deliver2.py --no-push` returned
`OK (dry run): commit ed27e1d20ca passes the preflight and compiles; nothing pushed`.

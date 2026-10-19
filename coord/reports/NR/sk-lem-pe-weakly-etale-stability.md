## Worker report

`Sheaf.AlgebraicGeometry.WeaklyEtaleStability` states the full stability package in
`sk-lem-pe-weakly-etale-stability` (blueprint main-20261015,
`sec-proetale-coefficients/sk-lem-pe-weakly-etale-stability/_section.md`, node order 702;
Stacks Project Tag 092A). The theorem proof is `sorry`; its docstring records the five
current source proof steps.

The node's clauses are rendered as follows. The first clause, stability of weakly étale
morphisms under base change, is
`MorphismProperty.IsStableUnderBaseChange @WeaklyEtale.{u}`. The second clause, stability under
composition, is `MorphismProperty.IsStableUnderComposition @WeaklyEtale.{u}`. Zariski locality on
source and target are respectively `IsZariskiLocalAtSource @WeaklyEtale.{u}` and
`IsZariskiLocalAtTarget @WeaklyEtale.{u}`. For the clause about an `X`-morphism between two weakly
étale `X`-schemes, the theorem quantifies schemes `S U V`, structure maps
`u : U ⟶ S`, `v : V ⟶ S`, and `f : U ⟶ V`, and states
`WeaklyEtale u → WeaklyEtale v → f ≫ v = u → WeaklyEtale f`; the displayed equality is exactly
that `f` is an `S`-morphism. Affine pro-étale composition quantifies affine schemes
`X Y Z`, maps `f : X ⟶ Y`
and `g : Y ⟶ Z`, and concludes `proAffineEtale (f ≫ g)` from `proAffineEtale f` and
`proAffineEtale g`. Affine base change quantifies affine schemes `X Y` and `f : X ⟶ Y`,
and states `proAffineEtale.{u}.IsStableUnderBaseChangeAlong f`. Its tested morphisms have
affine source because `proAffineEtale.isAffine`; their target is the affine scheme `Y`.
Thus both final clauses concern affine spectra of ind-étale ring maps, exactly as the
current server statement specifies. The equivalence is the recorded
`AlgebraicGeometry.proAffineEtale_Spec_iff` (and `proAffineEtale_iff_appTop`).

The statement dependency `sk-def-pe-morphisms` is used through the declarations exported by
`WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale`: `AlgebraicGeometry.WeaklyEtale`,
`AlgebraicGeometry.proAffineEtale`, and the associated morphism-property interfaces. The
proof-only dependency module `Sheaf.RingTheory.IndEtaleStability` is imported explicitly;
its declaration is `RingHom.indEtale_principalZariski_stability`.
The additional current statement dependency `def-weil-weakly-etale-morphism` uses
`AlgebraicGeometry.WeaklyEtale` in `Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`.
The dependency `def-weil-pbc-ind-etale-algebra` uses the imported module
`Sheaf.RingTheory.IndPrincipalZariski`, whose existing exported declarations include
`Algebra.IndEtale`, `Algebra.WeaklyEtale`, and `proAffineEtale_Spec_iff`.
All remaining proof dependencies are Mathlib declarations already imported transitively:
`CategoryTheory.Limits.pullback`, `AlgebraicGeometry.Flat`, `IsOpenImmersion`, `Flat.comp`,
`Flat.isStableUnderBaseChange`, and `pullbackSpecIso`.

Edge cases checked were identity morphisms, empty schemes, arbitrary (including empty) base
schemes, affine identity base change, and composition with an identity. The affine base-change
clause keeps both source and target affine and imposes no extra finiteness or
nonemptiness hypothesis. No clause of the source statement is dropped or strengthened.
There is no `STATEMENT-DISPUTED` issue, no new node, and no dependency module.

Searches for existing declarations were made with `msearch.py` and `rg`: LeanFinder query
“weakly etale morphisms stable under base change composition local on source target Zariski
affine pro-etale stable affine base change composition” returned only generic étale results;
Loogle query `WeaklyEtale, baseChange, proAffineEtale` returned zero hits (unknown identifier
for the unqualified name); grep query `WeaklyEtale|ProAffineEtale|baseChange` over Mathlib's
AlgebraicGeometry directory returned 25 unrelated base-change hits. A source/project grep for
`weaklyEtale.*between|HasOfPostcompProperty.*Weakly|proAffineEtale.*Stable|IsStableUnderBaseChange`
found no bundled declaration matching all clauses. The recorded dependency's upstream module
was then opened and its full signatures read. Thus this theorem is not a duplicate of one
existing declaration.

Validation: `scompile.py NR sk-lem-pe-weakly-etale-stability` compiles the module in both the
sandbox and library forms cleanly. The declaration has no auto-bound variables and all lines are
within 100 characters.

Earlier-attempt repairs: the theorem is now namespaced as
`AlgebraicGeometry.weaklyEtale_stability`. Every morphism-property clause explicitly uses
universe `u`, matching the quantified schemes; `set_option autoImplicit false` checks that
all binders are declared. The inherited second-reading text was removed for the independent
second reader. The initial shared checkout was stale: the server has the reviewed
stage-1 split with
three statement dependencies, five proof steps, and the affine-spectrum convention.
The sandbox node was refreshed from that current server node, changing only its `lean`.
The final clauses were restricted to affine schemes to follow that convention exactly;
this delivery makes no statement correction.

Fresh searches: LeanSearch via `msearch.py`, query “weakly etale morphisms stable under
base change and composition Zariski locality affine pro etale”, returned eight results
on ordinary étale stability, formal étaleness and generic descent; none is the full package.
Direct `rg` in Mathlib and upstream found the separate weakly étale instances and
`WeaklyEtale.of_comp` in `Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`, and the separate
pro-affine-étale composition and affine base-change instances in
`WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale`. These verify the individual
clauses and definitions but no existing single declaration states their conjunction.
The name `weaklyEtale_stability` and this blueprint id have no declaration hits in the
upstream tree, `dag/lean_names_upstream.json`, or the side library. The local blueprint
unit statement was read verbatim, and Stacks Tag 092A was resolved and read in
`more-algebra.tex` (section `section-weakly-etale`).

## Second reading by NR

I read the authoritative sandbox node copy (refreshed server statement) and the Lean module
against the source section and its cited definitions. The node's objects, hypotheses, and
conclusion are rendered as follows.

1. The weakly étale morphism property is `@AlgebraicGeometry.WeaklyEtale.{u}` from the
   Mathlib declaration recorded for `def-weil-weakly-etale-morphism` and exposed by
   `sk-def-pe-morphisms`; no private predicate is introduced. The category universe is
   `Scheme.{u}`, so every scheme and morphism in the property has the same universe as in
   the dependency declarations. The hypothesis and conclusion that this property is stable
   under arbitrary base change are rendered by
   `MorphismProperty.IsStableUnderBaseChange @WeaklyEtale.{u}`. Verdict: exact.
2. Stability under composition of weakly étale morphisms is rendered by
   `MorphismProperty.IsStableUnderComposition @WeaklyEtale.{u}`. This quantifies over two
   composable morphisms and requires each to have the property before asserting it for their
   composite. Verdict: exact.
3. Zariski locality on source and target is rendered respectively by
   `IsZariskiLocalAtSource @WeaklyEtale.{u}` and
   `IsZariskiLocalAtTarget @WeaklyEtale.{u}`. These are the two locality clauses of the
   node and do not add separatedness, quasi-compactness, or finiteness. Verdict: exact.
4. For the node's base scheme `S`, objects `U,V`, structure maps `u : U ⟶ S` and
   `v : V ⟶ S`, and `S`-morphism `f : U ⟶ V`, the Lean clause is
   `WeaklyEtale u → WeaklyEtale v → f ≫ v = u → WeaklyEtale f`.
   The equality is precisely the condition that `f` is an `S`-morphism; the two weakly
   étale hypotheses and the conclusion occur in the node's order. Verdict: exact.
5. For affine schemes `X,Y,Z`, maps `f : X ⟶ Y` and `g : Y ⟶ Z`, the composition clause
   is
   `proAffineEtale f → proAffineEtale g → proAffineEtale (f ≫ g)`, under
   `[IsAffine X] [IsAffine Y] [IsAffine Z]`. `proAffineEtale` is the recorded upstream
   affine inverse-limit/ind-étale morphism property, and the affine assumptions are the
   node's affine-composition convention. Verdict: exact.
6. For affine schemes `X,Y` and a base-change map `f : X ⟶ Y`, the final clause is
   `proAffineEtale.{u}.IsStableUnderBaseChangeAlong f`. This is the property that every
   pro-affine-étale map with codomain `Y` remains pro-affine-étale after pullback along
   this affine map. The source and target affine hypotheses are explicit and no
   nonemptiness or finiteness hypothesis is added. Verdict: exact.

The module imports the source declaration for `proAffineEtale` and the existing
`Algebra.IndEtale` interface through `Sheaf.RingTheory.IndPrincipalZariski`; it imports the
proof-only ring stability theorem `RingHom.indEtale_principalZariski_stability` through
`Sheaf.RingTheory.IndEtaleStability`. The five theorem-docstring proof paragraphs match the
five proof steps in the authoritative node: weakly étale base change, composition,
Zariski locality, the graph/diagonal argument for an over-base morphism, and affine
ind-étale base change/composition. No definition is hollow and the theorem is the sole
`sorry` declaration.

I checked edge cases: identity maps and identity composition, the zero/empty indexing
possibility in the ind-étale presentation (the upstream `IndEtale` convention supplies its
filtered nonempty index), empty schemes and arbitrary empty base schemes for the general
weakly étale clauses, and affine identity base change. The signature imposes no
characteristic, Noetherian, separatedness, quasi-compactness, or nonemptiness condition;
all such cases covered by the node remain covered.

For the one-definition-per-notion audit I reran the searches in the worker report. `rg`
found `AlgebraicGeometry.WeaklyEtale` and its stability interfaces in Mathlib, and the
upstream `AlgebraicGeometry.proAffineEtale`, `proAffineEtale_Spec_iff`, and
`Algebra.IndEtale`; none states the full conjunction. LeanSearch/LeanFinder returned only
ordinary étale stability and individual weakly étale declarations, while Loogle returned
the individual `WeaklyEtale` interfaces. Searches for `weaklyEtale_stability` and the
blueprint id found no duplicate in Mathlib, upstream, or `lean/Sheaf`. The exact existing
notions therefore remain cited rather than redefined.

The shared repository copy is older than the sandbox's refreshed server node: the sandbox
node adds `def-weil-weakly-etale-morphism` and `def-weil-pbc-ind-etale-algebra` to
`stmt_deps` and records the five detailed proof steps. I found no mismatch between that
authoritative node and the Lean signature, so no Lean or node repair was needed. The only
change in this second reading is this independent verification section.

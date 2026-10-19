## Worker report

Repair of the returned stage-2 packet at immutable head 0a047a23ea62 (H12/H13).
The initial saved-packet dry run passed at ea2b252309; the required semantic
dependency repair below is applied on top of that retained work. This delivery supplies
`Sheaf.AlgebraicGeometry.ProEtaleLocalSystemRepresentability`,
the item's complete Lean record, and this report. The only postponed theorem is
`AlgebraicGeometry.Scheme.proEtale_localSystem_representability`. Its proof is `sorry`.
The supporting `proEtaleUniverseLiftToOver` is an explicit functor, with real object
and arrow maps and completed functor laws; it contains no postponed data.

The node copy starts from the current shared item, rather than the returned
stage-1 version. Its statement, all eight proof steps, and `proof_deps` are
unchanged. In particular step 6 retains transport along the actual isomorphisms
E_{U_i} ≅ D_i and the citation
`lem-weil-pbc-closed-immersion-base-change`. The theorem docstring reproduces
these eight steps, including that correction. No statement correction is made.

Source read: Bhatt--Scholze, *The pro-etale topology for schemes*,
[arXiv:1309.1198](https://arxiv.org/pdf/1309.1198), Definition 7.3.1(1),(3),
Remark 7.3.2 and Lemma 7.3.9, forward inclusion Loc_X into Cov_X.
The node's locally Noetherian specialization is retained. The source PDF was
read online because the local literature directory contains the acquisition
lists but not this PDF.

Every hypothesis and clause is rendered as follows:

| Natural-language clause | Lean rendering |
| --- | --- |
| A scheme X | `(X : Scheme.{u})` |
| X locally Noetherian | `[IsLocallyNoetherian X]` |
| Its actual small pro-etale site | `ProEt.topology X` on `X.ProEt` |
| A sheaf of sets in that site's own universes | `(F : Sheaf (ProEt.topology X) (Type (u + 1)))` |
| A pro-etale covering family of X | `(I : Type (u + 1)) (U : I → X.ProEt)` and `hcover : (ProEt.topology X).CoversTop U` |
| Arbitrary sets S_i | `(S : I → Type (u + 1))` |
| Restriction F to U_i | `(proEtaleSetRestriction X (U i)).obj F`, the recorded canonical composition-of-structure-maps restriction |
| Isomorphic to the sheafified constant presheaf S_i | `htriv : ∀ i, Nonempty (... ≅ (constantSheaf (ProEt.topology (U i).left) (Type (u + 1))).obj (S i))` |
| There exist a scheme Z and a map over X | `∃ (Z : Scheme.{u + 1}) (q : Z ⟶ schemeUniverseLift.{u, u + 1} X), ...` |
| The representing map is etale | `Etale q` |
| Bijections F(U) ≃ Hom_X(U,Z) | `Nonempty (F.obj ≅ (proEtaleUniverseLiftToOver X).op ⋙ yoneda.obj (Over.mk q))` |
| Naturality for every site arrow | The same expression is a presheaf natural isomorphism, not unrelated component bijections; Yoneda restriction is precomposition |
| Every valuation ring and fraction field, bottom map b and compatible generic map a | `ValuativeCriterion q` quantifies over `ValuativeCommSq q`, whose fields are R, the valuation-domain structures, K, its field/fraction-ring structures, and the commuting scheme square |
| Existence of a lift over X extending a | `ValuativeCriterion q` supplies a nonempty `Unique` type of square lifts; `LiftStruct` contains both required triangle equalities |
| Uniqueness of that lift | The same `Unique` asserts uniqueness among all morphisms satisfying those equalities, not just a selected class of lifts |
| No finiteness or nonemptiness of S_i or Z | No such binder or conjunct occurs; nor does any quasi-compactness, properness, finite-type or separatedness hypothesis |

Universe check: `X.ProEt` has objects in `Type (u + 1)` and morphisms in
`Type u`; the sheaf values and local sets are in `Type (u + 1)`. A disjoint union
with an arbitrary `Type (u + 1)` set of sheets can be too large for `Scheme.{u}`.
We therefore use the already landed `def-trf-scheme-universe-enlargement`:
`schemeUniverseLift.{u, u + 1} X` is the same geometric base with enlarged
coordinate rings, canonically constructed as the colimit of its explicitly
ULifted affine diagram. No arbitrary scheme or comparison map is chosen.
The conclusion's Z is in `Scheme.{u + 1}`, enough for a presentation indexed by
the pairs (site object, section), which form a `Type (u + 1)` set.

The helper maps each original U to its canonically enlarged structure map over
the enlarged X, and each arrow to `schemeUniverseLiftMap` on its underlying
scheme map. Hence the value of the Yoneda composite is precisely the set of
maps from enlarged U to Z commuting with the enlarged structure maps. This is
the requested Hom_X(U,Z) in a common ambient universe. The original site is
unchanged. Valuation tests use rings in `Type (u + 1)`, matching the representing
scheme, so they are not made vacuous by quantifying in a smaller universe.

The helper's identity law follows directly from the affine-colimit universal
property: every affine leg composed with the lifted identity is the leg indexed
by the same affine map followed by identity. The identity triangle in the
costructured-arrow category equates that leg with the original leg. Its
composition law is the already recorded `schemeUniverseLiftMap_comp`.
These are the defining laws of this explicit functor, not extra theorem claims
or additional geometric hypotheses.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its `Hom`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`,
  and the existing forgetful/site objects and arrows.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`,
  defined as constant presheaf followed by `presheafToSheaf`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.RingTheory.Valuation.ValuationRing`: `ValuationRing`; the recorded
  `ValuationRing.TFAE` relates it to the fraction-field formulation.
- `Mathlib.AlgebraicGeometry.ValuativeCriterion`: `ValuativeCommSq` and
  `ValuativeCriterion`, encoding exactly full existence and uniqueness.
- `Sheaf.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover`:
  `Scheme.proEtaleSetRestriction`, and the already defined locally constant
  special case of `proEtale_locallyClassical_etaleCover` used in proof step 1.
- `Sheaf.AlgebraicGeometry.SchemeUniverseEnlargement`: `schemeUniverseLift`,
  `schemeUniverseLiftMap`, `schemeUniverseDiagram_hasColimit`, and
  `schemeUniverseLiftMap_comp`; these are reused without another enlargement.

The new definition node `def-a1-proetale-set-restriction` and the landed universe
enlargement node are added to `stmt_deps`. The theorem node
`lem-weil-pbc-proetale-locally-classical-etale-cover` is absent from `stmt_deps`
and remains unchanged in `proof_deps`: only its definition helper occurs in the
signature. The existing module supplies that helper via the new node's
`existing: true` record; no module or declaration is copied. Recorded proof inputs are imported for the classical unit,
constant-set representability, closed-immersion base change, and preservation of
colimits by a left adjoint. The other recorded modules (comparison, sheafification,
scheme coproducts and pullbacks) are in this import closure. The three proof-only
algebraic-space lemmas presently have no Lean records, so there are no modules
for them to import; the eight-step docstring names them explicitly. Their absence
does not prevent stating this theorem from its existing statement dependencies.

Edge cases checked before writing and again on the completed signature:

- X empty: the empty covering family is permitted. The empty scheme represents
  the unique sheaf on the empty site, and no nonempty valuation spectrum maps
  to the empty base.
- S_i empty: the empty constant sheaf and an empty representing component are
  permitted. A valuation lifting assertion with no generic map is vacuous.
- S_i infinite: the disjoint union is etale and has full unique valuation lifts
  even when not quasi-compact or proper. No bound on cardinality within the
  sheaf universe is introduced, including sets not small in universe u.
- Disconnected X: S_i may vary by cover member; no constant rank or connectedness
  assumption is made.
- A field as valuation ring: the generic restriction is an isomorphism, so the
  lift condition remains the expected existence and uniqueness assertion.
- Arbitrary site morphisms: no restriction to cover maps, affine maps or etale
  objects is made in the natural isomorphism.

Searches for an existing statement (all run under Q43 and this item):

- `msearch.py ... leanfinder "Locally constant sheaves of sets on the proetale site
  of a locally Noetherian scheme are represented by etale geometric coverings"`:
  eight hits, concerning condensed locally constant presheaves and etale sites;
  no scheme representability theorem with valuation lifts.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.Etale, LocallyConstant"`:
  zero hits.
- `msearch.py ... grep "geometric.?cover|locally.?constant.*represent|represent.*locally.?constant"
  AlgebraicGeometry`: zero hits in Mathlib.
- `rg` in upstream `WeilConjectures`, in `lean/Sheaf`, and in
  `dag/lean_names_upstream.json` for the item id and the proposed declaration
  names: no matching statement or name collision.
- Searches for scheme universe enlargement found the landed module and node
  `def-trf-scheme-universe-enlargement`. Reading its full declaration and
  docstrings supplied the canonical size transport used here.
- Reading `ProEtaleLocallyClassicalEtaleCover` found the exact existing restriction
  and the predicate whose expansion matches the explicit cover hypotheses.
  The restriction is reused; no second definition of local constancy is introduced.

No disputed mathematical statement or unresolved node fault remains.

## Second reading by Q43

This is the delivering worker's second pass with the current node and final
module open. No separate agent was started, as the dispatch brief forbids it;
the maintainer supplies the independent review.

The scheme and locally Noetherian binders match the first sentence. The site
and value universes match the recorded ProEt interface, including its distinct
object and morphism universes. `I`, `U` and `hcover` give exactly a pro-etale
cover. `S` has unrestricted sets in the sheaf universe. Each `htriv i` uses the
recorded restriction and actual sheafification of the constant presheaf.

The existential Z and q are over the canonical enlargement of the same base,
so the universe required by an arbitrary set of sheets is available. `Etale q`
is the recorded etale property. The full presheaf isomorphism provides every
component bijection and every naturality square. Its Yoneda object is in the
over category, so it gives X-morphisms rather than unbased scheme maps.
The helper was read on both objects and arrows to verify those exact structure
maps and the direction of precomposition.

`ValuativeCriterion q` was expanded against the Mathlib source: the square has
a valuation domain, its fraction field, a generic map to Z and a base map, and
`Unique LiftStruct` contains exactly extension and the condition of being over
the base, with uniqueness among all such lifts. It is the full criterion,
not only its existence part, and does not impose quasi-compactness or properness.

The empty and infinite cases above remain admissible on this second reading.
The only representation adjustment during writing was to use the existing
canonical universe enlargement instead of a size bound on local sets. The
compiler-guided helper repairs only changed its functor-law proofs. The natural
statement and all eight landed proof steps, particularly corrected step 6 and
its base-change citation, are preserved. The Lean record's statement is copied
verbatim from the final theorem signature.

## Repair checklist and validation

- H1: supplies the actual Lean module, a complete `lean` record, the worker
  report, and this clause-by-clause second reading.
- H2/H7: rebases the node copy on the current shared node. The natural statement,
  every proof step and `proof_deps` are preserved, including reviewer
  NT-cc-NN-7fda51070's step-6 transport and base-change fix. Only `lean` and
  the additions of the new restriction definition node and the landed universe
  enlargement definition node change.
- H8: the module and both declarations carry the source and blueprint id. The
  theorem docstring contains all eight proof steps.
- H3: both local triviality and the complete natural-representability and
  valuation-lifting conclusions are present with no finiteness, quasi-compactness
  or properness hypotheses.
- Per-file compilation and delivery dry run are performed through the prescribed
  `scompile.py` and `deliver2.py` wrappers; no library build or direct Git operation
  is used.
- Clean `scompile.py` result: sandbox check 10.3 seconds, named library-module
  check 9.1 seconds, exit code 0, no warnings. There is exactly one `sorry`,
  the whole proof of the named item theorem. All Lean lines are at most 100
  characters. A field comparison confirms that only `lean` and `stmt_deps`
  differ from the current item, and the signature record is verbatim.

## New nodes

`def-a1-proetale-set-restriction` records the exact existing definition
`AlgebraicGeometry.Scheme.proEtaleSetRestriction` in
`Sheaf.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover`, lines 40-46.
Its `existing: true` record identifies that published module as the definition's
source, using the explicit exception in brief-stage2 §5: no additional module,
wrapper or copied definition is written. The theorem in that same module is
used only by the proof. The optional packaging of the three classicality
predicates is unnecessary for this item's signature and is left with their
current theorem-node record.

The source is BS §4, Definition 4.1.1 and Lemma 4.1.6, together with the
restriction notation in Lemma 5.1.4. The source PDF and the full published
module returned by `scompile.py --source` were read. For an arbitrary scheme
`X : Scheme.{u}` and arbitrary object `U : X.ProEt`, its domain and codomain
are exactly the two set-sheaf categories in `Type (u + 1)`. The explicit
`MorphismProperty.Over.map` composes structure maps with `U.hom`.
`Functor.sheafPushforwardContinuous` precomposes objects and morphisms with
that functor's opposite; its continuity argument is
`ProEt.isContinuous_overMap U.prop`. Thus every object, restriction arrow
and sheaf-morphism clause in the new node is supplied by real existing data.
There is no assumption that U covers X or that X is locally Noetherian.
Empty U, empty X, disconnected objects and infinite section sets are allowed.

New searches, recorded verbatim by msearch.py on 2026-10-18:

- LeanSearch: "Restriction of sheaves of sets on a small proetale site to the
  small proetale site of a weakly etale object by composing structure maps".
  Eight hits, including `Sheaf.ΓRes`, open restriction and `smallEtaleTopology`;
  no specialized small-pro-etale set-sheaf restriction.
- LeanFinder: "Restrict set valued sheaves on a scheme proetale site to a weakly
  etale object by precomposition with the structure map composition functor".
  Eight hits on scheme open restrictions, etale forgetful functors and module
  restrictions; none is this set-sheaf construction.
- Mathlib grep: `proEtaleSetRestriction|sheafPushforwardContinuous|isContinuous_overMap`
  in AlgebraicGeometry. Six hits on other continuous pushforwards; no exact
  restriction declaration.
- Direct rg of DAG nodes, upstream WeilConjectures and `lean/Sheaf` for the
  exact restriction and predicate names finds the existing helper at the module
  above, its theorem-node declaration list and proof consumers; no definition
  node states this restriction. `blueprint_refs.py search 'pro-etale restriction'`
  returns zero blueprint nodes. The new node reuses the exact found declaration.

## H12/H13 repair second reading by Q43

Compared the retained packet with the current shared item: only `lean` and
`stmt_deps` differ. The restriction theorem node is now removed from statement
dependencies and is still a proof dependency, exactly as requested. Its
conclusion is nowhere in the item signature. The new definition node is cited
instead and has a verbatim signature from the existing declaration; its
`stmt_deps` are precisely the scheme and small-site definition nodes cited in
its statement. The ancestor is `lem-a1-affine-hc0`, confirmed by
`blueprint_refs.py ancestor`; its via chain begins with this item.

The item's Lean file, natural-language statement, all eight proof steps,
`proof_deps`, and theorem signature are unchanged from the reviewed packet.
In particular the existing clause-by-clause reading and all edge-case checks
above still apply. No mathematical statement correction or dependency-module
repair is introduced. No additional sorry or duplicate declaration is added.
The prescribed per-file compile and final delivery dry run are rerun below.

Repair validation: `scompile.py Q43 lem-a1-proetale-local-system-representability`
passed cleanly for the retained theorem module (sandbox 11.5 s, named module
14.9 s; exit 0). The explicit self-check confirms the field boundary, unchanged
proof dependencies, verbatim theorem signature, exactly one sorry, line width,
and the new node's existing-definition record without a delivered source copy.

The repaired-packet dry run compiled both the theorem and the existing-binding
probe, then reported a single metadata fault: the local item copy omits the
server blueprint via chain. The new definition node now records the full chain
required by preflight: this item, normal-locally-constant-finite-section,
normal-proetale-monodromy, smooth-lisse-integral-lattice, and
degree-zero-compact-support-sections (all with their lem-a1 prefixes). No Lean
change was needed. The dry run is repeated after this concrete repair.

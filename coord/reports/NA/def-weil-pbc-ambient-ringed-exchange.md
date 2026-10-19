## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleAmbientRingedExchange` defines
`AlgebraicGeometry.Scheme.proEtaleAmbientRingedExchange` and its helper
`proEtaleCanonicalDerivedPullbackComparison`. Definitions have real data; no theorem
or new `sorry` is added. The node's statement, dependencies and other fields are
unchanged; only its `lean` record is updated.

Each hypothesis and clause is rendered as follows:

- The four schemes and arrows are the explicitly bound `X'`, `X`, `Y'`, `Y` and
  `g'`, `f'`, `f`, `g`. The chosen cartesian square is
  `sq : ChosenCartesianSquare g' f' f g`. Only `sq.toCommSq.w` is used in the body,
  as the source specifies.
- The four coefficient sheaves are `R_X`, `R_Y`, `R_X'`, `R_Y'`, sheaves of
  commutative rings on their respective `ProEt.topology`. This is the identified
  commutative coefficient setting of the recorded derived operations.
- The four inverse-image identifications are the isomorphisms `c_f`, `c_g`,
  `c_g'`, `c_f'`. Their endpoints use the recorded `proEtaleSheafInverseImage`.
- Agreement of the two composite coefficient identifications is `hcoeff`, a
  heterogeneous equality of `proEtaleRingCompositeCoefficients`. Their endpoint
  scheme arrows differ before using commutativity, so `HEq` is required. The
  sigma equality `hPQ` combines scheme commutativity with coefficient compatibility.
  Applying the actual derived-pullback functor construction to that equality gives
  the transport `eqToIso hfun`.
- The helper selects the canonical composition isomorphism from
  `proEtaleRingDerivedPullbackComposition`. The local existence statement `hex`
  puts the derived comparison first and retains the dependency's entire
  characterization as its predicate: normalized ordinary adjunctions, the
  sectionwise direct-image comparison, its adjunction conjugate, its degreewise
  complex comparison, and the K-flat representative equation. `hex.choose`
  therefore chooses the characterized comparison. The units fix the adjunctions,
  sections fix the direct-image comparison, conjugation fixes the ordinary
  pullback comparison, and K-flat resolutions determine the derived comparison.
- `theta_left` is the inverse composition comparison for `f', g`;
  `theta_right` is the composition comparison for `g', f`. Their transported
  composite `alpha` is exactly the node's `theta_square`.
- `adj_f` and `adj_f'` are the recorded normalized derived adjunctions.
  `(mateEquiv adj_f adj_f' (TwoSquare.mk _ _ _ _ alpha)).natTrans` defines
  `Lg^* Rf_* -> Rf'_* Lg'^*`. Lean writes composition in application order:
  the domain is `proEtaleRingDerivedDirectImage f ...` followed by
  `proEtaleRingDerivedPullback g ...`, and the codomain is pullback along `g'`
  followed by direct image along `f'`.
- Mathlib's mate definition inserts the `f'` unit, applies the comparison, then
  applies the `f` counit. Its `mateEquiv_counit` signature is precisely the
  transpose characterization in the node. No completeness, constructibility,
  boundedness, properness, or finiteness condition is imposed.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`:
  `AlgebraicGeometry.ChosenCartesianSquare`, including the chosen pullback
  isomorphism and its two projection equations.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`; the underlying site is
  Mathlib's `Scheme.ProEt` with `ProEt.topology`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `proEtaleSheafInverseImage`, `proEtaleSheafAdjunction`, and the model-site
  module constructions used by the operations dependency.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage`, the current
  recorded operations module, publicly reexports
  `ProEtaleOperationsCanonicalAdjunction` and `ProEtaleOperations`:
  `proEtaleRingModules`, `proEtaleRingDerivedPullback`,
  `proEtaleRingDerivedDirectImage`, and `proEtaleRingDerivedAdjunction`.
  The general identified-coefficient operations are used, without specializing
  this definition to constant coefficients.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackComposition`:
  `proEtaleRingCompositeCoefficients` and
  `proEtaleRingDerivedPullbackComposition`. The current source was also read via
  `scompile.py --source` to confirm the entire normalized witness signature.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `CategoryTheory.mateEquiv`.
  The Mathlib leaf's full signature, definition and transpose lemma were read.

The mathematical source was checked directly at
[Stacks 07A7](https://stacks.math.columbia.edu/tag/07A7): for a commutative square
of ringed topoi, the exchange map is the adjunct of the pullback comparison
followed by pullback of the counit. The composition comparison is the one computed
on K-flat complexes with flat terms in
[Stacks 0D6D](https://stacks.math.columbia.edu/tag/0D6D). The local blueprint and
Stacks text files named by the node are absent in this read-only checkout; the
node's full blueprint statement and these primary online sources were read.

Edge cases: arbitrary scheme morphisms include identities and empty schemes.
The zero coefficient ring sheaf and zero derived objects are allowed. There is
no characteristic or nonemptiness hypothesis and no indexing set in the notion.
The small pro-etale site's object universe is `u+1`, its morphism universe is `u`,
and coefficient rings live in `u+1`, exactly as the recorded interfaces require;
no equality of object and morphism universes is imposed.

Searches repeated with the prescribed wrapper:

- LeanFinder: "canonical ambient ringed pro-etale exchange transformation mate
  derived pullback composition" returned eight generic/underived pullback,
  adjunction-conjugacy and scheme morphism candidates, including
  `SheafOfModules.pullbackComp`; none defines this pro-etale derived exchange.
- Loogle: `"mateEquiv"` returned twelve declarations, including the generic mate
  equivalence and transpose identities. The exact generic notion is reused.
- Mathlib grep: `mateEquiv|proEtaleAmbientRingedExchange|BeckChevalley` in
  `CategoryTheory` returned generic mates and their uses, no ambient exchange.
- `rg` in `WeilConjectures` and `lean/Sheaf` for `ambientRingedExchange`,
  `proEtaleAmbientRingedExchange`, `CanonicalDerivedPullbackComparison`, and
  `BeckChevalley` found no existing declaration. Searching the upstream source
  for the node id also found none. Earlier search output is retained in
  `searches.jsonl` and confirms the same conclusion.

Repair of the earlier sandbox attempt: removed the selector's conversion to an
existential with property `True`, which discarded its canonical normalization.
The replacement selects from the full characterization with the derived
comparison quantified first. Direct nested `choose_spec` projections exceeded
60 seconds; repackaging the same existential predicates compiles within the
original time limit. Removed unused coefficient-universe imports and dummy proof bindings;
imported the currently recorded operations module. The previous report described
an obsolete arbitrary `theta` parameter; this report describes the actual file.
The historical second reading is saved in `scratchpad/previous-report.md`; a
fresh second reader must read this repaired file before delivery. No independent
second reading is claimed here.

Validation: `scompile.py` compiled the module as a sandbox file and at its library
path. The final `deliver2.py NA def-weil-pbc-ambient-ringed-exchange --no-push`
dry run reported OK: compilation and preflight passed except for the independent
second reading, which the second reader writes. The module contains zero `sorry`
occurrences. No node field other than `lean` changed, and the recorded signature
is verbatim from `def` to the definition body. Nothing is pushed by this worker.


## Earlier second reading (a previous round; superseded)

Independent second reading of the repaired module, with the item node and all six
statement-dependency nodes open. No mathematical mismatch remains in this version;
no Lean declaration, node statement, dependency list, or definition body was changed.
This section adds the independent clause audit and checks the earlier worker's
canonical-choice repair, rather than relying on the historical second reading.

Source check: the referenced blueprint markdown and the local Stacks checkout are
absent on this machine. I read the primary Stacks TeX online:
[sites-cohomology.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/sites-cohomology.tex),
labels `remark-base-change` (07A7) and `lemma-derived-pullback-composition` (0D6D),
including the preceding derived-pullback setup. Remark 07A7 defines the map on
unbounded derived categories as the adjoint of the square comparison followed by
pullback of the counit. It assumes a commutative diagram of ringed topoi, without
properness, boundedness, completeness, constructibility or finiteness. The item's
chosen cartesian scheme square and inverse-image coefficient isomorphisms are the
specified specialization. I also read the ringed-site and ringed-topos definitions
in `sites-modules.tex` and the
[Stacks algebra conventions](https://raw.githubusercontent.com/stacks/stacks-project/master/conventions.tex).
There, rings are commutative with identity, including the zero ring. Accordingly
`CommRingCat` is the source's ring notion, not an extra hypothesis; both the
operations and composition dependency nodes explicitly use commutative rings.

The node's objects, hypotheses and defining clauses, matched individually:

1. Four schemes `X'`, `X`, `Y'`, `Y` and arrows `g'`, `f'`, `f`, `g` in the
   displayed square: exactly the explicit scheme and arrow binders, with the
   indicated domains and codomains. PASS.
2. A chosen cartesian identification with the fibre product: the binder
   `sq : ChosenCartesianSquare g' f' f g`. I opened its declaration: it extends
   `CommSq` and carries `isoPullback`, `hom_fst` and `hom_snd`. Only
   `sq.toCommSq.w` enters this definition, as the node specifies. PASS.
3. Four coefficient ring sheaves on the four small pro-etale sites:
   `R_X`, `R_Y`, `R_X'`, `R_Y' : Sheaf (ProEt.topology ...) CommRingCat.{u + 1}`.
   The site is Mathlib's `Scheme.ProEt`, the weakly etale over-category with its
   fpqc topology, not the etale site or a constant-coefficient category. PASS.
4. The four inverse-image identifications: binders `c_f`, `c_g`, `c_g'`, `c_f'`
   use the recorded `proEtaleSheafInverseImage` on exactly their respective
   coefficient sheaves and arrows. I opened its signature and body: it is the
   canonical sheafified inverse image along `proEtaleBaseChange`, with the
   recorded sheaf adjunction. PASS.
5. The two composite coefficient identifications agree after scheme
   commutativity: `hcoeff` is `HEq` of the two
   `proEtaleRingCompositeCoefficients`. I opened that construction and its
   `proEtaleRingInverseImageComp`: it composes the inverse-image composition
   comparison, inverse image of the first identification, and the second
   identification. The comparison is the adjunction conjugate of fibre-product
   pasting. `Sigma.ext sq.toCommSq.w.symm` with `hcoeff.symm` gives `hPQ`;
   `congrArg F hPQ` transports the actual derived pullback and its coefficient
   data together. This is exactly compatibility over the equal composite arrows,
   not literal equality between objects of unrelated types. PASS.
6. Ordinary uncompleted unbounded derived module operations on each edge:
   `proEtaleRingDerivedPullback` and `proEtaleRingDerivedDirectImage`. I read the
   operations module publicly reexported by the recorded
   `ProEtaleConstantDerivedDirectImage` module. Its `proEtaleRingModules` is
   sheaves of modules over the given ring sheaf; pullback is the inverse-image
   module followed by sheafified scalar extension along `c`; direct image is
   sectionwise with action through the adjoint coefficient map. The derived
   constructions are exact termwise descent and the K-injective right derived
   functor on all modules. The constant-coefficient primary declaration is not
   substituted for the general operations. PASS.
7. Their canonical adjunctions, including the counit for `f` and unit for `f'`:
   `adj_f` and `adj_f'` are `proEtaleRingDerivedAdjunction`. I opened its actual
   definition in `ProEtaleOperationsCanonicalAdjunction`: it is induced from
   `proEtaleRingModuleAdjunction`, selected by its unique tensor-unit transpose
   normalization, not from bare existence of an arbitrary adjunction. PASS.
8. Canonical composition isomorphisms `c_{h,k}` with the 0D6D representative
   characterization: `proEtaleCanonicalDerivedPullbackComparison`. I read the
   full current `proEtaleRingDerivedPullbackComposition` declaration, including
   through `scompile.py --source`. The helper's `hex` moves only the derived
   comparison witness to the front of the existential; it retains all three
   normalized ordinary adjunctions, the section formula for `d`, conjugation
   determining `a`, the degreewise formula for `b`, and the K-flat factorization
   equation for `c`. The `rcases`/tuple reconstruction does not discard any
   predicate. Thus `hex.choose` chooses a characterized comparison. Sectionwise
   unit normalization determines the adjunctions, sections determine `d`, the
   conjugate equivalence determines `a`, degrees determine `b`, and K-flat
   resolutions with flat terms determine `c` on every derived object. This is
   the allowed choice of uniquely determined data, not a hollow definition. PASS.
9. The first inverse composition comparison, equality of composite pullbacks,
   and second forward composition comparison defining `theta_square`:
   `theta_left` is the comparison for `f', g` inverted; `eqToIso hfun` is the
   dependent transport; `theta_right` is the comparison for `g', f` forward.
   `alpha = theta_left'.hom ≫ theta_right.hom` has exactly type
   `Lg^* ⋙ Lf'^* ⟶ Lf^* ⋙ Lg'^*` in Lean's application order. PASS.
10. The natural transformation `Lg^* Rf_* -> Rf'_* Lg'^*`, on
    `D(X_proet,R_X) -> D(Y'_proet,R_Y')`: the result type is
    `proEtaleRingDerivedDirectImage f ... ⋙ proEtaleRingDerivedPullback g ... ⟶
     proEtaleRingDerivedPullback g' ... ⋙ proEtaleRingDerivedDirectImage f' ...`.
    The derived categories at each endpoint are those of item 6. PASS.
11. The transformation is the mate for `G = Lg^*`, `H = Lg'^*` under the two
    adjunctions: the body returns
    `(mateEquiv adj_f adj_f' (TwoSquare.mk _ _ _ _ alpha)).natTrans`.
    I opened Mathlib's `mateEquiv` definition and `mateEquiv_counit`, not merely
    the declaration name. The latter says that its transpose is `alpha` at
    `Rf_*K` followed by `Lg'^*` of the `f` counit. PASS.
12. The explicit unit/comparison/counit formula, before completeness and
    constructibility: Mathlib's `mateEquiv.toFun` first inserts `adj_f'.unit`,
    then applies `alpha` under the direct image, then contracts `adj_f.counit`.
    Its associators and unitors express exactly the displayed composite.
    The signature has no other hypothesis and the categories have no such
    restrictions. PASS.

Edge cases: identity arrows and identity squares are included; the comparison
is fixed by its canonical normalization even in these cases. Empty schemes,
the zero ring sheaf and zero complexes/derived objects are allowed. There is no
index set or degree parameter to exclude an empty family or degree zero; the
representative predicate ranges over all `n : ℤ`, including zero and negative
degrees. No characteristic, nontriviality, nonemptiness, properness, flatness of
a scheme arrow, or boundedness instance is present. `u` is bound explicitly;
`Scheme.{u}` gives site object universe `u+1` and morphism universe `u`, and
coefficients and module values live in `u+1`. I read the model-site construction:
it enlarges Hom size internally and transports back, so the statement does not
identify the two site universes. All variables in the delivered file are bound;
`set_option autoImplicit false` also checks this mechanically.

Independent duplicate searches, with words different from the original searches:

- LeanFinder through `msearch.py`: `derived base change natural transformation
  ringed topoi pullback pushforward exchange` and `sheaf of rings on pro etale
  site derived pullback direct image base change mate`. Both returned ordinary
  module pullback/adjunction/composition declarations, not this derived exchange.
- Loogle through `msearch.py`, `"mateEquiv"`: twelve generic mate declarations.
  The exact generic notion is reused rather than redefined.
- Grep through `msearch.py`, `baseChange|BeckChevalley|mateEquiv`, and direct
  `rg` searches in Mathlib CategoryTheory and module sheaves, upstream
  `WeilConjectures`, the side framework, and project `lean/Sheaf` for
  `Beck.?Chevalley`, `exchange.*transformation`, `derived.*baseChangeMap` and
  declarations containing `BaseChange`/`Exchange`. I opened the closest actual
  declarations: `ProEtale.derivedBaseChangeMap` in
  `SixFunctors/ProEtale/Derived/UpperLowerStar.lean` uses one fixed abelian value
  category and sheaves valued in it; it does not encode modules over four
  varying coefficient sheaves. `ProEtale.baseChangeMap` in
  `BaseChange/WeaklyEtale.lean` is underived and requires weakly etale arrows.
  The current side framework's `CondensedRing.boundedConstructibleBaseChange`
  in `ModuleObject/BaseChangeTheorems/MorphismDefs.lean` restricts to bounded
  constructible modules with coefficient ring pulled from a condensed ring,
  over finite-type field schemes. I read `coord/pefw-upstream-framework.md`
  and this exact side source. None is this node's arbitrary identified-ring
  uncompleted exchange. The scheme-module base-change maps use the structure
  sheaf on the Zariski site. Mathlib's underived `SheafOfModules.pullbackComp`
  is already used through the dependency interfaces and is not this definition.
- DAG search found this notion's owning node and its citers, with no alternative
  recorded declaration giving the same interface. No existing exact match was
  found, and no new notion or dependency module is needed.

H5/H6/H8/H9 check: both declarations are definitions with concrete bodies; there
is no `sorry`, theorem, axiom or private copy in this delivery. The helper's
structural rearrangement of existential witnesses is part of its definition.
Both declaration docstrings name their source and the owning blueprint node;
the item is a definition node with an empty proof list, so there are no omitted
proof steps. Both explicit imports and the recorded dependency modules were
read. No file-local notation, local instance, private declaration or line over
100 characters occurs. The node's `lean.statement` was checked verbatim against
the primary declaration's signature; every node field other than `lean` agrees
with the repository node. There is no `statement_change`, new node or delivered
dependency module requiring a further audit.

Changes from this independent reading: report only; the repaired Lean and node
record already match the source and were left intact. Compilation and delivery
preflight results are recorded below after running the required wrappers.


Second-reader validation: the prescribed `scompile.py` completed successfully,
compiling the composition dependency overlay (7.3 s), the sandbox copy (18.7 s),
and the delivered library path (19.2 s), with no errors or warnings. The mechanical
signature, unchanged-node-fields, line-width and zero-sorry checks also passed.

Historical delivery tool failure (previous attempt): `deliver2.py NA def-weil-pbc-ambient-ringed-exchange --no-push`
failed at its branch checkout, before preflight, with:

```text
fatal: 'deliver/NA/def-weil-pbc-ambient-ringed-exchange' is already used by worktree at '/home/ubuntu/worktrees/weil-newtargets-qkbazimx'
```

No delivery was pushed. The sandbox is fully reviewed and compiled. Direct Git
cleanup, edits outside the sandbox, and workarounds of a refusing project tool
are outside the second reader's authorization; the launcher must repair its
worktree bookkeeping before the prescribed dry run and delivery can succeed.


## Retry review

The retry worker read the existing repaired module, item and all six statement
nodes, the current recorded dependency sources, the stage brief and H rules.
The live composition source was confirmed again with `scompile.py --source
Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackComposition`. The complete
normalized witness predicate in the helper agrees with that source; no data
is selected from bare uncharacterized existence. The actual square comparison
and mate match Stacks 07A7 and 0D6D, which were reopened online. The previous
independent second reading remains applicable: no Lean code or mathematical
node field changed during this retry.

The prescribed searches were repeated: LeanFinder query "ambient ringed
pro-etale exchange as mate of canonical derived pullback composition" returned
eight generic ordinary pullback/adjunction candidates; Loogle query `"mateEquiv"`
returned twelve generic mate declarations; Mathlib grep
`mateEquiv|proEtaleAmbientRingedExchange|BeckChevalley` in `CategoryTheory`
returned twenty generic mate declarations and uses. Direct `rg` searches of
upstream `WeilConjectures` and project `lean/Sheaf` for the two delivered names
and `ambientRingedExchange`, and of upstream for the node id, returned no matches.
No exact existing ambient identified-ring derived exchange was found.

Mechanical checks repeated: zero `sorry` occurrences, no line over 100
characters, explicit universe and variable binding, verbatim primary signature,
and exactly `lean` changed in the node copy. The UTC date remains 2026-10-15.
The earlier branch/worktree checkout failure is historical; the prescribed
wrapper now includes its own worktree handling, and is being rerun without any
direct Git command, tool edit, or edit outside this sandbox. Nothing is pushed.


Retry validation: `deliver2.py NA def-weil-pbc-ambient-ringed-exchange --no-push`
reported `OK (dry run): commit b572a83ee9 passes the preflight and compiles;
nothing pushed`. The only staged files were this item's report, node and Lean
module. The historical worktree checkout failure is resolved by the prescribed
wrapper. No direct Git cleanup or tool change was needed.

## Second reading by NA

Fresh independent reading on 2026-10-16. I opened the item node, the actual
sandbox module, all six statement-dependency nodes, and their declarations.
The existing repaired Lean matches the node; this reading changes the report
only. No mathematical statement, signature, dependency, or definition is changed.

Source: the blueprint file and local Stacks TeX are absent in this checkout.
I read the primary
[Stacks TeX](https://raw.githubusercontent.com/stacks/stacks-project/master/sites-cohomology.tex),
including `section-derived-pullback`, `lemma-derived-pullback-composition` (0D6D),
and `remark-base-change` (07A7), as well as the rendered
[07A7](https://stacks.math.columbia.edu/tag/07A7) and
[0D6D](https://stacks.math.columbia.edu/tag/0D6D).
The source assumes a commutative diagram of ringed topoi and uses unbounded
derived categories. It imposes no properness, completeness, constructibility,
flatness of the scheme maps, boundedness, or nonemptiness hypothesis. The
node specializes this to the stated chosen cartesian scheme square and
identified commutative coefficient sheaves, using only square commutativity.

Clause-by-clause list of the node, with its Lean rendering and verdict:

1. Four schemes and the four arrows with the displayed domains: the binders
   `{X' X Y' Y : Scheme.{u}}` and `{g', f', f, g}`. PASS.
2. The chosen cartesian identification: `sq : ChosenCartesianSquare g' f' f g`.
   I read its structure: it extends `CommSq` and includes `isoPullback` and
   both projection equations. Only `sq.toCommSq.w` is used here. PASS.
3. One ring sheaf on each small pro-etale site: `R_X`, `R_Y`, `R_X'`, `R_Y'`
   are `Sheaf (ProEt.topology T) CommRingCat.{u + 1}`. I read the site node
   and Mathlib's `Scheme.ProEt`/`ProEt.topology`: weakly etale objects with
   the fpqc topology. These are varying coefficient sheaves, not constants.
   The commutative coefficients agree with the operations and composition
   dependency nodes and the source convention. PASS.
4. Four inverse-image identifications: `c_f`, `c_g`, `c_g'`, `c_f'` use
   the recorded `proEtaleSheafInverseImage` for the corresponding arrows.
   Its body is canonical sheafified inverse image along `proEtaleBaseChange`;
   `proEtaleSheafAdjunction` supplies its adjunction. PASS.
5. Compatibility of the two composite identifications: `hcoeff` is the `HEq`
   of `proEtaleRingCompositeCoefficients g' f ...` and
   `proEtaleRingCompositeCoefficients f' g ...`. The dependency's construction
   composes its inverse-image composition isomorphism with inverse image of
   the first coefficient identification and then the second one. `Sigma.ext`
   uses `sq.toCommSq.w.symm` and `hcoeff.symm` to identify the arrow and its
   dependent coefficient data together. This imposes exactly compatibility
   after the composite arrows are identified. PASS.
6. Ordinary uncompleted unbounded operations: the recorded operations module
   `ProEtaleConstantDerivedDirectImage` publicly reexports the general
   `ProEtaleOperationsCanonicalAdjunction` and `ProEtaleOperations`.
   I read their signatures and bodies: `proEtaleRingModules` is all module
   sheaves over the supplied ring; module pullback uses inverse image and
   sheafified extension along `c`; direct image uses the adjoint ring map.
   `proEtaleRingDerivedPullback` is exact termwise descent and
   `proEtaleRingDerivedDirectImage` is the K-injective right derived functor.
   The constant-coefficient declaration is not substituted for these. PASS.
7. The canonical adjunctions and their unit/counit: `adj_f` and `adj_f'`
   are `proEtaleRingDerivedAdjunction`, induced from the uniquely normalized
   tensor-unit module adjunction, not bare arbitrary adjunction existence.
   I read the defining `existsUnique` characterization and derived body. PASS.
8. Canonical composition comparison: the helper
   `proEtaleCanonicalDerivedPullbackComparison` selects `hex.choose` from
   a reordering of the complete dependency theorem. I read that theorem
   locally and confirmed the current interface via `scompile.py --source`.
   The tuple reconstruction preserves the three section-normalized module
   adjunctions, the section formula for `d`, the conjugation equation for `a`,
   the degreewise formula for `b`, and the K-flat factorization equation for
   the selected `c`. Nothing is replaced by `True` or by bare isomorphism
   existence. These conditions determine `c`: the earlier witnesses are
   determined by their formulas and every derived object has a K-flat
   representative with flat terms. This is permitted canonical choice. PASS.
9. The square isomorphism: `theta_left` is `c_{f',g}` inverted; `eqToIso hfun`
   transports the composite pullback with its coefficients; `theta_right`
   is `c_{g',f}` forward. Thus `alpha` has exactly the node's direction
   `Lf'^* Lg^* -> Lg'^* Lf^*`, with Lean's left-to-right functor composition.
   No extra comparison is passed as a hypothesis. PASS.
10. The exchange natural transformation and its endpoints: the result type is
    `proEtaleRingDerivedDirectImage f ... ⋙ proEtaleRingDerivedPullback g ... ⟶
     proEtaleRingDerivedPullback g' ... ⋙ proEtaleRingDerivedDirectImage f' ...`,
    hence `D(X_proet,R_X) -> D(Y'_proet,R_Y')` as required. PASS.
11. It is the mate for `G = Lg^*`, `H = Lg'^*`: the return expression is
    `(mateEquiv adj_f adj_f' (TwoSquare.mk _ _ _ _ alpha)).natTrans`.
    I read Mathlib's `mateEquiv` body and `mateEquiv_counit`. The former
    inserts the `f'` unit, applies the square transformation, and contracts
    the `f` counit; the latter gives exactly the specified transpose. Both
    the explicit component formula and its transpose are therefore present
    through the reused mate definition. PASS.
12. Before completeness and constructibility: no restriction is imposed on
    the module categories or derived objects and no such hypotheses occur.
    The quantifiers introduce the schemes, square, coefficient sheaves,
    identifications, and their compatibility in that order. PASS.

Edge cases: empty schemes, identity arrows and identity squares, the zero ring
sheaf, and zero derived objects are allowed. There is no index set; no integer
or natural-number parameter restricts degree zero. The representative predicate
ranges over all integers. There is no characteristic or nontriviality assumption.
The single universe `u` is explicit; the site has object universe `u+1` and
morphism universe `u`. Ring and module values live in `u+1`, following the
recorded size convention. The model-site construction enlarges Hom size
internally and transports back; no equality between site universes is assumed.
Every variable is bound; `autoImplicit false` is also enabled.

Independent searches during this reading:

- `msearch.py ... leanfinder 'Beck Chevalley transformation on unbounded derived
  categories of ringed topoi'`: eight results, mostly exact derived-functor
  factorization declarations and ordinary module adjunctions; no exact match.
- `msearch.py ... loogle '"mateEquiv"'`: twelve generic mates declarations.
  The exact generic mate is reused, not duplicated.
- `msearch.py ... grep 'mateEquiv|BeckChevalley|ambientRingedExchange'`:
  twenty generic mate declarations and uses. Direct `rg` on upstream
  `WeilConjectures`, Mathlib CategoryTheory/module sheaves, and project
  `lean/Sheaf` with `derivedBaseChangeMap`, `Beck.?Chevalley`, and
  `exchange.*transformation`, and both delivered names, found no exact match.
  I opened upstream `ProEtale.derivedBaseChangeMap`: it uses a single fixed
  abelian value category, not modules over four varying ring sheaves.
  I read `coord/pefw-upstream-framework.md` and the exact side-framework
  `CondensedRing.boundedConstructibleBaseChange` in `MorphismDefs.lean`:
  it uses condensed coefficients on bounded constructible module objects
  over finite-type field schemes. Neither gives this arbitrary identified-ring
  ambient exchange. The existing ordinary module composition and generic mate
  constructions are already reused by the dependencies.

No new node, dependency module, or statement correction occurs, so H12/H13 and
the correction/citer audit have no additional delivery files to inspect.
Both declarations have concrete bodies and source/blueprint docstrings. There
is no `sorry`, theorem, axiom, private declaration, local instance, or local
notation in the delivered file. The helper's tuple reordering is definitional
bookkeeping, not a new proved mathematical statement. This definition node has
an empty proof list. The module imports the recorded dependency modules.
Mechanical checks confirm the primary `lean.statement` is verbatim from its
signature, only the node's `lean` field changed, and every Lean line has at
most 100 characters. No mismatch requiring a code change was found.

Fresh second-reader compilation: the prescribed `scompile.py NA
 def-weil-pbc-ambient-ringed-exchange <module>` succeeded for both the sandbox
(28.8 s) and the library path (31.9 s), with no errors or warnings, under the
unchanged 60-second limit. The sandbox contains one delivered Lean module.

Fresh second-reader dry run: `deliver2.py NA
 def-weil-pbc-ambient-ringed-exchange --no-push` reported
`OK (dry run): commit f3197d6e63 passes the preflight and compiles; nothing pushed`.
The staged set was exactly this item's module, node, and report. The temporary
wait was normal serialization behind another NA delivery, not a tool failure.

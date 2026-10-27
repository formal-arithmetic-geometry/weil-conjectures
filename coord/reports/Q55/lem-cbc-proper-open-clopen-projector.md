## Worker report

The module `Sheaf.AlgebraicGeometry.ProperOpenClopenProjector` jointly states
`lem-cbc-proper-open-clopen-projector` in fourteen declarations. Every theorem has
exactly `by sorry`; every definition is a concrete canonical categorical word.
The item statement is unchanged. The returned H2 dependency-ownership defect is repaired by the definition node described below.

Hypotheses and clauses, with namespace `AlgebraicGeometry.ProEtale.StrictTower`:

- The arbitrary commutative coefficient ring is `B : Type (u + 1)` with `[CommRing B]`.
  There is no finiteness, torsion, flatness, or boundedness assumption. `Modules B X`,
  `Towers B X = ℕᵒᵖ ⥤ Modules B X`, and `Derived B X` are the dependency's existing
  constant-ring module sheaves, strict towers, and ordinary unbounded localization.
  Index `n` represents positive level `n+1`. No category of towers of derived objects
  is substituted. The original site object/morphism universes are retained.
- The four schemes and maps are explicit binders in `properOpen_clopen_geometry`
  and `properOpen_clopen_projector`. `[IsOpenImmersion k]`, `[IsOpenImmersion i]`,
  `[QuasiCompact k]`, `[QuasiCompact i]`, `[IsProper r]`, `[IsProper p]`, and
  `h : k ≫ p = r ≫ i` render every square hypothesis. No cartesian or identity-left
  hypothesis is imposed on the general assertions.
- `pullback p i` is W_S; `pullback.fst p i` is b and `pullback.snd p i` is q.
  The existing `squareLift k r p i h` is s. `properOpen_clopen_geometry` states
  its open and closed immersion properties, `s ≫ b = k`, `s ≫ q = r`, and existence
  of an open `c : C ⟶ W_S` with range exactly the complement of the range of s.
- `clopen_section_decomposition` says that the actual pair of restrictions along
  `Scheme.ProEt.clopenTestInclusion s H` and the corresponding map for c is
  bijective. These are the sections on H times_X U and H times_X C, viewed on X
  by composition; thus the objects and restriction maps are specified. All scalar
  actions are the inherited ones in `F.val`, and the maps are already semilinear
  presheaf restriction maps. Their naturality follows from that existing API.
- `clopenModuleAdj` is the existing ordinary direct-image adjunction specialized
  to `coefficients B X`, `coefficients B U`, and `constantRingIso B s`.
  `clopenModule_openUnit_isIso` names the invertibility proof needed to define
  `clopenModuleToDirect`, the direct-image transpose of the inverse open unit.
  `clopenModuleToDirect_isIso` states precisely invertibility for clopen s.
- `clopenModulePi` is the actual right-adjunction unit followed by the inverse of
  that canonical transpose. `clopenModule_section_projector` identifies its target
  sections additively with F(H_U) and its section map with first-factor restriction.
  It also states the full natural-transformation equation t pi = eta, the identity
  on U expressed using the open unit, zero on C with zero target, and uniqueness
  among natural transformations with those two restrictions. No arbitrary map or
  non-unique choice is used in the definitions.
- `clopenTowerPi` is ordinary functor-category whiskering of that map.
  `clopenTower_section_projector` states the corresponding unit and zero-target
  equations on actual towers and on arbitrary unbounded cochain complexes.
- `clopenDerived_section_projector` states the representative equation comparing
  the existing `pi B s` on `DerivedCategory.Q.obj K` to Q of the termwise complex
  map, through the exact functors' specified `mapDerivedCategoryFactors`.
  This is the descent identification itself, not an assertion inferred by finite
  evaluations. It also states invertibility of `openToR B s`, the transformation
  equation `pi ≫ whiskerLeft G openToR = adj.unit`, the restriction/open-unit equation
  and the complement equation with zero target on all of `Derived B X`.
- `properOpen_clopen_projector` writes the alpha formula using the specified beta,
  pi, associators, `jComp`, `jCongr`, `gComp`, and the pullback equations.
  Its cartesian implication says that s is an isomorphism and alpha is exactly
  `beta B r k i p h.symm hsq.flip`. This expresses the canonical identification
  V ≅ W_S, rather than incorrectly asserting literal equality with identity before
  transport. Its final universally quantified specialization sets V=S and r=identity,
  states that the canonical lift is a section of q, and that pi selects this section
  with identity/open-unit and zero-complement equations.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.StrictConstantTowerOperations`: `coefficients`, `Modules`,
  `Towers`, `Derived`, `constantRingIso`, `modulePullback`, `moduleDirectImage`,
  `towerPullback`, `G`, `R`, `adj`, `gComp`. These transparently use the constant
  sheaf and the recorded ringed-site module category.
- `Sheaf.AlgebraicGeometry.StrictTowerOpenExtension`: `moduleJ`, `moduleJAdj`,
  `towerJ`, `J`, `jAdj`, `jComp`, `jCongr`.
- `Sheaf.AlgebraicGeometry.StrictTowerProperOpenArrows`: `squareLift`, its open
  and closed instances, `openToR`, `pi`, `beta`, `alpha`.
- `Sheaf.AlgebraicGeometry.ProEtaleClopenRingedModuleGluing`:
  `Scheme.ProEt.clopenTestPiece`, `Scheme.ProEt.clopenTestInclusion`.
  These unchanged plain definitions are now owned by
  `def-pur-clopen-test-piece-inclusion`, which replaces
  `lem-pur-clopen-ringed-module-gluing` in the item's `stmt_deps`.
  The gluing theorem's conclusion is not used to state the item.
- Mathlib `Scheme`, `Scheme.ProEt`, `constantSheaf`, `SheafOfModules`,
  `Functor.ofOpSequence` (the existing reindexing convention), `DerivedCategory`,
  `pullback`, `pullback.fst`, `pullback.snd`, `IsOpenImmersion`, `QuasiCompact`,
  `IsProper`, `IsClosedImmersion`, and `mateEquiv` retain their recorded meanings.
- `Scheme.proEtaleRingModuleAdjunction` in
  `Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction` fixes the ordinary
  adjunction used by the transpose. Proof-only imports include the recorded site
  localization, module-localization exactness, exact derived-functor theorem,
  cochain-derived-adjunction theorem, and localization universal property.
  `Sheaf.AlgebraicGeometry.StrictTowerAdjunctionRealization` now supplies the recorded
  `towerAdjunctionRealization` proof prerequisite and is imported. The as-yet unstated
  `lem-cbc-tower-open-beta-normalization` has no module to import.
  The existing `StrictTowerProperOpenCalculus` is downstream of this newly split
  item, so it is not imported to reuse its special-case component lemmas.

Sources read directly: `more-etale.tex`, `lemma-shriek-proper-and-open` (0F7B),
which requires both vertical arrows proper; `morphisms.tex`,
`lemma-image-proper-scheme-closed` (01W6), part (2); `sites-modules.tex`,
`lemma-extension-by-zero` (03DI). The DAG proof supplies the explicit arbitrary-ring
clopen refinement and its exact unbounded tower descent.

Edge cases checked: empty image U (zero first factor and zero projector target),
empty complement (identity projector), empty ambient scheme (both factors zero),
zero coefficient ring, infinite coefficient ring, arbitrary strict transition maps,
complexes unbounded in both directions, a noncartesian proper/open square, the
cartesian identification case, and r=identity. Properness of r is indispensable
for the clopen conclusion and is present. No extra hypothesis excludes these cases.

Searches for an existing full statement:

- `msearch.py` LeanFinder: “clopen immersion projection sheaves adjunction unit
  derived towers”: eight hits, chiefly Zariski structure-module restriction units
  and counits; none is the ordinary/derived pro-etale strict-tower assertion.
- `msearch.py` Loogle: `AlgebraicGeometry.IsProper, AlgebraicGeometry.IsOpenImmersion`:
  zero hits.
- `msearch.py` grep of Mathlib: `clopen.*(project|Project)|componentProjection|modulePi`:
  only `Ideal.Quotient.modulePi`, unrelated.
- `msearch.py` LeanSearch: “clopen immersion module sheaves product decomposition
  projection adjunction unit”: eight hits about condensed locally constant sheaves,
  Zariski scheme-module adjunctions and a module tensor unit; no full match.
- `rg` in `lean/WeilConjectures`: clopen rank-stratum projectors and finite-etale
  descent results, not this site or these tower transformations. The item's id has
  no upstream declaration.
- `rg` in `lean/Sheaf`: the recorded strict-tower arrows and downstream calculus,
  varying-ring semilinear projectors, and general finite-clopen module gluing.
  Reused the existing arrow definitions and test-piece helpers. The varying-ring
  categories are different, and none of these declarations jointly states this node.

Validation uses only the prescribed server scompile.py and deliver2.py wrappers.
The canonical representative equation uses `ClopenProjectorDescent`, a transparent
predicate spelling out the equation through Mathlib's exact-functor factorizations.
An inference failure in the locally-bijective/sheafification instance was repaired by
`clopenTowerAbelian`: the existing Mathlib abelian instance with all universes fixed,
using the published coefficient-universe sheafification and locally-bijective instances.
These canonical instances are supplied explicitly to the identity and composition
isomorphisms. No site/coefficient universe equality or mathematical hypothesis was added.

## Second reading by Q55

No independent worker was started: the dispatched brief explicitly forbids other agents.
The maintainer's independent delivery review is the independent reading. A local rereading
matched every clause above against the node and the module, checked that both properness
hypotheses remain, and replaced literal identity of the cartesian lift by its canonical
isomorphism and exact beta equation. All data definitions have concrete bodies, all theorem
proofs are sorry, and the node statement is unchanged.

The resumed reading checked the exact `squareLift`, `pi`, `openToR`, `alpha` and
`clopenTestInclusion` definitions against the final statements. The helper
`clopenTowerAbelian` selects precisely Mathlib's existing abelian structure;
`ClopenProjectorDescent` expands to the explicit representative equation, without
changing the localization or any operation. The newly landed adjunction-realization
proof prerequisite was added as a proof-only import. The server dry run passes.


## New nodes

`def-pur-clopen-test-piece-inclusion` records the existing definitions
`AlgebraicGeometry.Scheme.ProEt.clopenTestPiece` and
`AlgebraicGeometry.Scheme.ProEt.clopenTestInclusion` in
`Sheaf.AlgebraicGeometry.ProEtaleClopenRingedModuleGluing`, with `existing: true`.
The former is the actual base change of a pro-etale test object to Y for any
scheme map j; the latter, for an open immersion j, is its first projection,
viewed as an arrow over X by `Over.homMk` and `pullback.condition`.
Source: Stacks 04TR, `lemma-glue-sheaves`, whose explicit section formula uses
these component fibre products. The node cites scheme, pro-etale site,
fibre-product and open-immersion definition nodes. It requires no gluing theorem,
closedness, nonemptiness, quasi-compactness, or coefficient hypothesis.
The new node records the inclusion's signature verbatim and lists both declarations.

The actual LeanFinder query “canonical pro-etale test object pullback along open
immersion and inclusion” returned eight general open-immersion/pullback results;
LeanSearch “A canonical component test object and inclusion for an open immersion
of schemes in the small pro-etale site” returned eight open-immersion results.
Loogle `MorphismProperty.Over.pullback, MorphismProperty.Over.homMk` returned no
hits (unknown first identifier); Mathlib grep `clopenTestPiece|clopenTestInclusion`
returned no hits. The new node's search records preserve these results.
Direct rg of WeilConjectures found no matches; rg of Sheaf located the existing
constructions. DAG rg found them only in theorem lean records, not a definition
node; `blueprint_refs.py search "clopen test"` returned zero blueprint nodes.
Thus this adds an owning definition node, with no new Lean definition or module.

## Returned H2 repair

The returned immutable head was rejected solely because the item's statement
dependencies cited the gluing theorem for two plain definitions. The saved packet's
initial dry run passed, confirming there was no compile failure. I retained the
reviewed module unchanged and replaced that dependency with
`def-pur-clopen-test-piece-inclusion`, as explicitly requested by the maintainer.
The current base did not contain the theorem dependency: it had been added by the
returned packet, so the repair only adds the new definition dependency to the base.
The item's statement, proof, proof dependencies and all fourteen Lean declarations
are unchanged; there is no statement correction. I read the current server source
with `scompile.py --source` and confirmed the same concrete definitions at lines
64-74. The earlier full clause mapping and edge-case review above therefore stand.
For the new node I checked arbitrary j for the base-change object, open j for the
ambient inclusion, j=identity, empty Y, and an empty test object H: each is the same
pullback/projection construction with no extra hypotheses. Both schemes use the
same explicitly bound universe t, inherited from the existing pro-etale interface.

The resumed self-reading also checked that neither definition body refers to the
gluing theorem, that the new node's four cited definition nodes supply exactly its
notions, and that the item's existing two helper references now cite their own
notion. The module's existing source docstrings remain unchanged as requested.
No other agent was started; the maintainer performs the independent review.

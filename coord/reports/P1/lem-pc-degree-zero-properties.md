## Worker report

The module `lean/Sheaf/AlgebraicGeometry/DegreeZeroCohomology.lean` states the
node's two independent assertions as
`AlgebraicGeometry.cohomology_of_iso_invertible_single_zero` and
`AlgebraicGeometry.cohomology_of_iso_locallyFree_shift`. Both proofs are `sorry`;
there are no new definitions or additional mathematical claims.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Scheme X: `(X : Scheme.{u})` in both declarations.
- M in D(O_X): `(M : schemeDerivedCategory X)`, with the shared
  `[HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]`
  encoding of the localization; this imposes no geometric hypothesis on X.
- Invertible O_X-module N: `(N : X.Modules) [Scheme.Modules.IsInvertible N]`.
- M isomorphic to N[0]: `hM : Nonempty (M ≅ (DerivedCategory.singleFunctor
  (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj N)`.
- H^i(M)=0 for i≠0: the first conjunct universally quantifies `i : ℤ`, and
  uses `i ≠ 0 → IsZero ((DerivedCategory.homologyFunctor ... i).obj M)`.
- H^0(M) isomorphic to N: the second conjunct is `Nonempty (... ≅ N)`.
- E locally free of rank r: `(E : X.Modules) (r : ℕ)` and
  `[SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]`.
- Arbitrary shift degree i: `(i : ℤ)`; M isomorphic to E[-i] is the
  `Nonempty` isomorphism to the degree-zero single-functor image of E shifted
  by `⟦-i⟧`. This uses the actual shift, not a new definition of it.
- H^j(M)=0 for j≠i: the first conjunct universally quantifies `j : ℤ` and
  uses `j ≠ i → IsZero ((DerivedCategory.homologyFunctor ... j).obj M)`.
- H^i(M) isomorphic to E: the second conjunct is `Nonempty (... ≅ E)`.

The second assertion is stated independently, as the source's "same argument"
requires: the invertible sheaf in the first assertion is not an extra
hypothesis needed to compute the cohomology of the shifted E.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.DerivedCategory`,
  `AlgebraicGeometry.schemeDerivedCategory`: shared D(O_X), used in both statements.
  Its full carrier is `SheafOfModules.{u} (moduleRings X.toRingedSpace)`;
  Mathlib `DerivedCategory.homologyFunctor` gives its cohomology sheaves.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`,
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`: used for N, exactly the
  dependency's pointwise Zariski-local triviality class on X.Modules.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`,
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree` and
  `IsFiniteLocallyFreeOfDegree`: read in full. These concern scheme morphisms,
  so neither is used as the condition on the sheaf E.
- `Sheaf.AlgebraicGeometry.FiniteLocallyFreeStructureSheaf`,
  `AlgebraicGeometry.finiteLocallyFree_structureSheaf_properties`: read in full.
  This states the rank of a finite-locally-free morphism's structure-sheaf
  pushforward and its canonical fibre isomorphism. It is a contextual reference
  in this node, not a new hypothesis on E or a fact required in this signature.
- Added the already-landed node `def-amb-finite-locally-free-module` to
  `stmt_deps`. Its existing declaration in
  `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`,
  `SheafOfModules.IsFiniteLocallyFreeOfRank`, supplies the actual module-rank
  notion. Read its docstring and full class signature; no private copy,
  dependency module, new node, or statement correction is required.

Edge cases checked before writing: empty X (all module assertions are
compatible with the zero category; no nonempty assumption), r=0 (E is locally
zero), i=0 (the second assertion is the same single-degree computation),
negative and positive i (cohomological convention H^j(E[-i])=H^(j-i)(E)), and
zero M (allowed when its displayed representative is zero). All cohomology
degrees are arbitrary integers, ranks include zero, and the scheme and
localized-hom universes are explicitly bound. No Noetherian, quasi-compact,
separated, or characteristic assumption is introduced.

Searches made with the supplied msearch.py wrapper:

- leanfinder: "cohomology of a derived object isomorphic to an invertible sheaf
  in degree zero or finite locally free sheaf shifted by minus i". Eight
  results include `DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE`
  and general cohomological support lemmas, not the node's assertions.
- loogle: `DerivedCategory.singleFunctor, DerivedCategory.homologyFunctor`.
  Found `DerivedCategory.singleFunctorCompHomologyFunctorIso`, a natural
  isomorphism for the cohomology in the occupied degree of a single complex.
  Read its full signature/docstring in DerivedCategory/FullyFaithful.lean;
  it does not include arbitrary M, the isomorphism hypothesis, off-degree
  vanishing, or the two module hypotheses of this node.
- leansearch: "cohomology of a sheaf placed in a single degree in the derived
  category". Service unavailable: Internal Server Error.
- grep: `singleFunctor.*homology|homology.*singleFunctor`, subdirectory
  Algebra/Homology/DerivedCategory. Eleven hits, including the preceding
  natural isomorphism and uses in Ext exact sequences; no exact match.
- Direct rg over Mathlib, upstream WeilConjectures, and lean/Sheaf for
  `lem-pc-degree-zero-properties` and both proposed declaration names: no
  existing declaration or name collision. Direct concept search over these
  trees found the shared rank predicate and the Mathlib single-degree
  ingredients, but no complete theorem matching this node.
- Read dag/lean_names_upstream.json with the item and proposed-name search:
  no hits. Read every original statement dependency node and its recorded
  declaration, and the added landed rank-definition node.

Source read: the exact blueprint node at the recorded path, via read-only
ssh on the project server (literature is not installed in the local clone).
The source statement agrees with the DAG. Its final proof sentence says
"E in degree -i", a sign typo: E[-i] is in degree i, as its statement and the
stage-1 split proof correctly say. The module docstrings follow the three
split proof steps: quasi-isomorphism invariance, the degree-zero computation,
and the shifted computation. No statement is disputed or corrected.

Validation: server scompile.py returned exit code 0, compiled in 2.8 seconds,
with no warnings. Delivery dry run is the final check; the independent second
reader will supply the second-reading section and deliver.

## Second reading by P1

Independent reading of the sandbox node and DegreeZeroCohomology.lean, the
five statement dependency nodes, and their recorded declarations. I read the
exact source blueprint node and its unit `_section.md` by read-only ssh on
the server. This node's source is the blueprint, not a Stacks lemma. The unit
introduces a separably closed field and a smooth projective curve for its
Picard functor; the lemma explicitly introduces an arbitrary scheme X, and
its elementary cohomology computation has no such geometric hypotheses.
There is no `statement_change` and no new node or dependency module in this
delivery. The additional rank-definition dependency is already landed.

The statement checklist, with verdicts for every object, hypothesis and
conclusion:

- Arbitrary scheme X: `(X : Scheme.{u})` in each declaration. PASS: no field,
  characteristic, nonemptiness, Noetherian, separatedness or finiteness
  hypothesis is imposed.
- Object M of D(O_X): `(M : schemeDerivedCategory X)` in each declaration.
  PASS: opened `schemeDerivedCategory` in the dependency module; it is the
  derived category of `SheafOfModules.{u} (moduleRings X.toRingedSpace)`.
  The explicit `HasDerivedCategory.{w}` binder is the shared localization
  structure, not a restriction to bounded or quasi-coherent objects.
- Invertible O_X-module N: `(N : X.Modules)` and
  `[Scheme.Modules.IsInvertible N]` in the first declaration. PASS: opened
  the recorded class, whose `exists_isoUnit` gives a neighbourhood of each
  point on which N restricts to the structure sheaf. This is local rank one;
  no separate quasi-coherence assumption is needed.
- M isomorphic to N[0]: `hM : Nonempty (M ≅ (DerivedCategory.singleFunctor
  (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj N)`.
  PASS: the isomorphism is in the actual derived category and the single
  functor places N in degree zero.
- H^a(M)=0 for every a unequal to zero: the first conclusion is
  `∀ i : ℤ, i ≠ 0 → IsZero ((DerivedCategory.homologyFunctor ... i).obj M)`.
  PASS: sheaf cohomology objects, arbitrary integer degrees, exactly the
  required off-degree vanishing.
- H^0(M) isomorphic to N: `Nonempty ((DerivedCategory.homologyFunctor
  ... 0).obj M ≅ N)`. PASS: an isomorphism of module sheaves, not merely a
  stalkwise equality or an isomorphism of sections.
- Second assertion's locally free sheaf E of rank r: `(E : X.Modules)` and
  `(r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]`.
  PASS: opened the recorded class and its covering characterization
  `isFiniteLocallyFreeOfRank_iff_exists_over_iso_free`. It is constant rank
  r on an open covering, including rank zero. I also read the scheme
  bridges `isFiniteLocallyFreeOfRank_of_restrict_iso_free` and
  `IsFiniteLocallyFreeOfRank.exists_restrict_iso_free` in upstream
  Mathlib/AlgebraicGeometry/Modules/Sheaf.lean. The original dependencies
  `Scheme.Hom.IsFiniteLocallyFree`, `IsFiniteLocallyFreeOfDegree` and
  `finiteLocallyFree_structureSheaf_properties` concern morphisms and
  pushforwards, not the definition of E's rank. Adding the existing
  `def-amb-finite-locally-free-module` supplies the correct shared notion.
- Arbitrary integer i and M isomorphic to E[-i]: `(i : ℤ)` followed by
  `hM : Nonempty (M ≅ ((DerivedCategory.singleFunctor ... 0).obj E)⟦-i⟧)`.
  PASS: an actual derived shift, with the cohomological sign convention.
  This assertion is independently quantified; the source's second
  calculation does not need an invertible N as an extra hypothesis.
- H^j(M)=0 whenever j differs from i: `∀ j : ℤ, j ≠ i → IsZero
  ((DerivedCategory.homologyFunctor ... j).obj M)`. PASS: every off-degree
  sheaf vanishes, with j quantified after the fixed i.
- H^i(M) isomorphic to E: `Nonempty ((DerivedCategory.homologyFunctor
  ... i).obj M ≅ E)`. PASS: the entire required occupied-degree conclusion.

Edge cases: empty X is permitted and the local rank predicates are
vacuous there, as in the source; no cover-index nonemptiness is required.
For r=0, E is locally zero and the assertion still computes zero in every
degree. Zero M is permitted whenever the representative is zero (in the
invertible case this includes the empty scheme). At i=0, E[-i] is the
unshifted single complex. For positive and negative i, the shared shift
satisfies H^j(K[-i]) = H^(j-i)(K), hence the occupied degree is i.
The integers and natural rank include all requested cases, characteristic
is unrestricted, and both u and w are explicitly declared. The module
universe is the dependency's universe for O_X-modules; no test-object
universe or small-index assumption is introduced.

Independent searches (different queries from the worker):

- leanfinder through msearch.py: "derived category cohomology supported at
  one integer after shifting a vector bundle". Eight hits: T-structure
  support, single-complex morphisms for injectives/projectives, and a
  projective-resolution support instance. None states these computations.
- loogle through msearch.py: `DerivedCategory.homologyFunctor,
  CategoryTheory.Limits.IsZero`. Four hits, `isZero_of_isGE`,
  `isZero_of_isLE`, `isGE_iff`, `isLE_iff`; their types give support
  conditions, not either isomorphism-to-single computation. An initial
  query using `CategoryTheory.IsZero` failed name resolution and was
  corrected to `CategoryTheory.Limits.IsZero`.
- rg on Mathlib's homology tree, all upstream WeilConjectures, lean/Sheaf
  and dag/lean_names_upstream.json for `singleFunctorCompHomologyFunctorIso`,
  `isZero_single_obj_homology`, `homologyFunctor.*shift`,
  `shift.*homologyFunctor`, the node id and both proposed names. No
  matching complete theorem or declaration-name collision. Opened the
  general natural isomorphism in DerivedCategory/FullyFaithful.lean and
  the off-degree lemma in SingleHomology.lean: these are ingredients, not
  a statement for arbitrary M with the node's isomorphism hypotheses.
  Upstream HomologyProperty.lean's shift instance confirms the sign;
  it is a property-stability instance, not this statement.

No semantic mismatch found and no Lean or node change made. The source
proof's last sentence says E is in degree -i; this is a proof-text sign
 typo, not the statement's sign: E[-i] is in degree i. The stage-1 proof
and the Lean docstring already use the correct degree i. Both theorem
proofs remain `sorry`; there are no definitions, hollow data, private
notions, local notation or local instances. The docstrings carry the
source place, blueprint id and all three elementary proof steps.
The node's `lean.statement` was checked verbatim against the first
signature; the second declaration is recorded in `lean.declarations`.
Only this independent reading has been appended to the report.

## Worker report

Repaired the returned interface in `Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients`.
The theorem now states every clause of the blueprint node.  The first clause is
exactness of `moduleAbelianForget` for every scheme `T`, rendered as preservation
of finite limits and finite colimits.  The next four clauses are the canonical,
unit-compatible inverse-image comparisons for `f`, `f'`, `g`, and `g'`, rendered
as `IsIso (moduleAbelianUpperStarComparison Λ u)`.  The next two clauses are the
canonical direct-image comparisons for `f` and `f'`, rendered as
`IsIso (moduleAbelianDerivedLowerStarComparison Λ u)`.  The final clauses state
compatibility of the forgotten derived exchange map with the abelian exchange
map, followed by the iff criterion for invertibility.

The hypotheses are rendered by `Λ : Type (u + 1)` with `[CommRing Λ]`, schemes
`X X' Y Y' : Scheme.{u}`, morphisms `f`, `f'`, `g'`, `g`, the cartesian-square
input `sq : CommSq g' f' f g`, and
`K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
(ModuleCat.{u + 1} Λ)))`.  The exactness clause uses an explicitly bound
`T : Scheme.{u}` and therefore does not restrict the four square schemes.

Dependencies used are the declarations imported from
`Sheaf.AlgebraicGeometry.ModuleAbelianDerivedExchangeCompatibility`, including
`moduleAbelianForget`, `moduleAbelianUpperStarComparison`,
`moduleAbelianDerivedLowerStarComparison`, the two endpoint exchange isomorphisms,
and `derivedBaseChangeMapPlus`.  The four inverse-image comparisons and two
derived direct-image comparisons are precisely the recorded canonical
comparisons in those modules.

Edge cases checked: zero and arbitrary commutative coefficient rings, identity
and cartesian identity squares, empty schemes, zero sheaves, and bounded-below
complexes.  The universal exactness quantifier covers all schemes `T`; no
properness, finiteness, characteristic, or nonemptiness hypothesis was added.

Searches made: `rg` over project `lean/Sheaf` and the slopmaster2 source for
exchange, forgetting, inverse-image, and direct-image comparisons; Mathlib and
source grep for exact coefficient-forgetting declarations; and the prescribed
`msearch.py` LeanFinder/Loogle/grep queries.  No declaration exactly matching
the complete node statement was found.

The repaired module compiles with `scompile.py` under the required nice-19,
two-thread, 60-second-per-file settings; the expected `sorry` is the only
placeholder.

## Earlier second reading (a previous round; superseded)

The returned H3 finding is repaired: the interface now includes the cartesian-square
hypothesis, universal exactness of coefficient forgetting, all four inverse-image
comparison clauses, both direct-image comparison clauses, exchange compatibility,
and the final iff clause.  The server compiler passes, and the node lean record
was synchronized with the parsed theorem signature.

## Second reading by NC

Read the node, all six statement-dependency records, the proof-dependency records,
ChosenCartesianSquare, DerivedCategories, the upstream upper/lower-star definitions,
the upstream derived exchange construction, the constant-ring module equivalence,
the canonical module/abelian edge comparisons and exchange endpoint definitions,
and Mathlib DerivedCategory.Plus.isIso_iff. Read Stacks sites-cohomology.tex at
lemma-modules-abelian-unbounded (0D6J) and remark-base-change (07A7), and
etale-cohomology.tex at lemma-stalk-pullback (03Q1). These source passages assume
arbitrary ringed sites/topoi or arbitrary schemes and morphisms; they impose no
Noetherian, properness, finiteness, torsion, characteristic or nonzero-ring condition.

Object, hypothesis and conclusion checklist against the unchanged node:

- Commutative coefficient ring: `(Λ : Type (u + 1)) [CommRing Λ]`. Correct; arbitrary
  commutative rings, including the zero ring, in the recorded six-functor encoding.
- Four schemes: `{X X' Y Y' : Scheme.{u}}`. Correct; no geometric property added.
- Four arrows with the displayed orientation: `{f : X ⟶ Y}`, `{f' : X' ⟶ Y'}`,
  `{g' : X' ⟶ X}`, `{g : Y' ⟶ Y}`. Correct.
- Cartesian square with chosen identification: originally only `CommSq`. This was
  stronger than the node as a theorem (it applied to noncartesian squares too).
  Replaced by `sq : ChosenCartesianSquare g' f' f g`, the recorded declaration of
  def-weil-pbc-cartesian-square. Its `isoPullback`, `hom_fst`, `hom_snd` provide the
  chosen fibre-product identification; `sq.toCommSq` is the input to the unchanged
  exchange construction. No private square notion or dependency repair is needed.
- A bounded below module complex on X: `K : DerivedCategory.Plus
  (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))`. Correct, using the recorded
  DerivedCategories convention, with no boundedness above or torsion assumption.
- Underlying abelian-sheaf functor: `moduleAbelianForget Λ T`, whose body is
  `sheafCompose` with `forget₂ (ModuleCat Λ) AddCommGrpCat`. Correct. The recorded
  constant-ring module equivalence retains the underlying additive presheaf
  (`etaleConstantModuleUnderlyingIso`) and justifies this shared encoding; the
  proof-dependency module is now explicitly imported for stage 3.
- Exactness for every scheme: the conjunction of `PreservesFiniteLimits` and
  `PreservesFiniteColimits`, universally over `T`. Correct for these abelian
  categories; no restriction to the four corners.
- Termwise derived forgetting and cohomology comparison for every degree:
  `D+(moduleAbelianForget Λ T)` already is the recorded exact termwise lift.
  The original conclusion omitted the cohomology assertion. Added `∀ T i,
  Nonempty (D+(moduleAbelianForget Λ T) ⋙ homologyFunctor _ i ≅
  homologyFunctor _ i ⋙ moduleAbelianForget Λ T)` using fully qualified
  `DerivedCategory.Plus.homologyFunctor`. This asserts a natural identification,
  rather than literal equality between chosen models. The existing
  `Functor.mapDerivedCategoryPlusHomologyFunctorIso` supplies exactly its inverse
  orientation; no new functor or comparison definition is introduced.
- Clause (1), all four edges: `IsIso (moduleAbelianUpperStarComparison Λ f)` and
  the analogous clauses for `f'`, `g`, `g'`. Correct. Opened the comparison body:
  it is the adjoint of the forgotten module unit; naturality is built into this
  natural transformation, and its inverse supplies the node's orientation.
- Clause (2), both vertical arrows, natural in every input complex:
  `IsIso (moduleAbelianDerivedLowerStarComparison Λ f)` and the clause for `f'`.
  Correct. These are whole natural transformations, so the clauses cover every
  complex on each source, including complexes on X' unrelated to the bound K.
  Their definitions use the direct-image identity and the canonical derived
  base-change comparison; their normalization is by derived units. The source
  uses module and abelian K-injective replacements separately, as the docstring
  now explicitly explains, without assuming forgetting preserves injectives.
- Clause (3): the displayed equation maps the module exchange by derived
  forgetting and then composes with `moduleAbelianDerivedExchangeTargetIso`;
  the other side is `moduleAbelianDerivedExchangeSourceIso` followed by the
  abelian exchange on the forgotten K. Correct orientations and categories.
  Opened both endpoint definitions: they compose precisely the preceding
  inverse-image and direct-image comparisons, rather than arbitrary isomorphisms.
- Final iff: `IsIso` of the module exchange iff `IsIso` of the abelian exchange
  on the forgotten K. Correct, both directions and the same square and complex.
  Derived conservativity follows from the cohomology comparison and the recorded
  Mathlib `DerivedCategory.Plus.isIso_iff`, not from an unjustified resolution claim.

Edge cases: no index set is involved. Empty schemes and their identity/pullback
squares are admitted by ChosenCartesianSquare; zero sheaves and the zero derived
object remain allowed. The zero ring is not excluded by CommRing. All integers,
including degree zero and negative degrees, occur in the new cohomology clause.
There is no characteristic or invertibility hypothesis. `u` is explicitly bound,
with schemes in universe u and sheaf values and coefficients in u+1, exactly as
in the recorded six-functor dependencies; smaller coefficient rings can be lifted.
No independent small test-object universe or unbound variable is present.

Independent searches, with different wording from the worker:

- LeanFinder via msearch: "restriction of scalars sheaves derived base change
  comparison conservative" returned SheafOfModules.restrictScalars and underived
  pushforward/restriction-of-scalars ingredients, not this statement.
- Loogle via msearch: `"forget", "homology"` found the ModuleCat-to-Ab
  short-complex PreservesHomology instance, not the sheaf exchange theorem.
- LeanSearch via msearch: "forget coefficient ring etale sheaves derived exchange
  morphism" was unavailable (Internal Server Error); no verdict claimed for it.
- Local rg over project Sheaf, upstream WeilConjectures and Mathlib for
  `exchange_forget_coefficients`, `forget.*[Bb]ase[Cc]hange` and the reverse found
  no existing theorem with all these conclusions. The generic exact-functor
  cohomology comparison was found by `mapDerivedCategory.*[Hh]omology` and the
  reverse, then its signature/body in ExactFunctor.lean was read and reused.
  The existing exchange compatibility theorem covers the equality alone, and
  is used rather than copied as a new comparison construction.

Mismatches repaired: missing Cartesian data, missing cohomology conclusion,
missing stepwise source/proof documentation, and missing explicit proof imports.
Added the standard copyright header. The old Worker report and superseded reading
remain above as history; their claims of completeness are superseded by this
checklist. No informal statement, proof, dependency list, target, or dependency
node changed. There are no new definition nodes or dependency modules in this
delivery. The sole theorem proof is still `sorry`; there is no new definition,
private declaration, local notation or local instance. The node's lean.statement
is copied verbatim from the repaired signature and branch is newtargets-dag.

Validation: scompile.py accepted the repaired module with no warnings or errors
(server, nice 19, two threads, 60 seconds per file). Its dependency loader also
compiled the recorded ChosenCartesianSquare module. Every Lean line is at most
100 characters. Delivery dry run and final delivery use the prescribed tool.

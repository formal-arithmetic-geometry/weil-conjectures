## Worker report

Item: lem-asd-smooth-generic-direct-image. The module
`Sheaf.AlgebraicGeometry.SmoothGenericDirectImage` states
`AlgebraicGeometry.Etale.exists_nonempty_open_smooth_directImage_lisse_baseChange`.
Only its proof is postponed with `sorry`; no definitions or auxiliary theorems are added.
The node is unchanged except for its `lean` record.

Source read: the complete blueprint node
`sec-smooth-purity/sk-prop-sf-cbc/lem-asd-smooth-generic-direct-image.md`, together with the
DAG's six expanded proof steps. The declaration docstring carries all six steps, including
identification of the canonical exchange by its counit transpose and the empty-source case.

Clause-by-clause correspondence:

- The field is `(k : Type u) [Field k]`. The base is `(S : Scheme.{u}) [IsIntegral S]`.
  Its structure morphism `aS : S ⟶ Spec (.of k)` has `LocallyOfFiniteType aS` and
  `QuasiCompact aS`, exactly finite type. No separatedness of S over k is required.
- The coefficient prime is `(ℓ : ℕ) [Fact ℓ.Prime]`, with `hℓ : ℓ ≠ ringChar k`.
  The coefficient ring is `ULift.{u + 1} (ZMod ℓ)`, the same prime field with the
  universe lift used by the recorded ordinary small-etale derived categories.
- The source morphism is `(f : X ⟶ S)` with `IsSeparated f`, `Smooth f`,
  `LocallyOfFiniteType f` and `QuasiCompact f`; the last two express finite type.
  No pure-relative-dimension, properness, affineness, or surjectivity is imposed.
- L is a sheaf in `Sheaf X.smallEtaleTopology (ModuleCat ... )`, with
  `hL : Scheme.IsFiniteLocallyConstantSheaf L`. Over this finite field, the recorded
  predicate's finitely generated stalks are finite stalks.
- `∃ U : S.Opens, Nonempty U ∧ ...` is the nonempty open. To avoid choosing a special
  fibre product, the conclusion holds for every `XU`, `p`, `fU` with
  `IsPullback p fU f U.ι`. Such a pullback exists for every U; this quantification
  is the invariant formulation of the named base-changed scheme X_U.
- `singleFunctor _ 0` places L in degree zero, `L((p)^*[...])` restricts it to X_U,
  and `R((fU)_*[...])` is its ordinary unbounded derived direct image.
  Constant-coefficient inverse image is exact, so its left derived functor is the
  ordinary inverse image required by the statement.
- The first conjunct provides integers `a b`, `a ≤ b`, and `IsZero` of each
  `homologyFunctor _ i` outside `[a,b]`, exactly boundedness.
- The second conjunct requires `Scheme.IsFiniteLocallyConstantSheaf` of every
  cohomology sheaf of that same direct image, exactly finite locally constant cohomology.
  No extra constructibility assertion or choice of a stratification is imposed.
- The last conjunct quantifies every `(T : Scheme.{u}) [IsNoetherian T]` and every
  `v : T ⟶ U.toScheme`. It requires `IsIso` of the component of the recorded
  `derivedBaseChangeMap` on the restricted L, for every pullback
  `sq : IsPullback vX fT fU v`. The orientation `sq.toCommSq` gives
  `v^* RfU_* → RfT_* vX^*`, as checked against the actual source signature and docstring.
  This names the canonical ordinary exchange, rather than an arbitrary isomorphism.

Dependency declarations and interfaces read and reused:

- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Sheaf.AlgebraicGeometry.DerivedCategories`, importing
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`; the category used by the displayed
  functors is definitionally this ordinary derived category. Cohomology is
  `DerivedCategory.homologyFunctor`; placement in degree zero is `singleFunctor`.
- `Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets`, importing
  `WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded`:
  `AlgebraicGeometry.Etale.derivedBaseChangeMap`, the recorded module-coefficient
  declaration (the dependency's primary declaration is its abelian-coefficient helper).
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`; imported as the
  statement/proof dependency, while the conclusion spells out boundedness and lisseness.
  Its sheaf vocabulary reuses `WeilConjectures.ConstructibleSheaf.Defs`,
  `AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`, including
  its `Nonempty` field. The scheme-conventions node defines no new declaration;
  its finite-type and separated properties are the standard Mathlib ones above.

Every recorded proof dependency with a module is imported privately unless already
imported publicly as a statement dependency: Noetherianity, local constancy of smooth
relative dimension, Nagata compactification, geometric-stalk conservativity, derived
internal Hom, compact-support finiteness/exchange, finite lisse duality, and compactification
base change. The separated/finite-type base-change Mathlib modules are already publicly
available through Smooth and the exchange imports. The three proof nodes
`thm-asd-smooth-tensor`, `prop-asd-internal-adjunction`, and `prop-asd-smooth-base-change`
have no recorded module, so there is no module for them to import yet. They are proof
prerequisites, not missing objects needed to state this theorem.

Edge cases checked: integral S is nonempty by definition; the whole base is available as
an open. Empty X and zero L give the zero derived image with all cohomology zero. The
bounds allow a=b, and degree zero is included. No test T must be nonempty, finite type
over k, integral, or separated; identity and arbitrary Noetherian base changes are
included. No common relative dimension is required. Characteristic zero and every prime
distinct from a positive characteristic are allowed. A single universe u for schemes,
fields and test schemes follows the project's small-site size convention; coefficient
objects have the prescribed universe u+1.

Searches performed before writing:

- `msearch.py ... leanfinder`: "Smooth morphism finite locally constant etale sheaf
  generic direct image bounded locally constant and universal base change".
  Eight hits, all smooth/etale morphism facts; none states generic derived-image lisseness.
- `msearch.py ... loogle`: "AlgebraicGeometry.Etale.derivedBaseChangeMap,
  AlgebraicGeometry.Smooth". Zero hits; index reports unknown derivedBaseChangeMap.
  Its declaration was instead located and read directly in DerivedUnbounded.lean.
- `msearch.py ... grep`: "generic.*direct|smooth.*generic|generic.*baseChange".
  Zero Mathlib hits.
- `rg` of the same pattern and the exact node id over upstream `WeilConjectures`
  and project `lean/Sheaf`: neighboring generic curve and generic-open constructibility
  statements, no theorem with this statement. The generic-open theorem supplied a
  checked model for quantifying arbitrary pullback squares, not a duplicate theorem.
- Direct source searches located `IsFiniteLocallyConstantSheaf`, `DerivedCategoryModule`
  and `derivedBaseChangeMap`; their full definitions/signatures and docstrings were read.

No statement correction, new node, dependency repair, or statement dispute is needed.
Compilation and dry-run results are recorded after validation below.

Validation: prescribed `scompile.py NA lem-asd-smooth-generic-direct-image` compiled the
sandbox file and the library-path file successfully, with no errors or warnings.

## Second reading by NA

I independently read the complete node, all six DAG proof steps, its actual source
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/lem-asd-smooth-generic-direct-image.md`,
and the surrounding unit `_section.md`, then compared the sandbox declaration. This is
an ordinary small-etale, prime-field statement; the surrounding unit's adic coefficient
clauses do not replace this node's explicitly ordinary coefficient categories.

Objects, hypotheses and conclusions checked individually:

1. A field k: `(k : Type u) [Field k]`. Correct; no perfection or algebraic closure.
2. An integral finite-type k-scheme S: `(S : Scheme.{u}) [IsIntegral S]` and
   `aS : S ⟶ Spec (.of k)` with `LocallyOfFiniteType aS`, `QuasiCompact aS`.
   Correct. I read `IsIntegral` in Mathlib Properties: nonemptiness and domains of
   sections on nonempty opens. No separatedness of S is assumed.
3. A coefficient prime different from the characteristic: `(ℓ : ℕ) [Fact ℓ.Prime]`
   and `hℓ : ℓ ≠ ringChar k`. Correct; primality is implicit in the source's F_ell.
   `ULift.{u + 1} (ZMod ℓ)` is that finite field at the required coefficient size.
4. A separated smooth finite-type morphism f: `(X : Scheme.{u}) (f : X ⟶ S)`
   with `IsSeparated f`, `Smooth f`, `LocallyOfFiniteType f`, `QuasiCompact f`.
   Correct. I read Mathlib Smooth's affine smooth-ring condition. The last two
   instances express finite type; they do not add a stronger finiteness condition.
5. A finite locally constant F_ell-sheaf L: `L : Sheaf X.smallEtaleTopology
   (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))`, `hL :
   Scheme.IsFiniteLocallyConstantSheaf L`. Correct. I read the upstream classes:
   etale-local constancy together with finitely generated geometric stalks. Over
   this finite field those stalks are finite, as required.
6. One nonempty open U: `∃ U : S.Opens, Nonempty U ∧ ...`. Correct. The subsequent
   universal `XU p fU` and `IsPullback p fU f U.ι` express any realization of X_U;
   scheme pullbacks exist, so this is neither vacuous nor an extra hypothesis.
7. The ordinary derived image of restricted L: every occurrence is
   `R((fU)_*[...]).obj (L((p)^*[...]).obj (singleFunctor _ 0 |>.obj L))`
   (here the pipe is explanatory shorthand only). Correct. I read
   `DerivedCategoryModule` in upstream Coefficients: precisely the derived category
   of these module sheaves. Exact constant-coefficient inverse image makes Lp^*
   the restriction required by the node, including on degree-zero L.
8. Boundedness: `∃ a b : ℤ, a ≤ b ∧ ∀ i, (i < a ∨ b < i) → IsZero ...`.
   Correct: all cohomology vanishes outside a finite integer interval.
9. Finite locally constant cohomology: `∀ i : ℤ,
   Scheme.IsFiniteLocallyConstantSheaf ((homologyFunctor _ i).obj ...)`.
   Correct, for exactly the same derived-image object as in item 8.
10. Every Noetherian base change: `∀ (T : Scheme.{u}) [IsNoetherian T]
    (v : T ⟶ U.toScheme) ... (sq : IsPullback vX fT fU v), IsIso ...`.
    Correct. There is no finite-type-over-k, separatedness, smoothness or nonemptiness
    assumption on T. I read `derivedBaseChangeMap` in upstream DerivedUnbounded:
    its type is `Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*`, the mate of the inverse-image
    square. Substitution f=fU, g=v, g'=vX, f'=fT gives exactly the node's canonical
    arrow on restricted L. No arbitrary isomorphism replaces it.

Dependency review: I opened all six statement-dependency nodes and read their recorded
interfaces. I opened `DerivedCategories.lean`, `BaseChangeMapAbelianAndSets.lean`,
`BoundedConstructibleComplexes.lean`, its imported
`IsConstructibleEtaleModuleSheaf.lean`, upstream Coefficients, ConstructibleSheaf/Defs,
DerivedUnbounded, and Mathlib Smooth and Properties. The convention node introduces no
alternative scheme type. The constructible-complex predicate is a proof ingredient;
this theorem correctly spells out the stronger lisse conclusion instead of substituting
constructibility. The exchange helper module publicly imports the actual module-valued
exchange used here. No new nodes or dependency modules occur in this delivery.
The named proof imports with available modules agree with the DAG's proof plan; the
three unstated smooth-duality/adjunction results are proof prerequisites, not missing
objects of this statement. The declaration docstring follows all six proof steps,
including identification of the canonical arrow and finite-dimensional recombination.

Edge cases: zero L and empty X are admitted; the derived image is then zero and bounds
may be a=b=0. Empty S is correctly excluded by integrality. Empty T is admitted, as
are identity and arbitrary Noetherian base changes. No pure relative dimension is
assumed, so dimension zero and several dimension components are covered. Every prime
in characteristic zero and every prime distinct from positive characteristic is
included. The single scheme universe u is arbitrary, with the standard small-site
module universe u+1; no new universe equality or extra instance parameter is imposed.
There is no index family in the statement to restrict.

Independent searches, with queries different from the author's:

- LeanFinder through msearch: "A lisse finite field sheaf on a smooth scheme has locally
  constant higher direct images after shrinking an integral base, commuting with every
  Noetherian base change". Eight hits concerned constant sheaves, condensed modules,
  and scheme limits; no match.
- Loogle through msearch: `AlgebraicGeometry.Smooth, CategoryTheory.IsIso`.
  One hit, `Scheme.Hom.instIsIsoNormalizationPullbackOfSmooth`, concerns normalization,
  not this statement.
- Grep through msearch: `lisse|generic.*directImage|directImage.*generic`.
  Three unrelated separated-relation hits; no match. I therefore also searched directly
  with rg for `smooth.*direct.image|generic.*(lisse|direct.image)|direct.image.*generic`
  over Mathlib AlgebraicGeometry, upstream WeilConjectures and project lean/Sheaf.
  The hits concern finite pushforward, generic curve sheaves, or adic kernels and
  cokernels; none combines this smooth-source ordinary derived-image and exchange
  assertion. Exact declaration/node-id searches in upstream, project sources and
  dag/lean_names_upstream.json gave no duplicate.

Verdict: no mismatch found, and no Lean, statement, dependency or definition changes
were necessary. The module has one named theorem with whole proof `sorry`, no hollow
definition and no proved auxiliary results. I verified programmatically that
`lean.statement` equals the complete file signature verbatim. All universes and variables
are explicitly bound. The prescribed scompile.py run from the sandbox compiled both
its sandbox probe and library-path file cleanly (4.9 s and 5.2 s); no warnings or errors.
The second reading adds this independent review only.

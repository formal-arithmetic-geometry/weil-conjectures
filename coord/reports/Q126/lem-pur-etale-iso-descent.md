## Worker report

The module `Sheaf.Paper.EtaleIsoDescent` states
`WeilConjectures.isIso_of_surjective_etale_pullback`, with its proof `sorry`.
No definition or auxiliary theorem is introduced. The only node change is its
`lean` record. There are no new nodes, dependency repairs, statement corrections,
or disputed assertions.

Sources read: the item's complete DAG statement and five proof steps; the historical
blueprint `master/blueprint/sec-smooth-purity/sk-prop-cohsm/lem-pur-etale-iso-descent.md`;
and the current `main-20261015/blueprint/sec-six-functors-basics/sk-prop-cohsm/`
statement and proof files for the same item (order 2336). The two statements agree.
The theorem docstring follows the DAG's five-step cover/restriction/sheaf-gluing
proof. It does not assume geometric-stalk conservativity for arbitrary pro-etale
sheaves. No repair note for this item was present.

Hypothesis and conclusion correspondence:

- The fixed purity conventions are `P : PurityFiniteSetting.{u}`. This recorded
  structure contains the finite-field datum, the prime different from its
  characteristic, the fixed coefficient algebraic closure, its finite subextension,
  and `P.level` with `P.level_pos : 1 ≤ P.level`. Thus the coefficient ring is
  precisely `P.Ring = Padic.coefficientExtensionRing P.coefficients.l P.extension P.level`.
- The two k-schemes are `U X : Over (Spec (CommRingCat.of P.field.k))`.
  These have underlying schemes `U.left`, `X.left` and structure maps `U.hom`, `X.hom`.
- Separatedness is `[IsSeparated U.hom] [IsSeparated X.hom]`. Finite type is
  `[LocallyOfFiniteType U.hom] [QuasiCompact U.hom]` and the analogous pair for X,
  exactly the recorded finite-type convention, with no properness assumption.
- The morphism of k-schemes is `f : U ⟶ X` in `Over`; its defining commutativity
  makes it a k-morphism without a separate compatibility hypothesis.
- Surjectivity and etaleness are `[Surjective f.left] [Etale f.left]`.
- `M N` belong to `(intrinsicFiniteTorsionConstructible P.coefficients.l
  P.extension P.level P.level_pos X.left).FullSubcategory`. The recorded predicate
  says that finitely many integer-degree cohomology sheaves are nonzero and every
  cohomology sheaf is constructible on the small pro-etale site, with the prescribed
  finite quotient coefficients. It imposes no finite Tor-amplitude or etale-origin
  condition. The morphism in this category is `φ : M ⟶ N`.
- The hypothesis that `Lu^* φ` is invertible is `hφ : IsIso
  ((@sfIntrinsicDerivedPullback P.Ring _ (...) U.left X.left f.left).map φ.hom)`.
  This is the exact intrinsic constant-coefficient derived inverse image used
  in the body of the recorded `finiteDerivedPullback` definition. The finite-ring
  instance is supplied explicitly by `Padic.finite_coefficientExtensionRing ...
  P.level P.level_pos`; it is a theorem, not an additional hypothesis.
  The public wrapper `finiteDerivedPullback` indexes positive levels as `n+1`.
  Using its underlying published `sfIntrinsicDerivedPullback` directly at P.level
  avoids a redundant choice of predecessor and any cast of coefficient categories.
  It introduces no second construction: this is the identical canonical functor,
  transported through the published intrinsic realization, evaluated at the fixed
  positive level. No `let`, arbitrary coefficient map, or arbitrary isomorphism
  occurs in the signature.
- The conclusion `IsIso φ` is invertibility in the full bounded constructible
  category itself. Its ambient morphism is `φ.hom`; fullness makes the cohomology
  proof's ambient inverse an inverse in this category. No constructibility of the
  pullback is assumed or needed to formulate the stated hypothesis.

Statement dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`, its
  `Ring` and field/coefficient projections; also its imported
  `WeilConjectures.FiniteFieldDatum.CoefficientDatum` instance declarations.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `AlgebraicGeometry.Surjective`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: the recorded
  `AlgebraicGeometry.IsSeparated` reexport (defined in Morphisms.Separated).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`
  and `AlgebraicGeometry.QuasiCompact` (defined in Morphisms.QuasiCompact).
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`, the intrinsic constant-ring
  derived category underlying the constructible subcategory.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `WeilConjectures.finiteDerivedPullback`,
  read with its complete signature and body; its canonical underlying construction
  `AlgebraicGeometry.Scheme.sfIntrinsicDerivedPullback` is defined and reexported by
  `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations`. Its complete definition,
  exactness instances, and canonical intrinsic realization transport were read.
- `Padic.finite_coefficientExtensionRing`, provided through the recorded coefficient
  modules, supplies the actual finite quotient-ring instance.

Every stated proof dependency is imported, non-publicly when only the proof needs it:
`EtaleComparison`, `UniversallyOpen`, `AffineScheme`, `QuasiSeparated`,
`ProEtaleWeaklyEtaleLocalization`, `SfIntrinsicRealizationTransport`,
`ModuleCat.Sheaf.PushforwardContinuous`, `LocalizedModuleExactIndependent`,
`ShortComplex.PreservesHomology`, `SiteCoveringAxioms`, and
`DerivedCategory.HomologySequence`. Statement dependencies also used by the proof
retain their public imports.

Edge cases checked before writing:

- The empty scheme is permitted; no nonemptiness assumption is present. A surjection
  from an empty source forces the target empty. The empty-cover sheaf axiom gives
  the zero module category there, as explained in the proof docstring.
- Identity morphisms and isomorphisms of k-schemes are included. Pullback is the
  recorded canonical inverse image, including its identity comparison.
- Level 1 is included exactly: the statement uses the fixed positive P.level,
  without requiring a predecessor, level at least 2, or ramification divisibility.
- Zero complexes, arbitrary finite cohomological support including empty support,
  and arbitrarily shifted complexes are included. There is no common externally
  fixed cohomological interval and no amplitude assumption.
- Constructible complexes need not have finite Tor dimension; both M and N use
  intrinsicFiniteTorsionConstructible rather than finiteTorConstructible.
- Both schemes and the coefficient ring use universe u; the small site's objects
  retain universe u+1 and morphisms universe u. The canonical coefficient ULift
  and module-sheaf category are exactly those of the recorded derived category.
  No new site-size equality or test-object universe restriction is imposed.

Searches run for an existing exact statement:

- `msearch.py ... leanfinder "Pullback along a surjective etale map reflects
  isomorphisms of bounded constructible pro-etale derived complexes"`: 8 hits,
  including ring-map Etale.respectsIso and scheme fpqc descent of isomorphisms.
  None concerns the stated pro-etale derived pullback and constructible complexes.
- `msearch.py ... loogle '"ReflectsIsomorphisms", "pullback"'`: 0 hits.
- `msearch.py ... leansearch "Derived pullback along a surjective etale scheme
  morphism reflects isomorphisms"`: 8 hits on scheme isomorphism descent,
  scheme pullback comparisons, and stability of etaleness; no exact statement.
- `msearch.py ... grep 'ReflectsIsomorphisms|isIso_of_isIso' AlgebraicGeometry/Sites`:
  1 hit, AffineEtale.lean:102, an unrelated coefficient-category assumption.
- `rg` of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and shared `lean/Sheaf`
  for etale isomorphism descent, etale reflection, and surjective etale keywords:
  no exact statement. The hits concern etale refinements, sheaf conservativity,
  and other local-to-global statements. In particular ConcentratedComplexShift
  includes a distinct single-degree concentration/descent statement, not this one.
- Search by the exact item id in upstream WeilConjectures, shared lean/Sheaf,
  and `dag/lean_names_upstream.json`: no hit. Search for the proposed declaration
  `isIso_of_surjective_etale_pullback` and `etaleIsoDescent` in these locations:
  no existing declaration.

Validation: `scompile.py Q126 lem-pur-etale-iso-descent` compiled the sandbox
and library forms cleanly, with no compiler diagnostics (2.1 s and 2.2 s).
The node comparison confirms that only `lean` changed, the stored signature is
verbatim from the file, and the module contains exactly one theorem and one sorry.
The prescribed `deliver2.py --no-push` is being run. The independent second
reader will supply their own reading; this report does not claim that review.

## Second reading by Q126

Statement list and correspondence:

- The fixed purity conventions and finite coefficient are rendered by `P :
  PurityFiniteSetting.{u}`. Its `P.field.k`, `P.coefficients.l`, `P.extension`,
  `P.level`, and `P.level_pos` supply exactly the fixed finite-field datum, prime,
  coefficient extension, and positive quotient level from the conventions. Verdict:
  present with no extra hypothesis.
- The two schemes over the fixed field are `U X : Over (Spec
  (CommRingCat.of P.field.k))`; their underlying schemes and structure maps are
  `U.left`, `X.left`, `U.hom`, and `X.hom`. Verdict: same objects as the node's
  separated finite-type `k`-schemes.
- Separated finite type is rendered by the three instance binders
  `[IsSeparated U.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]` and the
  corresponding three binders for `X.hom`. Verdict: both clauses of finite type
  occur for each scheme, with no properness, Noetherian, or smoothness assumption.
- The surjective étale morphism is `f : U ⟶ X` in `Over`, with
  `[Surjective f.left] [Etale f.left]`. Verdict: the `Over` morphism supplies the
  required map over `k`, and the two stated properties are exactly those on its
  underlying scheme morphism.
- The bounded constructible complexes are `M N` in
  `(intrinsicFiniteTorsionConstructible P.coefficients.l P.extension P.level
  P.level_pos X.left).FullSubcategory`. The dependency definition gives finite
  cohomological support and constructible pro-étale cohomology sheaves at the fixed
  finite coefficient ring. Verdict: this is the convention's bounded constructible
  category and adds no finite Tor-amplitude or étale-origin condition.
- The morphism is `φ : M ⟶ N`. Verdict: present in the same full subcategory.
- The pullback hypothesis is
  `hφ : IsIso ((@sfIntrinsicDerivedPullback P.Ring _
  (Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level
  P.level_pos) U.left X.left f.left).map φ.hom)`. Verdict: this is the recorded
  canonical finite-level derived inverse image `Lu^*` on the ambient pro-étale
  derived category, applied to the ambient map of `φ`; no arbitrary map or choice is
  introduced.
- The conclusion is `IsIso φ`. Verdict: it is invertibility in the full bounded
  constructible category, exactly the node's conclusion.

Source and edge-case review: the historical blueprint statement and the
current `main-20261015` statement both say that a surjective étale map of separated
finite-type `k`-schemes reflects isomorphisms of bounded constructible complexes after
`Lu^*`; they agree with the Lean signature. Empty schemes and empty covers are
allowed; identity and isomorphic maps are allowed; level one is allowed by
`P.level_pos`; zero and shifted complexes are allowed because constructibility only
requires finite support; and no characteristic, nonemptiness, Noetherian, or universe
equality is added. The site retains the recorded object universe `u+1` and morphism
universe `u`.

Searches: I reran `msearch.py`/LeanFinder for surjective étale pullback and intrinsic
finite-torsion constructibility, and searched the source and shared Lean trees for
the item id and proposed declaration. The upstream declaration
`AlgebraicGeometry.Etale.isIso_of_isIso_leftDerivedUpperStar_map_of_surjective`
exists, but it is an ambient small-étale derived-category theorem for arbitrary
coefficients and arbitrary schemes; it does not state this finite purity/pro-étale
constructible theorem, so it is not an exact existing match. No exact project or
Mathlib declaration was found.

Mismatches and repairs: none. The node copy remains statement-identical to the Lean
theorem signature, the module has one theorem with one postponed proof, and the
prescribed `scompile.py` check passed for the module and library forms.

Additional independent checks: Loogle query `"ReflectsIsomorphisms",
"DerivedCategory"` returned zero hits. Direct `rg` searches of Mathlib's
AlgebraicGeometry/Sites and CategoryTheory/Sites found generic sheaf and point
reflection results, not this canonical derived pullback theorem. I read the exact
upstream small-etale theorem above, not merely its name. Its site differs from the
recorded intrinsic pro-etale site, so a blueprint-id mention does not justify an
`existing: true` binding. This supplements the worker's search report.

I read the recorded statement-dependency nodes and the definitions of
`PurityFiniteSetting`, `intrinsicFiniteTorsionConstructible`,
`proEtaleDerivedCategory`, `finiteDerivedPullback`, and
`sfIntrinsicDerivedPullback`. In particular, `finiteDerivedPullback` is literally
the latter canonical functor at exponent `n+1`; the explicit `Finite` witness in
this theorem instantiates it at the already positive `P.level`. The definitions
introduce real data, and there are no new definition nodes or dependency modules
to audit. I also read Stacks proetale.tex's covering definition and etale-cover
lemma (0989/098B), more-morphisms.tex's etale-to-weakly-etale lemma (094X),
sites-modules.tex's localized ringed-site definition (04IX), homology.tex's exact
functor lemma (010N), and derived.tex's acyclic/localization lemma (05RT). None
adds a hidden hypothesis to this statement. The module docstring covers all five
DAG proof steps, and the theorem's only proof remains `sorry`. The level-zero case
is excluded by the source itself (`n >= 1`), not by a new Lean restriction. There
is no independent index family in this statement to constrain.

## Worker report

The module `Sheaf.CategoryTheory.RightAnodyneMonoCancellation` states
`SSet.rightAnodyneExtensions_mono_cancellation`, with one `sorry` and no other
new declarations or definitions. Only the item's `lean` field changes.

Read the target statement, source, statement dependencies, all five proof steps,
and proof dependencies. Read Cisinski, *Higher Categories and Homotopical Algebra*,
[Corollary 4.1.10](https://cisinski.app.uni-regensburg.de/CatLR.pdf), printed p. 140,
PDF page 155 (zero-based), online on 2026-10-17. It states precisely the cancellation
assertion for composable monomorphisms, with the first map right anodyne.
There is no extra fibrancy assumption. No statement correction or disputed assertion
is needed. No repair note exists for this item.

Clause-by-clause correspondence:

- Any fixed containing universe is the explicitly declared `universe u` and
  `{A B C : SSet.{u}}`. No universe equalities or size restrictions are added.
- The simplicial maps `f : A → B` and `g : B → C` are `(f : A ⟶ B) (g : B ⟶ C)`.
  These are Mathlib simplicial sets and natural transformations, as used by the
  recorded enhanced-diagram dependency.
- Degreewise injectivity of `f` is
  `(hf : ∀ n : SimplexCategoryᵒᵖ, Function.Injective (f.app n))`.
- Degreewise injectivity of `g` is
  `(hg : ∀ n : SimplexCategoryᵒᵖ, Function.Injective (g.app n))`.
  These quantifiers cover every finite ordinal, including degree zero. No
  categorical-monomorphism equivalence is assumed as an extra hypothesis.
- Right-anodyneness of the first map is `(hfRight : rightAnodyneExtensions f)`.
- The conclusion that `g` is right anodyne iff `g ∘ f` is right anodyne is
  `rightAnodyneExtensions g ↔ rightAnodyneExtensions (f ≫ g)`.
  Lean's categorical composition reads first `f`, then `g`.
- The final exclusion of Kan/quasicategory hypotheses is respected: there are no
  `KanComplex`, `Quasicategory`, inhabitedness, connectedness, or nonempty binders.

Dependency declarations read and used:

- `def-cbc-enhanced-diagrams-cones`: imported publicly via its recorded module
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`. Read its primitive convention
  (`SSet`, `stdSimplex`, `horn`, `Quasicategory`, `KanComplex`, internal hom) and
  the recorded declaration `SSet.Enhanced.coneCategory`, whose full signature is
  `noncomputable def coneCategory {K C : SSet.{u}} (F : K ⟶ C) : SSet.{u}`.
  Its docstring specifies the degreewise pullback and endpoint conditions. This
  theorem uses the dependency's underlying Mathlib simplicial objects/maps;
  it does not require a cone or a quasicategory structure.
- `def-coef-infinity-right-anodyne`: imported publicly via
  `Sheaf.CategoryTheory.RightAnodyne`, using exactly
  `SSet.rightAnodyneExtensions : MorphismProperty SSet.{u}`. Read the full
  definition and docstring: its infimum ranges over classes containing
  isomorphisms, horns with `0 < i`, pushouts, small transfinite compositions,
  and retracts. `i : Fin (n + 1)` enforces `i ≤ n`; for `n = 0` there is no
  positive index. No private copy of this class is introduced.

The already stated proof dependencies are imported nonpublicly:
`Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases` (reexports
`SSet.Enhanced.rightFibration`), `Sheaf.CategoryTheory.RightAnodyneProduct`
(`SSet.rightAnodyneExtensions_pushoutProduct`),
`Sheaf.CategoryTheory.RightFibrationExponentiation`
(`SSet.rightFibration_exponentiation`),
`Mathlib.CategoryTheory.Limits.HasLimits` (`CategoryTheory.Limits.colimit`), and
`Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations`
(`SSet.modelCategoryQuillen.I`, together with `MorphismProperty.rlp` for trivial
Kan fibrations). The genuine proof-only node
`lem-coef-right-anodyne-lifting-characterization` has no recorded declaration
and is not imported or restated. The target signature does not require that
lemma; its five-step future proof in the docstring explicitly cites it.

Edge cases checked before writing: identity first map reduces the equivalence
to the same right-anodyne property, up to identity composition; identity second
map reduces to the assumed right-anodyneness of `f`. Empty simplicial sets
are permitted, as are all-empty identity chains; no vertex is chosen in the
statement. A nonempty target with empty source is neither silently asserted
right anodyne nor excluded by an added binder. Degree zero is tested by the
injectivity quantifier. Arbitrary non-Kan and non-quasicategory objects are
permitted. The proof docstring retains the final endpoint `{1}` in the right
horn, and the correcting homotopy restricts at endpoint zero.

Searches actually run on 2026-10-17:

- `msearch.py ... leanfinder "Right anodyne inclusions of simplicial sets satisfy
  right cancellation among monomorphisms"`: eight hits, including
  `SSet.modelCategoryQuillen.J_le_monomorphisms`, stability of monomorphisms,
  all-horn `J`, boundary `I`, and the cofibration characterization. None states
  cancellation for the one-sided right-horn class.
- `msearch.py ... loogle '"anodyne", "cancel"'`: zero hits.
- `msearch.py ... grep 'rightAnodyne|right_anodyne|mono.*cancellation'
  AlgebraicTopology`: zero hits.
- `msearch.py ... leansearch "For degreewise injective simplicial maps f and g,
  if f is right anodyne, then g is right anodyne if and only if their composite
  is right anodyne"`: eight hits concerning simplicial/cosimplicial composition,
  generic lifting composition, and degreewise-epi complexes; no exact match.
- `rg` of the source `WeilConjectures` and `dag/lean_names_upstream.json` for
  the node id and `rightAnodyne|right_anodyne`: zero hits.
- `rg` of `lean/Sheaf` for right-anodyne cancellation names: zero hits. Broader
  right-anodyne and cancellation searches find the existing definition,
  pushout-product and join results, plus unrelated spine/inner-horn cancellation;
  none is this theorem.
- Read the returned Mathlib candidates in
  `AlgebraicTopology/SimplicialSet/CategoryWithFibrations.lean:35–106` and
  `AnodyneExtensions/Basic.lean:63–105`: they use all horns, so do not provide
  an exact match for this node.

Validation: `scompile.py Q24 lem-coef-right-anodyne-mono-cancellation` compiled
the delivered file as both sandbox and library module with no errors or warnings.
The Lean signature is copied verbatim into `lean.statement`; all universes and
variables are explicit, and every Lean line is at most 100 characters.

## Second reading by Q24

Independent second reader, 2026-10-17. I opened the sandbox node and module,
the two statement-dependency node records and their source modules, and all
recorded proof-dependency interfaces. No repair note exists for this item.
There are no new nodes, dependency repairs, or statement corrections in this
packet. I found no mathematical or Lean-signature mismatch, so I preserved the
module and node record and added this independent reading only.

The actual source is Cisinski rather than Stacks: the node explicitly records
that no Stacks tag states this one-sided cancellation theorem. I independently
opened [Cisinski's book](https://cisinski.app.uni-regensburg.de/CatLR.pdf), read
Corollary 4.1.10 on printed p. 140 (PDF page 155, zero-based), and checked the
surrounding Section 4.1. Its hypotheses are composable monomorphisms with the
first map right anodyne, and its conclusion is exactly the displayed equivalence.
The surrounding discussion permits arbitrary simplicial sets; paragraph 4.1.1
explicitly extends the setting beyond quasicategories. There is no hidden Kan,
quasicategory, nonempty, finite, or coefficient hypothesis to restore.

My list of the node's objects, hypotheses, and conclusions, matched with Lean:

1. A fixed arbitrary containing universe: `universe u` and
   `{A B C : SSet.{u}}`. Verdict: exact. I read Mathlib's
   `AlgebraicTopology/SimplicialSet/Basic.lean:36`: `SSet` is
   `SimplicialObject (Type u)`, so these are actual simplicial sets, with no
   extra structure. One common universe is precisely the node's convention.
2. Three simplicial sets A, B, C: the same implicit binders. Verdict: exact.
   The enhanced-diagrams dependency's module explicitly uses these Mathlib
   primitives. I also opened its recorded
   `SSet.Enhanced.coneCategory {K C : SSet.{u}} (F : K ⟶ C) : SSet.{u}`
   and its defining comma construction: this theorem neither substitutes a
   cone category for A, B, C nor requires any cone data.
3. Composable simplicial maps f:A to B and g:B to C:
   `(f : A ⟶ B) (g : B ⟶ C)`. Verdict: exact natural transformations in the
   simplicial-set category. Their order is the node's order.
4. Degreewise injectivity of f:
   `(hf : ∀ n : SimplexCategoryᵒᵖ, Function.Injective (f.app n))`.
   Verdict: exact; the quantifier includes every degree, including zero.
   Although right-anodyneness also forces monicity mathematically, this binder
   is explicitly present in the node and source and was correctly retained.
5. Degreewise injectivity of g:
   `(hg : ∀ n : SimplexCategoryᵒᵖ, Function.Injective (g.app n))`.
   Verdict: exact, without any extra categorical instance assumption.
6. Right-anodyneness of the first map:
   `(hfRight : rightAnodyneExtensions f)`. Verdict: exact reuse of
   `SSet.rightAnodyneExtensions` from `Sheaf.CategoryTheory.RightAnodyne`.
   I read its full definition against `def-coef-infinity-right-anodyne`:
   it is the infimum of morphism properties containing isomorphisms and horns
   `(horn n i).ι` with `i : Fin (n + 1)` and `0 < i`, and closed under
   pushouts, small transfinite compositions, and retracts. Positive i implies
   n is positive; the upper bound i ≤ n is built into Fin. No private copy,
   all-horn class, inner-horn class, or arbitrary replacement predicate occurs.
7. Conclusion, both directions:
   `rightAnodyneExtensions g ↔ rightAnodyneExtensions (f ≫ g)`.
   Verdict: exact. Mathlib's `SSet.comp_app` confirms that `f ≫ g` is g after f.
   The left side is the second map; the right side is the composite. The
   quantifiers introduce A, B, C, then f, g, then the three assumptions;
   there are no extra quantified witnesses or extra conclusions.
8. No quasicategory or Kan hypotheses on A, B, C: there are no such binders or
   section variables, and `autoImplicit false` is set. Verdict: exact. The
   imported modules do not add assumptions to this theorem's signature.

Edge cases: empty simplicial sets are admitted by `SSet` with no inhabitedness
instance; the all-empty identity chain and all identity maps are covered.
With f the identity the two conclusions agree; with g the identity the
composite property is the assumed property of f. A map from the empty set
into a nonempty set is not declared right anodyne merely by being injective:
`hfRight` remains a real hypothesis. Dimension zero is included in both
injectivity hypotheses, while no zero-dimensional right horn is generated.
In dimension one the positive horn is Lambda[1,1] = {1}, matching endpoint one
in the proof, rather than endpoint zero. No index set, scheme, coefficient
ring, or characteristic parameter is present in this statement; their listed
edge cases add no hypotheses. The arbitrary u includes the smallest universe
as well as larger containing universes, without an independent test universe
or equality constraint. Arbitrary non-Kan simplicial sets remain in scope.

I checked the proof docstring against each of the node's five steps: lifting
characterization; composition closure and an initial diagonal for gf;
exponentiation and a boundary lift giving the homotopy; the endpoint-one
pushout product extending it; and the final lifting characterization for g.
In particular the extension at endpoint zero corrects the first diagonal.
I read `SSet.Enhanced.rightFibration` in `InfinityFibrations.lean`, reexported
by the currently recorded `InfinityFibrationsOverSimplicialBases` module: it
has exactly the positive-index horn lifting condition and no quasicategory
instances. I read `rightFibration_exponentiation`: q and i are arbitrary
simplicial maps, with the positive-index lifting hypothesis and right-anodyne
hypothesis, and the canonical relative internal-hom map satisfies `I.rlp`.
I read `rightAnodyneExtensions_pushoutProduct`: both maps have Mono instances,
and its canonical pushout-product map is right anodyne. Degreewise injectivity
in this theorem supplies those monomorphisms at proof time. I also checked
Mathlib `modelCategoryQuillen.I` (all boundary inclusions, including dimension
zero). Thus the nonpublic proof imports match their recorded purposes. The
lifting-characterization node currently has neither a Lean record nor a
Mathlib match, so no import can yet be supplied for it; it is cited explicitly
in the docstring and is not restated. No statement dependency is missing.

Independent duplicate searches run with `msearch.py` for this item:

- LeanFinder: `Cancel a final simplicial inclusion from a composite of
  monomorphisms using positive-index horns`. Eight hits: horn face inclusion
  identities, horn colimit identities, and Kan horn filling. None states
  cancellation for the weakly saturated positive-index class.
- Loogle: `"anodyne", "comp"`. Ten hits: ordinary/inner-anodyne transfinite
  closure and regular-pairing results. I opened Mathlib
  `AnodyneExtensions/Basic.lean:63-130` and
  `CategoryWithFibrations.lean:35-106`; ordinary anodyne extensions use all
  horns, whereas this node concerns only positive-index horns.
- Grep service: `anodyne.*cancel|cancel.*anodyne|rightAnodyne|right_anodyne`.
  Zero hits.
- LeanSearch: `A composite of inclusions and its first factor are final horn
  extensions; the second inclusion is then a final horn extension`.
  Eight hits, including `CategoryTheory.Functor.final_comp`, horn identities,
  and the all-horn `modelCategoryQuillen.J`. Ordinary categorical finality is
  not this simplicial morphism property; none is an exact match.
- Direct `rg` on source `WeilConjectures`, Mathlib's simplicial-set sources,
  project `lean/Sheaf`, and `dag/lean_names_upstream.json`, using
  `anodyne.*cancel|cancel.*anodyne|rightAnodyne|right_anodyne` and the
  alternative words `final.*extension|finalExtensions`. No existing theorem
  states this cancellation. The project hits are the shared definition,
  products, joins, terminal-vertex and factorization results; those are
  different statements. I also read ordinary `Mono.right_cancellation` in
  Mathlib's category basic module: it cancels equalities of morphisms and
  cannot replace this theorem.

H5/H6/H8/H9 checks: no definition is introduced, and the sole theorem body
is `by sorry`; nothing is proved. The module and declaration docstrings both
name the source and blueprint id. The proof docstring retains all five steps.
All Lean lines fit 100 columns; no local notation or instance, private helper,
let-bound statement, unbound universe, or implicit variable is introduced.
An exact text comparison verified that `lean.statement` is verbatim the file's
signature before `:= by`. The only changes made by this reader are this
report section; no source correction or citer audit is necessary.

Second-reader validation: the prescribed `scompile.py Q24
lem-coef-right-anodyne-mono-cancellation
lean/Sheaf/CategoryTheory/RightAnodyneMonoCancellation.lean` completed cleanly
for both its sandbox form (1.4 s) and library form (1.9 s), with no warnings.
The node comparison also confirms that only its `lean` field differs from
the read-only base. All delivered Lean files (one) were compiled.

## Worker report

The module `Sheaf.Paper.EtaleHomFiniteTorAmplitude` states
`WeilConjectures.finiteCoefficient_derivedHom_ctf_etale`, with one `sorry` and no new
construction or proof. It retains the arbitrary finite-type scheme, without a
separatedness assumption, and includes both the general and conditional sharp interval.
No node statement, dependencies, proof, or other node field is changed: only `lean`.

Hypothesis and clause correspondence:

- The global finite-field datum is `(D : FiniteFieldDatum.{u})`; its fields include the
  prime characteristic, positive finite-field exponent, finite base field of the specified
  cardinality, and chosen algebraic closure `D.k`.
- The coefficient prime and characteristic restriction are `(l : ℕ) [Fact l.Prime]`
  and `(_hl : l ≠ D.p)`.
- The finite extension is `(E : Type u) [Field E] [Algebra (Padic l) E]`
  `[FiniteDimensional (Padic l) E]`. The recorded quotient
  `Padic.coefficientExtensionRing l E n` uses the recorded valuation ring and chosen
  uniformizer. `(n : ℕ) (hn : 1 ≤ n)` includes exactly the positive integer levels.
- The chosen coefficient universe is `ULift.{u + 1, u}` of that quotient. This is the
  canonical ring lift required by the recorded étale module-sheaf category; no coefficient
  ring or scheme is replaced mathematically.
- The finite-type `k`-scheme is `(X : Scheme.{u}) [X.Over (Spec (.of D.k))]`, with
  `[LocallyOfFiniteType (X ↘ Spec (.of D.k))]` and
  `[QuasiCompact (X ↘ Spec (.of D.k))]`.
- The dimension parameter is `(m : ℕ)` and the bound is
  `topologicalKrullDim X ≤ (m : WithBot ℕ∞)`, the topological Krull dimension, including
  dimension minus infinity for the empty scheme.
- `(a b c d : ℤ) (_hab : a ≤ b) (_hcd : c ≤ d)` gives the ordered integer intervals.
- `K M : Etale.DerivedCategoryModule (ULift ... (Padic.coefficientExtensionRing ...)) X`
  are complexes on the small étale site with constant coefficients. The assumptions
  `_hK` and `_hM` use `finiteTorConstructibleEtale`, precisely the recorded étale
  bounded constructible plus finite-Tor predicate.
- `_hKt` and `_hMt` use `Etale.DerivedCategory.hasTorAmplitudeIn` at `[a,b]` and `[c,d]`.
  The definition quantifies over every module sheaf in degree zero, not just constructible
  or étale-origin tests.
- Every occurrence of the output is
  `((Etale.derivedHom (ModuleCat ...) X).obj (op K)).obj M`, the existing étale derived
  internal Hom in this category.
- The first conjunct asserts `finiteTorConstructibleEtale ...` of the output. The second
  conjunct asserts Tor amplitude in
  `(c - b - 2 * (m : ℤ))` through `(d - a + 2 * (m : ℤ))`.
- The third conjunct is the implication `Etale.DerivedCategory.IsSitePerfect K → ...`
  asserting the sharper interval `(c - b)` through `(d - a)`. Perfectness is not assumed
  in the general branch. The existing predicate uses an actual étale cover, bounded local
  complexes, and degreewise retracts of constant finite free sheaves, with bounds and ranks
  allowed to vary locally. No global projectivity or dualizability hypothesis is substituted.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and its instance fields.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its public construction module:
  `Padic.coefficientExtensionRing`, `coefficientExtensionIntegers`,
  `coefficientExtensionUniformizer`, `coefficientExtensionIdeal`, and
  `finite_coefficientExtensionRing`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology` and the étale site.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `Etale.DerivedCategory.isBoundedConstructible`, using the recorded
  `Scheme.IsConstructibleEtaleModuleSheaf` condition.
- `Sheaf.Paper.FiniteTorAmplitudeSites`:
  `WeilConjectures.finiteTorConstructibleEtale`. The dependency node's latest
  `FiniteTorAmplitudeProEtaleModule` explicitly preserves and publicly imports this
  unchanged étale presentation; the statement uses that presentation directly.
- `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `Etale.DerivedCategory.hasTorAmplitudeIn` and `Etale.DerivedCategoryModule`.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses`, its comparison and representative
  characterization, publicly imported as the recorded ringed-site construction. For
  fixed-coefficient module sheaves the existing category-specific presentation is
  `Etale.derivedHom`, from `WeilConjectures.SixFunctors.Etale.Derived.Hom`: the closed
  derived tensor right adjoint. This is the same derived internal Hom notion, rather
  than a private or newly assumed bifunctor.
- `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`:
  `SheafOfModules.IsPerfectOnRingedSiteOfUniverses` and the finite-free retract packages,
  imported as recorded. The equivalent existing fixed-coefficient étale presentation
  `Etale.DerivedCategory.IsSitePerfect` is used directly from
  `WeilConjectures.SixFunctors.Etale.Derived.Perfect.SitePerfect`. Its full live source
  was read using `scompile.py --source` because it is absent from the older local checkout.

Every stated proof dependency module is imported without `public`; the not-yet-stated
`lem-sf-site-perfect-tor-window` is not imported or restated. Its anticipated use is
retained in the nine-step theorem docstring. The docstring follows all nine node proof
steps, including the open-direct-image kernel argument realizing the finiteness unit,
not a geometric-stalk/internal-Hom interchange.

Sources read: the target node and all its statement-dependency records and declarations;
its archived blueprint statement and expanded proof; the current main-20261015 statement
at `sec-smooth-purity/sk-lem-sp-tower/thm-sf-hom-ctf.md`, whose text agrees; the separated
corollary `Sheaf.Paper.FiniteConstructibleHom`; the upstream stability theorem signatures
and their constructibility definitions; the existing étale site-perfect interface.
There is no maintenance repair note for this item.

Edge cases checked: the empty scheme is admitted (Krull dimension minus infinity, no
nonemptiness binder); `m = 0` specializes the general interval to the sharp one; positive
level `n = 1` is included and `n = 0` is excluded as in the statement; zero complexes and
rank-zero local free summands remain admitted; intervals may have negative or equal
endpoints; arbitrary degree-zero module tests remain in the Tor predicate. There is no
separatedness, smoothness, nonempty-site, finite-rank global model, or additional
coefficient-invertibility hypothesis. The prime-to-characteristic condition is retained.
The conclusion intervals are ordered for the given hypotheses; the formula uses signed
integer subtraction, not truncated natural subtraction. No mathematical statement fault
or STATEMENT-DISPUTED issue was found.

Searches made:

- `msearch.py Q04 thm-sf-hom-ctf leanfinder` with “Derived internal Hom of bounded
  constructible etale complexes with finite Tor amplitude has amplitude c minus b minus
  twice dimension to d minus a plus twice dimension”: eight generic derived category
  truncation/bound/fraction hits; no constructible internal-Hom preservation theorem.
- `msearch.py ... loogle` with
  `AlgebraicGeometry.Etale.derivedHom, AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn`:
  zero hits; identifier not indexed by Mathlib Loogle.
- `msearch.py ... grep` with
  `torAmplitudeIn_derivedHom|boundedConstructible_derivedHom|IsSitePerfect`: zero Mathlib hits.
- `msearch.py ... leansearch` with “Internal Hom of bounded constructible etale complexes
  of finite Tor amplitude preserves bounded constructibility”: eight generic closed
  internal-Hom, internally-projective and complex-size hits; no exact theorem.
- `rg` over the project's `lean/Sheaf` and upstream `WeilConjectures` for `derivedHom`,
  `finiteTorConstructibleEtale`, `IsSitePerfect`, `isBoundedConstructible`, and the target id:
  found the recorded notions and related separated/pro-étale statements. Upstream
  `boundedConstructible_derivedHom` and `torAmplitudeIn_derivedHom` use the distinct
  `boundedConstructible` convention based on finitely generated geometric stalks;
  they do not give this node's exact recorded finite-constant-value constructibility
  predicate. The sharp upstream result assumes dualizability. Hence no exact single
  declaration of this entire node is recorded as existing.
- Exact proposed-name search in Mathlib, upstream, and the side project found no
  `WeilConjectures.finiteCoefficient_derivedHom_ctf_etale` collision. The target-id search
  of `dag/lean_names_upstream.json` gave no binding.

## Compilation and dry run

The initial wrapper attempt exposed a duplicate declaration in the forced side overlay:
the finite-coefficient pro-etale `Defs` file redeclared
`AlgebraicGeometry.ProEt.overPullbackId` already provided by its imported published
module. A sandbox-local overlay copy removes only that duplicate re-export declaration;
no launcher, live library, or source file was edited. The target and its recursive
statement-side modules then compile cleanly with `scompile.py` (the target has the one
expected `sorry` warning suppressed by the project options). The required
`deliver2.py Q04 thm-sf-hom-ctf --no-push` dry run completed with `OK`; preflight passed
and staged exactly this report, node file, and Lean module. The second-reading section is
left for the independent reader as required by the dry-run tool.


## Second reading by Q04

I independently opened the base node, the sandbox node and complete Lean module, the
archived source theorem and its unit/chapter context, every statement-dependency node,
and the declarations used below. This is a statement-only delivery: one theorem, one
`sorry`, no new definition nodes, no dependency modules, and no `statement_change`.
The node copy differs from the base only in `lean`. No mathematical or Lean repair was
needed; I have left the correct module and signature unchanged.

Object, hypothesis and conclusion checklist, read first from the node:

1. Global finite-field datum, with algebraic closure k of a field of cardinality p^a:
   `(D : FiniteFieldDatum.{u})`. I read `FiniteFieldFiber.lean`: the structure has prime
   p, positive a, q = p^a, finite field k₀ of cardinality q, and an algebraic closure k
   with its algebra structure. Thus the field and characteristic are those of the node;
   an arbitrary algebraically closed field was not substituted. Verdict: exact.
2. Prime l distinct from p: `(l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)`.
   Neither characteristic equality nor an extra exponent hypothesis is hidden in the
   theorem's binders. Verdict: exact.
3. Finite extension E of Q_l: `(E : Type u) [Field E] [Algebra (Padic l) E]`
   `[FiniteDimensional (Padic l) E]`. I read the coefficient construction and finiteness
   module. `coefficientExtensionRing l E n` is the quotient of the recorded valuation
   subring by the nth power of the ideal generated by its chosen uniformizer.
   `(n : ℕ) (hn : 1 ≤ n)` is precisely the positive integer level. Verdict: exact.
4. Constant coefficient ring A_X on the small etale site: the arguments use
   `ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)` in
   `Etale.DerivedCategoryModule ... X`. I read the abbreviation in `Coefficients.lean`
   and `Scheme.smallEtaleTopology` in Mathlib: this is the derived category of
   module-valued sheaves on X.Etale, with its jointly surjective etale covers.
   The ULift changes the carrier universe by its canonical ring lift; it does not
   replace the coefficient ring or restrict the class of module sheaves. Verdict: exact.
5. Finite-type k-scheme X: `(X : Scheme.{u}) [X.Over (Spec (.of D.k))]` with
   `[LocallyOfFiniteType (X ↘ Spec (.of D.k))]` and
   `[QuasiCompact (X ↘ Spec (.of D.k))]`. I read both Mathlib class definitions and
   the dependency's recorded finite-type convention. Their conjunction is finite type.
   No separatedness, smoothness, Noetherian, nonempty or admissibility assumption is
   imposed. The source unit explicitly makes the general theorem unconditional in
   admissibility. Verdict: exact.
6. Nonnegative dimension parameter and topological bound: `(m : ℕ)` and
   `_hm : topologicalKrullDim X ≤ (m : WithBot ℕ∞)`. This uses the recorded dimension,
   with bottom for the empty space, rather than an affine-ring dimension. Verdict: exact.
7. Ordered integer intervals: `(a b c d : ℤ) (_hab : a ≤ b) (_hcd : c ≤ d)`.
   These endpoints precede the objects and their Tor hypotheses; all subtraction in
   the conclusion is integer subtraction. Verdict: exact.
8. K and M in D^b_ctf: the two objects have exactly the category in item 4 and
   `_hK`, `_hM` assert `finiteTorConstructibleEtale l E n hn X`.
   I read `FiniteTorAmplitudeSites.lean`, its public preservation in the latest
   `FiniteTorAmplitudeProEtaleModule.lean`, and `BoundedConstructibleComplexes.lean`.
   The predicate conjoins the recorded finite-constant-value constructibility of
   every cohomology sheaf and boundedness with existence of an ordered finite Tor
   interval. It is the etale version requested by this node, not the pro-etale
   fixed-scalar predicate or the alternative upstream geometric-stalk predicate.
   Verdict: exact.
9. Specified Tor intervals of K and M: `_hKt` and `_hMt` apply
   `Etale.DerivedCategory.hasTorAmplitudeIn` at a,b and c,d. I read its full definition
   in `Coefficients.lean`: for every module sheaf F, `K` tensor the degree-zero
   `singleFunctor` image of F has zero cohomology outside the interval. Tests are not
   limited to constructible, finite, flat or constant sheaves. Verdict: exact.
10. Derived internal Hom object: all three output expressions are
    `((Etale.derivedHom (ModuleCat ...) X).obj (op K)).obj M`.
    I read `Etale/Derived/Hom.lean`: this is the internal right adjoint to the existing
    derived tensor, with the contravariant K argument and covariant M argument in the
    correct positions. I also read the dependency's generalized Hom-complex
    localization and representative comparison. The constant-coefficient module-sheaf
    presentation uses the existing etale RHom, not an arbitrary bifunctor or a private
    definition. Verdict: exact.
11. Membership conclusion: the first conjunct is `finiteTorConstructibleEtale` of
    precisely that RHom object. It retains bounded constructibility and finite Tor
    amplitude, not merely bounded cohomology or finite-dimensional stalks. Verdict: exact.
12. General numerical bound: the second conjunct applies the same Tor predicate to
    precisely that object at `c - b - 2 * (m : ℤ)` and `d - a + 2 * (m : ℤ)`.
    Both signs and the dimension factor agree with the node and archived source.
    Verdict: exact.
13. Conditional sharper bound: the final conjunct is
    `Etale.DerivedCategory.IsSitePerfect K → hasTorAmplitudeIn ... (c - b) (d - a)`
    of the same RHom. I read the actual `SitePerfect.lean` definition, not just its
    docstring: an etale cover, a bounded cochain complex on each member, degreewise
    retracts of constant `(Fin r → A)` sheaves, and an isomorphism to restricted K.
    Bounds and ranks vary locally, r may be zero, and no chain-map splitting or
    global projectivity is required. Pullback to a member is the exact etale restriction.
    The general-site package dependency has the same local finite-free-retract notion.
    This condition is an implication, not an assumption on the general branch.
    Verdict: exact.

Edge cases: the empty scheme is admitted, with dimension bottom and no Nonempty binder;
an empty covering family is not ruled out. There is no external index set to restrict.
Zero objects and rank-zero free sheaves are admitted. The case m = 0 gives exactly the
sharp numerical endpoints even in the general branch. Level n = 1 is included; n = 0
is excluded exactly as in the source. Equal or negative integer endpoints are admitted.
The prime-to-characteristic condition is explicit, including characteristic 2 whenever
l differs from it. The module explicitly binds its sole universe u and all variables
under `autoImplicit false`; the etale site and coefficient/module universes are the
existing u/u+1 convention and use the explicit canonical coefficient lift, with no
site-object/morphism universe equality added as a mathematical hypothesis.

Independent searches, with different wording from the first reader:

- `msearch.py Q04 thm-sf-hom-ctf leanfinder` queried "Perfect constructible sheaf
  complexes internal Hom has finite Tor dimension with bounds shifted by twice the
  dimension of a scheme": eight hits (derived t-structure bounds, a condensed closed
  structure and projective Tor vanishing); no exact theorem.
- `msearch.py ... loogle '"derivedHom"'`: zero hits.
- `msearch.py ... leansearch` queried "Etale sheaf derived Hom preserves constructible
  complexes of finite Tor dimension over finite local coefficients": eight generic
  sheaf-Hom, module sheafification and etale algebra hits; no exact theorem.
- `msearch.py ... grep 'internalHom.*Tor|derivedHom.*construct|torAmplitude.*Hom'`:
  five Day-convolution internal-Hom hits, no theorem of this node.
- Direct `rg` in Mathlib, upstream `WeilConjectures`, and the project's `lean/Sheaf`
  found the upstream `boundedConstructible_derivedHom`, `torAmplitudeIn_derivedHom`,
  `torAmplitudeIn_derivedHom_of_isDualizable`, and the pro-etale perfect-Hom theorem.
  I opened the upstream `Stability/DirectImage.lean` signatures and `Stability/Matrix.lean`
  packaging, then `ConstructibleSheaf/Defs.lean` and the project's recorded
  `IsConstructibleEtaleModuleSheaf`. The upstream results use the other constructibility
  predicate, and the sharp result uses dualizability. The pro-etale theorem has another
  ambient category. None states this entire node with its recorded predicates; the
  existing notions RHom and site-perfectness are reused. No H4 duplicate was found.

H5/H6/H8/H9 checks: the delivery has no definition data and no proof other than `sorry`.
The source/blueprint docstrings are present and the theorem docstring follows all nine
node proof steps: slice comparison, finite-affine reduction, restrictions of flat
models, separated duality, finite open-direct-image kernel descent, prescribed perfect
window, Hom complex, flatness and endpoint computation, and final site-local descent.
Every already-stated proof dependency is imported; the not-yet-stated window lemma is
not copied or proved here. There are no private or file-local notions and no lines
longer than 100 characters. I checked that `lean.statement` is verbatim the theorem
signature before `:= by`. No statement correction or citer audit is needed.

Validation: I ran the required `scompile.py Q04 thm-sf-hom-ctf` on the sole delivered
module with the current default wrapper and overlay, without an override environment.
Both its sandbox and library-path checks exited zero with no diagnostics (14.5 s and
9.0 s). Thus this reading does not rely on the earlier sandbox-local overlay adjustment
mentioned in the worker report. Only this report was changed by the second reading.

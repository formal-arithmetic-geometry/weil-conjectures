## Worker report

The module `Sheaf.Paper.FiniteConstructibleHom` states the two site cases of
`cor-weil-finite-constructible-hom`, using two named theorems with `sorry` proofs:
`WeilConjectures.finite_constructible_derivedHom_etale` and
`WeilConjectures.finite_constructible_derivedHom_proEtale`.
No definitions, nodes, dependency repairs or statement corrections are added.
The item JSON changes only in `lean`.

Source read: the original blueprint file in the launcher literature cache,
`sec-six-functors/sk-prop-sf-biduality-general/cor-weil-finite-constructible-hom.md`,
order 2138. Its etale/pro-etale assertion and the two-duality interval computation agree
with the expanded current DAG statement and proof. Each theorem's docstring gives the
applicable proof steps and names all proof inputs used by that site argument.

### Hypotheses and clauses

Both declarations bind all their variables explicitly and set `autoImplicit false`.
They have the following common hypotheses, with exactly the same coefficient ring:

| Node text | Lean rendering |
| --- | --- |
| Global finite-field datum, k the fixed algebraic closure | `D : FiniteFieldDatum.{u}` and `D.k`; its fields specify p prime, a positive, q = p^a, the q-element field and its algebraic closure |
| Prime l different from p | `(l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)` |
| Finite extension E/Q_l | `(E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]` |
| Valuation ring, chosen uniformizer, A = O_E/varpi_E^n | `Padic.coefficientExtensionRing l E n`, the recorded quotient construction using `coefficientExtensionIntegers`, `coefficientExtensionUniformizer` and `coefficientExtensionIdeal` |
| Integer n at least 1 | `(n : ℕ) (hn : 1 ≤ n)` |
| X a k-scheme | `(X : Scheme.{u}) [X.Over (Spec (.of D.k))]` |
| X separated | `[IsSeparated (X ↘ Spec (.of D.k))]` |
| X of finite type | `[LocallyOfFiniteType (X ↘ Spec (.of D.k))]` and `[QuasiCompact (X ↘ Spec (.of D.k))]` |
| d nonnegative, dimension at most d | `(d : ℕ)` and `_hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)` |
| Ordered intervals [a,b] and [c,e] | `(a b c e : ℤ) (_hab : a ≤ b) (_hce : c ≤ e)` |

Etale case:

* `K L : Etale.DerivedCategoryModule (ULift.{u+1,u} A) X` are objects on the recorded
  small etale site, in the established `Sheaf ... (ModuleCat.{u+1} ...)` encoding.
  The universe lift changes no scalars: `Equiv.ulift` is the canonical scalar identification.
* `_hK` and `_hL` use the dependency's exact
  `Etale.DerivedCategory.isBoundedConstructible`, not the upstream alternative predicate
  `boundedConstructible`. The explicit `Finite.of_equiv` argument transports
  `Padic.finite_coefficientExtensionRing l E n hn` to the lifted scalar ring; no added
  finite-ring hypothesis or instance choice is required.
* `_hKt` and `_hLt` are `Etale.DerivedCategory.torAmplitudeIn` in the two specified
  intervals. This definition quantifies over every module sheaf in degree zero and tests
  derived tensor cohomology outside the interval. These hypotheses together with bounded
  constructibility express precisely membership in D^b_ctf with those intervals.
* The internal Hom is the existing `Etale.derivedHom` on that same module-sheaf derived
  category. It is the right adjoint to derived tensor, hence the derived internal Hom in
  this coefficient encoding, rather than an arbitrary bifunctor or global derived Hom.
* The conclusion's first conjunct is the same recorded bounded-constructibility predicate
  applied to that internal Hom. Its second conjunct is Tor amplitude in
  `(c - b - 2 * (d : ℤ), e - a + 2 * (d : ℤ))`.
  This also supplies finite Tor amplitude. For an arbitrary pair in D^b_ctf, choose its
  two ordered finite Tor intervals and apply the theorem; thus the initial unbounded-in-
  parameters closure assertion is included, not lost by giving the quantitative form.

Pro-etale case:

* `K L : proEtaleDerivedCategory X A` are objects in the recorded derived category of
  modules over the constant commutative ring sheaf on the original small pro-etale site.
* `_hK` and `_hL` use `finiteTorConstructible l E n hn X`, the dependency's conjunction
  of `intrinsicFiniteTorsionConstructible` and `HasFiniteProEtaleTorAmplitude`.
  It is the recorded intrinsic bounded-cohomology/finite-stratification condition.
* `_hKt` and `_hLt` use `HasProEtaleTorAmplitude X A` for the precise original intervals.
  This quantifies over every sheaf in degree zero and all K-flat representatives, so it
  specifies the actual derived tensor test independently of any resolution choice.
* Both conclusions concern exactly
  `(derivedInternalHomOfUniverses.{u+1,u,u} (ProEt.topology X)
  (proEtaleConstantRing X A)).obj (op K,L)`.
  This is the dependency's Hom-complex/K-injective localization, with site-object universe
  u+1, site-morphism universe u and module/scalar universe u+1. The chosen derived category
  is definitionally the standard one used by `proEtaleDerivedCategory`.
* The first conjunct puts that object in the same `finiteTorConstructible` predicate;
  the second supplies precisely `[c-b-2d,e-a+2d]` via `HasProEtaleTorAmplitude`.
  Every pair in the finite-Tor subcategory has some ordered intervals, so the universal
  membership assertion is again covered as well as the precise quantitative bound.

No properness, smoothness, site-perfectness, dualizability, nonemptiness or
compactification hypothesis has been added. There is no extra field, prime or coefficient
presentation assumption.

### Dependency declarations used

All statement-dependency records and their actual declaration signatures/docstrings were
read. Their interfaces are usable without any repairs.

* `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its public coefficient module:
  `Padic.coefficientExtensionRing`, its valuation/uniformizer/ideal constructions, and
  `Padic.finite_coefficientExtensionRing`.
* `Mathlib.AlgebraicGeometry.Morphisms.Proper` and its separated import:
  `AlgebraicGeometry.IsSeparated`. Properness itself is not assumed.
* `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and its quasi-compact import:
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
* `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
* `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.Etale`, `Scheme.smallEtaleTopology`.
* `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: `Scheme.proEtaleDerivedCategory`.
* `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `Etale.DerivedCategory.isBoundedConstructible`, on `Etale.DerivedCategoryModule`.
* `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `Scheme.intrinsicFiniteTorsionConstructible`, through the finite-Tor predicate.
* `Sheaf.Paper.FiniteTorAmplitude`: `WeilConjectures.finiteTorConstructible`, using
  `Scheme.HasFiniteProEtaleTorAmplitude` and `Scheme.HasProEtaleTorAmplitude` from
  `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude`.
* `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses` for the pro-etale ringed-site encoding.
  The etale coefficient-category encoding uses the existing
  `Etale.derivedHom` of `WeilConjectures.SixFunctors.Etale.Derived.Hom`, and the existing
  `Etale.DerivedCategory.torAmplitudeIn` of the sibling `TorAmplitude` module.

The stated proof dependencies `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`
and `Sheaf.Paper.ProEtaleConstructibleOrigin` are ordinary imports. The other five
proof dependencies have no Lean record in the current DAG and therefore supply no
additional recorded module to import; they are not needed to type either statement.

### Edge cases checked

* Empty X: no nonempty assumption; its Krull dimension is bottom and hence at most every d.
  The recorded constructibility predicates allow the empty scheme.
* d = 0: bounds specialize literally to `[c-b,e-a]`; no division or positive-dimensional
  restriction occurs.
* a = b or c = e, and negative endpoints: all endpoints are integers, and equality is allowed.
* Zero K or L: retained; a zero object can satisfy every ordered Tor interval.
* n = 1 is included; n = 0 is excluded exactly as in the source.
* The stated interval is ordered because
  `(e-a+2d) - (c-b-2d) = (e-c) + (b-a) + 4d ≥ 0`.
* Arbitrary E and scheme sizes can be placed in one common universe u; the prescribed
  pro-etale site still has object universe u+1 and morphism universe u. No equality of
  those two site universes was imposed.
* `l ≠ D.p` remains explicit; the datum determines characteristic p via its q-element
  base field and algebraic closure. No invertibility hypothesis was substituted for it.

### Searches

The prescribed `msearch.py Q28 cor-weil-finite-constructible-hom` searches were run:

* LeanFinder: `derived internal Hom of bounded constructible finite Tor complexes has
  dimension dependent Tor amplitude bounds` returned eight generic derived-category
  t-structure/Ext hits; none states the constructibility or dimension bound.
* Loogle: `"ihomCurryIso"` returned the abstract currying isomorphism and its two equations;
  these do not assert constructibility or finite Tor preservation.
* LeanSearch: `derived internal Hom preserves bounded constructible complexes of finite
  Tor amplitude` was unavailable with Internal Server Error, explicitly recorded as
  unavailable rather than absence evidence.
* Whole-Mathlib grep via msearch: `constructibleFiniteTor|verdierDual|torAmplitudeIn`
  returned zero hits.
* Direct upstream grep for the item id found
  `Etale.constructibleFiniteTor_derivedHom_of_isSeparated` in `Derived/Dualizing.lean`,
  and its uses in `Derived/Stability/DirectImage.lean`. The full signatures, surrounding
  section variables, and docstrings were read. They concern only the etale site, use the
  upstream `boundedConstructible` predicate, and the former additionally requires a
  compactification instance. They do not jointly state this item's two-site assertion
  using its recorded definitions. The general upstream stability theorems likewise use
  that different constructibility predicate. Therefore no exact existing match was claimed.
* Direct project/upstream searches for `finiteTorConstructible`,
  `intrinsicFiniteTorsionConstructible`, `derivedInternalHomOfUniverses`,
  `constructible.*internal`, `finiteTor.*internal`, and
  `derivedInternalHom.*bounded` located the interfaces used above but no matching theorem.
* Both proposed full declaration names were checked against Mathlib, upstream source,
  `lean/Sheaf` and `dag/lean_names_upstream.json`; no collisions were found.
* The current server source of `Sheaf.AlgebraicGeometry.ProEtaleOperations` was also read
  with `scompile.py --source`, confirming the original-site module and standard derived
  category interfaces. No alternate site model is introduced in this statement.

### Validation

The module compiled cleanly through the required `scompile.py` wrapper as both a sandbox
file and its library module, under the unchanged 60-second per-file limit. No warnings
were emitted. The file contains exactly two `sorry` terms, the two theorem proofs.
The delivery dry run is the remaining mechanical gate; no delivery is pushed by this worker.

## Second reading by Q28

I independently read the sandbox node and both theorem signatures, the original
blueprint node at order 2138 and its enclosing `sk-prop-sf-biduality-general/_section.md`,
and the recorded statement-dependency nodes and their actual declarations. The source
is a blueprint corollary, not a Stacks lemma. The enclosing unit supplies separated
finite-type schemes over the fixed algebraically closed finite-field base; the global
coefficient convention supplies a prime different from the characteristic and a positive
finite quotient level. The expanded DAG statement includes these hypotheses correctly.
I also read Stacks `sites-cohomology.tex`, Section 08J7 (construction and tensor-Hom
characterization of internal Hom, including 08J9) and Definition 08FZ (Tor amplitude):
these use a commutative ringed site, all degree-zero module sheaves as tensor tests, and
ordered integer endpoints, without a perfectness assumption.

The following is my object/hypothesis/conclusion inventory and its Lean match. Every row
passes; I found no mismatch requiring a statement or code change.

| Node item | Lean rendering and verdict |
| --- | --- |
| Fixed global datum, k an algebraic closure of the q-element field, characteristic p | `D : FiniteFieldDatum.{u}` and base `D.k`. I opened its fields: `prime`, `exponent_pos`, `cardinality_eq`, `card_base`, and `isAlgClosure` give exactly this datum. Pass. |
| Prime l distinct from p | `(l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)` in both declarations. Pass. |
| Arbitrary finite extension E/Q_l | `(E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`. No extra topology or valuation instance is assumed. Pass. |
| Valuation ring, chosen uniformizer, coefficient ring A | `Padic.coefficientExtensionRing l E n`. I read the construction: quotient of `coefficientExtensionIntegers` by `(Ideal.span {coefficientExtensionUniformizer l E}) ^ n`. It is the recorded coefficient object, with its valuation ring defined by the unique extending absolute value. Pass. |
| Positive level n | `(n : ℕ) (hn : 1 ≤ n)`. `Padic.finite_coefficientExtensionRing` supplies the finiteness that the etale constructibility predicate requires. Pass. |
| X a k-scheme | `(X : Scheme.{u}) [X.Over (Spec (.of D.k))]`. Both morphism properties below concern this same structure morphism. Pass. |
| X separated | `[IsSeparated (X ↘ Spec (.of D.k))]`. I read Mathlib's diagonal-closed-immersion definition; no properness is imposed. Pass. |
| X finite type | `[LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]`, exactly the conjunction recorded by the dependency. Pass. |
| Nonnegative dimension bound d | `(d : ℕ) (_hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))`. `topologicalKrullDim` is the dimension of irreducible closed subsets, including bottom for the empty space. Pass. |
| Either small site with constant coefficient sheaf | Separate etale and pro-etale theorems. Etale objects are in `Etale.DerivedCategoryModule (ULift A) X`, the recorded module-valued sheaf encoding. Pro-etale objects are in `proEtaleDerivedCategory X A`, the recorded constant-ring `SheafOfModules` encoding. Pass. |
| K and L bounded constructible on the etale site | `_hK`, `_hL` use `Etale.DerivedCategory.isBoundedConstructible`, whose definition requires every cohomology sheaf to satisfy `IsConstructibleEtaleModuleSheaf`, and vanishing outside one finite interval. The explicitly transported `Finite` proof introduces no hypothesis. Pass. |
| K and L in D^b_ctf on the pro-etale site | `_hK`, `_hL` use `finiteTorConstructible`, which unfolds to `intrinsicFiniteTorsionConstructible` and `HasFiniteProEtaleTorAmplitude`. I read both definitions: intrinsic finite stratifications and finitely supported cohomology, plus one common ordered Tor interval. Pass. |
| Arbitrary ordered intervals [a,b], [c,e] | `(a b c e : ℤ) (_hab : a ≤ b) (_hce : c ≤ e)` and the two exact Tor-amplitude hypotheses on each site. Etale `torAmplitudeIn` tensors with every module sheaf in degree zero; pro-etale `HasProEtaleTorAmplitude` tests every such sheaf and all K-flat representatives. Pass. |
| Actual derived internal Hom of K and L | Etale uses `((Etale.derivedHom ... X).obj (op K)).obj L`, the right adjoint of derived tensor. Pro-etale uses `(derivedInternalHomOfUniverses ...).obj (op K,L)`, the actual Hom-complex localization with canonical functorial K-injective replacement. Both are the intended contravariant/covariant internal Hom. Pass. |
| Bounded constructibility of that same object | First conjunct: `isBoundedConstructible` in the etale theorem, `finiteTorConstructible` in the pro-etale theorem. The latter also explicitly includes finite Tor amplitude. Pass. |
| Finite Tor amplitude with precise bound | Second conjunct: Tor amplitude in `(c - b - 2 * (d : ℤ), e - a + 2 * (d : ℤ))`, applied to exactly the same internal-Hom expression. Pass. |
| Closure for every pair in D^b_ctf, followed by the quantitative assertion | The universal quantified interval form covers closure by choosing finite ordered intervals for any pair in D^b_ctf. Conversely its assumptions imply membership in that category. Quantifier order introduces no dependence or restriction. Pass. |

Dependency interfaces were checked by opening `FiniteFieldFiber`,
`CoefficientExtensionFinite` and `CoefficientExtension`, Mathlib's `IsSeparated`,
`LocallyOfFiniteType`, `QuasiCompact`, `topologicalKrullDim`, `smallEtaleTopology` and
`Scheme.ProEt`, and the project's `DerivedCategories`, `BoundedConstructibleComplexes`,
`IntrinsicFiniteTorsionConstructibility`, `FiniteTorAmplitude`, `ProEtaleTorAmplitude`,
`ProEtaleDerivedCategory`, `ProEtaleOperations` and `DerivedInternalHomOfUniverses`.
I followed constructibility to `IsConstructibleEtaleModuleSheaf` and
`ProEtaleConstructibleSheaf`, and the constant coefficient abbreviation to
`ProEtaleInverseImage`. The derived Hom and Tor tests in the etale case were read in
upstream `Derived/Hom.lean`, `Derived/TorAmplitude.lean` and the generic
`CategoryTheory/DerivedCategory/TorAmplitude.lean`. These use the same categories and
coefficient ring as the signatures. There are no new nodes or dependency modules in
this delivery, and no statement correction or citer audit is needed.

Edge cases: the empty scheme is allowed. In particular, I checked that
`Topology.Stratification` permits empty strata, so the positive-stratum-count clause of
pro-etale constructibility does not exclude the empty scheme: use one empty stratum.
Zero K or L is allowed; no nonzero or nonempty hypothesis occurs. At d = 0 the output is
[c-b,e-a]. The output interval is ordered since its length is
(e-c)+(b-a)+4d, a sum of nonnegative integers. Singleton input intervals and arbitrary
negative integer endpoints are allowed. Level n = 1 is included, n = 0 is excluded as
in the source. Every prime different from D.p is allowed. All universes and variables
are bound explicitly; a common ambient u accommodates the scheme, base and extension,
and the pro-etale object/morphism universes remain u+1 and u. The scalar lift on the
etale site is canonical, rather than an extra coefficient choice or hypothesis.

Independent searches (different query wording from the worker):

* `msearch.py ... leanfinder "constructible sheaf internal Hom finite torsion coefficients
  bounded Tor interval dimension"` returned eight generic condensed/module/local-cohomology
  results; none states this result.
* `msearch.py ... loogle '"torAmplitude"'` returned zero hits.
* `msearch.py ... leansearch "constructible torsion sheaves derived Hom Tor dimension bound"`
  was unavailable with Internal Server Error. This is not absence evidence.
* Direct `rg` over all Mathlib, upstream `WeilConjectures`, project `lean/Sheaf` and
  `dag/lean_names_upstream.json` for `constructibleFiniteTor_derivedHom`,
  `derivedHom.*(constructible|torAmplitude)`, `[Cc]onstructible.*derivedHom`, and both
  proposed declaration names found no exact project/Mathlib match or name collision.
  I opened the full upstream `constructibleFiniteTor_derivedHom_of_isSeparated` signature
  with its section variables: it uses `boundedConstructible` and an extra
  `HasCompactification` instance. I also opened `boundedConstructible_derivedHom`,
  `Etale.constructibleFiniteTor_derivedHom` and
  `ProEtale.DerivedCategory.constructibleFiniteTor_derivedHom_mapDerivedCategory` in
  `Stability/DirectImage.lean` and `Stability/Matrix.lean`. They use the upstream
  constructibility predicate; the last only treats pulled-back etale objects and does
  not give the quantitative general-pro-etale statement in this delivery's encoding.
* I read `coord/pefw-upstream-framework.md` and searched the current shared 51-module
  overlay. I opened `ModuleObject/Derived/Hom.lean` and the
  `boundedConstructible_derivedHom_obj` signature in `ModuleObject/Derived/BoundedConstructible`.
  These concern modules over condensed coefficient ring objects, not the recorded finite
  constant-ring module category, and do not state the finite-level interval assertion.

No mismatch was found. I retained both theorem signatures and the node unchanged, and
appended this independent review only. Each theorem has the source/blueprint docstring
and the appropriate step-by-step duality, tensor and comparison proof plan. There are
no new definitions, private copies, file-local notation, or proved auxiliary results;
the only two `sorry` terms are the two named theorem proofs. All lines of the Lean
module are at most 100 characters, and `lean.statement` equals its primary signature
verbatim. Compared with the shared node, only `lean` is changed.

Validation: `scompile.py Q28 cor-weil-finite-constructible-hom
lean/Sheaf/Paper/FiniteConstructibleHom.lean` run from the sandbox succeeded for both
the sandbox file (3.5 seconds) and the library module (4.2 seconds), with no warnings
or errors and the unchanged 60-second limit. The required delivery dry run follows.

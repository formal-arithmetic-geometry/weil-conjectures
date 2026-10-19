## Worker report

The module `Sheaf.Paper.OpenExtensionFiniteTor` states
`AlgebraicGeometry.Scheme.finiteStageDerivedExtensionByZero_constructibleFiniteTor`.
Its proof is `sorry`. The auxiliary definition
`AlgebraicGeometry.Scheme.finiteStageDerivedExtensionByZero` is real data:
the recorded exact intrinsic extension-by-zero functor, descended termwise by
`CategoryTheory.Functor.mapDerivedCategory`. No object or map is chosen from a
mere nonempty existence assertion, and no theorem is proved in this delivery.

Hypotheses and conclusions, clause by clause:

- The fixed finite-field base is `D : WeilConjectures.FiniteFieldDatum`; its
  algebraic closure is `D.k`. The coefficient conventions are expanded as binders:
  `(l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)`, a finite extension
  `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`, and `(n : ℕ) (hn : 1 ≤ n)`.
  The ring A is exactly `Padic.coefficientExtensionRing l E n`, the recorded
  quotient by the nth power of the chosen uniformizer. The choice of an embedding
  of E in the fixed coefficient algebraic closure is immaterial here: neither
  the quotient construction nor any operation in this assertion uses it.
  `def-trf-coefficient-conventions` is a context convention, not a missing
  independent notion needed to type this statement: all its finite-stage data
  used here are the existing declarations just named. Its compact-support and
  point-fiber notation does not occur in this lemma, so no compact-support
  construction is introduced or assumed by this delivery.
- U and Y are schemes over `Spec (CommRingCat.of D.k)`. For each structure
  morphism the instances `LocallyOfFiniteType` and `QuasiCompact` render
  finite type. No separatedness, quasi-separatedness, compactification, or
  geometric descent datum is required in the lemma.
- `(j : U ⟶ Y) [IsOpenImmersion j]` is the open immersion. The instance
  `[j.IsOver (Spec (CommRingCat.of D.k))]` expresses that it is a morphism
  of k-schemes.
- `K : proEtaleDerivedCategory U (Padic.coefficientExtensionRing l E n)`
  is an object of the derived category of modules over the constant ring
  sheaf on the small pro-etale site. Its site has object universe u+1,
  morphism universe u, and module universe u+1; these are not identified.
- `hK : intrinsicFiniteTorsionConstructible l E n hn U K` is precisely
  boundedness (finitely many nonzero cohomology sheaves) and constructibility
  of every cohomology sheaf, using the existing global finite stratifications.
- `hTor : HasFiniteProEtaleTorAmplitude U A K` is finite Tor amplitude,
  tested against every module sheaf in degree zero, without constructibility
  or finiteness conditions on the test module.
- The first conjunct `WeilConjectures.finiteTorConstructible l E n hn Y
  ((finiteStageDerivedExtensionByZero l E n hn j).obj K)` is membership of
  j_!K in D^b_ctf(Y,A), with exactly the intrinsic bounded-constructibility
  and finite-Tor predicates.
- The second conjunct quantifies over all integers c,d and preserves the
  predicate `∀ r, (r < c ∨ d < r) → IsZero ((homologyFunctor _ r).obj K)`.
  This is exactly preservation of every cohomological range, with no change
  to its endpoints.
- The third conjunct quantifies separately over all integers a,b and takes
  `HasProEtaleTorAmplitude U A K a b` to
  `HasProEtaleTorAmplitude Y A (j_!K) a b`. In particular the Tor endpoints
  are not forced to equal the cohomological endpoints.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`, its
  field/closure instances, and the coefficient convention in its module
  documentation. `Sheaf.NumberTheory.Padics.CoefficientExtension` supplies
  `Padic.coefficientExtensionRing`; `CoefficientExtensionFinite` supplies
  `Padic.finite_coefficientExtensionRing`, used only inside the real helper
  definition to install the finite-ring instance.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `LocallyOfFiniteType` and `QuasiCompact` (read their full class fields).
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`:
  `Scheme.sfIntrinsicExtensionByZero`, transported by the canonical
  `sfIntrinsicModuleEquivalence`. `ProEtaleIntrinsicExtensionByZeroExact`
  supplies its additive and finite-limit/finite-colimit preservation instances.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor` and its representative factorization.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `Scheme.intrinsicFiniteTorsionConstructible`, with its full conjunction.
- `Sheaf.Paper.FiniteTorAmplitude`: `WeilConjectures.finiteTorConstructible`;
  `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude`:
  `Scheme.HasProEtaleTorAmplitude`, `Scheme.HasFiniteProEtaleTorAmplitude`.
  The former includes the ordered-interval condition and quantifies over
  arbitrary test sheaves and all K-flat resolutions of all representatives.
- The source's proof plan is retained in the theorem docstring, step by step.
  Plain proof imports include `Topology.Constructible` and
  `Topology.LocallyClosed` (the existing Mathlib matches for the two topological
  nodes), `ProEtaleRingedOpenClosed` (`proEtale_ringed_open_closed`), and
  `ProEtaleDerivedPullbackComposition`
  (`proEtaleRingDerivedPullbackComposition`).
- The finite-level intrinsic pullback interface used by the proof is
  `Sheaf.AlgebraicGeometry.ProEtaleOperations.proEtaleRingDerivedPullback`
  (declaration namespace `AlgebraicGeometry.Scheme`), imported explicitly.
  `lem-trf-open-tensor` has no recorded declaration and is only a proof
  prerequisite; no new proof theorem for it is needed to state this item.
  The exact tensor calculation is retained in the natural-language proof.

Edge cases checked before writing: the empty open, the identity open immersion,
the empty target scheme, and the zero derived object are admitted. A single
cohomological degree c=d and a point Tor interval a=b are admitted. The theorem
preserves independent intervals, including intervals wider than necessary.
If c>d the stated vanishing hypothesis says every cohomology sheaf is zero,
so this case is valid too; the Tor predicate itself already requires a≤b.
The first finite level n=1 is admitted. n=0 is excluded exactly by the source's
positive-level coefficient convention. There is no restriction to nonzero test
modules, to ordinary geometric stalks for checking a sheaf identity, or to
constructible test modules. There is no extra choice of map or adjunction.

Searches for the statement and its helper names:

- `msearch.py leanfinder`, query "Extension by zero of a constructible complex
  preserves cohomological interval and finite Tor amplitude": eight hits,
  concerning extension of complexes along index embeddings and derived
  t-structure bounds. None states constructibility or Tor preservation under
  extension by zero of pro-etale sheaves.
- `msearch.py loogle`, query `torAmplitudeIn, openImmersionLowerShriek`:
  no hits; unknown identifier `torAmplitudeIn`.
- `msearch.py grep`, query `extension.by.zero|openImmersionLowerShriek` in
  `Mathlib/AlgebraicGeometry`: no hits.
- `msearch.py leansearch`, query "Extension by zero on pro etale sheaves
  preserves bounded constructibility and finite Tor amplitude": service
  unavailable, Internal Server Error. This is recorded as unavailable.
- `rg` in the upstream project, the published side framework, and `lean/Sheaf`
  for the blueprint id and the proposed helper/theorem names: no declaration
  of this item or either proposed name. A conceptual search for
  `constructibleTorAmplitudeIn_mapDerivedCategory_openImmersionLowerShriek`
  finds the etale-site theorem in Etale/Derived/Stability/OpenImmersion; it
  uses a different site and a common cohomological/Tor interval. It does not
  state this pro-etale assertion with independent intervals. The pro-etale
  `LocalizationFiniteTor` theorem concerns derived direct image along an
  open, which is a different functor from extension by zero.
- The source check `scompile.py --source Sheaf.Paper.TrfCoefficientConventions`
  (and `TrfFiniteCoefficientConventions`) found no such published module.
  The actual constituent finite-coefficient declarations above were read
  directly; no competing coefficient definition is added.

No statement correction, new independent definition node, or mathematical dispute
is required. The original item statement, proof and proof dependencies are unchanged.
Its statement dependencies additionally cite the already landed
`def-weil-proetale-tor-amplitude` for the explicit interval predicate and
`def-weil-derived-pullback-tensor-hom` for the compatible intrinsic pullback
interface repaired below. The sole new postponed theorem has this item's DAG
node and complete proof docstring.

Validation: the module compiled cleanly in both sandbox and library views through
`scompile.py`, within the required 60-second per-file limit. The final dry run is
`deliver2.py Q11 lem-trf-open-ctf --no-push`; the independent second reader adds
its own section and delivers. No shared source was edited and no direct Git
command or global build was run.

## Dependency modules

`def-weil-finite-tor-amplitude`: lean-only repair using the already published
`Sheaf.Paper.FiniteTorAmplitude`, declaration
`WeilConjectures.finiteTorConstructible` (`existing: true`). The current record
uses fixed-scalar sheaves and bounded constructibility expressed as etale origin.
The item's other recorded dependencies instead use intrinsic modules over the
constant ring sheaf and intrinsic finite stratifications. The existing intrinsic
predicate is exactly their intersection with finite Tor amplitude and retains
all original integral and field-stage aliases in its module. Reusing it requires
no duplicate definition, new theorem, or assertion equating different notions.

`def-weil-derived-pullback-tensor-hom`: lean-only repair using the already
published `Sheaf.AlgebraicGeometry.ProEtaleOperations`, declaration
`AlgebraicGeometry.Scheme.proEtaleRingDerivedPullback`, and its termwise
factorization (`existing: true`). The old legacy `Derived.Hom` import closure
collides with `FiniteCoefficient.UpperLowerStar.Defs`, which is required by the
recorded intrinsic extension-by-zero functor. The intrinsic exact module
pullback is the same finite-stage derived inverse image with the canonical
constant coefficient identification. The existing intrinsic K-flat tensor and
K-injective Hom constructions remain in `Sheaf.Algebra.Homology.DerivedTensor`
and `DerivedInternalHomOfUniverses`; the finite pullback clause is the only
operation clause consumed here. Integral, rational and common-stage operations
are not changed or redefined. This is an interface repair with no mathematical
statement change; only the dependency node's lean field changes.


## Second reading by Q11

I did not author the module. I independently opened the item JSON, the Lean file,
all statement-dependency records and their declarations, both dependency-record
repairs, and the relevant proof-dependency declarations. The blueprint source
`sec-six-functors/sk-lem-sf-open-ctf/lem-trf-open-ctf.md` and its unit statement
were read from the available literature mirror. They give exactly the original
item statement. I also read the coefficient-conventions source, Stacks
`sites-modules.tex`, lemma-extension-by-zero-exact (03DJ),
`sites-cohomology.tex`, definition-tor-amplitude (08FZ), and `proetale.tex`,
lemma-open-immersion, lemma-jshriek-zero, and lemma-ses-associated-to-open
(09BN, 09AG, 09AH). Exactness needs only a ringed site and a localized object;
the open-closed sequence needs a quasi-compact complementary open. Finite type
over the field supplies Noetherianity and hence this quasi-compactness; it is
not an additional assumption on `j` in the Lean.

My object/hypothesis/conclusion checklist, written from the node before matching:

| Item from the node and its conventions | Lean rendering and verdict |
| --- | --- |
| The global field k, prime l different from its characteristic p | `D : WeilConjectures.FiniteFieldDatum.{u}`, `l`, `[Fact l.Prime]`, `_hl : l ≠ D.p`; the structure's `k` is the chosen algebraic closure of its finite base field. Exact. |
| Finite coefficient stage A = O_E / varpi_E^n, n positive | `E : Type u`, `[Field E]`, `[Algebra (Padic l) E]`, `[FiniteDimensional (Padic l) E]`, `n`, `hn : 1 ≤ n`, and `Padic.coefficientExtensionRing l E n`. I read the quotient, valuation-ring and uniformizer definitions. Exact. The embedding in the fixed coefficient algebraic closure carries no additional datum used by this statement: any finite extension admits it, and the quotient uses only E and its recorded valuation. |
| U and Y are finite-type k-schemes | `{U Y : Scheme.{u}}`, their `Over (Spec (CommRingCat.of D.k))` instances, and both `LocallyOfFiniteType` and `QuasiCompact` on each structure morphism. I read both Mathlib class fields. Exact finite type, with no separatedness or descent assumption added. The convention's separate X_0 is not an object in this lemma. |
| j is an open immersion between these k-schemes | `(j : U ⟶ Y)`, `[IsOpenImmersion j]`, `[j.IsOver (Spec (CommRingCat.of D.k))]`. The last instance is precisely compatibility of the two structure maps. Exact. |
| K is a complex of A-modules on the small pro-etale site of U | `K : proEtaleDerivedCategory U (Padic.coefficientExtensionRing l E n)`. I unfolded this abbreviation and `proEtaleRingModules`: these are the same derived category of intrinsic constant-ring module sheaves. Exact; no etale-origin predicate has been substituted. |
| K is bounded and has constructible cohomology | `hK : intrinsicFiniteTorsionConstructible l E n hn U K`. Its definition is finite support of cohomology and, in every degree, `IsConstructibleProEtaleModuleSheaf`. I read that predicate and its finite immersed locally closed stratifications, locally constant restrictions, and finite stalks. Exact. |
| K has finite Tor amplitude | `hTor : HasFiniteProEtaleTorAmplitude U A K`, where A is the displayed quotient. Its definition is one existential pair a,b and `HasProEtaleTorAmplitude`. That predicate includes a ≤ b and tests every degree-zero module sheaf, on every K-flat resolution of every representative isomorphic to K. Exact; no test sheaf is required constructible. |
| The object j_!K is extension by zero | `((finiteStageDerivedExtensionByZero l E n hn j).obj K)`. The helper installs only the named finite-ring witness and is literally `(sfIntrinsicExtensionByZero j A).mapDerivedCategory`. I opened the recorded underived functor: it transports the existing factorization-indexed presheaf extension and sheafification through the canonical scalar realization equivalences. The exactness instances justify termwise descent. Exact canonical construction. |
| j_!K belongs to D^b_ctf(Y,A) | First conjunct `WeilConjectures.finiteTorConstructible l E n hn Y (...)`. I unfolded it: the intrinsic bounded-constructibility predicate intersected with finite Tor amplitude, on exactly the same derived category. Exact. |
| Its cohomological range can be that of K | Second conjunct: for all integers c,d, vanishing of `DerivedCategory.homologyFunctor ... r` on K when `r < c ∨ d < r` implies the identical vanishing on j_!K. All degrees and both endpoints are preserved. Exact; no assertion of equality of minimal ranges is added. |
| Its Tor amplitude can be that of K | Third conjunct: independently for every a,b, `HasProEtaleTorAmplitude U A K a b` implies `HasProEtaleTorAmplitude Y A (j_!K) a b`. Exact. The Tor interval is not forced to coincide with c,d. |

Edge cases were checked from these actual definitions. There is no `Nonempty`
assumption on either scheme, a stratum, or a module. The empty open, the identity
open, the empty target, and K = 0 are admitted. Although constructibility asks
for a positive number of strata, the stratification definition does not require
nonempty strata, so an empty scheme is still covered. Zero test sheaves are
included. Single-degree ranges c = d and a = b are allowed; reversed c > d
expresses total cohomological vanishing, whereas reversed a > b is excluded by
the source Tor predicate itself. The first finite level n = 1 is allowed;
n = 0 is outside the source's n >= 1 convention. No characteristic apart from
the fixed finite-field convention is removed. All integers are quantified,
including negative degrees. `universe u` binds all input sizes; small pro-etale
objects live in u+1, site morphisms in u, and module values in u+1. I checked
that no site-universe equality or unbound implicit variable has been introduced.
The common size for schemes and finite coefficients is the existing dependency
interface's convention; it does not identify site object and morphism sizes.

Independent H4 searches, with different formulations from the author:

- `msearch.py leanfinder`, "Exact extension by zero along open subscheme preserves
  constructible cohomology and all Tor dimension bounds": only eight general
  derived t-structure/cochain interval results, no matching sheaf theorem.
- `msearch.py loogle`, `"PreservesHomology"`: generic exact-functor homology
  preservation, including `Functor.preservesHomologyOfExact`; these do not
  assert constructibility or Tor preservation.
- `msearch.py leansearch`, "For a quasi compact open immersion of schemes
  extension by zero preserves constructible finite Tor dimension complexes":
  the service succeeded on this reading; its eight results were scheme
  immersion and quasi-compactness facts, not the item.
- `msearch.py grep`, `lowerShriek|extensionByZero|extension_by_zero`: no Mathlib
  match. Independent `rg` searches in Mathlib, upstream `WeilConjectures`, the
  published side framework and `lean/Sheaf` also used combinations of
  `constructible`, `shriek`, `zero`, and `torAmplitude`, and searched the new
  names and `sfIntrinsicExtensionByZero.*mapDerivedCategory`.
  Existing consumers use the same termwise functor inline; none defines this
  finite-stage helper or states this theorem. I opened the nearest etale
  theorem `constructibleTorAmplitudeIn_mapDerivedCategory_openImmersionLowerShriek`:
  its objects are on `smallEtaleTopology` and its two intervals coincide.
  I also opened `ProEtale.IsAdicConstructibleSheaf.openImmersionLowerShriek`:
  it is about underived adic sheaves. Neither is an exact declaration of this
  pro-etale finite-stage assertion. No duplicate definition or statement found.

H12/H13: there are no new independent definition nodes and no new dependency
modules in this packet. The two dependency node copies use existing declarations.
I read their complete node statements, their blueprint source places, the old
recorded declarations, and the replacement declarations:

- `def-weil-finite-tor-amplitude`: the old `constructibleFiniteTor` has domain
  `DerivedCategory (Sheaf (ProEt.topology X) A)` and uses etale-origin
  constructibility. This cannot be directly applied to the intrinsic
  `SheafOfModules` object in this item. The already published
  `WeilConjectures.finiteTorConstructible` has exactly the required intrinsic
  intersection, and its integral predicate keeps one ordered Tor interval
  for every positive reduction. I also read its full-subcategory and
  field-alias declarations. The repair reuses these declarations and adds
  no assertion equating the two presentations.
- `def-weil-derived-pullback-tensor-hom`: the old derived Hom and tensor live
  in the fixed-scalar framework; its import closure cannot be combined with
  the intrinsic extension-by-zero framework. The existing
  `proEtaleRingDerivedPullback` is termwise exact inverse image followed by
  tensor scalar transport along the supplied coefficient identification;
  `proEtaleRingDerivedPullbackFactors` records its representative formula.
  At the constant finite stage the identification is the canonical
  constant-section comparison used by the constructible restriction, not a
  free map or a new hypothesis of the theorem. The repair concerns this
  finite pullback interface only; it does not replace integral completed,
  rationalized or common-stage operations by finite ones. The existing
  K-flat tensor and K-injective internal Hom constructions remain recorded
  in the repair note. No new operation or weaker mathematical node is stated.

H5/H6/H8/H9: the helper's data are a specified functor, with no `sorry`,
`Nonempty` choice, new axiom, private copy, file-local notation or local instance.
The only postponed theorem is the item itself, with `by sorry`.
Both declarations and the module have source/blueprint docstrings. I matched
all four proof steps in the theorem docstring against the node: exactness and
cohomology; extending strata and the complement; restriction identities and
pullback composition; arbitrary degree-zero tensor tests and preservation of
both bounds. The proof imports retain the available dependencies; the still
unstated open tensor theorem remains an explicitly named proof step.
All Lean lines satisfy the 100-character convention. The node's `lean.statement`
was compared byte-for-byte with the theorem signature, from `theorem` to `:=`.

No mathematical mismatch was found and no Lean statement or node statement was
changed in this second reading. This section and the independent search log are
the additions. In particular there is no statement correction and no citer audit
is required. Validation is recorded by the second-reader compile and the final
`deliver2.py --no-push` check before delivery.

Second-reader validation completed: `scompile.py` exited 0 with no diagnostics;
`deliver2.py Q11 lem-trf-open-ctf --no-push` printed
`OK (dry run): commit 00d01540f9 passes the preflight and compiles; nothing pushed`.
The packet contains one Lean module, the item record, the two lean-only dependency
repairs, and this report. The tool retains current maintainer review metadata.

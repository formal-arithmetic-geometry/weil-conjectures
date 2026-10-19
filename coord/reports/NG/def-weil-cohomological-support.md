## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport` defines
`AlgebraicGeometry.Scheme.proEtaleCohomologicalSupport`. It contains one complete
definition, no theorem and no sorry. No statement correction or new node is needed.

Clause-by-clause correspondence:

- The small pro-etale site is the site already used by
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`, imported from
  `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory` (dependency
  `def-weil-pbc-proetale-site`). The binders `Y : Scheme.{t}` and
  `A : Type t` with `[CommRing A]` supply exactly its scheme and coefficients.
- A complex of sheaves is viewed up to quasi-isomorphism as
  `K : proEtaleDerivedCategory Y A`, consistently with the node's split report
  and the cohomology-sheaf dependency. No boundedness, constructibility, or
  completeness hypothesis is imposed.
- The cohomology sheaf in degree `r` is
  `(@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) r).obj K`.
  This is the declaration recorded by the Mathlib dependency
  `def-weil-derived-cohomology-sheaves`, from
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`.
  The category argument is inferred from the recorded category of `K`, and the
  explicit standard localization is exactly the one in its definition.
  The full signature and docstring of `homologyFunctor` were read, as was
  `homologyFunctorFactors`, which identifies this value with the cohomology
  of a representing cochain complex.
- The integer degrees form `Set ℤ`, and its defining predicate is precisely
  `¬ CategoryTheory.Limits.IsZero` of that cohomology sheaf. `IsZero` is the
  categorical zero-object predicate (its full structure declaration and
  docstring were read in `Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects`).
  This implements the formula in the Mathlib match of
  `def-weil-derived-category-cohomological-support` verbatim, specialized to
  the recorded sheaf category. That leaf records an expression built out of
  `homologyFunctor`, not an already named support-set declaration. There is
  therefore no additional support definition to import or duplicate.

Edge cases checked mathematically: zero and acyclic complexes have empty
support; negative and positive degrees are both included; a nonzero sheaf
concentrated in degree zero has support `{0}`. The zero coefficient ring and
empty scheme are allowed and yield only vanishing cohomology. No boundedness
restriction excludes complexes with infinitely many nonvanishing degrees.
The universe is inherited unchanged from the dependency, including its
universe-lifted coefficient sheaf and module category. No file-local instances,
notations, or unbound variables are used.

Searches for an existing notion:

- `msearch.py ... leanfinder` with query "cohomological support set of integer
  degrees with nonzero cohomology of a derived category object": eight hits,
  all `DerivedCategory.IsLE`, `IsGE`, and associated t-structure facts; no
  support-set definition.
- `msearch.py ... loogle 'DerivedCategory.homologyFunctor'`: twelve hits,
  including the homology functor and factorization isomorphisms, no support set.
- `msearch.py ... grep 'cohomologySupport|homologySupport|cohomologicalSupport'
  Algebra/Homology`: zero hits.
- Local `rg` with `cohomolog.*[sS]upport|homologySupport|cohomologySupport|def-weil-cohomological-support`
  over Mathlib homological algebra, the upstream `WeilConjectures` sources,
  and `lean/Sheaf`: only unrelated spatial-support and compact-support results.
  The exact support-set names were also searched in `dag/lean_names_upstream.json`,
  the upstream sources, and project Lean; no matching declaration.
- The optional newer upstream ModuleObject/Derived paths mentioned by the
  framework notice are absent in this machine's source checkout. This definition
  needs none of those modules: its exact site/category dependency and Mathlib
  cohomology declaration were read directly and are checked by server compilation.

The blueprint source
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-def-sf-operations/def-weil-cohomological-support.md`
was read in full and agrees with the node. No node fault or disputed statement.

Validation: server compilation through `scompile.py` and delivery preflight
through `deliver2.py --no-push`; their final results are recorded below.

The server compile passed cleanly in 1.4 seconds, nice 19, two threads,
60 seconds per file. The delivery dry run printed OK: compilation and preflight
pass except for the independent second reading, which the next worker supplies;
nothing was pushed.

## Second reading by NG

I independently read the item node, its blueprint source at
`sec-smooth-purity/sk-def-sf-operations/def-weil-cohomological-support.md`
(order 1458), the containing section, all three statement-dependency nodes,
and their recorded Lean declarations. The source is a blueprint definition,
not a Stacks statement with additional standing hypotheses. The section's
separated finite-type morphism concerns the six operations, not this definition
of the degrees of nonvanishing cohomology.

Object/hypothesis/clause checklist, matched against the file:

1. A scheme and its small pro-etale site: `{Y : Scheme.{t}}` and the imported
   `AlgebraicGeometry.Scheme.proEtaleDerivedCategory` use exactly
   `Scheme.ProEt.topology Y`. I opened the dependency module and Mathlib's
   `Scheme.ProEt`, `ProEt.precoverage`, and `ProEt.topology`: these are weakly
   etale objects over Y with the pro-etale topology. Verdict: same site.
2. Coefficients and sheaves: `{A : Type t} [CommRing A]` specialize to the
   dependency's sheaves of modules over the constant commutative-ring sheaf,
   forgotten to RingCat, with `ULift` coefficients and module universe `t+1`.
   These are the coefficients meant by the node's cited derived-category
   dependency and its split report. No field, nonzero-ring, Noetherian,
   constructibility or completeness hypothesis is added. Verdict: exact.
3. A complex K: `(K : proEtaleDerivedCategory Y A)` is its quasi-isomorphism
   class in the unbounded derived category specified by the site dependency.
   The source's cohomology depends only on this class. The cohomology dependency
   expressly uses this derived category, not a category of strictly bounded
   complexes. Verdict: exact.
4. Every integer degree r and its cohomology sheaf: the result `Set ℤ` and the
   bound variable `r` in the set comprehension range over all integers.
   `(@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) r).obj K`
   is precisely the dependency's recorded Mathlib functor evaluated at K.
   I read its signature and `homologyFunctorFactors`: it factors the ordinary
   cochain-complex homology functor through localization. The explicit standard
   localization agrees with that used by `proEtaleDerivedCategory`.
   Verdict: exact cohomology sheaf, with no sign reversal.
5. The conclusion is exactly the set where that sheaf does not vanish:
   `{r | ¬ CategoryTheory.Limits.IsZero (...)}`. I read the `IsZero` structure;
   it expresses categorical zero, so this is invariant under isomorphism and
   is not comparison with a chosen representative of zero. No interval or
   finiteness clause is added. Verdict: exactly the displayed source formula.

Edge cases: zero and acyclic complexes give the empty set; a nonzero sheaf
in degree zero gives `{0}`. Negative degrees and infinite support are allowed.
The empty scheme, zero coefficient ring and every characteristic are allowed;
no nonemptiness hypothesis is present. There is no index family or natural-number
parameter requiring extra empty-index or n=0 clauses. All universe and object
variables are bound. The common universe t for scheme and ring does not impose a
mathematical size restriction: it may be enlarged to accommodate both, and the
coefficient sheaf/module universe is lifted as in the recorded dependency.

Independent H4 searches (2026-10-15):

- `msearch.py NG def-weil-cohomological-support leanfinder` with
  "set of integer degrees in which the homology object of a complex does not vanish"
  returned eight homology/vanishing results, including `DerivedCategory.isLE_iff`
  and `isGE_iff`, but no support-set definition.
- `msearch.py ... loogle 'DerivedCategory.homologyFunctor'` returned twelve
  declarations, including `homologyFunctor` and `homologyFunctorFactors`, with
  no named support set.
- `msearch.py ... grep 'homologicalSupport|supportDegrees|nonvanishingDegrees'`
  returned no hits. Direct `rg` also searched these names together with
  `cohomologicalSupport|cohomologySupport|homologySupport` throughout Mathlib,
  upstream WeilConjectures, project Lean, and the upstream name index. Hits were
  unrelated file names for spatial support. Broader searches combining support
  and homology/cohomology found spatial support and boundedness predicates,
  not this set of degrees. The general support dependency is a Mathlib leaf
  recording this set-builder expression, not a separate named definition to
  import. Its recorded `homologyFunctor` is used directly.

No mismatch was found; no Lean code or node fields changed. No new node or
additional dependency module is needed. Both imports are used, the module and
sole definition have the correct source/blueprint docstrings, and there are no
proofs, hollow data, local notation or private replacement definitions. The
node's `lean.statement` is verbatim the declaration signature in the file.

Second-reader validation: `scompile.py` compiled the sole delivered module cleanly
in 1.3 seconds, nice 19, two threads, 60-second limit. The subsequent
`deliver2.py NG def-weil-cohomological-support --no-push` printed
`OK (dry run)` and confirmed successful preflight and compilation.


## Maintainer independent search supplement (2026-10-15)

The immutable delivery recorded LeanFinder, Loogle and grep searches, but did
not record the LeanSearch attempt required by brief-stage2 §1 (H4). This
supplement supplies that missing search evidence; it does not attribute the
maintainer's search to either NG reader.

An independent POST to `https://leansearch.net/search`, with query
"The set of integers indexing nonzero cohomology objects of an object in a
derived category" and `num_results: 8`, returned `Internal Server Error`.
Verdict: LeanSearch unavailable, not "no match".

Independent direct `rg` searches covered Mathlib, slopmaster2 WeilConjectures,
the read-only NG project's Sheaf and WeilConjectures sources, and
`dag/lean_names_upstream.json`, using `cohomologicalSupport`,
`homologicalSupport`, `homologySupport`, `cohomologySupport`, `supportDegrees`,
`nonvanishingDegrees`, and the item id. No existing definition of this set was
found. Broader support/homology searches found spatial-support constructions,
compactly supported cohomology and boundedness predicates, not this notion.
`GradedObject.finrankSupport` (Mathlib Algebra/Homology/EulerCharacteristic,
line 108) uses nonzero finite rank of graded modules; it is not nonzero
cohomology in an arbitrary sheaf-module category. The general support leaf
records a set-builder specialization of `DerivedCategory.homologyFunctor`,
not a named support definition being duplicated here.

Reproducibility: the exact immutable delivered module was compiled using
`scompile.py NG def-weil-cohomological-support
snapshot/lean/Sheaf/AlgebraicGeometry/ProEtaleCohomologicalSupport.lean`.
Exit status 0; output:

```text
Sheaf/AlgebraicGeometry/ProEtaleCohomologicalSupport.lean: 1.3 s; nice 19; 2 threads; limit 60 s
```

There were no errors or warnings. This supplement changes only the report;
the delivered Lean and node record remain correct as written.

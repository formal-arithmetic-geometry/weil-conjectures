## Worker report

The module `Sheaf.AlgebraicGeometry.CompactBoundedConstructibleBaseChange` states
`AlgebraicGeometry.Etale.isBoundedConstructible_compactSupport_and_baseChange` with a single
`sorry` proof. It defines no new notion and changes only the item's `lean` record.

Hypothesis and conclusion correspondence:

- The prime ℓ implicit in the notation F_ℓ is `(ℓ : ℕ) [Fact ℓ.Prime]`. The coefficient ring is
  `ULift.{u + 1} (ZMod ℓ)`, the actual prime field transported to the coefficient universe.
- The base field is `{k : Type u} [Field k]`; characteristic different from ℓ is
  `hℓ : (ℓ : k) ≠ 0`. For prime ℓ these are equivalent, including characteristic zero.
- The finite-type k-schemes are `{X S : Scheme.{u}}`, with structure morphisms `aX`, `aS`, each
  having `LocallyOfFiniteType` and `QuasiCompact` instances. No separatedness over k is imposed.
- The separated finite-type morphism is `f : X ⟶ S`, with `IsSeparated f`,
  `LocallyOfFiniteType f`, and `QuasiCompact f`. Its compatibility with the k-structures is
  `hf : f ≫ aS = aX`.
- `c : Compactification f` specifies the compactification used in the recorded dependency
  `def-amb-etale-compact-support`. This is a choice of computing data, available by Nagata under
  the preceding hypotheses. The assertion holds for every such choice; it adds no geometric
  restriction on f. The base-changed compactification is `c.ofIsPullback sq`, as required by
  `def-cbc-exchange-map`.
- `K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat ...))` with
  `hK : DerivedCategory.isBoundedConstructible ... X K.obj` expresses K in D^b_c. The predicate
  is exactly the dependency's predicate, using the project's constructible sheaves and
  vanishing outside an interval. `Plus` is the full subcategory of the SAME unbounded category
  on bounded-below objects, not a replacement category of coefficients. Every bounded
  constructible object has a lower bound, hence can be packaged this way; conversely the
  displayed predicate makes every packaged input bounded constructible. The extra proof
  field adds no restriction and is used because the recorded exchange map is on D^+.
- The first conjunct is `DerivedCategory.isBoundedConstructible ... S` of
  `(rightDerivedLowerShriekOfCompactification (ModuleCat ...) c).obj K.obj`, exactly Rf_!K.
- The second conjunct quantifies over every `S' : Scheme.{u}` with `[IsNoetherian S']` and
  `v : S' ⟶ S`. There is no finite-type or separatedness restriction on v or S'. It then
  quantifies over a cartesian presentation by X', vX, f', and `sq : IsPullback vX f' f v`.
  No nonemptiness, surjectivity or bound on geometric fibres is imposed.
- `IsIso ((rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap ... sq c).app K)` is
  invertibility of the specified compact-support exchange, not existence of an unrelated
  isomorphism. This is the recorded map whose first factor is proper exchange and second
  factor is the extension-by-zero identification.

Statement dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible` (full definition read).
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification` (full definition and
  docstring read; it is D(j_!) followed by R(p_*) on the unbounded categories).
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange`:
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap`
  (current server module obtained with `scompile.py --source`, full declaration and docstring
  read, including its proper-exchange identification).
- `def-weil-pbc-scheme-conventions` is explicitly a convention record, not a declaration to
  import. Mathlib supplies `AlgebraicGeometry.Scheme`, `LocallyOfFiniteType`, `QuasiCompact`,
  `IsSeparated`, `IsNoetherian`, and `CategoryTheory.IsPullback`. The relevant full class
  signatures and docstrings were read. No definitions are copied.

The module imports the available recorded proof dependencies as non-public imports; the
unrecorded `sbc-prop-extension-by-zero-and-arbitrary-base-change` has no module to import.
The theorem docstring carries all six steps of the node's proof: Noetherian and finite-type
compactification, bounded constructible extension by zero, proper bounded constructibility,
base-changed compactification and open comparison, proper exchange with coefficient forgetting,
and the specified composite. No proof is implemented at stage 2.

Edge cases checked: characteristic zero satisfies the invertibility condition; ℓ=2 is allowed;
ℓ=0 or 1 is excluded precisely because F_ℓ denotes a prime field. Zero complexes and shifts with
arbitrary negative lower bounds remain in the statement. Empty source, target or new base are
not excluded. Nonseparated finite-type k-schemes are allowed; only f is separated. Arbitrary
Noetherian S' need not be finite type over k, and no global dimension bound is assumed for it.
Changing the cartesian presentation or compactification remains within the universal binders.

Searches for existing statements:

- `msearch.py leansearch`, query "compactly supported etale derived pushforward bounded
  constructible base change": service unavailable (Internal Server Error); no verdict assigned.
- `msearch.py leanfinder`, query "etale compact direct image of bounded constructible complexes
  preserves bounded constructibility and satisfies arbitrary base change": eight hits about
  constructible subsets and etale composition, no match.
- `msearch.py loogle`, query "rightDerivedLowerShriek, isBoundedConstructible": zero hits,
  unknown identifier rightDerivedLowerShriek.
- `msearch.py grep`, query "rightDerivedLowerShriek|CompactSupport", Mathlib AlgebraicGeometry:
  zero hits. Direct rg in Mathlib AlgebraicGeometry also found only constructible subsets.
- Direct rg of the upstream WeilConjectures tree for the node id: no occurrence. Searches for
  boundedConstructible and lowerShriek found `constructibleFiniteTor_rightDerivedLowerShriek`
  in `...Derived.Stability.DirectImage`, whose signature was read: it uses the upstream
  constructibility notion, finite Tor amplitude, a chosen canonical compactification, and
  does not state the specified conjunction. It is not this node's recorded predicate.
- Direct rg of `lean/Sheaf` found the proper-only theorem
  `isBoundedConstructible_rightDerivedLowerStar_of_proper` and the unbounded-above
  constructibility theorem `isConstructibleEtaleModuleSheaf_homology_compactSupportCandidate`;
  neither states this node. Search of the proposed theorem name in Mathlib/upstream/project
  and the upstream-name inventory found no duplicate.

Validation: the prescribed `scompile.py NS lem-fin-compact-bounded-and-base-change` compiled
this file cleanly using the local side-project overlay. The only postponed proof is the named
main theorem. No statement correction, new nodes, dependency repair, or disputed statement.

## Second reading by NS

Independent second reading: I opened the original node, sandbox node and full Lean module,
then the blueprint source at
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/lem-fin-compact-bounded-and-base-change.md`.
Its statement is unchanged in the DAG and says precisely the following list. I also read the
cited Stacks source passages in `etale-cohomology.tex`: Tag 03S6,
`lemma-shriek-base-change`, permits arbitrary scheme base change and applies to module sheaves;
Tag 095T, `theorem-proper-base-change`, requires properness and torsion coefficients, without
finite type over the original field for the new base. No ambient hypothesis has been omitted.

Object/hypothesis/conclusion checklist, in source order:

1. A field k and a prime ell different from its characteristic: `{k : Type u} [Field k]`,
   `(ℓ : ℕ) [Fact ℓ.Prime]`, `(hℓ : (ℓ : k) ≠ 0)`. This is exactly the condition for the
   prime ell in F_ell; over a field nonzero is equivalent to invertible. Verdict: exact.
2. Finite-type k-schemes X and S: `{X S : Scheme.{u}}`, structure maps `aX`, `aS`, and
   `[LocallyOfFiniteType aX] [QuasiCompact aX]` and the corresponding instances on `aS`.
   I read the Mathlib class definitions: locally of finite type is finite-type affine
   coordinate maps, quasi-compact is compact inverse images of compact opens. Their
   conjunction is finite type. Neither structure map is assumed separated. Verdict: exact.
3. A separated finite-type morphism f between these k-schemes: `(f : X ⟶ S)`,
   `[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]`, and
   `(hf : f ≫ aS = aX)`. The Mathlib separatedness class is closed diagonal, as required.
   The equation specifies compatibility with the displayed k-structures. Verdict: exact.
4. K in D^b_c(X,F_ell): the coefficient type is the actual prime field
   `ULift.{u + 1} (ZMod ℓ)`, and `K : DerivedCategory.Plus (Sheaf ... (ModuleCat ...))`
   with `hK : DerivedCategory.isBoundedConstructible ... X K.obj` supplies exactly this
   condition. I read the dependency module `BoundedConstructibleComplexes`: its predicate
   requires every homology sheaf to satisfy `Scheme.IsConstructibleEtaleModuleSheaf` and
   vanishing outside some integer interval `[a,b]`, with `a ≤ b`. I opened that sheaf
   predicate too: finite locally closed constructible stratification with etale-local finite
   constant module values. I also read Mathlib `DerivedCategory/TStructure.lean`: `Plus`
   is the full subcategory of the same derived category on bounded-below objects. Thus every
   bounded constructible K can be packaged here; no nonnegative bound is imposed. Verdict:
   exact, with a redundant lower-bound witness needed by the recorded exchange interface.
5. Compact direct image Rf_!K is bounded constructible: the first conjunct applies that SAME
   predicate on S to `(rightDerivedLowerShriekOfCompactification ... c).obj K.obj`.
   I read the dependency's source `Etale/Derived/LowerShriek.lean`: this is precisely
   `D((c.i)_!) ⋙ R((c.g)_*)`, on the unbounded derived category, not the right derived
   functor of an underived composite. The extra computing parameter
   `(c : Compactification f)` agrees with `def-amb-etale-compact-support` and
   `def-cbc-exchange-map`. I opened `Compactification/Defs.lean`: c has a proper g, open i,
   and the factorization equation; i is automatically quasi-compact because f is.
   Nagata supplies c under the existing hypotheses, and the assertion is universal in c.
   This is computing data, not an additional geometric restriction. Verdict: exact.
6. For every v:S'→S with Noetherian S': the second conjunct binds
   `∀ (S' : Scheme.{u}) [IsNoetherian S'] (v : S' ⟶ S)` followed by all cartesian
   presentations `(X', vX, f', sq : IsPullback vX f' f v)`. I read `IsNoetherian`:
   locally Noetherian plus compact, not a finite-dimensional or finite-type condition.
   No further assumption is imposed on v or its source. Verdict: exact.
7. The specified exchange v*Rf_!K→Rf'_!vX*K is invertible: the conclusion is `IsIso` of
   `(rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap ... sq c).app K`.
   I obtained and read the current published module with `scompile.py --source`, including
   its binders, definition body and the `derivedPlusFormalism_pfBaseChange` identification.
   It uses exactly c and `c.ofIsPullback sq`, proper derived exchange after extension by
   zero, then the inverse open-immersion base-change comparison. It has the required
   direction and is the specified map, rather than a bare existence of an isomorphism.
   The unbounded/Plus outputs are related by the explicit compatibility isomorphism in
   `LowerShriek.lean`. Verdict: exact; quantifier order and both clauses retained.

I read all four statement-dependency records and their declarations; the scheme-conventions
record explicitly introduces no declaration. No dependency repair or new definition node is
present or needed. There is no statement_change or citer audit to review. The sandbox node
changes only `lean`, and its recorded `lean.statement` agrees verbatim with the source signature.

Edge cases: empty X, empty S and empty S' are not excluded. Neither compactification nor the
cartesian square requires nonempty objects. Zero complexes and complexes supported in degree
zero are included, as are arbitrary negative shifts: there is no fixed lower bound or n>0
condition. There is no index set in this statement. Characteristic zero and ell=2 are included;
ell=0,1 are excluded exactly by primeness. The common scheme universe u is arbitrary; for any
set-sized base-change data one may choose a universe containing the whole diagram. The lifted
finite field is in the dependency's required coefficient universe u+1, and there is no extra
site-universe equality. The new base need not be finite type over k or have bounded dimension.

Independent H4 searches (using different wording from the worker):

- `msearch.py leanfinder`: "Finite field coefficients etale compact support pushforward
  constructible bounded complexes exchange isomorphism" returned eight unrelated affine-limit,
  Chevalley/constructible-subset and etale-locus hits, no matching statement.
- `msearch.py loogle`: `"compactlySupported"` returned 12 continuous-function declarations,
  no etale derived statement. The worker's recorded LeanSearch service failure remains noted.
- `msearch.py grep`: `boundedConstructible.*Shriek|isBoundedConstructible.*compact` returned
  no Mathlib hits. Direct rg across Mathlib, upstream WeilConjectures and project lean/Sheaf
  found no copy of the proposed full declaration name.
- A broader direct rg for bounded constructibility and lower shriek located upstream
  `Etale/Derived/Finiteness/DirectImage.lean:boundedConstructible_rightDerivedLowerShriek`.
  I opened its full signature: it uses the upstream `DerivedCategory.boundedConstructible`
  predicate, chosen compactification, and only the finiteness conclusion. It does not give
  this node's specified conjunction with the recorded project predicate and exchange.
  I also opened `Stability/DirectImage.lean:constructibleFiniteTor_rightDerivedLowerShriek`:
  it concerns finite Tor amplitude and likewise does not state this node. Reusing the
  established functors and the project's recorded predicate here is appropriate.

No mismatch found; no Lean or node content changed. The theorem has one named `sorry`, no
new definition or implemented proof, and its source/blueprint docstring carries the node's
six proof steps, including the absence of a finite-type hypothesis on the new base. All
variables and the sole universe u are explicitly bound. Prescribed independent validation:
`scompile.py NS lem-fin-compact-bounded-and-base-change` on the delivered module passed
both sandbox and library compilation cleanly (3.3 s and 3.7 s), with no diagnostics.

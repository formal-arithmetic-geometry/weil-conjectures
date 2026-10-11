## Worker report

The main module states `AlgebraicGeometry.proper_perfect_directImage_perfect`, with exactly one theorem proof, `sorry`. The earlier sandbox's always-true morphism predicate has been replaced by a genuine finite Tor dimension predicate. No assertion of an independent second reading from the old report is retained: that reading did not detect the invalid predicate, and the dispatcher will supply the second reader after this worker's dry run succeeds.

Clause-by-clause correspondence:

- Schemes X and Y: `{X Y : Scheme.{u}}`.
- Noetherian Y: `[IsNoetherian Y]`.
- A morphism f from X to Y: `(f : X ⟶ Y)`.
- Proper f: `[IsProper f]`.
- Perfect f, in the node's finite Tor dimension sense: `(hperfect : HasStalkwiseFiniteTorDimension f)`. The new predicate is `∀ x, ∃ n, ∀ M, ∀ i > n, IsZero (Tor_i(O_{X,x}, M))`, with scalar restriction along `(f.stalkMap x).hom`. Properness supplies finite type; Y Noetherian makes f pseudo-coherent. Thus Stacks Lemma 37.61.11 identifies this with perfectness and local relative finite Tor dimension; quasi-compactness makes the bound global. The predicate is deliberately named for its stalkwise condition, rather than claiming to define perfect morphisms without pseudo-coherence.
- P belongs to D(O_X): `(P : schemeDerivedCategory X)`.
- Perfect P: `(hP : Scheme.IsPerfect X P)`.
- Derived direct image Rf_*P: `((schemeDerivedDirectImage f).obj P)`.
- Perfectness of that direct image in D(O_Y): `Scheme.IsPerfect Y ((schemeDerivedDirectImage f).obj P)`.

The `HasDerivedCategory` instance binders for X, Y and their open restrictions select the localization infrastructure required by the existing `Scheme.IsPerfect` definition. They impose no geometric restriction. Every universe and variable is bound explicitly. The theorem docstring now carries both proof steps, including the uniform bounds and the application of `lem-pc-bounded-coherent-finite-tor-proper-pushforward-perfect` (Tag 08EV).

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom` and `Scheme.Hom.stalkMap`, from def-pc-scheme.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`, from def-weil-proper-morphism; it extends separatedness, universally closed and locally finite type.
- `Sheaf.AlgebraicGeometry.PerfectComplex`: `AlgebraicGeometry.Scheme.IsPerfect`, from def-pc-perfect-complex. The full definition restricts by `overFunctor.mapDerivedCategory` and asks locally for a strictly perfect representative.
- `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`: `AlgebraicGeometry.schemeDerivedDirectImage`, from def-pc-derived-direct-image. The full definition specializes `RingedSpace.derivedModuleDirectImage` to the underlying ringed-space morphism on the same moduleRings carrier.
- `Mathlib.CategoryTheory.Monoidal.Tor`: `CategoryTheory.Tor'`, from def-weil-pbc-tor-modules. Its first variable is resolved, so the predicate tests finite Tor dimension of O_{X,x} over O_{Y,f(x)}. `ModuleCat.restrictScalars` supplies precisely the action through f, without an arbitrary algebra structure.

Edge cases checked: an empty source gives a vacuous stalk condition (as it should), and its zero perfect objects stay within the statement. For an identity or flat morphism, n = 0 suffices. Bounds are point-dependent and independent of M; no uniform point-bound is added as a hypothesis. The dual-number quotient Spec k → Spec(k[ε]/ε²) is proper but fails the predicate: Tor_i(k,k) is nonzero for every i. This detects the old predicate's always-true fault. Zero derived objects are allowed. Test modules live in the same universe as the local rings; there is no independent smaller universe that could make the test vacuous.

Searches: msearch.py LeanFinder `proper perfect morphism derived direct image of perfect complex is perfect` found only derived-category and properness infrastructure; Loogle `IsPerfect, HasFiniteTorDimension` returned unknown identifier IsPerfect and no hits; Mathlib AlgebraicGeometry grep `perfect.*pushforward|pushforward.*perfect|PerfectMorphism` returned no hits. Additional msearch.py LeanFinder `finite Tor dimension of a morphism of schemes stalk local rings` returned eight stalk-map/local geometry results but no predicate; Loogle `Tor', ModuleCat.restrictScalars` returned no hits; grep `IsPerfectMorphism|HasFiniteTorDimension|perfect.*morphism` returned no hits. LeanSearch was attempted and returned a service error. `rg` of WeilConjectures found no finite Tor predicate or occurrence of the item id; `rg` of lean/Sheaf found only object-level finite Tor predicates. The DAG searches and blueprint_refs.py searches found no general morphism definition (the closed-immersion definition is a specialization). The Tor declaration and its full source signature were read directly in Mathlib, and the existing Tor node is reused.

Source checked online because the local Stacks TeX file is absent: https://stacks.math.columbia.edu/tag/0B6G and Section 37.61 at https://stacks.math.columbia.edu/tag/0685, especially Lemma 37.61.11 condition (3). No correction to the item's statement is needed.

Validation: both delivery modules compile cleanly together on the server (3.2 s, no warnings). The missing SchemeDerivedDirectImage.olean became available during this repair. The combined-file universe collision was repaired with the distinct universe name uTor in the definition module. The first dry run's preflight record-format and updated blueprint-ancestry faults were repaired. A fresh dry run verifies compilation and preflight; the independent second reading is intentionally left to the dispatcher’s next worker. No delivery is pushed.

## New nodes

`def-pc-perfect-morphism` supplies `AlgebraicGeometry.HasStalkwiseFiniteTorDimension`, the stalk-ring criterion for perfectness used in this Noetherian proper setting. Its own statement spells out every Tor vanishing test and the scalar action, cites def-pc-scheme and the existing def-weil-pbc-tor-modules, and notes the source's finite type/Noetherian context for equivalence to perfectness. Source: Stacks Lemma 37.61.11 condition (3), used by 0B6G. The LeanSearch attempt was unavailable; LeanFinder, Loogle and grep results are recorded verbatim in scope in mathlib_searches. The module supplies real data and no sorry. The new node is cited by the item's stmt_deps.

## Second reading by E1

I independently read the item node, its source place (Stacks Tag 0B6G / Lemma 37.61.13), the item module, and the added dependency module.

- The Noetherian target is rendered by `[IsNoetherian Y]`; verdict: exact.
- The schemes and morphism are `{X Y : Scheme.{u}}` and `(f : X ⟶ Y)`; verdict: exact.
- Properness is `[IsProper f]`, using the recorded Mathlib proper-morphism notion; verdict: exact.
- Perfectness of the morphism is the explicit hypothesis
  `(hperfect : HasStalkwiseFiniteTorDimension f)`.  The dependency definition quantifies
  each `x : X`, supplies a point-dependent `n : ℕ`, and requires vanishing for every
  `ModuleCat` test module and every `i > n`, with scalar restriction through
  `(f.stalkMap x).hom`; verdict: this is the node's finite Tor dimension condition.
- The perfect object is `(P : schemeDerivedCategory X)` with
  `(hP : Scheme.IsPerfect X P)`; verdict: exact.
- The conclusion is `Scheme.IsPerfect Y ((schemeDerivedDirectImage f).obj P)`;
  verdict: exact derived direct image and exact target category.
- The `HasDerivedCategory` binders for X, Y, and their open restrictions are the
  localization infrastructure required by the existing `Scheme.IsPerfect` and direct
  image declarations; they impose no geometric hypothesis.  All universes and variables
  are explicit.

The only mismatch was structural: the item node's `stmt_deps` omitted the newly supplied
`def-pc-perfect-morphism`, although its Lean signature uses that definition. I added that
node id to `stmt_deps`; the item statement, source, proof steps, and proof dependencies are
unchanged.

Edge cases remain covered: an empty source makes the stalk condition vacuous; zero perfect
objects are admitted; identity and flat maps allow bound `n = 0`; pointwise bounds are not
silently strengthened to a global hypothesis; and no universe restriction excludes test
modules. The stalkwise predicate also rejects the proper dual-number quotient with infinite
Tor, so it is not tautological.

Searches were rechecked against Mathlib, `WeilConjectures`, and `lean/Sheaf`: no existing
proper-perfect pushforward theorem or general finite-Tor morphism predicate was found. The
recorded LeanFinder/Loogle/grep searches in the worker report remain valid. The two delivery
modules compile together with `scompile.py` and contain only the intended `sorry` theorem
proof.

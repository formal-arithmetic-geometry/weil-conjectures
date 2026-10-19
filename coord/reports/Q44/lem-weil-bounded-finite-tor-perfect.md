## Worker report

The delivery states `DerivedCategory.exists_bounded_finite_projective_model_of_torAmplitudeIn`
in `Sheaf.CategoryTheory.DerivedCategory.BoundedFiniteTorPerfect`. It is one theorem with
`sorry`, not a proof. No definitions, dependency modules, or new nodes are introduced. The
item's node is copied with only its `lean` field changed. The stage-1 ring-level correction
already present in that node is retained verbatim.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A commutative Noetherian ring is `(R : Type u) [CommRing R] [IsNoetherianRing R]`.
  `IsNoetherianRing` is the recorded Mathlib predicate for all ideals being finitely generated.
- The given cochain complex is `K : CochainComplex (ModuleCat.{u} R) ℤ`.
  The hypothesis `hK : ∃ c d : ℤ, K.IsStrictlyGE c ∧ K.IsStrictlyLE d ∧
  ∀ i : ℤ, Module.Finite R (K.X i)` asserts boundedness of the actual complex, together
  with finite generation of every term. Strict bounds are termwise zero bounds, not just
  cohomological bounds. The integers `c,d` need not equal the prescribed Tor bounds.
- Regard it in the chosen derived category by `Q.obj K`, under
  `[HasDerivedCategory.{w} (ModuleCat.{u} R)]`. The localization universe `w` remains
  independent of `u`; it can in particular be the standard localization universe `u+1`.
- The prescribed integers and their order are `(a b : ℤ) (hab : a ≤ b)`.
- The universal Tor test is
  `hTor : torAmplitudeIn (ModuleCat.{u} R) a b (Q.obj K)`.
  The upstream definition in `WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude`
  unfolds to `∀ F : ModuleCat.{u} R,
  homologyConcentratedIn a b (Q.obj K ⊗ (singleFunctor (ModuleCat.{u} R) 0).obj F)`.
  Here `homologyConcentratedIn` is the canonical t-structure's `IsGE a ∧ IsLE b`,
  equivalent to vanishing of every cohomology object outside `[a,b]`. Thus the test is
  against every ordinary module in degree zero, with no finiteness, flatness, residue-field,
  coefficient-site, or boundedness restriction on the test module. The derived tensor
  structure is the upstream canonical derived tensor; the recorded K-flat tensor-model
  declaration identifies it with tensoring K-flat complexes, exactly as the node specifies.
- The first conclusion quantifies `∃ E : CochainComplex (ModuleCat.{u} R) ℤ`.
  Its support clause is `∀ i : ℤ, i < a ∨ b < i → IsZero (E.X i)`, precisely
  `E^i = 0` outside the prescribed interval, including both end points.
  Its terms satisfy `∀ i : ℤ, Module.Projective R (E.X i) ∧ Module.Finite R (E.X i)`.
  The comparison is `Nonempty (Q.obj E ≅ Q.obj K)`, an actual isomorphism in the
  localization, with the source's requested orientation. It is not a termwise isomorphism
  of complexes and does not strengthen quasi-isomorphism to a single chain map.
- The explicit perfectness clause is `IsPerfectRingComplex (Q.obj K)`, using the
  dependency's recorded generalized-universe definition, which is existence of a bounded
  finite-projective model in this same module category and chosen derived category.
- The final clause is conditional: `IsLocalRing R → ∃ E, ...`. For a commutative ring
  Mathlib's local-ring predicate is equivalent to having a unique maximal ideal. It is
  not imposed on the main assertion. The second model again has support in `[a,b]` and
  `Nonempty (Q.obj E ≅ Q.obj K)`, and its terms satisfy
  `∀ i : ℤ, Module.Free R (E.X i) ∧ Module.Finite R (E.X i)`.
  Free and finitely generated means finite free, including the empty basis for zero terms;
  free modules are automatically projective. A separate existential correctly renders
  “can be chosen finite free” rather than claiming all projective models are free.

Recorded statement dependencies used, with their source declarations read:

| Node | Module | Declaration |
| --- | --- | --- |
| def-weil-pbc-noetherian-ring | Mathlib.RingTheory.Noetherian.Defs | IsNoetherianRing |
| def-weil-finitely-generated-module | Mathlib.RingTheory.Finiteness.Defs | Module.Finite |
| def-weil-abstract-derived-category | Mathlib.Algebra.Homology.DerivedCategory.Basic | DerivedCategory, HasDerivedCategory, DerivedCategory.Q |
| lem-pc-source-kflat-module-tensor-model | WeilConjectures.CategoryTheory.DerivedCategory.FlatModel | DerivedCategory.QObjTensorQObjIsoOfKFlatLeft |
| def-weil-pbc-projective-module | Mathlib.Algebra.Module.Projective | Module.Projective |
| def-pc-perfect-ring-complex | Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral | DerivedCategory.IsPerfectRingComplex |
| def-weil-pbc-free-module | Mathlib.LinearAlgebra.FreeModule.Basic | Module.Free |

The upstream `torAmplitudeIn` docstring and full definition and the definition of
`homologyConcentratedIn` were read, as were the tensor-model declaration and its ambient
hypotheses. They use the same canonical derived tensor as the theorem's hypothesis.
`IsPerfectRingComplex` is used instead of upstream `IsPerfect`, whose older interface fixes
the localization universe to `u`. The recorded generalized predicate is already published,
so no repair or second definition is needed. Public imports expose the statement notions;
ordinary imports include every recorded proof-dependency module with a declaration, as
required even though the theorem is `sorry`. The Mathlib proof leaves import Noetherian
submodule finiteness, finite presentation, flatness, finite-presented-flat projectivity,
and finite-flat-local freeness. The declaration docstring carries all six DAG proof steps
and their node names, including the degree-`a` and degree-`a+1` truncation checks.

Sources read: the exact blueprint node at
`literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-rf-shriek-preservation/lem-weil-bounded-finite-tor-perfect.md`;
Stacks `more-algebra.tex`, `definition-perfect` and `lemma-perfect` (Tags 0657 and 0658),
and `algebra.tex`, `lemma-finite-flat-local` (Tag 00NZ), using the read-only literature copy
under the launcher. The current DAG statement has already repaired the original blueprint's
inapplicable site-perfect wording; this delivery states its ordinary-ring result unchanged.
The source gives the prescribed interval and the local finite-free refinement, not merely
existence of some finite projective resolution.

Edge cases checked before finalizing the signature:

- The zero complex admits the zero model for every `a ≤ b`; zero terms are finite,
  projective, and free with empty basis. No nonzero-object assumption is added.
- The zero ring is allowed in the main assertion. Every module is zero, so all conclusions
  there hold. It has no maximal ideal, so the unique-maximal-ideal local clause does not
  apply; `IsLocalRing` correctly requires nontriviality.
- For `a = b`, the model is allowed only in that single degree, matching the bottom
  finite-flat/projective module in the source's good truncation. `a,b` may be negative.
- Boundedness is boundedness of terms, as in the node, and finite generation is not confused
  with a finite underlying set or finite rank over an arbitrary ring.
- Over a field, finite projective and finite free coincide, giving the expected vector-space
  statement. Over a nonreduced local ring such as the dual numbers, the residue field in
  degree zero has unbounded Tor; it is not a counterexample to the universal Tor hypothesis.
- There are no site/scheme variables or nonempty-site assumptions in this ordinary-ring
  theorem. No projective or flat term hypothesis is imposed on the given complex `K`.

Searches made through `msearch.py Q44 lem-weil-bounded-finite-tor-perfect`:

1. LeanFinder query: “A bounded complex of finite modules over a Noetherian ring with Tor
   amplitude in [a,b] has a finite projective model concentrated in [a,b], finite free over
   a local ring”. Result: eight hits, including `CochainComplex.isKProjective_of_projective`,
   projective Tor-vanishing, and projective-dimension results. None gives this theorem.
2. Loogle query: `CochainComplex, Module.Projective`. Result: zero hits.
3. Mathlib grep query: `torAmplitude|finiteTorAmplitude|IsPerfectRingComplex|bounded_finite_projective`
   in `Algebra/Homology`. Result: zero hits.
4. LeanSearch query: “A bounded complex of finitely generated modules over a commutative
   Noetherian ring with Tor amplitude [a,b] has a finite projective model in [a,b] and a
   finite free model when the ring is local”. Result: service unavailable, Internal Server
   Error; no mathematical verdict is attributed to the unavailable service.
5. `rg` in upstream `WeilConjectures`, the project's `lean/Sheaf`, and
   `dag/lean_names_upstream.json` for the new declaration name and exact blueprint id:
   no existing declaration. Related-concept searches for finite-projective models,
   Tor amplitude, and perfectness found the upstream `DerivedCategory.isPerfect_of_finiteTorAmplitude`
   and `DerivedCategory.isPerfect_of_torAmplitudeIn`. Their signatures and docstrings were
   read: they yield `IsPerfect`, without a model in the specified interval or the local
   finite-free clause, so they are not an exact existing declaration for this node.
6. The same project search found
   `DerivedCategory.exists_bounded_finite_projective_model_of_flat_of_finite_homology`
   in `Sheaf.CategoryTheory.DerivedCategory.NoetherianFlatComplexPerfect`; its source and
   signature were read. It has a different flat-model hypothesis and only an unspecified
   bounded finite-projective model, so it is not the requested statement.

No statement is disputed. No dependency declaration was replaced. No additional helper
notion was required, and no existing project definition was duplicated.

Validation: `scompile.py Q44 lem-weil-bounded-finite-tor-perfect` compiled the final module
with its complete six-step proof docstring and all required proof-dependency imports. Both
the sandbox and library-path checks passed without errors or warnings (15.0 and 54.4 seconds).
A final static check confirmed that only `lean` changed in the node, the recorded signature
is verbatim, the single theorem has exactly one `sorry`, and all Lean lines are at most
100 characters. The prescribed `deliver2.py ... --no-push` is the final gate. No delivery
is pushed by this worker; the independent second reader adds its review and delivers.

## Second reading by Q44

I independently read the current DAG node, its seven statement-dependency nodes and
their recorded declarations, the sandbox module, and the original blueprint text.
The literature copies used were under `/home/ubuntu/weil-launcher-nt/literature/`:
`more-algebra.tex`, definition-perfect, lemma-perfect and
lemma-Noetherian-pseudo-coherent (Tags 0657, 0658 and 066E), and `algebra.tex`,
lemma-finite-flat-local (Tag 00NZ). Tag 0658 explicitly gives the prescribed
interval, and Tag 00NZ gives finite freeness over a local ring. The Noetherian
hypothesis gives pseudo-coherence by Tag 066E. These are ordinary commutative-ring
statements, with no field, characteristic or scheme hypothesis. The earlier stage-1
ring-level repair is already on the base; this delivery has no `statement_change`.

My object/hypothesis/conclusion checklist, made from the node before comparing Lean:

1. A commutative Noetherian ring R: `(R : Type u) [CommRing R]
   [IsNoetherianRing R]`. PASS. I opened Mathlib's `IsNoetherianRing` and
   `isNoetherianRing_iff_ideal_fg`: the predicate is precisely finite generation of
   all ideals, without nontriviality or a field assumption.
2. A bounded cochain complex K of finite R-modules: `K : CochainComplex
   (ModuleCat.{u} R) ℤ`, and `hK : ∃ c d : ℤ, K.IsStrictlyGE c ∧
   K.IsStrictlyLE d ∧ ∀ i : ℤ, Module.Finite R (K.X i)`. PASS. The definitions
   and `isStrictlyGE_iff`/`isStrictlyLE_iff` in Mathlib's
   `Algebra/Homology/Embedding/CochainComplex.lean` confirm that these are bounds
   on terms, not merely cohomology. `Module.Finite` is finite generation of the
   top submodule. The bounds c,d are existential and independent of a,b.
3. Regard K in D(R): `Q.obj K`, with
   `[HasDerivedCategory.{w} (ModuleCat.{u} R)]`. PASS. I opened the dependency
   node's localization signature and Mathlib's `DerivedCategory.Basic`; this is
   localization at quasi-isomorphisms, not the homotopy category. Universe w is
   independently bound, with no equality to u imposed.
4. Fixed integers a <= b: `(a b : ℤ) (hab : a ≤ b)`. PASS. Both endpoints
   remain arbitrary integers, preceding the Tor hypothesis and model existentials.
5. For every ordinary module M, all cohomology of K tensor-derived M outside
   [a,b] vanishes: `hTor : torAmplitudeIn (ModuleCat.{u} R) a b (Q.obj K)`.
   PASS. I opened `TorAmplitude.lean`: its definition quantifies over every
   `F : ModuleCat.{u} R` and tensors with `(singleFunctor _ 0).obj F`.
   `homologyConcentratedIn` in the upstream t-structure file is exactly
   `IsGE a ∧ IsLE b`. There is no finite, flat or residue-field restriction on F.
   I also read `FlatModel.lean`, including its ambient assumptions and
   `QObjTensorQObjIsoOfKFlatLeft`: this is the recorded canonical derived tensor
   with its K-flat total-complex comparison, for arbitrary second complexes.
   The module-category instances supply its categorical infrastructure; none is
   added as a mathematical hypothesis to the item.
6. There exists a finite-projective complex E, supported in [a,b], isomorphic to
   K in D(R): the first `∃ E : CochainComplex (ModuleCat.{u} R) ℤ`, followed by
   `∀ i, i < a ∨ b < i → IsZero (E.X i)`,
   `∀ i, Module.Projective R (E.X i) ∧ Module.Finite R (E.X i)`, and
   `Nonempty (Q.obj E ≅ Q.obj K)`. PASS. `E.X i` is a categorical module object,
   so `IsZero` is the appropriate notion. I read Mathlib's projectivity
   splitting definition. The comparison is an isomorphism in the localization,
   without demanding an isomorphism of complexes or a particular chain map.
7. K is perfect: `IsPerfectRingComplex (Q.obj K)`. PASS. I opened the recorded
   `PerfectRingComplexGeneral.lean`: it asks for a bounded finite-projective
   complex in the very same module category and localization universe, with an
   isomorphism in D(R). No private definition or restricted upstream `IsPerfect`
   has been substituted.
8. If R has a unique maximal ideal, E can be chosen finite free in the same
   degrees: `IsLocalRing R → ∃ E, ...` with the same support and comparison
   clauses and `∀ i, Module.Free R (E.X i) ∧ Module.Finite R (E.X i)`. PASS.
   Mathlib's local-ring predicate includes nontriviality, as does having a unique
   maximal ideal. Its `Module.Free` supplies a basis; together with finite
   generation this means finite free. A second existential correctly states
   existence of a free model. No locality is assumed in the main conclusion.

Edge cases: the zero complex and all zero terms are allowed, with empty bases;
the zero ring is allowed in the main assertion and is correctly excluded only
from the conditional local case. The singleton interval a=b, including a=b=0,
is included. Negative endpoints and all characteristics are included. No
nonempty index set is required for a basis. There is no scheme/site variable,
so an empty scheme adds no case here. The coefficient/module universe u is
arbitrary, and the chosen localization universe w is independent; the universal
Tor test ranges over all modules in the coefficient category used by the node.

Independent H4 searches (different wording from the first reader):

- `msearch.py ... leanfinder`: "A Noetherian commutative ring complex of finite
  modules with bounded Tor dimension admits a projective resolution supported
  in the given Tor interval, free when local". Eight hits: projective-dimension
  predicates, Tor-vanishing for projectives, and general projective resolutions;
  none states the node's result.
- `msearch.py ... loogle 'Module.Finite, Module.Free, CochainComplex'`: zero hits.
- `msearch.py ... leansearch`: "A finite complex over a Noetherian ring with Tor
  amplitude a b is represented by finite projective modules in degrees a through b".
  The service returned Internal Server Error; no mathematical verdict is inferred.
- Direct `rg` of Mathlib's `Algebra/Homology` and `RingTheory` for Tor amplitude
  and finite-projective complexes found no statement. Direct searches of
  upstream `WeilConjectures`, project `lean/Sheaf`, and `dag/lean_names_upstream.json`
  found no declaration with the new name or blueprint id. Searches for finite
  projective/free models also found
  `DerivedCategory.isPerfect_of_pseudoCoherent_finiteTorAmplitude` in the project.
  I opened its complete signature: it gives an unspecified bounded projective
  model from pseudo-coherence, without the prescribed interval or local clause.
  I likewise read the upstream `isPerfect_of_finiteTorAmplitude` and project
  `exists_bounded_finite_projective_model_of_flat_of_finite_homology` signatures;
  neither is the exact statement. The upstream `isPerfect_of_torAmplitudeIn`
  is a private induction lemma, also returning only `IsPerfect`.

No missing notion or unusable recorded dependency was found. There are no new
nodes or dependency modules in this delivery. No hollow definition, extra
theorem, proof, local notation or unbound variable/universe was found. The
theorem's source/blueprint docstring carries all six DAG proof steps, including
the checks in degrees a and a+1 and the local bottom-term argument. The imports
include the recorded statement dependencies and the available proof dependencies.

Mismatches found: none. Changes made: this independent review section only;
the Lean file and node signature are preserved. A static check verified the
node's `lean.statement` verbatim against the file, one theorem with one `sorry`,
and the 100-column convention. I reran the prescribed `scompile.py` on the
delivered file: sandbox and library-path compiles both passed (31.9 s and 18.3 s),
with no errors or warnings.

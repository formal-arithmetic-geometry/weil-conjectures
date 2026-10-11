## Worker report

The module `Sheaf.AlgebraicGeometry.IsProperOfFieldBaseChange` states
`AlgebraicGeometry.isProper_of_field_baseChange`, with its sole proof `sorry`.
No definition or dependency module is added, and no statement correction is needed.

Hypothesis and clause mapping:

- The field extension `k ⊆ K` is `{k K : Type u} [Field k] [Field K] [Algebra k K]`.
  The embedding is `algebraMap k K`; a homomorphism between fields is injective.
  Its induced scheme morphism is `Spec.map (CommRingCat.ofHom (algebraMap k K))`.
- The scheme `X` over `k` is `{X : Scheme.{u}} (f : X ⟶ Spec (.of k))`.
  An explicit structure morphism contains precisely the data of a scheme over this base;
  it imposes no affine, nonempty, integral, smooth, or separated hypothesis.
- Finite type over `k` is `[LocallyOfFiniteType f] [QuasiCompact f]`, the two parts of
  `def-weil-finite-type-morphism`'s recorded Mathlib match.
- The base change `X_K = X ×_{Spec k} Spec K` is the domain of
  `pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))`.
  This is the second projection, hence its structure morphism over `K`.
- Properness of `X_K` over `K` is the `IsProper` instance on that second projection.
- Properness of `X` over `k`, the entire conclusion, is `IsProper f`.

Dependency declarations read and used:

- `def-pc-field-extension`: `Algebra`, `algebraMap` from
  `Mathlib.Algebra.Algebra.Defs`, and `AlgebraicGeometry.Spec.map` from
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` from
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, and `AlgebraicGeometry.QuasiCompact`
  from `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `def-pc-base-change`: `Sheaf.AlgebraicGeometry.BaseChangeConventions` is imported.
  Its module docstring and node record specify `CategoryTheory.Limits.pullback` and
  `pullback.snd` for scheme base change (also explicitly confirmed by `coord/STATE.md`).
  The recorded main declaration `Scheme.Modules.moduleBaseChange` is module base change,
  and is intentionally not applied to schemes.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsProper` from
  `Mathlib.AlgebraicGeometry.Morphisms.Proper` is imported. It uses locally finite type,
  separatedness and universal closedness; universal closedness implies quasi-compactness,
  so this is precisely the node's properness, not a weakened version.

Edge cases checked: `K = k` is allowed; no finite, algebraic or separable extension is
required, so transcendental extensions such as `k(t)` are included. The empty scheme is
allowed and proper. Any characteristic is allowed. No geometric integrality or connectedness
is imposed. The universe `u` is explicit and arbitrary; placing schemes and both fields in
one common universe matches Mathlib's scheme category and does not impose a cardinality bound.
There are no auto-bound variables or universes.

Source checked: the local Stacks checkout is absent on this machine. Opened
[Stacks Tag 02L1](https://stacks.math.columbia.edu/tag/02L1), Lemma 35.23.16,
which states fpqc locality of properness on the base. The node is its field-extension
specialization with the stated finite-type assumption retained. The declaration docstring
contains all four steps of the node's proof, with their dependency ids.

Searches (real tool output is recorded in `searches.jsonl`):

- `msearch.py leanfinder`: “If a finite type scheme over a field becomes proper after
  extending the field then it is proper”: eight hits, including finite implies proper,
  properness consequences and `isProper_eq`; none is this descent statement.
- `msearch.py loogle`: `AlgebraicGeometry.IsProper, CategoryTheory.Limits.pullback.snd`:
  only `AlgebraicGeometry.IsProper.instSndScheme`, the forward base-change implication.
- `msearch.py grep`: `IsProper.*(descend|pullback)|proper.*descend`, subdirectory
  `AlgebraicGeometry`: twenty hits on descent machinery and base-change stability,
  no field-extension properness descent statement.
- `msearch.py leansearch`: “Properness of a scheme descends along any field extension”:
  service unavailable (Internal Server Error), recorded as unavailable.
- `rg -n 'proper.*descend|IsProper.*of_|of_.*IsProper'` in upstream
  `WeilConjectures` and project `lean/Sheaf`: found
  `AlgebraicGeometry.isProper_smoothOfRelativeDimension_geometricallyIntegral_of_isPullback`
  in upstream `WeilConjectures.AlgebraicGeometry.EffectiveDescent`. Its full signature
  additionally assumes smoothness of a specified relative dimension and geometric integrality
  of the base change, and its conclusion contains all three properties. It is not the node's
  statement. Other hits concern base-change stability, composition, or special schemes.
- `grep -rn 'lem-pc-proper-descends-field'` upstream: no result.
- Name search `isProper_of_field|isProper_of.*baseChange|proper_descends_field` in
  `dag/lean_names_upstream.json`, project Lean, and upstream: no existing declaration.

Validation: `scompile.py C1 lem-pc-proper-descends-field` compiled the module on the server
in 1.8 seconds, exit code 0, without errors or warnings.

## Second reading by C1

I independently read the item node and its four proof steps alongside
`IsProperOfFieldBaseChange.lean`, and opened all five statement dependency nodes.
The local Stacks .tex checkout is absent. I read the authoritative
[descent.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/descent.tex),
section `section-descending-properties-morphisms-fpqc` and lemma
`lemma-descending-property-proper`, together with [Tag 02L1](https://stacks.math.columbia.edu/tag/02L1).
The section concerns arbitrary morphisms of schemes; it imposes no standing Noetherian,
separated, finite-presentation or characteristic hypothesis. Properness is fpqc local on
this base. The node retains its explicit finite-type hypothesis and specializes the source
to the singleton field-spectrum cover. This is a valid specialization, without a node
correction.

My object/hypothesis/conclusion inventory and its Lean matching:

1. A field `k`: `{k : Type u} [Field k]`. Exact.
2. An extension field `K` with a chosen embedding of `k`: `{K : Type u} [Field K]
   [Algebra k K]`. Exact. The dependency `def-pc-field-extension` explicitly identifies
   this convention with a field and a ring map. I read `Algebra` in
   `Mathlib/Algebra/Algebra/Defs.lean:95`; it records the ring map `algebraMap k K`,
   with scalar multiplication determined by that map, so adds no restriction to a field
   extension. In `Scheme.lean:479`, `Spec.map` reverses this map to `Spec K ⟶ Spec k`.
3. A scheme `X` over `k`: `{X : Scheme.{u}} (f : X ⟶ Spec (.of k))`. Exact.
   I read `Scheme` and `Scheme.Hom` in `Scheme.lean:42,74`: local affine schemes and
   morphisms of locally ringed spaces, as `def-pc-scheme` requires. The morphism `f`
   supplies the entire over-base structure, without an extra `CanonicallyOver` instance.
4. Finite type of that structure morphism: `[LocallyOfFiniteType f] [QuasiCompact f]`.
   Exact. I read `def-weil-finite-type-morphism` and both classes in `FiniteType.lean:43`
   and `QuasiCompact.lean:43`: affine ring maps of finite type and compactness of open
   preimages. These are precisely the dependency's two conditions, not merely local
   finite type and not finite presentation.
5. The scheme `X_K` and its morphism to `Spec K`: the domain and map
   `pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))`. Exact.
   I opened the landed `BaseChangeConventions.lean`: its module convention specifies
   `pullback f T.hom`, `pr_T = pullback.snd`, `f_T = pullback.fst`. The dependency's
   recorded main declaration `moduleBaseChange` concerns modules only; using it here
   would be the wrong object. The imported module and its expressly recorded scheme
   convention are usable without a dependency repair or private definition.
6. Hypothesis proper over `K`: `[IsProper (pullback.snd f (...))]`. Exact.
7. Conclusion proper over `k`: `IsProper f`. Exact; the only conclusion.
   For both occurrences I opened `def-weil-proper-morphism` and `Proper.lean:42`.
   `IsProper` combines separatedness, universal closedness and local finite type;
   `UniversallyClosed.lean:167` supplies quasi-compactness, so it is exactly separated,
   finite type and universally closed as the node defines it.

The quantifier order fixes the two fields and their chosen extension structure before
`X` and `f`; properness of its chosen base change implies properness of that same `f`.
There is no added smoothness, integrality, affineness, connectedness, nonemptiness,
Noetherianity or separability instance. The Lean does not drop a hypothesis or clause.

Edge cases: the empty scheme is allowed (no inhabitant or point of `X` is requested).
The trivial extension `K = k`, arbitrary transcendental extensions and inseparable
extensions are allowed; both characteristic zero and positive characteristic are allowed.
The zero ring is not a field in the node or Lean; zero/empty schemes remain permitted.
There is no indexed family or natural number parameter, so empty index sets and `n = 0`
are not additional restrictions to check. `universe u` is explicitly declared and arbitrary;
using a common universe is Mathlib's ambient scheme-category convention. Any fields and
scheme can be placed in a sufficiently large common universe, with no fixed size bound.
All variables and universes in the signature are bound.

Independent searches, with different wording from the first worker:

- `msearch.py C1 lem-pc-proper-descends-field leanfinder` with “A morphism to the spectrum
  of a field is proper if its pullback to an extension field is proper”: eight hits,
  including `compactSpace_of_universallyClosed`, `isProper_iff`, and properness
  consequences; no matching descent statement.
- `msearch.py ... loogle '"IsProper", "IsPullback"'`: zero hits.
- `rg` in Mathlib, upstream `WeilConjectures` and project `lean/Sheaf` for properness
  paired with “faithfully”, “surject”, “descend” or “field”, and for
  `IsProper.*descendsAlong|DescendsAlong.*IsProper|isProper_of_field_baseChange|02L1`:
  no existing exact statement or conflicting declaration name. I opened upstream
  `WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/FlatDescent.lean`; it descends
  flatness, affineness and finiteness, not this statement. I also opened the full
  `isProper_smoothOfRelativeDimension_geometricallyIntegral_of_isPullback` signature
  in `EffectiveDescent.lean:142`: its smooth-relative-dimension and geometric-integrality
  hypotheses are absent from this node, so it cannot replace this theorem.
- Name checks also included `dag/lean_names_upstream.json`.

No mismatch was found and no Lean or node change was necessary. There are no new
nodes or dependency modules in this delivery, no definition with postponed data, and
nothing is proved: the theorem's sole proof is `by sorry`. Its docstring includes the
source and blueprint id and faithfully follows the node's four proof steps: field-spectrum
fpqc cover; separatedness descent; universal-closedness descent; the finite-type conjunction.
The header, namespace, imports and line widths follow the project's conventions. The
`lean.statement` record matches the theorem signature verbatim, ending before `:= by`.

Second-reader validation: `scompile.py C1 lem-pc-proper-descends-field` with the sandbox
module's absolute path compiled on the server in 1.8 seconds, exit code 0, with no
errors or warnings. An initial invocation with a repository-relative path failed locally
because this module exists only in the sandbox; using its absolute path resolved that.

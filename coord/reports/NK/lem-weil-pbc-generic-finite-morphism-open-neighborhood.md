## Worker report

The module `lean/Sheaf/AlgebraicGeometry/Morphisms/GenericFiniteOpenNeighborhood.lean`
states `AlgebraicGeometry.Scheme.Hom.exists_dense_open_isFinite_of_finite_generic_fibers`.
Its sole proof is `sorry`; no definitions or auxiliary theorems are introduced.
The statement is unchanged. Source checked directly in
`literature/stacks-project/morphisms.tex`, lemma-generically-finite (Tag 02NW):
(1) implies (4) gives a finite restriction about each component generic point.
Their union is still a finite restriction, by target locality, and is dense.

Clause-by-clause correspondence:

- Schemes and morphism: `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
  The universe `u` is explicit and arbitrary; no implicit variables are auto-bound.
- Quasi-compact morphism: `[QuasiCompact f]`.
- Quasi-separated morphism: `[QuasiSeparated f]`, using the quasi-compact diagonal class.
- Locally of finite type: `[LocallyOfFiniteType f]`; this does not impose finiteness
  of all fibres, separation, or affineness.
- Noetherian target, explicitly locally Noetherian and quasi-compact:
  `[IsLocallyNoetherian Y] [CompactSpace Y]`.
- Every component: `∀ (Z : Set Y), Z ∈ irreducibleComponents Y → ...`.
- Every generic point of that component: `∀ (η : Y), IsGenericPoint η Z → ...`.
- Finite set-theoretic fibre: `(f ⁻¹' {η}).Finite`, in the hypothesis `hfinite`.
  This concerns the actual underlying point map, with no residue-degree condition.
- Open subscheme: `∃ V : Y.Opens, ...`, whose canonical scheme is `V.toScheme`.
- Dense: `Dense (V : Set Y)`.
- Contains all component generic points: the second conjunct repeats the same
  universal component and generic-point binders and concludes `η ∈ V`.
- Full inverse-image restriction finite: `IsFinite (f ∣_ V)`. The existing
  `AlgebraicGeometry.morphismRestrict` has domain `(f ⁻¹ᵁ V).toScheme` and codomain
  `V.toScheme`; this is not an independently chosen open in X.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`:
  `AlgebraicGeometry.QuasiCompact` (also imported through the statement modules).
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`:
  `AlgebraicGeometry.QuasiSeparated`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.Topology.Sober`: `IsGenericPoint` (closure of a singleton).
- `Mathlib.Topology.Irreducible`: `irreducibleComponents` (maximal irreducible sets).
- `def-weil-pbc-scheme-conventions` expressly introduces no separate declaration;
  its underlying properties above are used directly.
- `Mathlib.AlgebraicGeometry.Restrict`: `AlgebraicGeometry.morphismRestrict`,
  supplied by the imported morphism modules.

All available proof-dependency modules are imported without `public` when not
already statement imports: Pullbacks, Fiber, Properties, OpenImmersion,
Morphisms.ClosedImmersion, IdealSheaf.Subscheme, RingTheory.Spectrum.Prime.Topology,
GroupTheory.MonoidLocalization.Away, Sheaf.AlgebraicGeometry.FiniteDiscreteFiber,
WeilConjectures.Mathlib.AlgebraicGeometry.Properties, and
WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact.
The algebra input `lem-weil-pbc-minimal-prime-finite-type-algebra-finite-away`
has no Lean record on the provided base, so there is no import for it yet.
The theorem docstring carries all six original proof steps and their dependency ids.

Edge cases checked before writing:

- Empty target: the quantifiers over components are vacuous, and the empty open
  is dense in the empty target; its full inverse image is empty and finite.
  There is no `Nonempty` hypothesis.
- Empty source and empty generic fibres: `Set.Finite` includes the empty set.
  Stacks' construction uses the empty affine scheme if needed; the complement
  removal gives a neighbourhood with empty inverse image.
- Reducible or disconnected targets: the hypothesis and conclusion quantify over
  every component, not a chosen component or only one nonempty open. The proof
  takes a union of neighbourhoods rather than their intersection.
- Nilpotents are retained: neither scheme is assumed reduced or integral, and
  the conclusion is the genuine finite scheme morphism property.
- No characteristic restriction, algebraic closure, separatedness, or affineness
  was added. `CompactSpace Y` is topological quasi-compactness without Hausdorffness.

Searches for existing declarations (2026-10-15):

1. `msearch.py ... leanfinder` query:
   "A quasi compact quasi separated locally finite type morphism of schemes with
   finite fibers over component generic points is finite over a dense open
   containing these points". Eight hits, including `LocallyQuasiFinite`,
   `instLocallyQuasiFiniteOfIsFinite`, `LocallyOfFiniteType`,
   `Scheme.instIsDominantToImageOfQuasiCompact`, `locallyQuasiFinite_iff`,
   `instLocallyQuasiFiniteOfIsImmersion`, and
   `LocallyQuasiFinite.quasiFinite_appLE`; none states this neighbourhood theorem.
2. `msearch.py ... loogle 'AlgebraicGeometry.IsFinite, IsGenericPoint'`:
   zero hits.
3. `msearch.py ... grep 'generically.*finite|finite.*generic' AlgebraicGeometry`:
   hits in Mathlib Properties and Morphisms.Smooth, concerning finite-type generic
   stalks and smooth loci, not this assertion.
4. `rg -n 'generically.*finite|finite.*generic|<item id>'` over the upstream
   `WeilConjectures/` and side `lean/Sheaf/`: related generic splitting, curve,
   module, and etale extension statements, plus upstream GenericFiniteness.lean.
   Read GenericFiniteness.lean in full: its irreducible-space theorem additionally
   assumes affine irreducible target, locally quasi-finite morphism, and separation;
   its Noetherian-space theorem assumes affine source and local quasi-finiteness
   and gives only a nonempty open. Neither is this node's statement.
5. `rg` over `dag/lean_names_upstream.json` for finite/dense/generic combinations:
   no exact match. Searched the chosen declaration name in Mathlib, upstream,
   and `lean/Sheaf/`: no collision.
6. `grep -rn '<item id>'` over upstream `WeilConjectures/`: no hits.
7. `msearch.py ... leansearch` query:
   "A quasi compact quasi separated morphism locally of finite type with finite
   generic fibers is finite over a dense open of a Noetherian target".
   Service unavailable (Internal Server Error); no mathematical verdict inferred.

Validation: `scompile.py NK lem-weil-pbc-generic-finite-morphism-open-neighborhood`
compiled this module cleanly on the server in 1.4 seconds, nice 19, two threads,
with the 60 second per-file limit. No local compiler was run.
No statement correction, new nodes, unusable dependencies, or statement dispute.

## Second reading by NK

I independently read the sandbox node and its Lean file against
`literature/stacks-project/morphisms.tex`, lines 13184--13268, including the
section introduction, the complete statement of lemma-generically-finite
(Tag 02NW), and its proof. There is no ambient field, characteristic,
separatedness or integrality assumption. Its (1) implies (4) applies at each
component generic point under precisely the morphism assumptions here.
The node additionally assumes Noetherian Y; those explicit node hypotheses
must remain even though this source implication does not need them.
Taking the union of the resulting neighbourhoods gives the stated dense open.
No correction of the node is required.

My object/hypothesis/conclusion checklist (all verdicts: exact):

- Arbitrary schemes X and Y, and their morphism f: `{X Y : Scheme.{u}}`
  and `(f : X ⟶ Y)`. I opened Scheme and Scheme.Hom in Mathlib's
  AlgebraicGeometry/Scheme.lean: these are locally affine locally ringed
  spaces and their locally ringed space morphisms.
- Quasi-compact f: `[QuasiCompact f]`. I opened Morphisms/QuasiCompact.lean:
  this requires compact inverse images of compact opens, equivalent to the
  affine-open formulation of def-weil-finite-type-morphism.
- Quasi-separated f: `[QuasiSeparated f]`. I opened its class in
  Morphisms/QuasiSeparated.lean: its field is quasi-compactness of the
  pullback diagonal, exactly def-weil-quasi-separated-morphism.
- Locally finite type f: `[LocallyOfFiniteType f]`. Its class in
  Morphisms/FiniteType.lean requires finite-type ring maps on affine pairs,
  the equivalent affine-pairs version of the dependency node's cover definition.
- Noetherian Y, meaning locally Noetherian and quasi-compact:
  `[IsLocallyNoetherian Y] [CompactSpace Y]`. I opened the class in
  Noetherian.lean, requiring Noetherian section rings on affine opens;
  pqf-def-locnoeth records its equivalence with the affine-cover formulation.
  CompactSpace asserts quasi-compactness without a Hausdorff assumption.
- Every component Z: `∀ (Z : Set Y), Z ∈ irreducibleComponents Y →`.
  I opened Topology/Irreducible.lean: components are maximal irreducible sets.
- Every generic point eta of each such Z:
  `∀ (η : Y), IsGenericPoint η Z →`. I opened Topology/Sober.lean:
  this is `closure {η} = Z`, with membership automatic. Scheme sobriety
  ensures these quantifiers see every component, so the hypothesis is not hollow.
- Finite set-theoretic fibre at each such eta: `(f ⁻¹' {η}).Finite` in
  `hfinite`. It is the preimage under f's underlying point map, not a
  stronger algebraic, geometric-fibre or residue-degree requirement.
- An open subscheme V of Y: `∃ V : Y.Opens`. The canonical scheme is
  `V.toScheme`; no noncanonical open embedding or independent source open.
- V dense: `Dense (V : Set Y)`.
- V contains all component generic points: the second conjunct repeats
  exactly the component and generic-point quantifiers and concludes `η ∈ V`.
- The entire inverse-image restriction is finite: `IsFinite (f ∣_ V)`.
  I opened morphismRestrict in Restrict.lean: its source is
  `(f ⁻¹ᵁ V).toScheme`, its target V.toScheme. I opened IsFinite in
  Morphisms/Finite.lean: it extends IsAffineHom and requires finite ring
  maps on every affine open, precisely def-weil-finite-integral-morphism.
  The existential V follows hfinite and all the universal input binders.

I opened all eight statement dependency node records and read their statements,
Lean records and Mathlib matches. def-weil-pbc-scheme-conventions explicitly
collects conventions without defining another object; the other seven are
rendered by the declarations checked above. None needs a substitute, an extra
instance, or a dependency module. There are no new nodes, dependency modules,
private notions, definitions with postponed data, or auxiliary results in this
delivery. The sole theorem proof is `sorry`. Its module and theorem docstrings
name the source and blueprint id; the theorem docstring reproduces all six
proof steps and their dependency ids. Available proof dependency modules are
imported. The algebraic localization proof dependency has no Lean declaration
yet; it is not required to state or compile this theorem.

Edge cases: empty Y has no component generic points, and its empty open is
dense with empty inverse image; no Nonempty binder excludes it. Empty X and
empty generic fibres are allowed by Set.Finite, including the n=0 construction
in the proof. Reducible and disconnected Y are covered component by component;
the union of neighbourhoods contains all generic points. Nonreduced schemes
are allowed: no reduction or integral structure was substituted. There is no
characteristic, coefficient-ring or field restriction. The explicit arbitrary
universe u is shared by the scheme category and its morphism, with no test
objects in an independently smaller universe. No implicit variable is unbound.

Independent searches (2026-10-15):

- LeanFinder via msearch.py, query "finite morphism on an open neighbourhood
  of every maximal generic point for a qcqs morphism with finite point fibres":
  eight hits, chiefly LocallyQuasiFinite and finite-type ring-map properties;
  none is this theorem.
- Loogle via msearch.py, `AlgebraicGeometry.IsFinite, Dense`: zero hits.
- LeanSearch via msearch.py, "A morphism locally of finite type that is quasi
  compact and quasi separated and has finite generic fibers is finite over an
  open containing all generic points": service unavailable (Internal Server
  Error), recorded as unavailable; no absence verdict taken from that service.
- Direct rg with `generically.?finite|finite.*generic|generic.*finite` in
  Mathlib/AlgebraicGeometry, and finite/generic/dense variants in upstream
  WeilConjectures and this project's lean/Sheaf: no exact existing theorem.
  I located and opened upstream AlgebraicGeometry/GenericFiniteness.lean in
  full. Its irreducible-space theorem assumes affine irreducible target,
  separation and local quasi-finiteness; its Noetherian-space theorem assumes
  affine source and local quasi-finiteness and only produces a nonempty open.
  These signatures do not state the present assertion and cannot replace it.

No mathematical or convention mismatch was found; the Lean file and node are
unchanged. A direct string comparison confirms lean.statement equals the
complete theorem signature before `:= by` verbatim. Only this independent
second-reading section was appended to the report. Server compilation and
final delivery preflight are recorded below.

Second-reader validation: scompile.py compiled the sole delivered module cleanly
on the server in 1.3 seconds, nice 19, two threads, limit 60 seconds; no warnings
or errors. The first invocation used a relative path from the read-only checkout
and failed before compiling; rerunning from the sandbox resolved that path.

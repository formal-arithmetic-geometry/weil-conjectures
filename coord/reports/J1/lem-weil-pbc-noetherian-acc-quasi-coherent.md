## Worker report

The module `Sheaf.AlgebraicGeometry.NoetherianQuasicoherentSubmodules` states
`AlgebraicGeometry.noetherian_quasicoherent_submodules`. It introduces no definitions and
leaves precisely this named theorem with proof `sorry`. The item is unchanged outside
its `lean` field; no new nodes, dependency modules, or statement correction are needed.

Hypotheses and clauses, matched individually:

- A scheme X: `(X : Scheme.{u})`.
- X locally Noetherian and quasi-compact: `[IsNoetherian X]`, whose Mathlib declaration
  extends both `IsLocallyNoetherian X` and `CompactSpace X`. The former is the declaration
  recorded by `pqf-def-locnoeth`; its every-affine-open definition is equivalent to the
  existence-of-an-affine-Noetherian-cover definition in that node.
- An O_X-module F: `(F : SheafOfModules.{u} (moduleRings X.toRingedSpace))`, the same
  carrier as the coherence dependency.
- F coherent: `(hF : RingedSpace.IsCoherent X.toRingedSpace F)`, exactly the dependency's
  definition: finite type, and finite-type kernels of maps from finite free modules on
  every open. No quasi-coherence hypothesis on F is added.
- A sequence of submodules of F: `G : ℕ → Subobject F`. Subobjects are monomorphisms
  into F modulo isomorphisms commuting with that embedding; thus equality is equality
  of submodules, rather than a choice of presentation of an embedded sheaf.
- Increasing: `Monotone G`, the inclusion order on subobjects.
- Every member quasi-coherent: the hypothesis
  `∀ n, (G n : SheafOfModules.{u} (moduleRings X.toRingedSpace)).IsQuasicoherent`.
  The coercion picks the underlying module of the subobject. Quasi-coherence is invariant
  under isomorphism, so this choice has no mathematical effect.
- Eventually constant: `∃ n, ∀ m, n ≤ m → G m = G n` (first conjunct).
- Every nonempty set of quasi-coherent submodules of F: `S : Set (Subobject F)`,
  `S.Nonempty`, and quasi-coherence of each `G ∈ S` (second conjunct).
- It has a maximal element for inclusion: `∃ G ∈ S, ∀ H ∈ S, G ≤ H → H = G`.
  This asserts maximality, with no greatest-element requirement.
- Every nonempty set of quasi-coherent ideal sheaves of O_X: the third conjunct uses
  `S : Set (Subobject (SheafOfModules.unit (moduleRings X.toRingedSpace)))`, with
  `S.Nonempty` and the same memberwise quasi-coherence condition. `SheafOfModules.unit`
  is the structure sheaf as a module over itself, not the constant sheaf. Its sections
  are O_X(U) with the regular module structure. A subsheaf of these regular modules is
  precisely a sheaf of ideals. The final maximality formula is the same as for F.
  This clause does not require a separate coherence hypothesis on the structure sheaf.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`
  (recorded by `pqf-def-locnoeth`) and `AlgebraicGeometry.IsNoetherian`.
- `Sheaf.AlgebraicGeometry.Coherent`: `AlgebraicGeometry.RingedSpace.IsCoherent`
  (recorded by `pqf-def-coherent`); its docstring explicitly uses Mathlib's
  `SheafOfModules.IsQuasicoherent` and `SheafOfModules.IsFiniteType` for the node's
  other two notions.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`:
  `SheafOfModules.IsQuasicoherent`, imported through the coherence module.
- `Mathlib.CategoryTheory.Subobject.Basic`: `CategoryTheory.Subobject`, its inclusion
  order and its coercion through `Subobject.underlying`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf`: `SheafOfModules.unit`, imported through
  the coherence module; its full definition and docstring were read.
- `Sheaf.Paper.DerivedHomMayerVietoris`: `AlgebraicGeometry.moduleRings`, imported
  through the coherence module and used on `X.toRingedSpace`.

Edge cases checked before writing: the empty scheme is permitted; its finite cover can
be empty and every module subobject is the zero subobject. The zero module is permitted
and its only subobject gives immediate stabilization. Sequences start at zero, as in
Stacks 01Y8; the first possible stabilization index is zero. Empty sets are explicitly
excluded from the two existence clauses; singleton sets and sets containing only the
zero ideal satisfy them. Increasing includes equal successive terms. Neither
separatedness nor a base field, characteristic, affine hypothesis, or reducedness is
assumed. The universe `u` is explicit and shared with the recorded coherence predicate.
The identity `G ≤ H → H = G` asserts maximality, not uniqueness among incomparable
members. No statement fault or disputed case was found.

Sources: the local Stacks source is absent on this machine, so the source statement
and proof were read at https://stacks.math.columbia.edu/tag/01Y8 (Lemma 30.10.1).
It states stabilization and proves it by a finite affine cover and module ACC. The
node supplies the detailed five-step proof and the maximal-element argument used
with 088C / 088E; all five steps and their dependencies are carried into the docstring.

Searches performed (recorded also in `searches.jsonl`):

- LeanFinder, query `Every increasing sequence of quasi-coherent submodules of a
  coherent sheaf on a Noetherian scheme stabilizes`: eight hits, including
  `eventuallyConst_of_isNoetherian`, `monotone_stabilizes_iff_noetherian`,
  `CategoryTheory.monotone_chain_condition_of_isNoetherianObject`, and scheme
  Noetherianness declarations. These concern ordinary modules or assume categorical
  Noetherianness; none states the geometric result or all three clauses.
- Loogle, query `SheafOfModules.IsQuasicoherent, Subobject`: zero hits, unknown
  identifier `Subobject` in that service.
- LeanSearch, query `ascending chain condition quasi coherent submodules coherent
  sheaf Noetherian scheme`: service unavailable (Internal Server Error), recorded
  as unavailable rather than as a successful negative search.
- Mathlib grep through msearch, query
  `noetherian.*coherent|coherent.*noetherian|chain.*quasi`, directory
  `AlgebraicGeometry`: no hits.
- Direct rg of the source repository and `lean/Sheaf` for the item ID,
  `acc_quasi`, `noetherian.*[Cc]oherent`, and subobject/quasi-coherence combinations:
  no matching declaration; source comments mention coherent pushforward and cohomology.
- Direct rg for `chain.*coherent|coherent.*chain|[Mm]aximal.*(submodule|ideal sheaf)`
  in the source and `lean/Sheaf`: comments about maximal ideal sheaves in approximation
  and a theorem about ordinary finite modules, no matching geometric statement.
- Candidate-name rg for `noetherian_quasicoherent_submodules` in Mathlib, the source,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`: no collision.
- Read Mathlib's `Scheme.IdealSheafData` documentation: it deliberately encodes affine
  ideal data rather than actual subsheaves of O_X. The statement instead uses actual
  module subobjects of `SheafOfModules.unit`, so it needs no second ideal-sheaf notion.

Validation: the server single-file compile exited 0 in 2.4 seconds, with no warnings
or errors. The delivery dry run printed OK: compilation and preflight passed except
for the independent second reading, which the second reader supplies. Nothing was pushed.

## Second reading by J1

Independent reading of the node, its delivered module, both statement-dependency nodes,
and the implementations of their recorded declarations found no mismatch. No Lean or
node changes were necessary; this section records the second reading.

Source read: Stacks `coherent.tex`, section `section-coherent-quasi-compact`, label
`lemma-acc-coherent` (01Y8), including its introductory paragraph and proof. The local
Stacks checkout is absent, so I read the upstream TeX at
https://raw.githubusercontent.com/stacks/stacks-project/master/coherent.tex and the tag
page https://stacks.math.columbia.edu/tag/01Y8. The section introduces no standing
hypothesis beyond those in the lemma. Also read the maximal-ideal-sheaf arguments of
088C and 088E (the paragraphs citing `lemma-acc-coherent` in the same TeX). These use
maximality among a collection, not a greatest ideal. The additional maximal-element
clauses are precisely the node's explicit consequences of the chain statement.

Objects, hypotheses, and conclusions matched individually (all verdicts: match):

1. Arbitrary scheme X: `(X : Scheme.{u})`, with explicit arbitrary universe `u`.
2. Locally Noetherian and quasi-compact: `[IsNoetherian X]`. Read
   `Mathlib.AlgebraicGeometry.Noetherian`: the class at line 280 extends exactly
   `IsLocallyNoetherian X` and `CompactSpace X`. The recorded locally-Noetherian
   declaration has Noetherian rings on every affine open; the already-proved
   `isLocallyNoetherian_iff_of_iSup_eq_top` and
   `isLocallyNoetherian_iff_of_affine_openCover` identify it with the node's affine-cover
   form. No separatedness, properness, or affine hypothesis occurs.
3. An O_X-module F: `(F : SheafOfModules.{u} (moduleRings X.toRingedSpace))`.
   Read `moduleRings` in `Sheaf.Paper.DerivedHomMayerVietoris`: this is the scheme's
   structure sheaf with only commutativity forgotten, not a constant coefficient sheaf.
4. F coherent: `hF : RingedSpace.IsCoherent X.toRingedSpace F`. Read
   `Sheaf.AlgebraicGeometry.Coherent` in full against `pqf-def-coherent`: its body is
   `F.IsFiniteType` and finite-type kernels for every open U, finite rank n, and map
   from the free module to `F.over U`. This is the recorded Stacks coherence notion;
   no finite-presentation substitute or additional quasi-coherence hypothesis is used.
5. Increasing sequence of embedded submodules of F: `G : ℕ → Subobject F`,
   `Monotone G`. Read `Subobject.Basic`: its order means factorization of the monic
   embedding and its equality identifies isomorphic presentations over F. Thus this
   expresses inclusion and actual equality of subsheaves, rather than abstract
   isomorphism of their underlying sheaves.
6. Each term quasi-coherent: `∀ n, (G n : SheafOfModules ...).IsQuasicoherent`.
   Read Mathlib's class in `Sheaf.Quasicoherent`, including the
   `isQuasicoherent.IsClosedUnderIsomorphisms` instance at line 398. The coercion is
   `Subobject.underlying`; its chosen representative does not affect quasi-coherence.
   The class means local free presentations, the scheme-equivalent form explicitly
   used by the recorded coherence dependency. No condition on the quotient is added.
7. Sequence eventually constant: the first conjunct concludes
   `∃ n, ∀ m, n ≤ m → G m = G n`. This is the entire tail, with n chosen after G and
   its two hypotheses, just as the node requires.
8. Every nonempty set of quasi-coherent submodules: the second conjunct quantifies
   `S : Set (Subobject F)`, assumes `S.Nonempty` and memberwise quasi-coherence, and
   concludes `∃ G ∈ S, ∀ H ∈ S, G ≤ H → H = G`. This is maximality for inclusion,
   allowing incomparable members, with no directedness or closure condition on S.
9. Every nonempty set of quasi-coherent ideal sheaves: the third conjunct replaces F
   by `SheafOfModules.unit (moduleRings X.toRingedSpace)` and repeats the same set,
   quasi-coherence, and maximality clauses. Read `SheafOfModules.unit` at line 173:
   its underlying presheaf is the regular rank-one module of the structure rings.
   Its module subobjects are exactly ideal subsheaves. No new ideal-sheaf definition
   and no coherence hypothesis on this unit object are introduced.

Edge cases: the empty scheme and zero F are permitted; there is no `Nonempty X` or
nonzero assumption. On the empty scheme the finite cover can be empty, all module
subobjects coincide, and the stabilization index can be zero (interpret the finite
maximum as zero for an empty cover). On the zero module the chain is constant at zero.
The ℕ indexing includes zero and permits repetitions. The maximality clauses explicitly
exclude empty S and include singleton S; the third clause is still required when F is
zero. There is no base ring/field or characteristic restriction. The one explicit
universe matches the recorded coherence predicate and permits every scheme and module
in that ambient universe; no independent test-object universe or index bound occurs.

Independent searches, using different terms from the worker (also logged by msearch):

- LeanFinder: `quasi coherent sheaf subobjects maximal ascending chain finite module
  scheme` returned eight hits, chiefly `SheafOfModules.IsFiniteType` and generators /
  local-presentation definitions; none states this result.
- Loogle: `"IsNoetherianObject"` returned twelve hits. Opened
  `Mathlib.CategoryTheory.Subobject.NoetherianObject`: the chain theorem requires an
  already Noetherian object and says nothing about coherent sheaves on schemes or
  the restriction to quasi-coherent subobjects. It cannot replace this statement.
- LeanSearch: `maximal quasi coherent subsheaf coherent sheaf Noetherian scheme`
  returned Internal Server Error; recorded unavailable, not a negative result.
- Direct rg for `noetherianobject|chain.condition|stabiliz|maximal.*sub` across
  Mathlib AlgebraicGeometry, upstream WeilConjectures, and project `lean/Sheaf`, then
  a narrower `noetherian.*coher|coher.*noetherian|ascending|chain condition|stabiliz`
  search in their AlgebraicGeometry directories: no matching theorem. Hits concern
  coherent cohomology, other finiteness results, ordinary modules, or group stabilizers.
- Searched the item id and `noetherian_quasicoherent_submodules` in the upstream name
  table, upstream source and project modules: no declaration collision. Opened the
  upstream `AlgebraicGeometry/Modules/Coherent.lean`: its `Scheme.Modules.isCoherent`
  is quasi-coherent plus finite presentation, not the dependency's general Stacks
  definition; the delivery correctly uses the recorded dependency instead.

No new definition nodes, dependency modules, or statement corrections are delivered.
The three imports respectively supply the recorded coherence predicate/module carrier,
Noetherian scheme class, and subobjects. The sole theorem has only `sorry` as proof;
there are no definitions or auxiliary proved results. The module and declaration
source docstrings carry the blueprint id; the theorem docstring reproduces all five
node proof steps with their dependencies, including the separate unit-module argument.
All variables/universes are explicitly bound, and the stored `lean.statement` agrees
verbatim with the file's signature.

Second-reader validation: `scompile.py` exited 0 (2.4 seconds), with no errors or
warnings. An exact textual comparison confirmed the node's `lean.statement` equals
the signature, and every Lean line is at most 100 characters. `deliver2.py --no-push`
printed OK: preflight and server compilation passed with this independent reading.

## Reviewer fix (R-nac1253)

Third conjunct (quasi-coherent ideal sheaves of O_X) restated on `X.IdealSheafData` per STATE line
QUASI-COHERENT IDEAL SHEAVES (the abstract mono ideal form, here subobjects of `SheafOfModules.unit`
with an `IsQuasicoherent` condition, is reserved for non-quasi-coherent ideals): now
`∀ S : Set X.IdealSheafData, S.Nonempty → ∃ I ∈ S, ∀ J ∈ S, I ≤ J → J = I`; import
`Mathlib.AlgebraicGeometry.IdealSheaf.Basic` added, docstring adjusted. The worker and second-reading
descriptions of the third clause above refer to the delivered form. Fixed file compiled clean (2.3 s);
`#check` confirms `IsNoetherian` resolves to `AlgebraicGeometry.IsNoetherian`.

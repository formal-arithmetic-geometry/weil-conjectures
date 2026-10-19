## Worker report

The module `Sheaf.AlgebraicGeometry.TopCoherentCohomologyFinite` states
`AlgebraicGeometry.finiteDimensional_top_coherent_cohomology`, with its sole proof
`sorry`. It introduces no definition and changes only the item's `lean` field.
The source was read in `literature/stacks-project/etale-cohomology.tex`,
label `lemma-top-cohomology-coherent` (Tag 0A3M), including its induction proof.
The declaration docstring carries all nine DAG proof steps and their supporting nodes.

Hypothesis and conclusion correspondence:

- The field is `(k : Type u) [Field k]`.
- The scheme over that field is `(X : Scheme.{u}) [X.Over (Spec (.of k))]`.
  Its specified structure morphism is `X ↘ Spec (.of k)`.
- Separatedness is `[IsSeparated (X ↘ Spec (.of k))]`.
- Finite type is the pair `[LocallyOfFiniteType (X ↘ Spec (.of k))]` and
  `[QuasiCompact (X ↘ Spec (.of k))]`, exactly the recorded finite-type interface.
- The nonnegative integer is `(d : ℕ)`; its inclusion in all integers >= 0 is exact.
- Dimension equal to d is `(hd : topologicalKrullDim X = (d : WithBot ℕ∞))`.
- An arbitrary O_X-module is `(F : SheafOfModules.{u} (moduleRings X.toRingedSpace))`.
  Coherence is `(hF : RingedSpace.IsCoherent X.toRingedSpace F)`.
- Degree-d coherent cohomology is
  `(RingedSpace.moduleCohomology X.toRingedSpace d).obj F`, the right derived
  global-sections functor used by the recorded cohomology node.
- Finite-dimensionality, meaning existence of a finite basis, is `FiniteDimensional k`
  on this module after `ModuleCat.restrictScalars` along
  `((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (X ↘ Spec (.of k)).appTop).hom`.
  This is the canonical k-action, not an arbitrary or existential module structure.
- No properness, smoothness, algebraic closedness, characteristic, connectedness,
  integrality or local Noetherianity assumption is added. Local Noetherianity follows
  from finite type over a field in the proof rather than being a theorem hypothesis.

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field`, `Mathlib.Algebra.Field.Defs`.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsSeparated` from
  `Mathlib.AlgebraicGeometry.Morphisms.Proper` (defined in its Separated import).
  `IsProper` and `UniversallyClosed` were read but are not hypotheses here.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact`, `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
- `def-kun-topological-krull-dimension`: `topologicalKrullDim`,
  `Mathlib.Topology.KrullDimension`.
- `pqf-def-coherent`: `AlgebraicGeometry.RingedSpace.IsCoherent`,
  `Sheaf.AlgebraicGeometry.Coherent`.
- `pqf-def-cohomology`: `AlgebraicGeometry.sheafCohomologyAndHigherDirectImages`,
  `Sheaf.Paper.PQFCohomology`; its recorded cohomology definition is
  `AlgebraicGeometry.RingedSpace.moduleCohomology` in
  `Sheaf.Topology.RingedSpaceModuleCohomology` (read in full).

All 22 additional distinct recorded proof-dependency modules are imported without
`public`. The two proof nodes with no recorded Lean declaration,
`lem-weil-pbc-finite-type-algebra-noetherian` and
`lem-weil-pbc-top-degree-open-restriction-surjective`, are retained in the docstring
and DAG proof; no nonexistent import or extra assumption replaces them.

Edge cases checked: d=0 gives finite global sections of a finite scheme; no positivity
assumption is present. The zero module is included and has zero cohomology. The empty
scheme has dimension bottom, so cannot satisfy the explicit equality to natural d;
there is no silent nonemptiness binder. Nonproper affine schemes of positive dimension
are included (their positive cohomology vanishes). Reducible, nonreduced and nonpure
schemes and fields of arbitrary characteristic are included. All universes and variables
are explicitly bound. The common universe u follows the existing Scheme/Spec/module
interfaces and can be enlarged; it imposes no finite-cardinality condition.

Searches for reuse (2026-10-15):

- `msearch.py ... leanfinder "Top cohomology of coherent sheaf on separated finite type
  scheme over field is finite dimensional"`: eight hits concerning cotangent H1,
  finite morphisms, finite fibres, finite generation of sheaves and affine limits;
  none is this theorem.
- `msearch.py ... loogle "FiniteDimensional, cohomology"`: zero hits; `cohomology`
  is unknown as an identifier. The earlier DAG search with quoted cohomology and
  FiniteDimensional likewise has no hit.
- `msearch.py ... grep "coherent.*cohomology|cohomology.*coherent"`: zero Mathlib hits.
- `rg` in upstream `WeilConjectures` and project `lean/Sheaf` for this node id and
  top/cohomology/finite combinations found no existing theorem; the two ring
  pseudo-coherence matches concern complexes of rings, not coherent sheaves on schemes.
- `rg` in `dag/lean_names_upstream.json`, upstream and project sources for
  `topCoherentCohomology|finite_top_coherent|finiteDimensional_top` found no collision.
- Project cohomology finiteness and scalar-restriction searches found reusable
  `ModuleCat.restrictScalars`, `RingedSpace.moduleCohomology` and the canonical
  `ΓSpecIso.inv ≫ f.appTop` pattern, all reused directly.

No node fault or disputed statement was found. No new nodes or dependency repairs
are needed. Server compilation through `scompile.py` passed cleanly (1.6 seconds
for this module, nice 19, two threads, 60-second limit); only statements were written.

## Second reading by NR

I independently read the node, the Lean module, Stacks Tag 0A3M
(`etale-cohomology.tex`, `lemma-top-cohomology-coherent`, including the entire
proof), all seven statement-dependency records, and their declaration sources.
The lemma is self-contained: the preceding characteristic-p lemmas impose no
standing hypotheses on it. It assumes neither properness nor algebraic closure.
There is no statement_change, new definition node, or dependency module in this
delivery to audit. The statement matches the node and source; no repair is needed.

Object-by-object and hypothesis-by-hypothesis checklist:

- Arbitrary field k: `(k : Type u) [Field k]`. Mathlib's Field extends
  CommRing and DivisionRing, including nontriviality. Exact.
- Scheme X over k: `(X : Scheme.{u}) [X.Over (Spec (.of k))]` supplies the
  structure map `X ↘ Spec (.of k)`. Mathlib Scheme is a locally ringed space
  with affine neighbourhoods. This is the recorded scheme notion. Exact.
- Separated over k: `[IsSeparated (X ↘ Spec (.of k))]`. I read
  Morphisms/Separated: the condition is that the relative diagonal is a closed
  immersion. This is the separated clause of def-weil-proper-morphism, not
  a properness assumption. Exact.
- Finite type over k: `[LocallyOfFiniteType (X ↘ Spec (.of k))]` and
  `[QuasiCompact (X ↘ Spec (.of k))]`. I read both Mathlib class definitions:
  affine-local finite type and quasi-compact inverse images. Their conjunction
  is precisely the recorded finite-type notion. Exact.
- Nonnegative integer d: `(d : ℕ)`. This encodes every integer >= 0 without
  excluding zero. Exact.
- Dimension d: `(hd : topologicalKrullDim X = (d : WithBot ℕ∞))`.
  Mathlib defines topologicalKrullDim as krullDim of IrreducibleCloseds;
  the equality fixes the supremum of chain lengths, rather than merely
  bounding it. Exact, including the node's direction of equality.
- Every O_X-module F: `(F : SheafOfModules.{u} (moduleRings X.toRingedSpace))`.
  This is the carrier of the recorded coherent-module and cohomology interfaces,
  not a different category of abelian sheaves. Exact.
- Coherent F: `(hF : RingedSpace.IsCoherent X.toRingedSpace F)`.
  I opened Coherent.lean: this means finite type and finite-type kernels for
  all maps from finite free modules on every open. It is exactly the third
  clause of pqf-def-coherent, with no extra quasi-coherence hypothesis. Exact.
- Degree-d coherent cohomology: `(RingedSpace.moduleCohomology
  X.toRingedSpace d).obj F`. I opened PQFCohomology and
  RingedSpaceModuleCohomology: this is R^d of module-valued global sections,
  computed in O_X-modules. The extra derived-category binders in the separate
  higher-direct-image clause of PQFCohomology are not needed here. Exact.
- Finite dimension over the specified field: `FiniteDimensional k` on that
  cohomology after the displayed `ModuleCat.restrictScalars`. I opened
  ChangeOfRings and Scheme.ΓSpecIso: the inverse of ΓSpecIso maps k into
  Γ(Spec k), then appTop maps into Γ(X). Restriction acts by this ring map
  on the existing cohomology module. Thus this is the canonical scalar
  action, not a freely chosen action. FiniteDimensional is Module.Finite,
  equivalent over a field to admitting a finite basis. Exact.
- Quantifiers and scope: the assertion holds for every d and every coherent F
  on each such X. Reordering the independent introduction of X and d does not
  change the assertion. No properness, smoothness, algebraic closure,
  characteristic, integrality, reducedness, or local Noetherianity binder was
  added. All variables and the universe are explicitly bound.

Edge cases: d=0 is included, and a zero-dimensional separated finite-type
scheme over k is finite, giving the expected finiteness of global sections.
The zero module is allowed. Empty X has dimension bottom by the recorded
Krull-dimension convention, so satisfies no equality to natural d; this agrees
with the node's explicit d>=0 and dimension-equality hypotheses. There is no
index family, so no empty-index restriction. Reducible, nonreduced, nonpure,
and positive-dimensional nonproper schemes are included. The field can have
any characteristic. The universe u is arbitrary, and the common module
universe is that of both recorded dependency interfaces; there is no new
universe equality hypothesis or size instance. Coherent sheaves are locally
finitely generated over the structure sheaf, so larger presentations do not
introduce new mathematical coherent modules missing from this size convention.

Independent reuse searches (2026-10-15):

- LeanFinder via msearch: `finite dimensional highest cohomology coherent sheaf
  separated algebraic scheme`. Eight hits, including cotangent finiteness,
  general sheaf cohomology, and finite morphisms; none states this theorem.
- Loogle via msearch: `"FiniteDimensional", "H"`. Twelve hits concerning
  linear algebra, Krull orders, and field towers, not this assertion.
- Direct rg of Mathlib/AlgebraicGeometry for FiniteDimensional or Module.Finite
  paired with cohomology or .H found no matching theorem. Direct rg of
  WeilConjectures and project lean/Sheaf with the same alternatives found
  proper/projective finiteness, curves and unrelated derived-fibre results.
  I opened finiteDimensional_H_of_isProper in DirectImage/AffineMorphism,
  finiteDimensional_H in Modules/Ample, and the projective-line and
  finiteDimensional_H_of_isCurve declarations in Cohomology/ProjectiveLine.
  They require properness, invertibility, or special projective curves and
  therefore cannot replace the present nonproper theorem. Project
  projective/Chow finiteness results likewise supply ingredients, not the
  separated finite-type top-degree assertion.
- Exact declaration-name rg in the upstream name table, WeilConjectures and
  project lean/Sheaf found no collision.

H5/H6/H8/H9: there are no definitions, private copies, local instances, local
notations, hidden let/show binders, or newly proved facts. The only theorem
has `by sorry`. Its source/blueprint docstring follows all nine proof steps,
including lower-dimensional support, shrinking the nonvanishing open, Leray,
and the projective-closure quotient. Proof-dependency imports are non-public;
statement-dependency imports are public. The node's lean.statement is verbatim
the theorem signature, excluding `:= by`. No mismatch was found and no Lean
or node change was made; this section is the only second-reader addition.

Validation: scompile.py compiled the delivered module on the server cleanly
in 1.6 seconds, nice 19, two threads, 60 seconds per file. The tool also
compiled its required side-source IntegralChowRelativelyAmple overlay in
1.4 seconds. No local compiler or library build was run.

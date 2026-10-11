## Worker report

The module `Sheaf.AlgebraicGeometry.FinitePresentationOfFiniteLocallyNoetherian`
states `AlgebraicGeometry.finitePresentation_of_finite_over_locallyNoetherian`.
The theorem has one `sorry` proof; no definitions, instances or proofs were added.
Only the item's `lean` record is changed, with its signature copied verbatim
(including line breaks) from the module. No new or dependency modules are needed.

Hypothesis and conclusion correspondence:

- Schemes S and T: `{S T : Scheme.{u}}`, with the universe explicitly declared.
- The locally Noetherian base S: `[IsLocallyNoetherian S]`, the recorded declaration
  of `pqf-def-locnoeth` in `Mathlib.AlgebraicGeometry.Noetherian`.
- The morphism p from T to S: `(p : T ⟶ S)`.
- Finiteness of p: `[IsFinite p]`, the affine-local finite-ring-map class in
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`. This is the finite-morphism
  convention of `def-weil-pbc-scheme-conventions`.
- The conclusion that p is of finite presentation:
  `LocallyOfFinitePresentation p ∧ QuasiCompact p ∧ QuasiSeparated p`.
  Its three clauses are exactly the convention node's Stacks 01TP definition.
  `LocallyOfFinitePresentation` is the `mathlib_match` of
  `def-sbc-locally-finite-presentation`, in
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation` (imported by Noetherian).
  Quasi-compactness and quasi-separatedness use Mathlib's `QuasiCompact` and
  `QuasiSeparated` classes; the convention node is a pointer collection, with
  no declaration or module to import. No private finite-presentation predicate
  is introduced. Mathlib's module prose uses a weaker two-clause convention;
  this delivery follows the project's explicitly corrected three-clause convention.

The recorded dependency declarations and their full signatures/docstrings were
read in the local Mathlib source. `IsLocallyNoetherian` requires Noetherian rings
on every affine open, equivalent to an affine Noetherian cover by the equivalences
already recorded on its dependency node. `LocallyOfFinitePresentation` requires
finite presentation on affine pairs, matching the pointwise local definition via
its existing `HasRingHomProperty` instance. `IsFinite` extends `IsAffineHom` and
requires finite maps on sections of affine target opens. The natural-language
proof in the docstring records all three DAG proof steps and their node names.

Source checks: the literature blueprint file is absent from this machine, so I
read the exact recorded source file read-only over SSH on the project server:
`literature/blueprint/master/blueprint/sec-nagata-compactification/sk-prop-nagata-sketch-zmt/pqf-lem-finite-fp-locnoeth.md`.
Its statement is verbatim the node's statement. I also opened
https://stacks.math.columbia.edu/tag/01TP and checked all three finite-presentation
clauses. The node's original blueprint proof omits explicitly stating affine
implies quasi-separated; the current DAG proof supplies that step, and the module
uses the current DAG proof. No statement correction is needed.

Edge cases checked before writing: empty source schemes are allowed (no nonempty
binder); an empty base introduces no extra assumption and allows the empty source;
identity and finite closed-immersion examples are covered. The base need not be
affine, quasi-compact, separated, globally Noetherian or a scheme over a field.
Arbitrary characteristic and the zero coordinate ring remain allowed. The common
arbitrary universe u is the usual Mathlib scheme-category universe and is explicitly
bound. None of the hypotheses is an automatically true identity-map condition.

Searches for an existing declaration:

- `msearch.py leansearch`, query `finite morphism to locally Noetherian scheme finite presentation`:
  service unavailable (Internal Server Error); recorded in `searches.jsonl`.
- `msearch.py leanfinder`, query `finite morphism over a locally Noetherian scheme is of finite presentation`:
  eight hits, including `IsFinite.instLocallyOfFiniteType`,
  `LocallyOfFinitePresentation`, and ring-level finite-type/presentation equivalences.
  No exact theorem with the complete scheme-level conjunction.
- `msearch.py loogle`, query `AlgebraicGeometry.IsFinite, AlgebraicGeometry.LocallyOfFinitePresentation`:
  one hit, `Scheme.Hom.isLocallyConstant_finrank`, which assumes local finite
  presentation and flatness and does not state the item.
- `msearch.py grep`, query `finite.*[Pp]resentation|[Pp]resentation.*[Ii]sFinite`
  in `AlgebraicGeometry`: local finite presentation definitions and unrelated
  flat/etale results, not the full item.
- Direct `rg` of Mathlib `Noetherian.lean` and `Morphisms/Finite.lean` found the
  locally finite type instance and the Noetherian-target conversion at lines
  265--276. These supply only one part of the conclusion, rather than an exact match.
- Direct `rg` across `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for the item id and finite/presentation/Noetherian patterns found related
  compactification and module results, and a docstring citing the item in
  `ConstructibleModuleFinitePushforwardEmbedding.lean`; no exact declaration.
- Name collision search for `finitePresentation_of_finite_over_locallyNoetherian`
  across Mathlib, `WeilConjectures`, and `lean/Sheaf`: no hits.

Validation: `scompile.py C1 pqf-lem-finite-fp-locnoeth` compiled the module on the
server in 1.7 seconds, exit code 0, with no warnings or errors. The dry run result
is recorded below after the delivery checks complete. No statement dispute or
unresolved node fault was found.

`deliver2.py C1 pqf-lem-finite-fp-locnoeth --no-push` printed OK: compilation
and preflight passed except for the independent second-reading section, which
is deliberately left for the second reader. Nothing was pushed.

## Second reading by C1

I independently read the sandbox node and module, all three statement dependency
nodes, and the recorded Mathlib declarations and their docstrings. I read the
blueprint source at its exact recorded path over read-only SSH, and Stacks
`morphisms.tex`, definition-finite-presentation (01TP) and
lemma-locally-finite-presentation-characterize, together with `properties.tex`,
definition-noetherian (01OV). The Stacks definitions introduce arbitrary schemes
and morphisms, without a field, characteristic, nonemptiness or separation
assumption. The enclosing blueprint proposition starts with a qcqs base, but
this standalone lemma explicitly introduces a locally Noetherian base; its
argument is affine-local and needs no global quasi-compactness. The node's
standalone generality is valid and its Lean preserves it.

Object/hypothesis/conclusion inventory and item-by-item verdict:

- Base scheme S: `{S T : Scheme.{u}}` introduces S as the Mathlib scheme
  used by the dependencies. MATCH; no affineness or global Noetherian assumption.
- Source scheme T: the same binder introduces an arbitrary scheme T. MATCH;
  T is not replaced by an affine scheme or a ring spectrum.
- Morphism p from T to S: `(p : T ⟶ S)`. MATCH, including its direction.
- S locally Noetherian: `[IsLocallyNoetherian S]`. MATCH to
  `pqf-def-locnoeth`'s recorded `AlgebraicGeometry.IsLocallyNoetherian`.
  I read its `component_noetherian` field and the signatures of
  `isLocallyNoetherian_of_affine_cover`, `isLocallyNoetherian_iff_of_iSup_eq_top`
  and `isLocallyNoetherian_iff_of_affine_openCover`. These give the exact
  equivalence of the every-affine-open encoding and the node's affine-cover
  definition. No stronger hypothesis is smuggled into this class.
- p finite: `[IsFinite p]`. MATCH to the convention node's pointer to finite
  morphisms. `IsFinite` extends `IsAffineHom` and its `finite_app` field
  requires finite ring maps on affine opens of the target, exactly the
  finite-module condition on coordinate rings. It is not mere finite fibres.
- p locally of finite presentation: `LocallyOfFinitePresentation p`.
  MATCH to `def-sbc-locally-finite-presentation`'s recorded Mathlib match.
  I read the class's `finitePresentation_appLE` field and
  `HasRingHomProperty.iff_exists_appLE`: the all-affine-pairs condition is
  equivalent to the node's affine neighbourhood condition at each source point.
  Stacks' characterization explicitly supplies the same equivalence.
- p quasi-compact: `QuasiCompact p`. MATCH to the convention node.
  I read the class and `quasiCompact_iff_forall_isAffineOpen`; testing all compact
  opens is equivalent to testing target affine opens, without a compact base.
- p quasi-separated: `QuasiSeparated p`. MATCH to the convention node.
  Its `quasiCompact_diagonal` field is precisely quasi-compactness of p's
  diagonal. The three conjuncts, in their displayed order, are Stacks 01TP's
  complete definition of finite presentation. No clause is omitted or added.

All objects are quantified before the hypotheses and conclusion. The universe
`u` is explicitly bound and arbitrary. The common scheme universe is the
Mathlib category encoding; there is no independently smaller test universe.
Empty source and base schemes and the zero coordinate ring are included.
There is no nonempty index set, rank, n, characteristic, coefficient field,
reducedness, integrality or separatedness restriction. The affine presentations
used by the existing definitions allow zero generators and zero relations.
Identity maps and finite closed immersions are covered. Local Noetherian and
finite are substantive hypotheses on S and p, not assumptions on identity maps.

Independent searches (different wording from the first reader):

- `msearch.py leanfinder`: `finite scheme map Noetherian target finitely
  presented quasi separated`. Eight hits included
  `LocallyOfFiniteType.isLocallyNoetherian`,
  `quasiCompact_of_noetherianSpace_source`, `IsFinite.instLocallyOfFiniteType`
  and `isFinite_iff`; none states the complete three-clause conclusion.
- `msearch.py loogle`: `AlgebraicGeometry.IsFinite,
  AlgebraicGeometry.QuasiSeparated`. Zero hits.
- `msearch.py leansearch`: `A finite map of schemes with locally Noetherian
  target is finitely presented`. The service returned Internal Server Error;
  its unavailability is recorded, not treated as a negative result.
- Direct `rg` of Mathlib Noetherian and Finite, source
  `WeilConjectures/AlgebraicGeometry` and project `lean/Sheaf/AlgebraicGeometry`
  for finite/locallyNoetherian and finite-presentation phrases found related
  module and Hilbert statements, not this complete scheme theorem.
- A multiline signature search across all Mathlib AlgebraicGeometry,
  WeilConjectures and lean/Sheaf for an IsFinite binder followed by a
  LocallyOfFinitePresentation conclusion found no exact declaration.
- Direct name and blueprint-id search across WeilConjectures, lean/Sheaf and
  `dag/lean_names_upstream.json` found only the citation in
  ConstructibleModuleFinitePushforwardEmbedding, not an existing declaration.
  Mathlib already supplies the local-finite-type and Noetherian conversion
  instances, but no single declaration states this full conjunction.

No mismatch was found; the correct module, imports, signature and node record
were retained verbatim. There are no new nodes or dependency modules to review,
no statement correction and no statement dispute. There is exactly one theorem,
whose proof is `sorry`; no definition, instance, auxiliary proof, file-local
notation, hidden let/show binder or unbound variable is introduced. The module
and theorem docstrings name the exact blueprint source and tag, and the theorem
records all three DAG proof steps with their cited nodes. Lines obey the
100-character convention and the namespace is AlgebraicGeometry.
The node's `lean.statement` is verbatim the theorem signature before `:=`.

Independent validation: `scompile.py C1 pqf-lem-finite-fp-locnoeth` on the
module returned exit code 0 (compiled in 2.5 seconds), no errors or warnings.

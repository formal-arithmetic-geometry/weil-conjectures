# Q23: lem-sfb-space-etale-finite-fp-envelope

## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceEtaleFiniteFpEnvelope` states
`AlgebraicGeometry.AlgebraicSpace.exists_finite_finitePresentation_envelope_of_etale`.
Its sole theorem has proof `by sorry`. It adds no definitions. The module docstring
identifies Stacks Tags 082K and 0874; the theorem docstring gives the seven steps of
the accepted DAG proof, with its named dependencies.

The inherited BLOCKED ending concerned the stage-1 unchanged-split gate, rather than
a Lean statement delivery. The current node is stage-2 queued and has no Lean record.
This delivery preserves the reviewed split and uses `deliver2.py`, as the stage-handoff
paragraph of `coord/brief-stage2.md` prescribes. No repair note for this item exists.

Clause-by-clause correspondence:

| Node hypothesis or conclusion | Lean rendering |
| --- | --- |
| Scheme S, with the stated size convention | Explicit `universe u` and `{S : Scheme.{u}}`; no extra universe equality or smallness hypothesis |
| Algebraic spaces W and T over S | `{W T : AlgebraicSpace S}`; these are the existing full subcategory of big-fppf sheaves with representable diagonal and an etale surjective atlas |
| The given morphism f | `(f : W ⟶ T)`, a sheaf natural transformation in that full subcategory |
| T quasi-compact, meaning existence of a surjective representable etale atlas from a quasi-compact scheme | `(hTqc : IsQuasiCompact T.obj)`; this is exactly the existential atlas predicate, not a chosen atlas |
| T quasi-separated in the absolute sense | `(hTqs : IsAbsolutelyQuasiSeparated T)`; its affine-pair test is equivalent to quasi-compactness of the absolute diagonal by Stacks 0AHR, even when S is not quasi-separated |
| f quasi-compact, tested after pullback to affine schemes | `(hfqc : MapIsQuasiCompact f.hom.hom)` |
| f separated, meaning representable closed relative diagonal | `(hfsep : MapIsSeparated f)`; this uses `IsRepresentableWith` on `pullback.diagonal f.hom.hom` and `IsClosedImmersion` on scheme projections |
| f etale on every compatible pair of etale scheme charts | `(hfet : MapIsLocally (@Etale) f)`; this is precisely the node's chart test, and does not assume representability of f |
| An algebraic space Y over S | `∃ (Y : AlgebraicSpace S)` |
| A morphism j from W to Y | `(j : W ⟶ Y)` |
| j representable open immersion | `IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) j.hom.hom` |
| j quasi-compact | `MapIsQuasiCompact j.hom.hom` |
| A morphism pi from Y to T | `(π : Y ⟶ T)` |
| pi finite and representable on all scheme tests | `IsRepresentableWith (fun _ _ p ↦ IsFinite p.left) π.hom.hom` |
| pi locally of finite presentation, on compatible etale charts | `MapIsLocallyOfFinitePresentation π` |
| pi quasi-compact, the second finite-presentation clause | `MapIsQuasiCompact π.hom.hom` |
| pi quasi-separated, the third finite-presentation clause | `MapIsQuasiCompact (pullback.diagonal π.hom.hom)` |
| f equals pi composed with j | `j ≫ π = f`, using Lean's diagrammatic composition order |

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `IsEtale`, `IsSurjective`, `IsAlgebraicSpace`.
  In particular `IsEtale` here is the representable scheme-test predicate, whereas the
  theorem's etale hypothesis uses the compatible-chart predicate below.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicSpace.fibreProduct_isAlgebraicSpace`, together with the sheaf pullbacks.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation` (used by the chartwise predicate).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion` (used by `MapIsSeparated`).
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- The metatheoretic `def-weil-size-convention` has no declaration or module; explicit
  universe polymorphism implements its role.

Four already landed definition nodes are added to `stmt_deps` under the standing
STMT_DEPS MAY GAIN LANDED NODES rule. These supply predicates used in the statement,
without copying definitions or modifying the source statement:

- `def-sfb-space-morphism-properties`, module
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `MapIsLocally`, `MapIsSeparated`, `MapIsLocallyOfFinitePresentation`.
- `def-sfb-stack-qcqs-morphism`, module
  `Sheaf.AlgebraicGeometry.StackQcqsMorphism`: `AlgebraicSpace.IsQuasiCompact`.
- `def-sfb-space-absolute-quasi-separated`, module
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `AlgebraicSpace.IsAbsolutelyQuasiSeparated`.
- `def-sfb-proper-curve-moduli`, module
  `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `AlgebraicSpace.MapIsQuasiCompact`.

Every currently recorded proof-dependency module is imported. At preparation time the
following proof dependencies have no recorded Lean module; none is required to type
the statement, and the natural-language proof still cites them:
`lem-sfb-space-separated-fp-composition`,
`lem-sfb-space-normalization-quasifinite-locus`,
`lem-sfb-space-relative-integral-factorization`,
`lem-sfb-space-integral-qcqs-permanence`, `lem-sfb-space-qc-cancellation`,
`lem-sfb-space-affine-limits-schematic-stages`,
`lem-sfb-space-limit-open-cover-descent`, `lem-sfb-space-qcqs-permanence`,
`lem-sfb-space-qc-open-finite-presentation`, `lem-sfb-space-relative-lfp-permanence`,
`lem-sfb-space-affine-locality`.

Edge cases checked before writing:

- W empty is allowed: choose Y empty, with its empty open immersion and finite finitely
  presented map to T. There is no nonemptiness hypothesis in the Lean statement.
- T empty forces W empty; the same conclusion applies. S itself may be empty.
- If f is finite etale, Y can be W and j the identity. Finiteness and local finite
  presentation together give the required finite-presentation clauses.
- For f the identity on any qcqs space, Y = W = T works, so no separatedness of T over
  S is implicitly required. In particular S need not be quasi-separated.
- A general open immersion need not be finite: only j is required to be open, and only
  pi is required to be finite. The envelope pi is not required to be etale.
- Neither W nor T is required to be a scheme. There is no Noetherian, reducedness,
  characteristic, finite-type-over-S or chosen-atlas restriction. Nilpotents and
  non-Noetherian bases are included.
- The theorem has a single explicit scheme universe u throughout, following the existing
  algebraic-space API; all schemes and tests live in that bound. No independent lower
  test universe makes the quantification vacuous.

Searches for an existing statement:

1. `msearch.py ... leanfinder` query: "A quasi compact separated etale morphism of
   algebraic spaces over a quasi compact quasi separated base factors as a quasi compact
   open immersion followed by a finite finitely presented morphism". Eight hits: scheme
   immersion factorization, scheme etale permanence and flat descent; no algebraic-space
   finite finitely presented envelope.
2. `msearch.py ... loogle '"IsEtale", "IsFinite"'`: zero hits.
3. `msearch.py ... grep 'finite.*[Ee]nvelope|finite_finitePresentation.*etale|etale.*finite_finitePresentation|Zariski.*Main' AlgebraicGeometry`:
   eight hits, all scheme Zariski Main references. Reading
   `Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean` shows its statement is the
   scheme relative-normalization isomorphism-locus result (Tag 03GW), not this envelope.
4. `msearch.py ... leansearch` query: "A separated quasi compact etale morphism of
   algebraic spaces over a qcqs base has a finite finitely presented envelope".
   Eight hits: ring etale finite presentation and scheme quasi-separatedness/etaleness;
   no matching theorem.
5. `rg -n 'finite.fp.envelope|finiteFpEnvelope|finite_finitePresentation_envelope|lem-sfb-space-etale-finite-fp-envelope'`
   in each of `lean/WeilConjectures` and `lean/Sheaf`: no hits. A declaration-name search
   for `exists_finite_finitePresentation_envelope_of_etale` in both source roots and
   `dag/lean_names_upstream.json` also finds no existing declaration. Filename searches
   for envelopes, Zariski Main and compactifications identify no exact statement.
6. Opened `WeilConjectures/AlgebraicGeometry/QuasiFiniteAffineOpenInFinite.lean`: its
   envelope is for morphisms between affine schemes, and has no finite-presentation
   conclusion. Opened `WeilConjectures/AlgebraicGeometry/SeparatedEnvelope.lean` and
   `Sheaf/AlgebraicGeometry/NagataFinitePresentationEnvelope.lean`: those construct a
   closed immersion of a scheme into a separated finitely presented scheme, rather
   than an open immersion of an algebraic space into a finite envelope. None matches.
7. Local source reads identified the four landed definition nodes listed above, so no
   new definition node or dependency repair module is needed.

The source in `literature/stacks-project/spaces-more-morphisms.tex`, labels
`lemma-quasi-finite-separated-pass-through-finite` (082K) and
`lemma-quasi-finite-separated-pass-through-finite-addendum` (0874), supplies exactly
this conclusion: the first gives a quasi-compact open immersion into a finite space;
the addendum gives finite presentation when f is locally finitely presented. The node
specializes this to quasi-compact separated etale f, which meets those hypotheses.
There is no statement correction or statement dispute.

## Second reading by Q23

A separate second pass by this same worker re-opened the node, statement module and
predicate definitions. The dispatcher explicitly prohibits starting other agents, so
this is not represented as an independent-agent review; the maintainer supplies the
independent review of this delivery.

The pass checked every row of the correspondence table against the actual signature:
`hTqc` uses the existential quasi-compact atlas, `hTqs` is absolute rather than relative
to S, `hfqc` uses affine tests, `hfsep` uses the closed relative diagonal, and `hfet`
is the compatible-chart test. The conclusion retains representability and open immersion
for j, quasi-compactness for j, scheme-test finiteness for pi, all three finite-presentation
conditions for pi, and the exact factorization equation. No nonempty/scheme/Noetherian
or representable-f assumption has appeared. No clause is missing. No mathematical
mismatch was found. A direct import of `Mathlib.AlgebraicGeometry.Scheme` was added to
make the original scheme dependency explicit; no signature change was needed.

## Validation

All compilations and the delivery preflight use the prescribed server wrappers.

Final-file `scompile.py Q23 lem-sfb-space-etale-finite-fp-envelope <module>` passed
for both the sandbox module (15.0 s) and the library module (10.5 s). No errors or
unexpected warnings were emitted. A source-only check also confirmed that the node
changes only `lean` and the four added `stmt_deps`, its recorded signature is verbatim,
the module has exactly one `sorry`, and every Lean line is at most 100 characters.

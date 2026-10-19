## Worker report

Reuse the existing theorem
`AlgebraicGeometry.smooth_iff_flat_locallyOfFinitePresentation_smooth_fiberToSpecResidueField`
in `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber`.
No new module, definition, theorem, dependency module, or node is needed.
Only the item's `lean` record changes; its statement and dependency list are unchanged.
The incomplete previous attachment already named this same theorem. This delivery supplies
its complete stage-2 record after independently checking the source.

Clause-by-clause comparison:

- An arbitrary morphism of schemes is `{X Y : Scheme.{u}} (f : X ⟶ Y)`;
  the ambient universe is explicitly `universe u` in the source module.
- “Smooth if and only if” is `Smooth f ↔`.
- Flatness is `Flat f`, the first conjunct on the right.
- Local finite presentation is `LocallyOfFinitePresentation f`, the second conjunct.
  This remains a conjunct, rather than an additional hypothesis.
- Every fibre smooth over its residue field is
  `∀ y, Smooth (f.fiberToSpecResidueField y)`.
  Mathlib's `Scheme.Hom.fiberToSpecResidueField` is the actual second pullback projection
  `f.fiber y ⟶ Spec (Y.residueField y)`, not smoothness over an unspecified base.
- No finite type, Noetherian, separatedness, characteristic, nonemptiness, or
  equidimensionality restriction is imposed. The parenthetical finite-type/Jacobian
  sentence is explanatory source attribution, not an additional theorem clause.

Dependency `def-sbc-smooth-morphisms` records `AlgebraicGeometry.Smooth` from
`Mathlib.AlgebraicGeometry.Morphisms.Smooth`. Its full class signature and docstring were
read: it is affine-local smoothness of ring maps, exactly the notion the node accepts
via Stacks 02H6. The reused theorem uses this very predicate, not a duplicate.
The fibre projection's full signature and docstring were also read in Mathlib's
`AlgebraicGeometry/Fiber.lean`.

The blueprint source was read at
`sec-smooth-base-change/sk-def-smooth/sbc-lem-smooth-criterion.md`.
Its proof route is already implemented by the reused theorem: smoothness supplies the
flatness and local finite presentation instances; base change supplies smoothness of
fibres; `Smooth.of_smooth_fiberToSpecResidueField` gives the converse.
The full existing theorem signature and docstring were read in the upstream checkout
and again through `scompile.py --source` in the current published server source.

Edge cases checked by inspection: empty X gives empty smooth fibres and a smooth map;
empty Y forces empty X, with the fibre quantifier vacuous; an empty fibre is permitted;
identity morphisms are included; arbitrary characteristics and arbitrary scheme universe
u are retained. No extra assumptions are needed. No statement dispute or node fault.

Searches (2026-10-15):

- `msearch.py ... leanfinder`: “A morphism of schemes is smooth if and only if flat
  locally of finite presentation and all residue field fibres are smooth”. Eight
  results, principally affine-local smoothness characterizations; no full iff there.
- `msearch.py ... loogle`: `AlgebraicGeometry.Smooth, AlgebraicGeometry.Flat,
  AlgebraicGeometry.LocallyOfFinitePresentation`. Found
  `AlgebraicGeometry.Smooth.of_smooth_fiberToSpecResidueField` in Mathlib, giving
  the converse with precisely flatness and local finite presentation assumptions.
- `msearch.py ... grep`: `smooth_iff|class Smooth|def Smooth` in AlgebraicGeometry.
  Found the Mathlib Smooth class and chart characterizations.
- `rg` of upstream WeilConjectures for the item id and exact theorem name found
  `Mathlib/AlgebraicGeometry/Morphisms/SmoothFiber.lean`, containing the exact iff.
  `rg` of project `lean/Sheaf` for those patterns found no competing declaration.

Validation: the required deliver2 dry run checks the existing declaration on the server
with an import and `#check`, and runs the maintainer's stage-2 preflight. No delivered
Lean file requires compilation because this delivery reuses an existing declaration.

## Second reading by NV

Independently read the sandbox node, its blueprint source, the dependency node
`def-sbc-smooth-morphisms`, the full upstream theorem, and the current server source
obtained by `scompile.py --source
WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber`.
The current server has additional sibling theorems, but the recorded signature is
unchanged and is verbatim equal to this declaration's signature.

Objects, hypotheses, and conclusions, checked individually:

- Arbitrary schemes X and Y: `{X Y : Scheme.{u}}`, with explicit `universe u`.
  Verdict: exact; no Noetherian, separatedness, or field-base restriction.
- Arbitrary scheme morphism f: `(f : X ⟶ Y)`, with no instance assumptions.
  Verdict: exact; neither flatness nor finite presentation is assumed beforehand.
- Smoothness of f: `Smooth f`. Verdict: exact. Opened the recorded dependency's
  Mathlib class: `smooth_appLE` requires smooth ring maps on every pair of affine
  opens. Stacks 02H6 identifies this with locally finitely presented and formally
  smooth morphisms, precisely as the dependency node explicitly allows.
- Equivalence, in both directions: `Smooth f ↔ ...`. Verdict: exact.
- Flatness: `Flat f`, the first conjunct. Verdict: exact.
- Local finite presentation: `LocallyOfFinitePresentation f`, the second conjunct.
  Verdict: exact; not finite type or global finite presentation.
- Every point y of Y: `∀ y, ...`, after the two conjuncts. Verdict: exact;
  y is inferred as a point of Y, without choosing a point or requiring one.
- Fibre X_y with its residue-field structure: opened Mathlib's `Scheme.Hom.fiber`,
  defined as `pullback f (Y.fromSpecResidueField y)`, and
  `Scheme.Hom.fiberToSpecResidueField`, whose full type is
  `f.fiber y ⟶ Spec (Y.residueField y)` and whose data is `pullback.snd _ _`.
  Verdict: the actual scheme-theoretic fibre and its canonical structure map.
- Smoothness over kappa(y): `Smooth (f.fiberToSpecResidueField y)`.
  Verdict: exact; not regularity of the underlying fibre or smoothness over
  an arbitrary base. The finite-type/Jacobian parenthesis is source commentary,
  not a separate universally quantified conclusion.

Read the Stacks TeX at morphisms.tex, section `section-smooth`, and labels
`lemma-smooth-flat-smooth-fibres` (01V8), `lemma-base-change-smooth` (01VB),
`lemma-smooth-locally-finite-presentation` (01VE), `lemma-smooth-flat` (01VF);
also more-morphisms.tex `lemma-smooth-formally-smooth` (02H6).
01V8 assumes exactly a morphism of schemes, flatness, local finite presentation,
and smooth fibres. 02H6 likewise concerns arbitrary scheme morphisms; neither
source imposes a standing Noetherian or characteristic assumption.
The existing theorem docstring gives the same proof steps: flatness and local
finite presentation from smoothness, smooth fibres by base change, then the
Mathlib fibre criterion for the converse. Its Stacks attribute and module
references identify 01V8. There is no new module to impose new docstring rules on.

Edge cases: empty X and empty fibres are permitted; empty Y forces empty X and
makes the point quantifier vacuous. Identity maps and the empty scheme from the
zero ring are included. There is no index set or relative-dimension n in this
statement. All characteristics and arbitrary scheme universe u are covered;
the common scheme universe is the ambient Mathlib category, not an extra
smallness hypothesis or equality between independently used site universes.
All source variables are explicitly bound. No new data, hollow definition,
proof, postponed theorem, helper node, or dependency module is introduced.

Independent searches used different concept queries from the worker:

- `msearch.py NV sbc-lem-smooth-criterion leanfinder` with
  `scheme morphism flat locally finite presentation smooth geometric fibers criterion`:
  eight hits, chiefly affine chart criteria and smoothness instances; no full iff.
- `msearch.py NV sbc-lem-smooth-criterion loogle` with
  `AlgebraicGeometry.Smooth, AlgebraicGeometry.Flat`: three hits, including
  `Smooth.of_smooth_fiberToSpecResidueField`, whose signature was opened.
- `msearch.py NV sbc-lem-smooth-criterion grep` with `smooth.*fiber|smooth.*fibre`:
  found the Mathlib converse in Morphisms/SmoothFiber and ring-level analogues.
- Direct `rg` over upstream WeilConjectures, Mathlib, and project lean/Sheaf using
  `smooth_iff|of_smooth_fiber|geometricallyRegular.*[Ff]iber|[Ff]iber.*geometricallyRegular`
  found the exact existing upstream iff and a distinct field-base-change criterion.
  Opened the exact iff; retained its existing record rather than duplicating it.

Mismatches found: none. Changes: appended this independent review only; retained
all node fields and the existing declaration record. No statement correction
or citer audit is needed. Server import/#check compilation and preflight are
performed by the required deliver2 dry run and delivery; there are no delivered
Lean source files to compile separately.

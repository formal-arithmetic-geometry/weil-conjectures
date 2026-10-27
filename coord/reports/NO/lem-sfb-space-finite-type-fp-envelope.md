## Worker report

Item: `lem-sfb-space-finite-type-fp-envelope`, group NO, stage 2.

The module `Sheaf.AlgebraicGeometry.SpaceFiniteTypeFPEnvelope` states
`AlgebraicGeometry.AlgebraicSpace.exists_finitePresentation_closed_envelope`.
It has one theorem with proof `by sorry`, no new definition, and no helper theorem.
The source is Stacks Project, Limits of Spaces, Tag 0872,
`lemma-finite-type-closed-in-finite-presentation`, read in
`literature/stacks-project/spaces-limits.tex`, lines 2818–2871, including its proof.
The node's mathematical statement and proof plan are unchanged.

Hypothesis-by-hypothesis and clause-by-clause rendering:

- Schemes and algebraic spaces: `AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))` is the
  existing full subcategory of fppf sheaves with representable diagonal and a
  representable surjective étale scheme atlas. Its morphisms `f : X ⟶ Y` are
  the existing sheaf natural transformations.
- Working over `Spec ℤ`: `Spec (.of (ULift.{u} ℤ))` gives exactly this base with
  the integers lifted to the arbitrary explicitly declared scheme universe `u`.
  No structure morphism, chart, or underlying space is chosen as additional data.
- Universe convention: `universe u` is explicit; the existing algebraic-space
  construction uses `Scheme.{u}`, `(Over S)ᵒᵖ`, and `Type u` sheaves. The statement
  adds no universe equality or smallness hypothesis. `autoImplicit` is disabled.
- Quasi-compactness of X: `hXqc` is the existence of an `Over` scheme `U` and a
  map `a : yoneda.obj U ⟶ X.obj.obj` such that `CompactSpace U.left`, `IsEtale a`,
  and `IsSurjective a`. The last two predicates include representability.
- Quasi-separatedness of X: `hXqs` asserts `IsQuasiCompactPresheafMap` of
  `prod.lift (𝟙 X.obj.obj) (𝟙 X.obj.obj)`, the presheaf diagonal over the fixed
  base `Spec ℤ`. Thus this is the absolute diagonal in this statement.
- Quasi-compactness of Y: `hYqc` is the identical atlas-existence condition for Y.
- Quasi-separatedness of Y: `hYqs` is the identical absolute-diagonal condition for Y.
- Local finite type of f: `hlft : MapIsLocally (@LocallyOfFiniteType) f` uses
  every compatible pair of representable étale scheme charts, and applies the
  recorded scheme `LocallyOfFiniteType` to the induced scheme morphism.
- Existence: `∃ (W : AlgebraicSpace ...) (j : X ⟶ W) (h : W ⟶ Y)` introduces
  precisely the space and two maps in the node's conclusion.
- Closed immersion: `IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
  j.hom.hom` requires every scheme base change to have a scheme representing
  pullback square whose projection is a scheme closed immersion. This includes
  representability, rather than just a condition on the underlying point map.
- Finite presentation of h: the next three conjuncts are
  `IsQuasiCompactPresheafMap h.hom.hom`,
  `IsQuasiCompactPresheafMap (pullback.diagonal h.hom.hom)`, and
  `MapIsLocallyOfFinitePresentation h`. These are respectively quasi-compactness,
  quasi-separatedness, and local finite presentation on compatible étale charts.
- Factorization: `j ≫ h = f` is the required equation `h ∘ j = f`.
- No separatedness of h is asserted. There is no separatedness, flatness,
  properness, or representability assumption on f or h.
- The node's introductory definitions of finite type and separatedness are
  conventions, not additional conclusions. Its finite-presentation convention is
  expanded into all three conjuncts above; finite type is not used to replace
  its weaker local-finite-type hypothesis.

The existing `IsQuasiCompactPresheafMap` has the node's exact affine-test atlas
meaning: after a test `h_T → Y` with affine T, it supplies a quasi-compact scheme U
with an étale surjective map to the actual presheaf fibre product. In its definition
this map is `pullback.lift q (yoneda.map p) hp`; its `(p,q,hp)` encoding is exactly
a map into that fibre product, by its universal property. No scheme
representability is required of the entire pullback.

Dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme.Hom`.
- `def-trf-algebraic-space`: `Sheaf.AlgebraicGeometry.AlgebraicSpace`, declarations
  `AlgebraicGeometry.AlgebraicSpace`, `.IsRepresentableWith`, `.IsEtale`, and
  `.IsSurjective`, with the full signatures and docstrings read.
- `def-weil-size-convention`: metatheoretic convention, not a Lean object;
  rendered by explicit universe polymorphism as its record prescribes.
- `def-sbc-locally-finite-presentation`:
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation`, used through the chart predicate.
- `def-weil-closed-immersion`:
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`, used in every representing scheme test.
- `lem-trf-space-fibre-products-etale-covers`:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`,
  `AlgebraicGeometry.AlgebraicSpace.fibreProduct_isAlgebraicSpace`, supplying the
  categorical sheaf-fibre-product convention. The relative diagonal in the
  conclusion uses the canonical presheaf pullback.
- `def-weil-finite-type-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`; its quasi-compact scheme predicate was
  also read in `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- Added already-landed `def-sfb-space-morphism-properties` to `stmt_deps`:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`, declarations
  `AlgebraicGeometry.AlgebraicSpace.MapIsLocally` and
  `.MapIsLocallyOfFinitePresentation`. This cites the shared notions used above.
- Added already-landed `def-sfb-space-quasi-compact-presheaf-map` to `stmt_deps`:
  `Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal`, declaration
  `AlgebraicGeometry.AlgebraicSpace.IsQuasiCompactPresheafMap`, supplying exactly
  the shared affine-test quasi-compact-atlas predicate. The owning definition node
  has an `existing: true` record on this declaration. The locality theorem
  `quasiCompact_separated_etaleLocal` is not a statement dependency.

Plain proof imports are
`Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality`
(`AlgebraicGeometry.AlgebraicSpace.flat_proper_fp_locality`) and
`Mathlib.AlgebraicGeometry.Noetherian`
(`AlgebraicGeometry.LocallyOfFinitePresentation.iff_locallyOfFiniteType` for
`pqf-lem-lft-fp-locnoeth`). Other proof dependencies have no recorded Lean or
Mathlib declaration in the read snapshot, so no import was invented for them.
Their complete three-step mathematical proof plan is retained in the docstring.

Edge cases checked before writing:

- Empty source: allowed. Its empty scheme atlas is quasi-compact, and W may be
  empty; no nonemptiness binder was introduced.
- Empty target: any map to it has empty source; both atlas conditions allow the
  empty scheme. No positive dimension, field, or nonzero-ring condition appears.
- Nonseparated qcqs spaces and nonseparated f: allowed; neither the hypotheses
  nor the conclusion has `MapIsSeparated`. Quasi-separatedness only says the
  diagonal is quasi-compact, never closed.
- Non-Noetherian spaces: allowed. No Noetherian or finite-presentation assumption
  was added to X or Y; Noetherian approximating stages occur only in the proof plan.
- Closed immersions need not be finitely presented. The closed immersion j has
  no finite-generation-of-ideal assumption; finite presentation is required of h.
- No quasi-compactness hypothesis on f was substituted for the two qcqs-space
  hypotheses, and no representability hypothesis on f or h was introduced.
- `u` is arbitrary, including `u = 0`; `ULift.{u} ℤ` provides the correct base
  universe without changing the base ring up to its canonical isomorphism.

Searches for an existing statement (all performed using the prescribed wrappers):

- LeanFinder: “A locally finite type morphism between quasi compact quasi separated
  algebraic spaces has a closed immersion into a space of finite presentation over
  the target”. Eight hits, all scheme properties/instances, no space-envelope theorem.
- Loogle: `"IsClosedImmersion", "LocallyOfFiniteType"`. One hit,
  `AlgebraicGeometry.instLocallyOfFiniteTypeOfIsClosedImmersion`, a scheme-only
  property implication, not this existence statement.
- LeanSearch: “finite presentation closed envelope algebraic spaces”. Eight hits
  about algebra/module presentations, no matching theorem.
- Wrapper grep: `AlgebraicSpace|finiteType.*finitePresentation|finite.*type.*closed.*presentation`.
  Ten Mathlib hits concerning rings and scheme finite-presentation properties;
  no algebraic-space envelope.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for `finitePresentation_closed_envelope`, `exists_fpEnvelope`, `fpEnvelope`,
  `finitePresentationEnvelope`, and the item id. The existing
  `Scheme.Hom.exists_fpEnvelope` in
  `WeilConjectures.Compactification.NagataCompactification` is scheme-only and
  assumes separatedness (signature and its preceding variable assumptions read).
  `SpaceSeparatedFiniteTypeFPEnvelope` states Tag 0873 with separatedness, not 0872.
  Other hits cite this item only in proof docstrings.
- Inspected existing `AlgebraicSpaceMorphismProperties`,
  `SpaceQCSeparatedEtaleLocal`, `SpaceQuasiCompactAffineTests`, and
  `AlgebraicSpaceAbsoluteQuasiSeparated` to reuse the existing notions.
  No duplicate definition, new node, or dependency repair is needed.

No mathematical fault or statement dispute was found. The only node-field changes
are `lean` and the two added already-landed statement-dependency IDs.

Validation: `scompile.py NO lem-sfb-space-finite-type-fp-envelope` compiled this
file both as a sandbox module and under its intended library module name, in
1.9 s and 1.7 s respectively, with no error or unexpected warning. All delivered
Lean lines are at most 100 characters. No local/global build was run.

## Second reading by NO

I reread the node, the delivered Lean file, the source statement and proof, and
all predicates appearing in the signature. This is a separate pass by the same
worker; the dispatcher forbids starting another agent, and the maintainer's
independent delivery review is still required.

The node's X and Y are both qcqs: the signature has separate `hXqc`, `hXqs`,
`hYqc`, `hYqs`, and no relative substitute for either absolute diagonal. With
base `Spec (ULift ℤ)`, `prod.lift` is the correct absolute diagonal, rather than
requiring arbitrary-base relative quasi-separatedness to mean absolute qs.
The node's sole morphism hypothesis is local finite type, rendered by `hlft`.
Its chart predicate quantifies over all compatible étale scheme charts, without
assuming the given morphism representable. The conclusion binds exactly W, j,
and h; the first conjunct includes representability and all scheme closed-immersion
tests, the next three give all constituents of finite presentation, and the last
conjunct is the factorization equation in the correct composition order. In
particular the diagonal conjunct for h was checked separately from that for X
and Y, and no separatedness conjunct was introduced. No mismatch was found in
this second pass. The source's general-S statement is represented at the fixed
integer base explicitly prescribed by this node; this includes all absolute
spaces and maps under the chosen size convention. No statement correction was made.


## Repair of returned delivery e52b78cee375

H2: replaced `lem-trf-space-qc-separated-etale-local` in `stmt_deps` with the
landed definition node `def-sfb-space-quasi-compact-presheaf-map`. I read that
node's statement and its `existing: true` Lean record, and reread the full
`IsQuasiCompactPresheafMap` definition in
`Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal`. The predicate is plain defined
data, not a choice from the locality theorem. The dependency list and the
worker report now cite its owning definition node. The module import remains
the same because the definition is declared in that module.

I compared the retained delivered node against current main and rebuilt its
node copy from current main, preserving every field except `lean` and the
addition of the two landed definition dependencies. The delivery wrapper will
base the repair on current main. The Lean file remains byte-identical to the
returned delivery, as permitted by the return; its statement, proof docstring,
and single `sorry` are unchanged.

I also read the advisory definition `AlgebraicSpace.IsQuasiCompact` in
`Sheaf.AlgebraicGeometry.StackQcqsMorphism`: its body is verbatim the two
atlas-existence hypotheses. I retain the reviewed expanded hypotheses, so this
repair changes only the requested dependency attribution and report.

Repair second reading: `hXqc`, `hXqs`, `hYqc`, `hYqs`, and `hlft` still render
all the source hypotheses; the closed immersion, three finite-presentation
constituents, and factorization still render every conclusion. H2 is repaired
by the owning definition dependency; no theorem statement dependency remains
merely to access its plain definition. No mathematical correction is needed.

Repair validation: the prescribed `scompile.py` recompiled the retained Lean
file against the current published server library, in 1.6 s under the sandbox
name and 1.7 s under the intended library name, cleanly.

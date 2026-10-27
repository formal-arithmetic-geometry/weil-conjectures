## Worker report

Stage 2 for `lem-sfb-space-two-field-scalar-algebraicity`, group Q27. The resumed
assignment explicitly says stage 2; `coord/queue.tsv` lists the item at stage 2,
and the maintenance handoff at the start of `coord/brief-stage2.md` explains
that its accepted stage-1 split is the input, not a prohibition on this work.
The stage-2 sandbox is the environment's `WEIL_SANDBOX`,
`/home/ubuntu/weil-newtargets-stage2-sandbox/Q27/lem-sfb-space-two-field-scalar-algebraicity`.
There was no saved Lean module, node copy, report, or interrupted delivery here.
No agent was started. The accepted statement, dependencies, six-step proof,
source, blueprint lineage, status and reviewed record are retained unchanged.

Files delivered:

- `lean/Sheaf/AlgebraicGeometry/SpaceTwoFieldScalarAlgebraicity.lean`: one theorem,
  `AlgebraicGeometry.AlgebraicSpace.scalar_algebraicity_of_two_locallyOfFiniteType`,
  with proof `by sorry` and the accepted six-step proof in its docstring.
- `dag/nodes/sec-six-functors-basics/lem-sfb-space-two-field-scalar-algebraicity.json`:
  only its `lean` record is added.
- `report.md`: this report.

Hypothesis and conclusion correspondence:

- `S : Scheme.{u}` and `E : AlgebraicSpace S` use the recorded scheme and
  algebraic-space notions. In `Sheaf.AlgebraicGeometry.AlgebraicSpace`, the latter
  is the full subcategory of big-fppf sheaves with representable diagonal and a
  representable surjective etale atlas. Its underlying presheaf is `E.obj.obj`.
- `k₁`, `k₂`, and `F`, each with `Field`, are the three arbitrary fields. The
  common universe is the same one as schemes in the algebraic-space interface;
  there is no cardinality, characteristic, algebraic-closedness, or finite
  extension restriction. The universe parameter itself is arbitrary.
- `s₁`, `s₂`, and `sF` are the maps of the three spectra to S. A natural map to
  `yoneda.obj (Over.mk sᵢ)` is precisely a map to that spectrum over S. Thus `p₁`
  and `p₂` are the two S-structure maps, and `e` is the field-valued S-point.
- `hp₁` and `hp₂` quantify over every scheme `U : Over S` and every chart
  `a : yoneda.obj U ⟶ E.obj.obj` with `AlgebraicSpace.IsEtale a`. This is the
  recorded representable-etale condition, without a surjectivity restriction.
  The composites with `pᵢ` are maps between representables; `yoneda.preimage`
  recovers the scheme map over S, and `.left` forgets the S-structure. The
  hypotheses say these maps are `AlgebraicGeometry.LocallyOfFiniteType`.
- `j₁` and `j₂` are ring homomorphisms between fields, hence embeddings. The
  equations `hj₁` and `hj₂` say that their spectrum maps are exactly the maps
  obtained from `e ≫ pᵢ`. These equations identify the induced homomorphisms;
  they impose no new mathematical hypothesis because Spec is fully faithful.
- The first conjunct asserts for every `x : k₁` the existence of a polynomial
  `P : Polynomial k₂` with `P ≠ 0` and `P.eval₂ j₂ (j₁ x) = 0`. This is exactly
  algebraicity over the image `j₂(k₂)`: transport coefficients along the
  injective `j₂`. Polynomials over k₂ and polynomials over its image correspond
  coefficient by coefficient and nonzeroness is preserved. The second conjunct
  swaps both fields and both embeddings. There is no additional clause.
- No `IsReduced`, connectedness, quasi-compactness, or finite-type condition on
  E over S is present. The only finiteness is chartwise local finite type for
  the two stated maps, just as in the node.

Recorded declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Spec`, `Spec.map`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`
  and `AlgebraicGeometry.AlgebraicSpace.IsEtale`; the actual declarations and
  docstrings were read, including `IsRepresentableWith` and the atlas condition.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`, its all-affine-pairs definition read
  at lines 39–47. The etale notion used in the chart predicate is the scheme
  notion provided by `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `Mathlib.Algebra.Polynomial.Eval.Defs`: `Polynomial` and `Polynomial.eval₂`,
  read at line 57. Field structures are Mathlib's `Field`.
- Yoneda's existing fully faithful interface supplies `yoneda.preimage`; the
  category of schemes over S is Mathlib's `Over S`, with morphism projection
  `.left`. No new definition or alternative algebraic-space encoding is added.

All currently stated proof-dependency modules are plain imports: ResidueField,
AffineScheme, OpenImmersion, Properties, RingTheory.Spectrum.Prime.Topology,
and Topology.Connected.Basic. Dependencies already visible through the public
statement imports are not repeated. The only proof-dependency node without a
Lean declaration or Mathlib match is
`lem-sfb-connected-reduced-scalar-field-uniqueness`; its future module cannot
be imported yet. This is a proof prerequisite, not a missing statement notion,
so it does not prevent the stage-2 statement.

Sources read: `literature/stacks-project/varieties.tex`, Tag 04MK,
`proposition-unique-base-field`, statement and beginning of its proof at
lines 5964 onward; and `literature/stacks-project/stacks-morphisms.tex`, Tag
0DTM, `lemma-universally-injective-point`, at lines 2763–2822. The former
compares integral closures on a connected reduced scheme with both maps
locally of finite type. The accepted split reduces an arbitrary point of E
through an atlas and a prime quotient to precisely that situation. The latter
source explicitly uses this scalar consequence in a common point field.
The docstring preserves all six arguments and their node citations.

Edge cases checked: if E is empty there is no `e`; if it is disconnected or
nonreduced the theorem adds no restriction; x = 0 and x = 1 allow T and T−1;
equal embeddings and equal fields are included; generic or nonclosed points
and arbitrary large point fields are not replaced by closed or finite points.
The two induced embeddings can differ even when the underlying fields agree.
There is no assumption that E is a scheme or that an atlas is quasi-compact.

Searches were actually run with the prescribed `batch2/msearch.py`; their
unaltered query/result summaries are in `searches.jsonl`:

1. leanfinder: `For an algebraic space locally of finite type over two fields, the images of the fields in every field valued point are algebraic over each other`.
   Hits included `finite_appTop_of_universallyClosed`,
   `Algebra.finite_of_essFiniteType_of_isAlgebraic`, and `LocallyOfFiniteType`.
2. leansearch: `Two fields of scalars on a locally finite type algebraic space give algebraic scalar images at a point`.
   Hits included `Scheme.Γevaluation`, residue-field instances and
   `IntermediateField.restrictScalars_adjoin_of_algEquiv`.
3. loogle: `"LocallyOfFiniteType", "IsAlgebraic"`. No hits.
4. grep: `unique.base.field|two.field.structures|scalar.*[Aa]lgebraic`,
   subdirectory `AlgebraicGeometry`. No hits.
5. leanfinder: `Uniqueness of fields of definition up to algebraicity for two locally finite type morphisms from the same scheme to spectra of fields`.
   Hits included `Scheme.SpecToEquivOfField`, its equality lemma,
   `Scheme.RationalMap.fromFunctionField_ofFunctionField`, and the same
   universally closed global-section results.

Every service answered successfully. I read the relevant candidate sources:
Proper.lean lines 148–173 requires universal closedness and compares global
sections to one field, so cannot instantiate this theorem; ResidueField.lean
lines 78–104 and 330–365 identify points and residue maps but do not compare
independent fields of scalars. Neither a match nor a one-line specialization
states the item. Searches by the exact blueprint tag, the proposed full
name, and two-field/scalar-field keywords in `lean/WeilConjectures`,
`lean/Sheaf`, and `dag/lean_names_upstream.json` found no existing statement.
No source declaration is attached and no duplicate notion is introduced.
No new DAG node or dependency module is needed. No statement correction,
STATEMENT-DISPUTED, source error, or WANTED source is present.

Validation: the first compile found only a parser error from using the reserved
Lean token λ as a binder name. I changed that binder to x; no mathematical
part of the statement changed. The required `batch2/scompile.py Q27
lem-sfb-space-two-field-scalar-algebraicity <file>` then completed with exit 0:
sandbox compile 40.0 s and library-module compile 7.5 s, both within the
unchanged 60 s per-file limit. No error or unexpected warning remained.

## Second reading by Q27

This is the same worker's separate second pass, with the accepted node, source,
actual dependency interfaces, and completed Lean module open. No separate
worker was started, as instructed. I compared the objects first: E remains
an algebraic space over arbitrary S, rather than a scheme or its global-section
ring; the source and target of every natural transformation are the correct
representables in `(Over S)ᵒᵖ ⥤ Type u`. I checked that the chart predicate is
`IsEtale a`, whose definition already includes representability, and that the
local-finite-type conclusion uses the chart composite, not either structure
map detached from that chart. Neither test demands a surjective chart.

I then checked the point and the two scalar maps. The order `e ≫ pᵢ` maps
Spec F to Spec kᵢ, so the corresponding ring homomorphism must go kᵢ → F.
That is exactly the direction of `jᵢ`; `Spec.map (CommRingCat.ofHom jᵢ)` in
`hjᵢ` makes this identification explicit. Without these equalities the
statement would wrongly concern arbitrary embeddings. They are present and
are canonical identifications, not extra assumptions on the point.

Finally, I read each conclusion: the polynomial uses coefficients from the
other field, and its evaluation uses the other embedding but the selected
scalar's own embedding. Both nonzero conditions and both universal scalar
quantifiers are present. The coefficient identification with the image
subfield preserves nonzeroness because a ring homomorphism from a field is
injective. No topological hypothesis on E is smuggled into the binders.
I compared the six docstring steps with the accepted six-step split, including
the atlas lift, the prime quotient, nonemptiness for 04MK, and reflection along
F → L. The unstated scalar-uniqueness lemma remains a proof prerequisite only.
The only correction during compilation was the reserved-token binder name;
no mismatch or mathematical correction remained after this reading.
The node copy differs from the current accepted node only by `lean`.

Final stage-2 dry run: `python3 /home/ubuntu/weil-launcher-all/batch2/deliver2.py Q27 lem-sfb-space-two-field-scalar-algebraicity --no-push` exited 0 and printed `OK (dry run): commit 168145e70e8 passes the preflight and compiles; nothing pushed`. The same invocation was polled to completion before starting delivery. The only subsequent change was this validation record.

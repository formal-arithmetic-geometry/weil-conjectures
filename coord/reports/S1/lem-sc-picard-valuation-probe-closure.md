## Worker report

The module `Sheaf.AlgebraicGeometry.ValuativeSquareOfMemClosureRange` states
`AlgebraicGeometry.exists_valuativeCommSq_of_mem_closure_range`, with proof `sorry`.
No definition, new node, dependency module, or statement correction is needed.

Hypotheses and clauses, individually matched:
- Schemes Z and S: `{Z S : Scheme.{u}}`; the universe is explicitly bound.
- Scheme morphism j: `(j : Z ⟶ S)`.
- Quasi-compact immersion: `[QuasiCompact j] [IsImmersion j]`, retaining both assumptions.
- Every point s in the closure of j(Z): `{s : S}` and
  `(hs : s ∈ closure (Set.range j))`.
- There exists a valuation ring A: `∃ sq : ValuativeCommSq j` carries `sq.R`,
  `sq.commRing`, `sq.domain`, and `sq.valuationRing`.
- Its fraction field K: the same square carries `sq.K`, `sq.field`, `sq.algebra`,
  and `sq.isFractionRing`. This imposes exactly fraction-field status, not an
  arbitrary field extension.
- The map g from Spec(A) to S is `sq.i₂`.
- The map h from Spec(K) to Z is `sq.i₁`.
- Generic commutativity is `sq.commSq.w`:
  `sq.i₁ ≫ j = Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ sq.i₂`.
  This is the node's equality in the reverse orientation.
- The closed point maps to s:
  `sq.i₂ (IsLocalRing.closedPoint sq.R) = s`.

Dependency declarations read and used:
`def-weil-scheme-morphism-properties` is an existing convention node, with
null declaration/module, explicitly directing citers to the individual notions.
Quasi-compactness is `AlgebraicGeometry.QuasiCompact` in
`Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, also recorded in
`def-weil-finite-type-morphism`. Immersion is `AlgebraicGeometry.IsImmersion`
in `Mathlib.AlgebraicGeometry.Morphisms.Immersion`, identified by the
`mathlib_match` of `def-weil-closed-immersion`. Their signatures and docstrings
were read. The sole import `Mathlib.AlgebraicGeometry.ValuativeCriterion`
provides these properties and `AlgebraicGeometry.ValuativeCommSq`; its full
structure signature and all fields were read. Thus there is no private copy.

The docstring records both proof steps of the node. The proof dependencies'
source declarations were also read: `AlgebraicGeometry.exists_specializes_of_mem_closure_range`
(`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`) and
`AlgebraicGeometry.ValuativeCommSqWithPt.ofSpecializes`
(`WeilConjectures.Compactification.ValuativeCriterion`). They are not imported
because the proof remains `sorry` and neither is needed to elaborate the statement.

Edge cases checked before writing: for empty Z its image and closure are empty,
so there is no s satisfying hs; empty S has no point s. Fields are permitted as
valuation rings, so constant probes are included. No Noetherian, separated,
finite-type, characteristic, or positive-dimension restriction is imposed.
The square uses the same universe u as the schemes. The construction in the
source uses a valuation subring of the residue field of a point of Z, which
lives in u, so this universe does not exclude any closure point. There is no
universal quantification over a smaller universe of test rings.

Source: the local `literature/stacks-project/morphisms.tex` is absent on this
machine. Read the official source instead:
https://stacks.math.columbia.edu/tag/02JQ (Lemma 29.6.5). Its footnote identifies
the underlying scheme-theoretic image with the closure of the image for a
quasi-compact morphism; its valuation diagram has exactly the required two
legs and closed-point condition. The node specializes the hypothesis to an
immersion; no correction is necessary.

Searches made (msearch results are also in searches.jsonl):
- LeanFinder via msearch: "a point in the closure of the image of a quasi compact
  immersion admits a valuation ring probe with generic point in the source and
  closed point at that point". Eight hits, including range_fromSpecStalk,
  Existence.specializingMap and instIsDominantToImageOfQuasiCompact; no exact statement.
- Loogle via msearch: "AlgebraicGeometry.ValuativeCommSq,
  AlgebraicGeometry.QuasiCompact". Zero hits.
- Mathlib grep via msearch: "closure.*range|ValuativeCommSqWithPt" in
  AlgebraicGeometry. Fifteen hits, on scheme-theoretic image support and other
  closure facts; no exact valuation-probe statement.
- LeanSearch via msearch: "valuation ring generic point source closed point
  closure image quasi compact morphism". Service unavailable: Internal Server Error.
- rg in WeilConjectures and lean/Sheaf for
  "valuation.*closure|closure.*valuation|valuation_probe|ValuativeCommSqWithPt":
  finds the existing structure, ofSpecializes, ofIsDominant, and the landed
  ClosedImmersionOfValuativeFactorization consumer. The dominant-source constructor
  requires dominance and applies to every target point; it is not the item.
  The specialization constructor requires a supplied source point; it is not the item.
- rg for the item id and proposed declaration name in WeilConjectures and
  dag/lean_names_upstream.json: no hits. The proposed declaration is fresh.

Validation: server single-file compilation and deliver2 --no-push dry run are
run before reporting READY. Only the expected sorry warning is permitted.

## Second reading by S1

I independently read the node statement, its source (Stacks Project Tag 02JQ, Lemma
29.6.5), and the Lean module. The node introduces schemes `Z S : Scheme`, a morphism
`j : Z ⟶ S`, instances `[QuasiCompact j]` and `[IsImmersion j]`, and a point
`{s : S}` with `hs : s ∈ closure (Set.range j)`. The Lean binders
`{Z S : Scheme.{u}} (j : Z ⟶ S) [QuasiCompact j] [IsImmersion j] {s : S} (hs :
 s ∈ closure (Set.range j))` render these objects and hypotheses exactly, with one
shared universe. Its conclusion is rendered by
`∃ sq : ValuativeCommSq j, sq.i₂ (IsLocalRing.closedPoint sq.R) = s`: the bundled
square supplies the valuation ring `sq.R`, fraction field `sq.K`, maps
`Spec sq.K ⟶ Z` and `Spec sq.R ⟶ S`, the generic commutativity equation, and the
closed-point equation. Thus every clause of the node's existential conclusion is
present; the square's `commSq` field is the stated restriction equality, with the
same equality up to the bundled `CommSq` orientation.

The source lemma is stated for a quasi-compact morphism and a point of its
scheme-theoretic image. The node is the explicitly recorded immersion/closure
specialization used by this unit; these additional node hypotheses are retained
verbatim and make the source construction applicable. No hypothesis is added by
the Lean statement beyond those in the node. Empty `Z` gives an empty range and
there is no admissible `s`; empty `S` has no point; valuation fields are allowed
as valuation rings; no Noetherian, separated, finite-type, characteristic, or
positive-dimension condition appears; and `u` is shared by both schemes and the
valuation square.

I checked the dependency declarations and their source modules: `QuasiCompact`,
`IsImmersion`, and `ValuativeCommSq` are the project/Mathlib declarations named by
the node, not private copies. Searches (LeanFinder, Loogle, LeanSearch, and `rg`
over Mathlib, WeilConjectures, and `lean/Sheaf`) found no existing declaration of
this closure valuation-probe statement. The module has the required source and
blueprint docstrings, and its only proof is the permitted `sorry`. No mismatch was
found, so no Lean or node change was needed.

Validation: `scompile.py S1 lem-sc-picard-valuation-probe-closure
lean/Sheaf/AlgebraicGeometry/ValuativeSquareOfMemClosureRange.lean` compiled cleanly;
only the expected `sorry` proof remains.

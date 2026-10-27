## Worker report

Delivered module: `Sheaf.AlgebraicGeometry.AffinePuncturedLocalDimension`.
Main declaration:
`AlgebraicGeometry.ringKrullDim_le_one_of_isAffine_puncturedSpectrum`.
This is a stage-2 statement only; its sole proof is `sorry`.

Read the item, all five statement-dependency records, their source declarations and
docstrings, and Stacks `literature/stacks-project/divisors.tex`,
`lemma-affine-punctured-spec`, Tag 0BCR, lines 3348–3406. The source states an iff;
the node asks for exactly its only-if implication. No correction is needed.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| A commutative ring A | `(A : Type u) [CommRing A]`, with explicit `universe u` |
| A Noetherian | `[IsNoetherianRing A]` |
| A has a unique maximal ideal, so is local | `[IsLocalRing A]` |
| P = Spec A minus its maximal point, with the open subscheme structure | `(puncturedSpectrum A).toScheme` |
| P affine | `(hP : IsAffine (puncturedSpectrum A).toScheme)` |
| dim A at most one | `ringKrullDim A ≤ 1` in `WithBot ℕ∞` |

`IsLocalRing` is Mathlib's local-ring predicate, equivalent in the commutative
case to existence of a unique maximal ideal (as documented in
`Mathlib.RingTheory.LocalRing.Defs`). It includes nontriviality, which follows
already from the node's existence of a maximal ideal. There is no additional
nontriviality hypothesis. The name m need not be separately quantified: it is
`IsLocalRing.maximalIdeal A`, and its point is `IsLocalRing.closedPoint A`.

The following recorded statement-dependency declarations are used:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing` (lines 195–205 include the finite-ideal characterization).
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `Spec.map` (lines 469–480).
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion` (lines 35–39). The open subscheme is
  Mathlib's `Scheme.Opens.toScheme`; its inclusion has this open-immersion
  structure, with no extra immersion hypothesis on the theorem.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `Scheme.Hom` (lines 35–48 and 73–75).
  Affineness uses `AlgebraicGeometry.IsAffine` from
  `Mathlib.AlgebraicGeometry.AffineScheme` (lines 58–60), the predicate that the
  canonical morphism to Spec of global sections is an isomorphism.
- `def-weil-pbc-krull-dimension-ring`: `Mathlib.RingTheory.KrullDimension.Basic`,
  `ringKrullDim` (lines 26–31), the supremum of lengths of strict prime chains.

The already existing upstream helper `AlgebraicGeometry.puncturedSpectrum`,
`WeilConjectures.AlgebraicGeometry.PuncturedCurveBranches`, lines 32–34, is
used directly, without any new definition: it is
`⟨{IsLocalRing.closedPoint A}ᶜ, (isClosed_singleton_closedPoint A).isOpen_compl⟩`.
Its signature requires only a commutative local ring, not the excellent,
one-dimensional or strictly henselian assumptions of the later theorem in
that module. Thus importing it adds none of those assumptions to this theorem.
No new node or dependency-interface repair is necessary.

All stated proof-dependency modules are imported, using plain `import` for
proof dependencies and `public import` for statement dependencies. The sole
unstated proof dependency `lem-sfb-power-torsion-cokernel-length` has neither
Lean record nor Mathlib match, so has no module to import yet. It is not needed
to type this statement; its exact use in the future proof is documented in
step 6. The full eight-step DAG proof is in the theorem docstring, including
the explicit connecting maps, zero-module case, and final closed-map argument.

Edge cases checked before writing:

- A field: the closed point is the sole prime, the puncture is the empty scheme
  (affine as Spec of the zero ring), and dimension zero satisfies the conclusion.
- Every zero-dimensional Noetherian local ring, including nonreduced ones: the
  same empty-puncture case is retained. No reducedness or domain assumption is added.
- Dimension one, multiple minimal primes and nilpotents: all are admitted; the
  docstring reduces the proof to the reduced ring, not the theorem's hypotheses.
- The zero ring has no maximal ideal, so is excluded by precisely the node's
  unique-maximal-ideal hypothesis. This is not an excluded case of the node.
- No characteristic or residue-field restriction; arbitrary ring universe u.
- The empty puncture is allowed by `IsAffine`; there is no nonempty or positive
  dimension assumption. A higher-dimensional local ring would force the
  affineness hypothesis to fail, which is exactly the conclusion's content.

Searches performed (all service queries via the prescribed msearch wrapper):

- LeanFinder: “An affine punctured spectrum of a Noetherian local ring has
  Krull dimension at most one”. Eight hits: Noetherian local dimension
  finiteness, dimension-drop/quotient bounds, and a Dedekind-domain DVR
  dimension bound. None is this affineness implication.
- Loogle: `AlgebraicGeometry.IsAffine, ringKrullDim`. Zero hits.
- msearch grep: `punctured|puncture|0BCR` in Mathlib `AlgebraicGeometry`.
  Zero hits.
- LeanSearch: the same natural-language query as LeanFinder. Eight hits:
  `Ring.DimensionLEOne`, Dedekind-ring bounds, finite dimension, affine-scheme
  definitions, localization/dimension-zero statements, and Noetherian-space
  facts. None states the implication from puncture affineness.
- Direct rg of `lean/WeilConjectures` and `lean/Sheaf` for puncture spellings and
  `0BCR`: found the upstream puncture construction, curve-branch descriptions,
  completion/purity applications and punctured affine-line results. Read the
  general puncture construction in full; none gives this theorem. Direct grep
  by the exact item id in `lean/WeilConjectures` had no hit.
- Direct rg for `def .*punctur`, `abbrev .*punctur` and related capitalization
  in Mathlib, WeilConjectures and Sheaf identified the existing
  `AlgebraicGeometry.puncturedSpectrum`; it is reused.
- Direct rg of the chosen declaration name and `0BCR` in Mathlib,
  WeilConjectures, Sheaf and `dag/lean_names_upstream.json` found no collision.

Validation: prescribed `scompile.py Q111 lem-sfb-affine-punctured-local-dimension`
compiled both its sandbox probe (2.5 s) and intended library module (7.9 s),
with no errors or warnings. All variables and universes are explicitly bound;
all Lean lines have at most 100 characters. Only `lean` changes in the node.

## Second reading by Q111

This is a second pass by the same dispatched worker; no independent worker
has been started, in accordance with the explicit dispatch instructions.
The maintainer's independent review remains the independent reading.

Reopened the item and the complete written module and compared each binder
and conclusion with Stacks 0BCR. `CommRing`, `IsNoetherianRing` and
`IsLocalRing` render precisely the ring hypotheses. In particular, the
puncture helper does not require the strictly henselian or dimension-one
hypotheses appearing later in its owning module. Its actual data is exactly
the complement of the unique maximal point, so `.toScheme` gives the required
restricted structure sheaf, not an arbitrary scheme with that underlying set.
`IsAffine` states exactly the antecedent, and `ringKrullDim A ≤ 1` states the
one requested conclusion. The zero-dimensional empty-puncture case survives;
no field, reducedness, positivity, finiteness of dimension or residue-field
assumption has slipped into the signature. No mismatch was found, and no
statement correction, new node or dependency module was required. The sole
`sorry` belongs to the matching theorem and its docstring records all eight
proof steps from the accepted node. There are no diagnostic declarations.

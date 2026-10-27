## Worker report

Stage 2, Q22, 2026-10-23. The module
`Sheaf.AlgebraicGeometry.LftFiniteRelativeAffineAtlas` states
`AlgebraicGeometry.exists_finite_relative_affine_atlas`, with its sole proof `sorry`.
No definitions, new nodes, dependency modules, or statement corrections are needed.
Only the item's `lean` field changes in its node copy.

The inherited BLOCKED ending confused an accepted stage-1 split with an accepted
stage-2 statement. The current node's Q159 review explicitly concerns four proof
steps and no Lean files; its `lean` field is absent and `coord/queue.tsv` lists it
at stage 2. This delivery preserves that accepted statement and split, following
the stage-handoff rule in coord/brief-stage2.md section 0.

Hypothesis and conclusion correspondence:

- The three schemes are `S U V : Scheme.{u}`. Each has both `CompactSpace` and
  `QuasiSeparatedSpace`, retaining all six qcqs assumptions even where stronger
  than necessary for the chart construction.
- The structure maps are `s : U ⟶ S`, `v : V ⟶ S`, and `g : U ⟶ V`;
  `hcomp : g ≫ v = s` is precisely the over-base compatibility.
- Local finite type is `[LocallyOfFiniteType g]`.
- The first conclusion is `QuasiCompact g`.
- Nonnegative integers are `m : ℕ` and `n : Fin m → ℕ`. The charts `W`, `Y`,
  `X` are families of actual scheme opens, with respective index types `Fin m`,
  `Fin m`, and `Fin (n j)`. All three families have `IsAffineOpen` proofs.
- The finite target covering is `(⨆ j, Y j) = ⊤`; each finite source covering
  is `(⨆ k, X j k) = g ⁻¹ᵁ Y j`. These source charts are opens in U itself.
- `hYW` asserts `Y j ≤ v ⁻¹ᵁ W j`; `hXY` asserts
  `X j k ≤ g ⁻¹ᵁ Y j`. `hXW` records the resulting factorization over W
  under the given structure map s; it is the inclusion needed to type its
  canonical section map, and follows from hcomp, hXY and hYW.
- The coordinate rings are the actual canonical commutative rings
  `Γ(S, W j)`, `Γ(V, Y j)`, and `Γ(U, X j k)`. Affineness identifies their
  spectra with the corresponding open subschemes via Mathlib's
  `IsAffineOpen.isoSpec`. No unrelated coordinate rings are quantified over.
- The R-to-B and R-to-C structure maps are respectively `v.appLE` and
  `s.appLE`. The B-to-C map φ is exactly `g.appLE`. Its `.hom.FiniteType`
  expresses finite generation of C over B for the induced algebra structure.
- The equation `v.appLE ... ≫ g.appLE ... = s.appLE ...` says precisely
  that φ respects these R-algebra structures. Ring homomorphisms with this
  compatibility are R-algebra homomorphisms; the formulation supplies their
  defining property without replacing the canonical maps by arbitrary maps.
- The last equation, `Spec.map (g.appLE ...) ≫ (hY j).fromSpec =
  (hX j k).fromSpec ≫ g`, identifies the spectrum map with the actual
  restricted g, using the canonical affine chart immersions. Since the target
  chart immersion is a monomorphism this is exactly the restricted-map assertion.
- Empty finite covers are admitted by `Fin 0`, and no Nonempty or nontrivial-ring
  assumptions occur.

Dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-pbc-scheme-conventions` is explicitly a convention record, not a
  separate definition; it supplies the meanings of qcqs, rendered with
  `CompactSpace` and `QuasiSeparatedSpace`.
- `def-weil-finite-type-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`, together with
  `AlgebraicGeometry.QuasiCompact` in `Morphisms.QuasiCompact`.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map` in
  `Mathlib.AlgebraicGeometry.Scheme`; `IsAffineOpen.isoSpec`, `fromSpec`, and
  `SpecMap_appLE_fromSpec` in `Mathlib.AlgebraicGeometry.AffineScheme` supply
  the canonical affine presentation and interpretation.
- Proof dependency `def-weil-pbc-quasi-compact-scheme` is `CompactSpace`.
  `lem-weil-pbc-affine-opens-basis` uses the recorded Mathlib match
  `Scheme.isBasis_affineOpens` from AffineScheme. The relevant clause of
  `lem-weil-pbc-qcqs-morphism-permanence` is the recorded match
  `quasiCompact_of_compactSpace` in Morphisms.QuasiSeparated. These modules
  are imported; all other proof dependencies are already among the statement
  dependencies. Mathlib dependencies require no replacement modules.

Source read: literature/stacks-project/limits.tex, Situation
`situation-descent-property` at line 1739 and Tag 0C4W
`lemma-descend-unramified`, first proof paragraph at lines 1806 onward.
The hypotheses of that situation supply exactly the qcqs schemes and the
over-base triangle retained here. No assumption about a later unramified limit
is used in this finite-chart reduction.

Edge cases checked before writing: V empty permits m = 0, and then U is empty
because g exists. An empty inverse image permits n j = 0. U empty with V
nonempty also causes no restriction. S empty forces both other schemes empty.
The empty affine scheme and its zero coordinate ring are permitted, including
nonempty chart index sets with empty affine members. No separatedness, integral,
field, characteristic, or nonzero-ring condition was introduced. All objects
use the common scheme universe u, all variables are explicitly bound, and the
finite index types do not impose an extra universe equality or nonemptiness.

Searches actually run through msearch.py (retained in searches.jsonl):

- LeanFinder: "A locally finite type morphism between quasi compact quasi
  separated schemes over a base has finite affine source target charts mapping
  into affine base opens with compatible finite type coordinate ring maps".
  Eight hits, principally locallyOfFiniteType_iff and finiteType_appLE, give
  individual ingredients, not this complete nested relative atlas.
- Loogle: `AlgebraicGeometry.LocallyOfFiniteType,
  AlgebraicGeometry.Scheme.OpenCover`: zero hits.
- Grep: `finiteSubcover|finiteType_appLE|affine.*[Aa]tlas`, subdirectory
  AlgebraicGeometry: 25 hits including Cover.Open finiteSubcover,
  Morphisms.FiniteType finiteType_appLE, and uses of these ingredients.
- LeanSearch: "Finite affine source and target charts for a locally finite
  type morphism over affine open subsets of a base scheme": eight hits on
  LocallyOfFiniteType, sourceAffineLocally, finiteType_appLE, and IsAffineHom;
  none states all clauses of this node.
- Direct rg in both lean/WeilConjectures and lean/Sheaf searched the node id,
  finite-relative-affine naming, relative atlas naming and finite affine covers.
  No matching statement; the larger UnramifiedLimitDescent theorem mentions
  these charts in its proof docstring but does not state their existence.
  RelativeFiniteAffinePresentation defines selected finite-presentation data
  over a base and does not state this locally-finite-type nested-atlas theorem.
- Direct rg of Mathlib and both project trees checked the proposed declaration
  name `exists_finite_relative_affine_atlas`: no collision. The signatures and
  docstrings of Scheme, Spec, Spec.map, LocallyOfFiniteType, QuasiCompact,
  Scheme.Hom.appLE, IsAffineOpen.isoSpec/fromSpec, and the relevant proof
  matches were read in their actual source modules.

No STATEMENT-DISPUTED issue remains. The theorem docstring contains all four
accepted proof steps and their existing dependency-node names.

Validation: the prescribed scompile.py compiled the sandbox and library module
cleanly (4.8 s and 5.0 s); no errors or non-sorry warnings were reported.

## Second reading by Q22

A separate agent was expressly prohibited by this dispatch. This is an honest
second pass by the same worker; independent delivery review remains with the
maintainer. I reopened the node statement and the complete Lean signature and
checked each clause against the correspondence above. In particular, the base
triangle is a hypothesis, not assumed through hidden Over instances; both
source and target covers are finite; the source cover equals the full inverse
image; all three chart families are affine; and both finite generation and
the R-algebra compatibility are present. The spectrum equation names the
canonical chart immersions and actual g. It is an equality of the correct
scheme maps and not merely an existence of some isomorphism. There is no
hidden separatedness hypothesis and no nonempty-index assumption. I also
checked that hXW is the inclusion forced by the original triangle, rather
than an independent stronger condition. No signature changes were needed.

## Worker report

The module `Sheaf.AlgebraicGeometry.CompactGenericsFlatOpen` states
`AlgebraicGeometry.exists_compact_dense_open_flat_of_compact_genericPoints`.
Its only postponed proof is this named theorem, with the complete five-step DAG proof
in the declaration docstring. The natural-language node is unchanged; only its `lean`
record is added. No new nodes, dependency repairs, or disputed statements are needed.

Source checked: [Rydh, Submersions and effective descent of étale morphisms](https://davidrydh.se/papers/submersion20100305.pdf),
Notation (3.1) and Lemma (3.5), printed page 12. The lemma assumes a reduced qcqs
base with quasi-compact generic-point subspace and a finitely presented morphism.
Its proof explicitly chooses an open quasi-compact neighbourhood containing all generic
points. Thus the containment clause in this DAG node is justified by the source proof.

Clause-by-clause translation:

- Schemes C and Z and their morphism: `{C Z : Scheme.{u}}` and `(h : Z ⟶ C)`.
  The universe `u` is declared explicitly and arbitrary, with auto-implicit variables disabled.
- Reduced base: `[IsReduced C]`, using Mathlib's sectionwise reducedness, equivalent to
  reducedness of all local rings as specified by def-pc-reduced-scheme.
- Quasi-compact base: `[CompactSpace C]`; Mathlib compactness does not require Hausdorffness.
- Quasi-separated base: `[QuasiSeparatedSpace C]`, the topological quasi-separatedness
  equivalent to quasi-separatedness of the structure morphism, as fixed by the conventions.
- The set of generic points of irreducible components is exactly Mathlib's `genericPoints C`,
  defined by `closure {x} ∈ irreducibleComponents C`. Its coerced subtype has the induced
  Zariski topology. `[CompactSpace (genericPoints C)]` is precisely the assumed
  quasi-compactness of this subspace; no discreteness or finiteness is assumed.
- Finite presentation of h: the three hypotheses `[LocallyOfFinitePresentation h]`,
  `[QuasiCompact h]`, `[QuasiSeparated h]`. None of these finiteness clauses is omitted.
- Existence of an open subscheme: `∃ U : C.Opens`; its canonical scheme is `U.toScheme`.
- Quasi-compactness of the chosen open: `IsCompact (U : Set C)`, equivalently compactness
  of the corresponding open subspace.
- Containment of all component generic points: `genericPoints C ⊆ (U : Set C)`.
- Density in C: `Dense (U : Set C)`.
- Flatness of the canonical restricted map: `Flat (h ∣_ U)`. Mathlib's global notation
  expands to `morphismRestrict h U : (h ⁻¹ᵁ U).toScheme ⟶ U.toScheme`; its definition uses
  the canonical pullback identification, not an arbitrary morphism or an extra assumption.
- No Noetherianity or irreducibility hypothesis is present. Neither scheme nor open
  is required to be nonempty. There is no additional hypothesis on the source Z.

Statement dependency declarations read and used:

- def-pc-scheme: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom`, including the locally affine condition and LRS morphisms.
- def-pc-reduced-scheme: `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsReduced`;
  its `component_reduced` field and stalk equivalence were read.
- def-weil-pbc-scheme-conventions: its record is explicitly a convention, without a module
  or single declaration. The statement uses its prescribed `CompactSpace`,
  `QuasiSeparatedSpace`, `QuasiCompact`, `QuasiSeparated` and locally finite presentation.
  Read `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`, including the diagonal definition
  and `quasiSeparatedSpace_iff_quasiSeparated`.
- def-sbc-locally-finite-presentation: `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation`, the recorded affine-local condition.
- def-weil-flat-morphism: `Mathlib.AlgebraicGeometry.Morphisms.Flat`, `AlgebraicGeometry.Flat`
  and `AlgebraicGeometry.Flat.iff_flat_stalkMap`, giving exactly flatness on local rings.
- def-weil-irreducible-components: its Mathlib match `irreducibleComponents` in
  `Mathlib.Topology.Irreducible`, maximal nonempty irreducible subsets. No Lean repair is
  needed for this Mathlib leaf. `Mathlib.Topology.Sober` supplies `genericPoints` on exactly
  those components and the induced subtype topology; no private definition is introduced.

Proof dependency imports preserve the stage-3 plan. The two recorded project modules are
`WeilConjectures.AlgebraicGeometry.SpecStalkLimitAffineNeighbourhoods`
(`AlgebraicGeometry.Scheme.fromSpecStalk_limit_affine_neighbourhoods`) and
`WeilConjectures.AlgebraicGeometry.DescendFlatFinitePresentation`
(`AlgebraicGeometry.exists_flat_stage_of_limit`). Their source signatures and docstrings
were read, including qcqs stage hypotheses and the directed-index universe.
Other proof inputs use their recorded Mathlib matches, imported by
`Mathlib.AlgebraicGeometry.AffineScheme`, `Mathlib.AlgebraicGeometry.OpenImmersion`,
`Mathlib.RingTheory.Spectrum.Prime.Topology`, `Mathlib.RingTheory.KrullDimension.Zero`,
and the public statement imports: affine basis/stalk localization, components/minimal primes,
minimal-prime localization fields, qcqs permanence, flatness over a field, affine qcqs,
components covering, and scheme sobriety. Proof imports are plain imports.

Edge cases checked before writing:

- Empty C: its generic-point subspace is empty and compact. Choose the empty open;
  it is compact and dense in the empty space. The restriction has empty source and is flat.
- Empty generic-point set: sobriety and the covering by irreducible components imply
  that C is empty, so the same choice works.
- Empty Z over nonempty C: flatness is vacuous, and the whole C is an eligible open.
- A field spectrum: the generic-point set is the single point; the whole base works,
  and every scheme mapping to it is flat.
- Reducible bases and infinitely many components remain admitted whenever the generic
  subspace is compact. No finite set of components or single generic point is substituted.
- The finite union in the proof can be empty and is not asserted affine. U is only open
  and quasi-compact, exactly as stated. Reducedness is retained; the field-stalk argument
  would fail for a nonreduced generic local ring.

Searches actually run:

- `msearch.py ... leanfinder`: “A finitely presented morphism over a reduced quasi compact
  quasi separated scheme with compact set of generic points is flat over a quasi compact
  dense open containing all generic points”. Eight hits: Flat, its generalizing-map,
  stalkwise and open-immersion properties, UniversallyOpen.of_flat,
  LocallyOfFinitePresentation, and descent interfaces. None states this existence theorem.
- `msearch.py ... loogle`: `"Flat", "LocallyOfFinitePresentation"`. Four hits concerning
  faithful pullback, fppf/fpqc descent and effective epimorphisms; no flat-open existence.
- `msearch.py ... grep`: `generic.flat|genericFlat|flat.*locus|flatLocus` in
  `AlgebraicGeometry`. No Mathlib hits.
- `rg` in Mathlib AlgebraicGeometry and Topology, live `lean/WeilConjectures` and
  `lean/Sheaf`: searched genericPoints, generic/flat, compact generic points, and
  flat-open existence names. Found the exact notion `genericPoints` and related
  integral-base generic-flatness results, but no matching theorem. In particular,
  `WeilConjectures.AlgebraicGeometry.GenericFlatFinitePresentation` requires an integral
  base and asserts a nonempty open; its full declaration was read and is not this statement.
  The existing `Sheaf.AlgebraicGeometry.AffineIntegralCompactGenericsCover` also uses
  `CompactSpace (genericPoints C)`, consistently with this statement's topology.
- `rg` by the exact node id in `lean/WeilConjectures`: no declaration found.
- Searched the proposed declaration name in the project, Mathlib-relevant searches and
  `dag/lean_names_upstream.json`: no duplicate found.

Validation: all compilation is through the prescribed `scompile.py`; delivery preflight
and its separate per-file compilation are through `deliver2.py`.

## Second reading by NF

Independent second reading by the maintainer reviewer (the delivered section stated that no
second reading was made). Read the node, its source place, the six stmt_dep records, the
module `Sheaf.AlgebraicGeometry.CompactGenericsFlatOpen` and the Mathlib declarations used.

Node statement as a list, with the Lean that renders it and the verdict:

1. Scheme C (def-pc-scheme): `{C : Scheme.{u}}`. Correct.
2. C reduced (def-pc-reduced-scheme, record `AlgebraicGeometry.IsReduced`): `[IsReduced C]`.
   Correct; the stalk form follows from `isReduced_stalk_of_isReduced`.
3. C quasi-compact (conventions): `[CompactSpace C]`. Correct.
4. C quasi-separated (conventions): `[QuasiSeparatedSpace C]`, which is equivalent to
   quasi-separatedness of `C ⟶ Spec ℤ` by `quasiSeparatedSpace_iff_quasiSeparated`. Correct.
5. C_gen = generic points of the irreducible components (def-weil-irreducible-components),
   subspace topology, quasi-compact: `[CompactSpace (genericPoints C)]`. Mathlib
   `genericPoints C = {x | closure {x} ∈ irreducibleComponents C}` (Topology/Sober.lean:277),
   with the induced subtype topology. Exact.
6. h : Z → C of finite presentation (def-sbc-locally-finite-presentation, Stacks 01TP):
   `(h : Z ⟶ C) [LocallyOfFinitePresentation h] [QuasiCompact h] [QuasiSeparated h]`.
   All three clauses present, nothing stronger.
7. ∃ quasi-compact open subscheme U ⊆ C: `∃ U : C.Opens, IsCompact (U : Set C)`. Correct.
8. U ⊇ C_gen: `genericPoints C ⊆ (U : Set C)`. Correct.
9. U dense in C: `Dense (U : Set C)`. Correct.
10. h⁻¹(U) → U flat (def-weil-flat-morphism, record `AlgebraicGeometry.Flat`):
    `Flat (h ∣_ U)`, Mathlib `morphismRestrict`, the canonical restriction. Correct.
11. No Noetherian or irreducibility assumption: none present; no assumption on Z. Correct.

Universes: one explicit universe `u`; `Z ⟶ C` forces Z and C into the same universe, as for
any morphism of schemes. autoImplicit is off; no unbound variable.

Source: Rydh, Lemma (3.5), printed p.12: reduced qcqs base with quasi-compact generic
subspace, finitely presented morphism, flat over a quasi-compact dense open; its proof
chooses an open containing all generic points, which justifies clause 8.

Edge cases: empty C (genericPoints empty and compact, U = ⊥ is compact, dense in the empty
space, restriction flat); C nonempty forces C_gen nonempty (sober, components cover), so the
empty U only occurs for empty C; empty Z (flatness vacuous); infinitely many components with
compact C_gen are admitted. The statement is not weaker or stronger than the node.

Searches (other words than the worker's): `rg` of `genericPoints` and `Flat (. ∣_` in Mathlib
AlgebraicGeometry/RingTheory, in the side-live `lean/Sheaf` and `lean/WeilConjectures`:
only Mathlib's `Flat (f ∣_ V)` instance for flat f, and the integral-base results
`exists_nonempty_open_flat_restrict` (GenericFlatness.lean) and GenericFlatFinitePresentation,
which assert a nonempty open over an integral base — not this statement. No duplicate of the
declaration name or the node id.

Gates: one postponed theorem with `sorry`; module and declaration docstrings carry the
source place and `(blueprint: lem-sfb-compact-generics-flat-open)`; the declaration
docstring carries the node's five proof steps. `lean.statement` is verbatim the signature
in the file. Only the item's `lean` record changed; no dependency record changed.

Mismatches found: none in the Lean or the records. Changed: this section only.

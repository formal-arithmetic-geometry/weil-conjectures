## Worker report

The node is already stated exactly by the sorry-free upstream declaration
`AlgebraicGeometry.IsAdmissible` in
`WeilConjectures.Blowup.AdmissibleBlowup` (lines 133--143), so no duplicate
module is written.  The declaration is a structure whose parameters are a
scheme `X` and an open `U : X.Opens`; its fields are a quasi-coherent ideal
sheaf `I : X.IdealSheafData`, finite-typeness `I.ofFiniteType`, and
`Disjoint (U : Set X) (I.support : Set X)`.  The same module supplies
`I.blowup` and `I.blowupMap`, the canonical blow-up and its map to `X`, and
`disjoint_support_iff_comap_ι_eq_top` records the stated equivalent
restriction-to-the-unit-ideal formulation.  Thus the node's hypotheses and
both clauses (the admissible blow-up and its center disjoint from `U`) are
rendered by the existing structure and its canonical blow-up data.

The node has no `stmt_deps`, so no dependency declarations are used.  The
exact existing declaration signature printed by `scompile.py` is
`structure AlgebraicGeometry.IsAdmissible.{u} (X : AlgebraicGeometry.Scheme)
(U : X.Opens) : Type u`; the source declaration itself is written verbatim as
`structure IsAdmissible where`, which is recorded in the node's `lean.statement`.

Edge cases checked against the structure and source definitions: `U = ⊤`
forces the ideal support to be empty; `U = ⊥` imposes no disjointness beyond the
empty open; the zero ideal has full support and is admissible only for empty
`U`; the unit ideal has empty support and is admissible for every `U`; and
nonreduced or disconnected schemes require no extra hypotheses.

Searches made:

- `msearch.py ... grep 'IsAdmissible|admissible' WeilConjectures/Blowup`: 25
  hits, including the defining module.
- `msearch.py ... leanfinder 'U-admissible blow-up ideal sheaf blowup scheme'`:
  8 Mathlib hits, none matching the notion.
- `msearch.py ... leanfinder 'finite type quasi coherent ideal support disjoint open U admissible blowup'`:
  8 Mathlib hits, none matching the notion.
- `msearch.py ... loogle 'IsAdmissible, blowup, IdealSheafData'`: no match
  (unknown identifier in the Mathlib search environment).
- `rg`/`grep` over the project and DAG found this existing upstream attachment
  and no separate project declaration defining the same notion.

The upstream declaration was compiled with `scompile.py`; it printed the
structure signature and fields without errors or warnings.  No new nodes and
no dependency modules are needed.

## Second reading by Q77

I reread the target statement and the upstream source declaration.  `X` and
`U` are the same scheme/open objects; finite type is the `finiteType` field;
`I|_U = O_U` is represented by the source's equivalent support-disjointness
field; and the associated blow-up map is the canonical `I.blowupMap`.  No
hypothesis or conclusion is added or removed, and the existing declaration is
sorry-free according to the source audit.

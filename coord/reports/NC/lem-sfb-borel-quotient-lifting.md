## Worker report

Stage 2 statement of `lem-sfb-borel-quotient-lifting`, group NC. The live node has
no Lean record; NV's accepted work is a stage-1 split, preserved here. There is no
released repair note. The sandbox initially contained only dispatcher brief markers.
The item changes only `lean` and adds `def-sfb-borel-subgroup-scheme` to `stmt_deps`.
No mathematical statement or accepted proof split is changed.

`Sheaf.AlgebraicGeometry.GroupScheme.BorelQuotientLifting` states
`AlgebraicGeometry.exists_borelGroupScheme_lift`; its only proof is `sorry`.
The definition module contains real Prop-valued data and no postponed theorem.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Algebraically closed field F | `{F : Type u} [Field F] [IsAlgClosed F]` |
| F-group schemes G and H | `G H : Over (Spec (.of F))`, with `[GrpObj G] [GrpObj H]` |
| Affine | `[IsAffine G.left] [IsAffine H.left]` |
| Finite type over F | `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`, and the same for H |
| Smooth and connected | `[Smooth G.hom] [ConnectedSpace G.left]`, and the same for H |
| Homomorphism q | `(q : G ⟶ H) [IsMonHom q]` |
| F[H] to F[G] faithfully flat | `(hq : q.left.appTop.hom.FaithfullyFlat)` |
| Every Borel C in H | `(C : Over (Spec (.of F))) [GrpObj C] (iC : C ⟶ H) (hC : IsBorelGroupScheme iC)` |
| There is a Borel B in G | `∃ B, ∃ (_ : GrpObj B), ∃ iB, IsBorelGroupScheme iB ∧ ...` |
| q restricted to B lands in C | `∃ r : B ⟶ C, IsMonHom r ∧ iB ≫ q = r ≫ iC ∧ ...` |
| Restricted map faithfully flat | `r.left.appTop.hom.FaithfullyFlat` |
| Locally of finite presentation | `LocallyOfFinitePresentation r.left` |
| Quasi-compact | `QuasiCompact r.left` |
| Quasi-separated | `QuasiSeparated r.left` |
| No kernel restriction | No kernel hypothesis or kernel binder |

`IsBorelGroupScheme i` unfolds to `IsClosedSubgroupScheme i`, `Smooth B.hom`,
`ConnectedSpace B.left`, `IsSolvableGroupScheme B`, and maximality. If another
closed smooth connected solvable subgroup `j : D ⟶ G` contains B (there is
`f : B ⟶ D` with `f ≫ j = i`), maximality supplies `r : D ⟶ B` with
`r ≫ i = j`. These two factorizations express equality of closed subgroup
subobjects. Because the inclusions are monomorphisms, the two factor maps are
inverse and respect the induced group laws. This does not choose a representative
of a quotient or use rational points in place of subgroup schemes.

All subgroup schemes in the item are affine and of finite type: closedness in
the affine finite-type ambient group implies both. Thus the theorem does not
need to assume these properties a second time for C, or add extra output
conditions for B. Its Borel predicate retains all subgroup scheme structure.

Dependencies read and reused:

- `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.FieldTheory.IsAlgClosed.Basic`:
  `IsAlgClosed` (the algebraically closed clause of def-weil-algebraic-closure).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`; the monoid
  homomorphism predicate is `CategoryTheory.IsMonHom` from Monoidal.Mon.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `AlgebraicGeometry.IsSubgroupScheme`, `IsClosedSubgroupScheme` (extends the
  subgroup/homomorphism predicate and asserts a closed immersion on `.left`).
  Its full signatures and group-scheme conventions were read.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`;
  `Mathlib.Topology.Connected.Basic`: `ConnectedSpace` (includes nonemptiness).
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`; `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`:
  `QuasiSeparated`.
- `Sheaf.AlgebraicGeometry.GroupScheme.Semisimple` (node
  `def-sfb-semisimple-group-scheme`): `groupSchemeCommutator`,
  `IsDerivedGroupScheme`, `GroupSchemeDerivedLength`, `IsSolvableGroupScheme`.
  The last is the reused notion: finite length of the scheme-theoretic derived
  series, with the derived subgroup characterized as the smallest closed
  subgroup containing the commutator morphism. No second solvability definition.
- `Mathlib.RingTheory.RingHom.FaithfullyFlat`: `RingHom.FaithfullyFlat`, defined
  by `Module.FaithfullyFlat` for the algebra structure induced by the ring map.
  This is flatness plus faithfulness of tensoring, hence exact extension of
  scalars detecting zero modules, as required by the node.
- The stated proof dependencies `def-weil-closed-immersion` and
  `def-weil-proper-morphism` use `IsClosedImmersion` and `IsSeparated`/`IsProper`
  from Morphisms.ClosedImmersion and Morphisms.Proper, imported plainly.
  `lem-sfb-quotient-borel-torus-images` and
  `lem-sfb-algebraic-group-homomorphism-factorization` currently have no Lean
  record or Mathlib match; there is therefore no module to import for them.
  They are proof dependencies only; their natural-language steps are included
  in the theorem docstring, and their statements were read.

Sources checked locally with pdftotext on
`literature/milne-algebraic-groups_iAG2017.pdf`: Definition 17.6 (p.353),
Proposition 17.20 and its conjugacy argument (pp.357–358), and Theorem 5.39 /
Remark 5.40 (p.108). The current blueprint was searched through
`literature/blueprint/latest/blueprint`; this auxiliary is not itself a unit
statement. The existing null blueprint ancestor and via chain are preserved
for the new definition, as `tools/blueprint_refs.py ancestor` reports.

Edge cases checked mathematically before writing:

- Trivial groups and the quotient G to 1: the unique target Borel is trivial;
  maximality is meaningful and the conclusion gives an ordinary Borel of G.
- Identity quotient: use the prescribed C itself. The triangle permits this
  and does not require a nontrivial map or a proper subgroup.
- Frobenius on G_m in characteristic p: the kernel is nonreduced mu_p, and
  the map is faithfully flat and finitely presented. No separability or smooth
  kernel is assumed. Likewise SL_2 to PGL_2 is allowed in every characteristic.
- Projection G_m times G_a to G_m: the positive-dimensional kernel is allowed.
- The empty scheme is excluded by the stated ConnectedSpace hypothesis, in
  agreement with the definition node; the trivial group is not excluded.
- Solvability is scheme-theoretic, so nonreduced tests are not silently replaced
  by an assertion just about F-points. Every universe and variable is explicit;
  the field and schemes share the usual scheme universe u, with no independent
  smaller test-algebra universe.

Searches (all through the prescribed wrappers or read-only rg):

- LeanFinder: "Borel subgroups lift along faithfully flat quotients of smooth
  connected affine group schemes over an algebraically closed field". Eight
  hits: a Galois-category lifting lemma, formally smooth algebra lemmas, smooth
  flatness lemmas, and affine flat/surjective criteria. None states this item.
- LeanSearch: "Borel subgroup scheme maximal smooth connected solvable closed
  subgroup". Eight hits on topological ClosedSubgroup, abstract IsSolvable,
  IsSmooth.casesOn and measurable Borel structures; no Borel group scheme.
- Loogle: `"BorelSubgroup"` and `"IsBorelGroupScheme"`: zero hits each.
- Mathlib grep: `IsBorel|BorelSubgroup|borel.*quotient`: four hits, all measurable
  Borel quotients. `BorelSubgroup|IsBorelGroupScheme|IsBorel` restricted to
  AlgebraicGeometry: zero hits.
- rg of lean/WeilConjectures and lean/Sheaf for Borel subgroup definitions:
  no match. rg for the item id in WeilConjectures: no match. Derived-subgroup
  search located the existing Semisimple module, which is reused.
- DAG search found many statements using Borel groups but no Borel definition
  node. `tools/blueprint_refs.py search 'Borel subgroup'`: zero blueprint nodes.
  New declaration names were also searched in dag/lean_names_upstream.json.

No STATEMENT-DISPUTED claim or statement correction is needed. Initial server
compilation of both modules succeeded cleanly; only the theorem is postponed.

## New nodes

`def-sfb-borel-subgroup-scheme` introduces only the missing Borel predicate in
`Sheaf.AlgebraicGeometry.GroupScheme.Borel`, declaration
`AlgebraicGeometry.IsBorelGroupScheme`. Its source is Milne Definition 17.6,
with scheme-theoretic solvability from the existing
`def-sfb-semisimple-group-scheme` / Milne Proposition 6.30. The definition
works for group schemes generally and specializes to the affine finite-type
setting required here. The LeanSearch, Loogle and grep searches above found
no existing predicate; the DAG and blueprint searches found no owning node.
There are no additional theorem obligations or choices in this definition.

## Second reading by NC

This is a second pass by the same dispatched worker, not a claimed independent
agent review: this brief explicitly prohibits starting other agents. The
maintainer supplies the independent review of this delivery.

Reopened the item node, new definition node and both modules. Checked every
row of the correspondence table against the actual binders and conjunctions.
The inclusion triangle was checked in composition order: `iB ≫ q` and
`r ≫ iC` are both B to H. `appTop` reverses direction, giving F[C] to F[B]
in the conclusion and F[H] to F[G] in the hypothesis. The finite-presentation
conclusion has all three clauses. Borel maximality quantifies over all larger
smooth connected solvable closed subgroups, without normality, torus, or
kernel restrictions. Compared the solvability definition to the existing
Semisimple source in full. No semantic mismatch found. Added the explicit
plain ClosedImmersion import to cover the stated proof dependency.

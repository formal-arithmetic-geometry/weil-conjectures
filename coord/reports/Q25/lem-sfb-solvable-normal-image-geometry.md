## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.SolvableNormalImageGeometry` states
`AlgebraicGeometry.solvableNormalImage_geometry`, with one `sorry` and no definitions
or proved theorems. Its docstring carries all seven accepted proof steps and their
DAG citations. The natural-language statement and accepted split are unchanged.
Only `lean` and the addition of the already landed definition node
`def-sfb-semisimple-group-scheme` to `stmt_deps` change in the item.

Hypotheses and clauses, checked against the node and the source:

- Algebraically closed field F: `{F : Type u} [Field F] [IsAlgClosed F]`.
- F-group schemes G,H,N,I: `Over (Spec (.of F))`, with an explicit `GrpObj` instance
  for each. These are the dependency's group objects, not point groups or Hopf-algebra
  stand-ins. Their structure morphisms and all morphisms are over the specified field.
- G and H affine: `[IsAffine G.left] [IsAffine H.left]`.
- G and H finite type: `LocallyOfFiniteType` and `QuasiCompact` on each structure
  morphism, precisely the two conditions in the finite-type dependency record.
- f a homomorphism: `(f : G ⟶ H) [IsMonHom f]`.
- Faithful flatness of f: `hf` is `Module.FaithfullyFlat` from `Γ(H.left, ⊤)` to
  `Γ(G.left, ⊤)`, with module structure explicitly induced by the ring homomorphism
  `f.left.appTop.hom.toAlgebra.toModule`. No unrelated module action is implicit.
- N a normal closed subgroup: `(i : N ⟶ G) [IsClosedSubgroupScheme i]` and
  `[IsNormalSubgroupScheme i]`, using the recorded upstream notions. The former
  includes the homomorphism and closed immersion. N is consequently affine and of
  finite type, as a closed subscheme of the given affine finite-type G; those are
  consequences and are not extra binders.
- N smooth and connected: `[Smooth N.hom] [ConnectedSpace N.left]`.
- N solvable in the node's exact derived-series sense: `hN : IsSolvableGroupScheme N`.
  The existing definition unfolds to existence of a natural-number derived length;
  its successors use the smallest closed commutator subgroup and its zero case is
  terminality over F. This preserves nonreduced scheme structure and is not merely
  solvability of rational points. The landed definition is reused, not copied.
- I affine finite type: its explicit `IsAffine`, `LocallyOfFiniteType`, and
  `QuasiCompact` instances.
- q a faithfully flat homomorphism N to I: `(q : N ⟶ I) [IsMonHom q]` and `hq`
  expressed with `Γ(I.left, ⊤)`, `Γ(N.left, ⊤)` and the module action from q's pullback.
- j a closed immersion: `(j : I ⟶ H) [IsClosedImmersion j.left]`. There is deliberately
  no `IsMonHom j` hypothesis: the node does not assume it; step 1 derives it.
- The restriction factorization is `hfactor : i ≫ f = q ≫ j`.
- I smooth, connected, solvable: the first three conjuncts are `Smooth I.hom`,
  `ConnectedSpace I.left`, and `IsSolvableGroupScheme I`.
- j identifies I with a normal closed subgroup: the fourth conjunct is
  `IsNormalSubgroupScheme j`, which includes its subgroup and homomorphism properties.
  Its closed immersion is already a given hypothesis, so it need not be repeated as
  a tautological conjunct. Normality quantifies over every F-algebra as in the dependency.
- The final sentence adds no kernel hypotheses; the signature has none.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (lines 170--180); and
  `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed` (lines 59--63), the
  algebraically-closed clause of `def-weil-algebraic-closure`'s Mathlib record.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj` (lines 40--47);
  the group-scheme specialization and `IsMonHom` convention are explicitly documented
  in `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` (module docstring).
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`: `IsSubgroupScheme`,
  `IsNormalSubgroupScheme`, `IsClosedSubgroupScheme`, including their full signatures
  and docstrings (lines 71--101). Normality is on all small algebra-valued points.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType` (lines 39--47)
  and `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact` (lines 38--46).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth` (lines 59--66), the node's
  recorded notion; its node records the equivalence with the infinitesimal definition.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace` (lines 697--708), including
  nonemptiness; `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `IsClosedImmersion` (lines 42--46).
- Added landed statement dependency `def-sfb-semisimple-group-scheme`:
  `Sheaf.AlgebraicGeometry.GroupScheme.Semisimple`, declarations `groupSchemeCommutator`,
  `IsDerivedGroupScheme`, `GroupSchemeDerivedLength`, `IsSolvableGroupScheme`.
  Read the whole module and the node; these exactly supply the inline notion of
  solvability in this item. No new definition node or dependency repair is needed.
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`: `Module.FaithfullyFlat` (line 63)
  with the explicitly specified coordinate-ring module structures.

Proof dependency imports are plain imports. Read the recorded statement and source of
`Module.FaithfullyFlat.tensorProduct_mk_injective`,
`PrimeSpectrum.comap_surjective_of_faithfullyFlat` (both in
`Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`), `AlgebraicGeometry.Spec`,
`AlgebraicGeometry.pullbackSpecIso` and its projections, `Algebra.TensorProduct.productMap`
and `ext`, `AlgebraicGeometry.Smooth.geometricallyReduced` in
`WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced`,
`AlgebraicGeometry.IsReduced`, `AlgebraicGeometry.smooth_of_grpObj`,
`AlgebraicGeometry.exists_smooth_connected_derived_subgroup` in
`Sheaf.AlgebraicGeometry.GroupScheme.SmoothConnectedDerivedSubgroup`, and
`AlgebraicGeometry.affineGroupHom_exists_faithfullyFlat_closedImmersion` in
`Sheaf.AlgebraicGeometry.GroupScheme.AffineHomomorphismFlatImage`.
Their imports expose the accepted proof plan for stage 3. None needs an interface repair.

Source reading: opened the local Milne Algebraic Groups (2017) PDF through its
`pdftotext -layout` text, Theorem 5.39 and Remarks 5.40--5.42 (printed p.108),
Proposition 1.62(b) and its following nonsmooth-kernel example (p.24),
Propositions 6.27 and 6.30 (pp.131--132), and Lemma 19.14's proof (p.400).
Smooth quotient, solvable quotient and normality under a surjective ambient map
agree with the node. No source correction or disputed statement was found.

Edge cases checked mathematically before writing: N trivial and derived length zero;
f or q an isomorphism; positive-characteristic Frobenius on G_a or G_m, whose
kernel can be nonreduced (the G_m case is Milne's explicit example). These are
included. Empty group schemes over a field cannot carry an identity section;
`ConnectedSpace` retains the dependency's nonempty convention. No assumption of
perfectness, characteristic zero, or smooth/finite kernel was introduced. Schemes
and test algebras use the standard common universe u, which can be enlarged; no
independent smaller test universe makes a condition vacuous.

Actual duplicate searches run with `msearch.py Q25 lem-sfb-solvable-normal-image-geometry`:

- LeanSearch: `Image of a smooth connected solvable normal closed subgroup scheme under
  faithfully flat homomorphism is smooth connected solvable normal`. Eight results:
  abstract-group `solvable_of_surjective`, `Subgroup.Normal.map`, and general smoothness
  results, but no theorem with this scheme-theoretic statement.
- LeanFinder: `solvable affine group scheme derived series smallest closed subgroup
  commutator`. Eight results about abstract-group or Lie-algebra solvability, no match.
- Loogle: `IsSolvable, IsNormalSubgroupScheme`. Zero results, with unknown identifier
  `IsNormalSubgroupScheme`; that name is project-specific, and its actual source was read.
- Mathlib grep: `IsSolvable|IsDerivedGroupScheme|solvable.*image`, restricted to
  `AlgebraicGeometry`: zero hits.
- Local `rg` in `lean/WeilConjectures`: `Solvable|solvable|IsDerivedGroupScheme` finds
  Lie-algebra material and no group-scheme image theorem. Search by the item's id in
  that tree gives no hit. `solvable.*normal.*image|normal.*image.*solvable` in both
  project Lean trees gives no exact statement. `rg` in `lean/Sheaf` by solvability
  and derived-subgroup names finds the reused Semisimple definitions and the distinct
  derived-subgroup and central-isogeny results. Search in `dag/lean_names_upstream.json`
  gives no conflicting declaration for the chosen name. The only exact definition
  needed already belongs to `def-sfb-semisimple-group-scheme`.

Validation: the prescribed `scompile.py` compiled this module individually both in
sandbox and its library module path, in 1.6 seconds each, without errors or warnings.
All variables and the universe are explicitly bound; `autoImplicit` is disabled.
The only postponed proof is the named theorem matching this DAG node.

## Second reading by Q25

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

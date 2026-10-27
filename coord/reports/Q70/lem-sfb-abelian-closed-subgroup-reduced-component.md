## Worker report

The module `Sheaf.AlgebraicGeometry.AbelianVariety.ClosedSubgroupReducedComponent` states
`AlgebraicGeometry.closedSubgroup_reduced_identityComponent`, with one `sorry` and no
new definitions. Only the item's `lean` record is changed. No statement correction,
new node, or dependency repair is needed.

Clause-by-clause correspondence:

- The algebraically closed field is `(k : Type u) [Field k] [IsAlgClosed k]`.
- The abelian variety is `A : Over (Spec (.of k))`, with `[GrpObj A]` and
  `[IsAbelianVariety A]`. The latter is exactly proper, smooth and connected.
- The closed subgroup is `H : Over (Spec (.of k))`, `[GrpObj H]`,
  `(i : H ⟶ A) [IsClosedSubgroupScheme i]`. The existing class contains the
  homomorphism, injectivity on algebra points, and closed-immersion requirements.
- `H_red` is the existing `GrpObj.reduced H`, definitionally the nilradical
  subscheme of `H.left`, with its composite structure morphism to `Spec k`.
  `∃ gR : GrpObj (GrpObj.reduced H), IsClosedSubgroupScheme (GrpObj.reducedι H) ∧ ...`
  asserts the induced group structure and the reduced-subgroup clause as conclusions.
  This is not a new assumption on the input subgroup.
- `∃ U : (GrpObj.reduced H).left.Opens` with `(U : Set ...) =
  connectedComponent (GrpObj.onePoint (GrpObj.reduced H))` identifies precisely
  the component containing the identity with its open subscheme structure.
  `U.toScheme` is B; its structure morphism is `U.ι ≫ (GrpObj.reduced H).hom`.
  The group structure `gB` is existentially concluded on `Over.mk` of that morphism.
- `IsAbelianVariety (Over.mk (U.ι ≫ (GrpObj.reduced H).hom))` states that B
  is proper, smooth and connected; `gB` supplies its group structure.
- The `IsClosedSubgroupScheme` conjunct is on the actual composite
  `Over.homMk U.ι ≫ GrpObj.reducedι H ≫ i`. Thus the embedding is the canonical
  inclusion B → H_red → H → A, over k, with its scheme structure intact.
- `topologicalKrullDim U.toScheme = topologicalKrullDim H.left` is dim B = dim H,
  in `WithBot ℕ∞`, without prematurely replacing dimension by a natural number.
- `topologicalKrullDim U.toScheme = 0 → IsFinite H.hom` is the final implication
  for the original H, including its nilpotents, not just for H_red.

The existential group structures are canonical: requiring the fixed inclusions to
be homomorphisms determines all their operations uniquely, since closed immersions
are monomorphisms. In particular their unit, product and inverse cannot be arbitrary.
The equality of underlying opens also uniquely fixes U and hence its open scheme
structure. This formulation avoids auxiliary finite-type assumptions, local
instances and local abbreviations. There are no `let` or `show` terms in the signature.
All universes and variables are explicitly bound; `autoImplicit` is disabled.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.FieldTheory.IsAlgClosed.Basic`:
  `IsAlgClosed` (the algebraically closed part of def-weil-algebraic-closure).
- `WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`:
  `AlgebraicGeometry.IsAbelianVariety`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `AlgebraicGeometry.IsClosedSubgroupScheme`, `IsSubgroupScheme` and their
  `CategoryTheory.IsMonHom` compatibility. Group structures use `CategoryTheory.GrpObj`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic` and `.Subscheme`:
  `Scheme.nilradical`, `Scheme.IdealSheafData.subscheme`, `subschemeι`.
  The existing wrapper `GrpObj.reduced` and `GrpObj.reducedι` in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Reduced` use exactly these.
  I read its complete construction of restricted group operations and its inclusion.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, `connectedComponent`;
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Basic`: `GrpObj.onePoint`,
  `identityComponent`, `identityComponentOpens` and `identityComponentι` were read.
  The signature uses the open and equality encoding because its finite-type facts
  are conclusions of the input geometry, not additional hypotheses to assume.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- Proof imports include every recorded project/upstream proof-dependency module:
  `GeometricReducedFiniteTypePerfectField.geometricallyReduced_finiteType_of_perfectField`,
  `ProperDimZeroFiniteOverField.proper_dim_zero_finite_over_field`,
  `GroupNeutralComponentTranslates.GrpObj.finiteTypeGroup_neutralComponent_translates`,
  `ClosedImmersionProducts.closedImmersion_comp_products_and_finiteType_openImmersion`,
  the upstream `Dimension.Scheme.dim` and `Scheme.dim_eq_topologicalKrullDim`,
  `ReductionUniversalHomeomorphism.reduction_isReduced_isClosedImmersion_isSurjective_isUniversalHomeomorphism`,
  and the upstream closed-immersion reduced-source factorization. These signatures
  and docstrings were read. Mathlib proof leaves use Proper, Noetherian, Smooth,
  ZariskisMainTheorem, Geometrically.Reduced and Group.Smooth, including
  `smooth_of_grpObj` and reducedness of the flat geometrically reduced pullback.

Edge cases checked before writing:

- A group scheme is nonempty because of its unit. The empty-scheme dimension `⊥`
  convention cannot produce a false zero-dimensional conclusion.
- H = A and the identity subgroup give B = A and B = Spec k respectively.
- A disconnected finite subgroup has identity reduction a point and is finite.
- In characteristic p, infinitesimal subgroups such as μ_p or α_p when embedded
  in an abelian variety have reduced component a point; H remains nonreduced
  and the conclusion is finiteness, not étaleness or reducedness.
- For a positive-dimensional subgroup, including nilpotent thickenings, the
  reduction homeomorphism preserves topological dimension. The final implication
  imposes no conclusion of finiteness unless dim B = 0.
- No characteristic-zero, reducedness, connectedness, smoothness or finite-type
  hypothesis is added on H. Properness of A and its closed embedding imply the
  finite-type and quasi-compact facts needed in the proof.

Searches for an existing full statement:

1. `msearch.py ... leanfinder "The reduced identity component of a closed subgroup
   scheme of an abelian variety is an abelian variety of the same dimension, and
   zero dimension implies finite"`: 8 hits, chiefly `AlgebraicGeometry.IsReduced`,
   elliptic-curve group structures and affine-space facts; no full match.
2. `msearch.py ... loogle '"IsClosedSubgroupScheme", "IsAbelianVariety"'`: 0 hits.
3. `msearch.py ... grep 'reduced.*[Ss]ubgroup|[Ss]ubgroup.*reduced|identityComponent'
   AlgebraicGeometry`: 0 hits in Mathlib.
4. `msearch.py ... leansearch "The reduced connected component of a closed subgroup
   scheme of an abelian variety is an abelian subvariety"`: 8 hits, scheme
   reducedness constructors and restriction facts; no full match.
5. `rg -n` of reduced subgroup, nilradical group and identity-component/abelian
   combinations in both `lean/WeilConjectures` and `lean/Sheaf` found the reusable
   `GroupScheme/Reduced.lean` construction and `GroupScheme/Basic.lean` component
   construction, but no theorem with all four conclusions. General-linear-group
   components concern affine matrix groups and do not give this statement.
   `grep -rn` for the exact node id in `lean/WeilConjectures` found nothing;
   project matches in PolarizationCalculus are proof-docstring citations only.
6. `dag/lean_names_upstream.json`, Mathlib and both project roots have no declaration
   named `closedSubgroup_reduced_identityComponent`.

Sources checked directly: Milne PDF printed pp. 17–18, including Corollary 1.35,
Proposition 1.38, Corollary 1.39 and the dimension discussion; Stacks local
`groupoids.tex` at reduced-subgroup-scheme-perfect and proposition-connected-component.
No mathematical fault or STATEMENT-DISPUTED issue was found.

The assigned CompactObject example is withdrawn in the live checkout. I read its
node, followed its current record to the upstream CompactObject module, and used
that module's header, source-docstring and public-section conventions.

Validation: server `scompile.py` compiled the final statement form in sandbox mode
and its actual library-module path with no errors or warnings. Earlier probes
exposed instance synthesis through `Over.mk`; the delivered form concludes the
necessary group structures instead of adding assumptions. All probe commands and
probe files have been removed. The only postponed proof is the item's named theorem;
its docstring carries all seven DAG proof steps and their cited nodes.

## Second reading by Q70

Self-review, not an independent agent review: the dispatcher expressly forbids
starting agents; the maintainer supplies the independent review. I reread the node
and final signature together. The subgroup input uses the exact existing class;
the reduced scheme is the nilradical construction; its group structure is concluded;
the open is exactly the connected component of its induced identity; the abelian
structure and actual composite closed inclusion are concluded; dimensions use the
recorded topological definition on B and H; finiteness is for H.hom. No hypothesis
on characteristic or on H's reducedness is present. I removed an unnecessary
additional conjunct about the intermediate inclusion B → H_red: the delivered
conjunct is precisely the required closed subgroup embedding in A. No node statement
or dependency record changed.

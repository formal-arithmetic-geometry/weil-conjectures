## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.FieldSplitTorusFlatQuotient` states
`AlgebraicGeometry.exists_iso_splitTorus_of_faithfullyFlat`. The sole theorem has
proof `sorry`; no definitions or subsidiary theorems are introduced.

Hypothesis and conclusion correspondence:

- Any field k: `{k : Type u} [Field k]`; there is no infinitude, perfection,
  algebraic-closedness, or characteristic hypothesis.
- T and Q are k-group schemes: `T Q : Grp (Over (Spec (.of k)))`. Bundled group
  objects carry multiplication, identity and inverse with their group diagrams.
- T is split of some finite rank, including zero:
  `hT : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus k r)`.
  This is an isomorphism of group objects over Spec k, not only of schemes.
- Q is affine: `[IsAffine Q.X.left]`.
- Q has finite-type structure map: `[LocallyOfFiniteType Q.X.hom]` together with
  `[QuasiCompact Q.X.hom]`, exactly the recorded finite-type convention.
- q is a homomorphism: `q : T ⟶ Q` in the category of bundled group objects.
- The coordinate map makes k[T] faithfully flat over k[Q]:
  `hq : q.hom.hom.left.appTop.hom.FaithfullyFlat`. `appTop` is the pullback of
  global sections, in the required direction k[Q] -> k[T]. Mathlib's ring-map
  predicate installs the module structure through precisely that ring map.
- Conclusion: `∃ t : ℕ, Nonempty (Q ≅ MultiplicativeType.splitTorus k t)`.
  This supplies the required nonnegative rank and group-scheme isomorphism over k.
- No kernel predicate occurs: in particular neither smoothness, reducedness nor
  finiteness of the kernel is imposed. Both rank quantifiers include zero.

Dependency declarations read and used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj` and its bundled category
  `CategoryTheory.Grp`, Mathlib.CategoryTheory.Monoidal.Grp. Read the source
  signatures and WeilConjectures.AlgebraicGeometry.GroupScheme.Defs's terminology
  docstring; bundled morphisms are the recorded multiplication-compatible maps.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType, and
  `AlgebraicGeometry.QuasiCompact`, Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact.
- `def-weil-pbc-faithfully-flat-ring-map`: `Module.FaithfullyFlat`,
  Mathlib.RingTheory.Flat.FaithfullyFlat.Basic; its ring-map specialization
  `RingHom.FaithfullyFlat`, Mathlib.RingTheory.RingHom.FaithfullyFlat.
- Added the already landed `def-sfb-tori-multiplicative-type` to `stmt_deps`:
  `AlgebraicGeometry.MultiplicativeType.splitTorus`,
  Sheaf.AlgebraicGeometry.ToriMultiplicativeType. Its rank-zero value is the tensor
  unit, and its successor is G_m times the preceding product. Read also the
  StandardGroupSchemes.multiplicative and multiplicativeGroup definitions:
  these use the Laurent-polynomial spectrum and its canonical Hopf group law.
  No private split-torus definition or algebraic-closure splitting replaces it.

The added statement dependency is an existing notion already in the node's prose;
this is the authorized addition of a landed definition node, with no statement
correction. No new node or dependency module is necessary.

Proof-dependency imports: Mathlib.AlgebraicGeometry.Group.Affine supplies the
coordinate Hopf structure and affine spectrum correspondence;
Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra supplies universal injectivity;
Mathlib.LinearAlgebra.FreeModule.PID supplies Submodule.basisOfPid. Tensor-product
and group-object definitions are exposed through these and the public imports.
`lem-sfb-diagonalizable-group-geometric-criteria` has no Lean record or Mathlib
match, so its proof import cannot yet be added; it is named in the proof docstring.
It is not needed to type the statement. All four DAG proof steps, including the
coefficient projection that splits the tensor map, are in the theorem docstring.

Source checked locally with pdftotext in
`literature/milne-algebraic-groups_iAG2017.pdf`: Theorem 12.9(b),(c), printed
pp.233--234, and Definition 12.14 and its following paragraph, printed p.236.
The source proves diagonalizable quotients using the character subgroup and
explicitly says a quotient of a split torus is split. The module retains the
node's direct coordinate-subalgebra proof plan.

Edge cases checked before writing: rank-zero T has coordinate ring k, and a
faithfully flat quotient is again the trivial group; projections onto fewer
factors have positive-dimensional kernels; in characteristic p the p-th power
map on G_m has nonreduced kernel mu_p and is covered; finite and imperfect fields
are included because the argument extracts coefficients rather than evaluating
rational points. No independent smaller universe occurs in a test-object
quantifier. Affineness and finite type are genuine assumptions about Q, not
predicates of its identity map. There is no statement dispute or source fault.

Searches for an existing statement:

- msearch.py LeanFinder: `A faithfully flat quotient of a split torus over an
  arbitrary field is a split torus` returned eight hits on faithfully flat
  descent and formal smoothness; none states this result.
- msearch.py LeanSearch: `A faithfully flat quotient of a split algebraic torus
  is split over the base field` returned eight hits on flat modules and ring
  maps, not the torus classification.
- msearch.py Loogle: `"torus", "quotient"` returned zero hits.
- msearch.py Mathlib grep in AlgebraicGeometry:
  `(torus|Torus|diagonalizable).*(quotient|Quotient)|(quotient|Quotient).*(torus|Torus|diagonalizable)`
  returned zero hits.
- rg of lean/WeilConjectures and lean/Sheaf for splitTorus, split-torus quotients,
  and diagonalizable groups found the existing split-torus construction and
  related geometric semiabelian and diagonalizable quotient results. Reading
  ToriMultiplicativeType and GeometricSemiabelianSplitQuotient confirms the former
  is a definition and the latter concerns a different semiabelian extension.
  No exact arbitrary-field quotient theorem was found. Word-boundary torus/tori
  search in WeilConjectures found no matching statement.
- rg for the item id in lean/WeilConjectures returned no hits; the new theorem's
  name has no hits in Mathlib, WeilConjectures, Sheaf or dag/lean_names_upstream.json.
- Read the caller GroupScheme.FieldSplitTorusRationalContainment: it already uses
  precisely `MultiplicativeType.splitTorus` with the same group-object encoding.

Validation: prescribed scompile.py compiled the module in both sandbox and
library modes cleanly (1.9 s and 2.0 s). Dry-run and delivery results follow below.

## Second reading by Q20

Author's second reading (independent review is the maintainer's, as required by
the dispatcher): reopened the node, module, dependency source declarations and
FieldSplitTorusRationalContainment. Checked each correspondence above against
the actual signature. In particular, the torus condition is over k itself,
`appTop` reverses q in the correct direction, affine/finite type are properties
of Q, the isomorphism lives in Grp (Over (Spec k)), and neither characteristic
nor kernel restrictions have slipped in. The finite-type conjunction has both
parts. The explicit existential hT retains arbitrary split presentations of T;
the output existential retains rank zero. No mismatch found and no statement
correction made. The only DAG addition is the already recorded definition node
needed by the actual split-torus term in the signature.

Additional candidate checked: `DiagonalizableQuotientCharacterKernel.lean` has
`[IsAlgClosed F]`, a character-map cokernel and a subgroup quotient conclusion;
it does not state this arbitrary-field quotient theorem. The separate
`RingGroupSchemes.splitTorus` construction is unnecessary here: the selected
field construction already matches the caller's terms, and no copy is made.

Dry run: deliver2.py --no-push returned OK at 83580058f4e: the server preflight
and per-file compilation passed. No source, dependency interface or node
statement correction was required.

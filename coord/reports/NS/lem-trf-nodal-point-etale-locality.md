## Worker report

The module `Sheaf.AlgebraicGeometry.NodalPointEtaleLocality` states
`AlgebraicGeometry.nodalPoint_etale_locality`, with its proof entirely `sorry`.
It also constructs `Scheme.Hom.completedLocalScalarMap`, the canonical coefficient
map to the completion: constants via `(Scheme.ΓSpecIso (.of k)).inv`, pullback
`f.appTop`, the global germ map `X.presheaf.Γgerm x`, and the canonical completion
algebra map. Its data contain no postponed proof and no chosen coefficient splitting.
This is a helper for the owning node, listed in `lean.declarations`.

The node's hypotheses and clauses correspond as follows:

- The algebraically closed field is `{k : Type u} [Field k] [IsAlgClosed k]`.
- The locally finite type k-scheme is `{C : Scheme.{u}}`, with its explicit
  structure morphism `f : C ⟶ Spec (.of k)` and `[LocallyOfFiniteType f]`.
  The explicit structure map supplies the canonical coefficient maps on both completions.
- Pure dimension one is exactly `hpure : C.IsPureDimension 1`, using the recorded
  definition, which tests every irreducible component with its subspace topology.
- The étale morphism is `e : D ⟶ C` with `[Etale e]`, for `{D : Scheme.{u}}`.
  The induced structure morphism on D is literally `e ≫ f`.
- The arbitrary point is `y : D`; the image x is written `e y` throughout.
- Each completion is `AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
  (X.presheaf.stalk x)`, so it is specifically maximal-ideal-adic completion.
- The model is `MvPowerSeries (Fin 2) k` modulo the ideal spanned by `X 0 * X 1`:
  exactly the two-variable formal power-series algebra modulo uv.
- Each isomorphism condition is `Nonempty (@AlgEquiv k ... ... _ _ _ ... inferInstance)`.
  The source algebra structure is explicitly `(f.completedLocalScalarMap (e y)).toAlgebra`,
  respectively `((e ≫ f).completedLocalScalarMap y).toAlgebra`; the target has its
  standard quotient k-algebra structure. Hence these are k-algebra isomorphisms.
- The first conjunct is precisely the equivalence of the two isomorphism conditions.
- The second conjunct has the disjunction of these same conditions as its antecedent
  and `e y ∈ closedPoints C ∧ y ∈ closedPoints D` as its conclusion.
- There is no separatedness, quasi-compactness, global finite-type, closed-point,
  reducedness, connectedness, or additional dimension hypothesis on D.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (through the field imports).
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`.
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`; its ring/algebra
  structure is imported from `Mathlib.RingTheory.AdicCompletion.Algebra`.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, `MvPowerSeries.X`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, the algebraic-closedness
  component explicitly identified by the algebraic-closure dependency's match.
- `Mathlib.Topology.JacobsonSpace`: `closedPoints`.

The proof dependency `lem-weil-pbc-local-completion-local-ring` is a Mathlib leaf:
its recorded local-ring and residue-field statements are supplied by
`Mathlib.RingTheory.AdicCompletion.LocalRing`, imported non-publicly.
The other proof dependency, `lem-trf-etale-completed-local-ring-iso`, has no
published declaration in the read DAG; its future import is therefore omitted.
It is used only in the natural-language proof plan, not to define the statement.
No statement prerequisite is missing. The two proof directions, including the
Noetherian and residue-field reduction and automatic closedness, are in the docstring.

Source read: `literature/stacks-project/curves.tex`, section-nodal, especially the
completed-local presentation, and lemma-node-etale-local (Tag 0C57) with its proof.
The node is the algebraically closed specialization with closedness moved to an
explicit consequence at arbitrary points. No statement correction was necessary.

Edge cases checked before writing: the empty source has no y and is vacuous; the
empty target admits no point in a source mapping to it. The identity and open
immersions give the same nodal test on the two stalks. A disjoint union of copies
is allowed. A smooth closed point satisfies neither nodal condition. At a generic
point the local completion is a field, so neither nodal presentation occurs.
Characteristic two is retained: uv and its two distinct formal variables make
sense without a characteristic restriction. Non-quasi-compact and nonseparated
locally finite type curves are not excluded. The common arbitrary universe u is
the ordinary category-of-schemes universe and imposes no dimension/cardinality bound.

Searches for existing statements and notions (2026-10-17 UTC):

- `msearch.py ... leanfinder` query: “A point on a curve has nodal completed local
  k-algebra if and only if a point above it under an etale morphism does”. Eight
  hits on `Algebra.etaleLocus`, `Algebra.IsEtaleAt`, their basic properties, and
  standard étale algebras; none gives the completed nodal presentation equivalence.
- `msearch.py ... leansearch` query: “Nodal completed local rings of curves are
  invariant under etale morphisms”. Eight hits on `RingHom.Etale`,
  `Algebra.Etale.of_equiv`, formal étaleness and scheme étaleness; no match.
- `msearch.py ... loogle` query: `"nodal"`. Twelve hits, all Lagrange nodal
  interpolation polynomials or nodal weights, unrelated to curve singularities.
- `msearch.py ... grep` query: `nodal|completed.*local.*ring`, subdirectory
  `AlgebraicGeometry`: zero hits returned by the service.
- `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for
  `lem-trf-nodal-point-etale-locality`: no hits. Concept search for `nodal` and
  completed stalks finds comments about nodal fibres, not the requested statement.
- `rg` in `lean/Sheaf` for nodality and étale locality finds the family/chart
  theorems, the nodal local criterion, and `IsOrdinaryNode`. The latter includes
  closedness and only an abstract ring isomorphism; it does not express this node's
  arbitrary-point k-algebra condition. No such predicate is duplicated here.
- `rg` across Mathlib, the upstream source, `lean/Sheaf` and
  `dag/lean_names_upstream.json` for `completedLocalScalarMap` and
  `nodalPoint_etale_locality`: no pre-existing declarations with either name.

Validation: `scompile.py NS lem-trf-nodal-point-etale-locality <module>` compiled
both the sandbox and library-name versions cleanly, approximately two seconds each.
No errors or unexpected warnings. No node faults or disputed statements found.

## Second reading by NS

Author's separate self-check; the maintainer supplies the independent review.
I reread the node beside the full signature after compilation. Its two conditions
use the identical quotient model and the respective canonical coefficient maps;
there is no accidental use of an abstract ring equivalence. The equivalence is
parenthesized independently of the closedness implication. Both sides of the
disjunction imply both closed-point conclusions. The arbitrary y binder does not
assume closedness. Pure dimension is required only for C, as in the node. The
structure morphism on D is the composite, not a separately chosen k-structure.
No change to the natural statement or its dependency list was needed.

## Worker report

The module states `AlgebraicGeometry.globalSections_isSeparable_of_isSmoothProjectiveCurve`. It binds a field `k`, a scheme `X` over `Spec k`, the smooth-projective-curve structure-morphism class, and `hA : IsField Γ(X, ⊤)`, which expresses that the structure map makes global sections a field extension. Its conclusion is `Algebra.IsSeparableExtension k Γ(X, ⊤)` for the canonical algebra structure induced by `Scheme.globalSectionsRingHom`.

The field hypothesis is rendered by `[Field k]`; the smooth projective curve hypothesis by `[Scheme.Hom.IsSmoothProjectiveCurve (X ↘ Spec (.of k))]`; the global-sections field-extension assumption by `(hA : IsField Γ(X, ⊤))` and the canonical algebra map in the conclusion; separability is rendered by `@Algebra.IsSeparableExtension k Γ(X, ⊤) _ hA.toField (...)`. The theorem proof is `sorry`, as required for stage 2. The intended proof follows projective implies proper, smooth implies geometrically reduced, then `proper_geometricallyReduced_globalSections_isSeparable`.

Dependencies used: `Sheaf.AlgebraicGeometry.SmoothProjectiveCurve`, declaration `AlgebraicGeometry.Scheme.Hom.IsSmoothProjectiveCurve`; `Sheaf.AlgebraicGeometry.ProperGeometricallyReducedGlobalSectionsSeparable`, declaration `AlgebraicGeometry.proper_geometricallyReduced_globalSections_isSeparable`; Mathlib `Field` and `IsField`; `Algebra.IsSeparableExtension` from `Sheaf.FieldTheory.SeparableExtension`; `Scheme.globalSectionsRingHom` and notation `Γ` from `WeilConjectures.AlgebraicGeometry.Cohomology.Defs` imported by the dependency module.

Edge cases checked: arbitrary characteristic and arbitrary field (including imperfect fields), arbitrary universe `u` shared by `k` and `X`, and the empty index issue does not arise because global sections are a fixed ring. The theorem does not impose finite type or nonemptiness beyond the smooth-projective-curve class.

Searches: `rg` over `lean/Sheaf` and `WeilConjectures` for global-sections separability found only the general dependency theorem; `rg` over Mathlib AlgebraicGeometry found no such theorem. The recorded node searches (LeanSearch, Loogle, and Mathlib grep) report no matching global-sections separability declaration. No `STATEMENT-DISPUTED` issue.

## Earlier second reading (a previous round; superseded)

The declaration was reread against the node. `k` is a field, `X` is a scheme over `Spec k`, and the structure morphism carries exactly the smooth-projective-curve class. `hA` supplies the field structure on `Γ(X, ⊤)`, while the conclusion uses the canonical structure-map algebra and the separable-extension predicate. Every clause of the node statement is represented; no additional mathematical hypothesis is introduced.

## Second reading by H1

Read the item JSON and its source, Stacks `varieties.tex`,
`lemma-proper-geometrically-reduced-global-sections` (0BUG), clauses (1)-(4) and
proof. The repository's literature checkout is absent on this machine; read the
available Stacks TeX at `/home/ubuntu/c1-stacks-review/varieties.tex:1933` and
cross-checked the upstream TeX at
https://raw.githubusercontent.com/stacks/stacks-project/master/varieties.tex.
The source assumes only a field k and a proper k-scheme before its clauses;
clause (4) assumes geometric reducedness. Clauses (1)-(3) make the sections a
product of finite field extensions; the item's field hypothesis leaves one
factor. No geometric connectedness or algebraically closed base is required.

Item-by-item statement checklist (all pass):

- Object k, a field: `(k : Type u) [Field k]`. Opened the field node and Mathlib
  `Field` in `Algebra/Field/Defs.lean`; this is the stated commutative nonzero
  field, with no characteristic restriction.
- Object X, a scheme over k: `(X : Scheme.{u}) [X.Over (Spec (.of k))]`.
  The chosen structure morphism is `X ↘ Spec (.of k)` throughout.
- Hypothesis smooth projective curve: the instance
  `[Scheme.Hom.IsSmoothProjectiveCurve (X ↘ Spec (.of k))]`.
  Opened its dependency node and `SmoothProjectiveCurve.lean`, then
  `Variety.lean`: the class extends `IsCurveOverField`, `Smooth`, and
  `IsProjective`; the curve is integral, separated, finite type, dimension
  exactly one, precisely the dependency node. It is not upstream's weaker
  `IsCurve` (dimension at most one, without integrality).
- Object k' = Gamma(X,O_X): `Γ(X, ⊤)` is the actual structure-sheaf section
  ring, not an abstract field or a chosen field merely isomorphic to it.
- Hypothesis that the structure map makes k'/k a field extension:
  `(hA : IsField Γ(X, ⊤))` and
  `(Scheme.globalSectionsRingHom k (X := X)).toAlgebra` in the conclusion.
  Opened the field-extension node, Mathlib `Algebra` and `RingHom.toAlgebra`,
  `IsField.toField`, and upstream `Cohomology/Defs.lean:258`.
  The ring homomorphism is exactly Gamma of the structure morphism composed
  with the inverse of Gamma(Spec k) = k. `hA.toField` retains the given ring
  operations and supplies inverses; it imposes exactly fieldness, and the
  map out of k is automatically injective. No unrelated algebra is assumed.
- Sole conclusion, k'/k separable: the explicit
  `@Algebra.IsSeparableExtension k Γ(X, ⊤) _ hA.toField ...`.
  Opened the separable-field-extension node and `SeparableExtension.lean`:
  every finitely generated intermediate field is separably generated,
  using a transcendence basis and a separable algebraic extension. This is
  the node's Stacks 030O predicate. No finite-dimensionality, equality k'=k,
  or geometric integrality is added to the conclusion. Quantifiers have the
  required order k, X with its structure, fieldness, then separability.

Also opened `ProperGeometricallyReducedGlobalSectionsSeparable.lean`: its
hypotheses are properness, geometric reducedness, and fieldness of the same
sections ring; its conclusion uses the same canonical algebra and predicate.
It is a more general dependency theorem, not a duplicate of this statement.
No new definition nodes or dependency modules are in this delivery.
The item has no statement correction, so there are no citer verdicts to audit.

Edge cases: an empty scheme and the zero section ring cannot satisfy the
curve/field hypotheses (integrality and exact dimension one, and nontriviality
in `IsField`). They are excluded by the node itself. No index set or n occurs;
empty products in Stacks correspond to the zero ring and are likewise ruled
out by fieldness. Dimension-zero schemes are not curves in this dependency.
The conclusion allows k'=k and nontrivial finite separable constants, e.g.
P^1 over a finite separable extension viewed over k. All characteristics and
imperfect base fields are allowed. `universe u` is explicitly bound and
arbitrary, following the dependency and Mathlib scheme conventions; different
sizes can be placed in one common universe. No test-extension quantifier uses
a smaller universe. No unbound variable or universe remains.

Independent H4 searches (different words from the first reading):

- LeanFinder via msearch: `global functions smooth proper variety separable
  constants`: eight hits, including `isField_of_universallyClosed`, which
  establishes fieldness only; none states separability of global sections.
- Loogle via msearch: `"IsSeparable", "Scheme"`: zero hits.
- LeanSearch via msearch: `regular functions on a proper smooth scheme form
  a separable extension of the base field`: unavailable, HTTP 500; no verdict
  is inferred from this failure.
- Direct rg, case-insensitive, for `global.?sections.*separ`,
  `separ.*global.?sections`, and `constants.*separ` across pinned Mathlib,
  upstream WeilConjectures, and repository lean/Sheaf: only the more general
  proper/geometrically-reduced dependency is relevant. Other hits concern
  etale cohomology or separation. Checked the full proposed declaration name
  and node id in upstream, project Lean, and `dag/lean_names_upstream.json`:
  no existing declaration matching this item. The new module is retained.

Mismatch repaired: the original proof docstring compressed the DAG's two
steps and omitted their node identifiers and the passage from geometrically
reduced fibres to X over Spec k. Expanded only that docstring to give both
steps, their dependencies, and the residue-field identification. The correct
signature, imports and node statement were retained; `lean.statement` is
verbatim the theorem signature. No definitions or extra theorems are present;
the sole theorem proof is `sorry`. Header, source/blueprint docstrings,
namespace, explicit universe and 100-character line limit checked.

Validation: initial signature compiled cleanly on the server via scompile
(exit 0, no warnings). The final module and delivery are checked below by the
prescribed dry run and delivery tools.

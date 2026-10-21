## Worker report

The node is stated without changing its statement or any dependencies. This is a mixed
record: the definitions are the existing upstream declarations, and the delivered module
`Sheaf.AlgebraicGeometry.CurveGenus` states just the extension-invariance parenthetical.
The theorem's entire proof is `sorry`. No new definition, auxiliary node or dependency
module is needed. No statement dispute or source error was found.

Source read: the complete current blueprint unit
`literature/blueprint/main-20261015/blueprint/sec-abelian-varieties/sk-def-curve/_section.md`.
Also read both statement dependencies, including their `blueprint_update` records, and
the complete declarations and docstrings in
`lean/WeilConjectures/AlgebraicGeometry/Curve.lean`. Those current definitions implement
the updated differential-form genus, rather than an obsolete H1-only definition.

Clause-by-clause correspondence:

- A field k: the existing declarations have `{K : Type u} [Field K]` and
  `{C : Scheme.{u}}`, with `f : C ⟶ Spec (.of K)` as structure morphism. Algebraic
  closedness is not imposed on the definitions, exactly as the unit allows arbitrary
  fields while using algebraically closed fields in this chapter.
- A curve is separated and of finite type: `AlgebraicGeometry.IsCurve f` extends
  `IsSeparated f`, `LocallyOfFiniteType f` and `QuasiCompact f`. The last two together
  express finite type; no reducedness, integrality or equidimensionality is added.
- Dimension at most one: its field `krullDim_le_one : topologicalKrullDim C ≤ 1`.
  The value is in `WithBot ℕ∞`, so the empty scheme is allowed.
- Smooth, respectively proper: `Smooth f`, respectively `IsProper f`, are the existing
  morphism properties. Neither is made a condition on all curves. I read their Mathlib
  class signatures and docstrings in `Morphisms/Smooth.lean` and `Morphisms/Proper.lean`.
- A connected curve: `AlgebraicGeometry.IsConnectedCurve f` extends `IsCurve f` and has
  `connectedSpace : ConnectedSpace C` and `krullDim_eq_one : topologicalKrullDim C = 1`.
  `ConnectedSpace` includes nonemptiness (also exposed by `IsConnectedCurve.nonempty`).
  Thus this is nonempty and connected of exactly dimension one, with no smoothness
  or properness implicit in that definition.
- Spec k is a curve but not a connected curve: its dimension zero satisfies the former
  inequality and contradicts the latter equality. This parenthetical illustrates the
  definitions; no replacement notion excluding zero-dimensional curves is introduced.
- For C smooth proper connected: the new theorem has precisely
  `[IsConnectedCurve f] [Smooth f] [IsProper f]`. These assumptions restrict the use of
  the existing genus to the intended objects, without restricting the general definition.
- Genus is dim_k H0(C, Omega1_C/k): `AlgebraicGeometry.Scheme.Hom.genus` is literally
  `Module.finrank K Γ(f.relativeDifferentials, ⊤)` after installing `f.ΓAlgebra` and
  the scalar-restriction module structure. I read the sheaf-of-relative-differentials
  definition and docstring in `WeilConjectures.AlgebraicGeometry.Modules.Differentials`:
  it is the sheafification of relative Kahler differentials. Global sections are H0;
  the existing `Scheme.Hom.genus_eq_finrankH_zero` records this identification explicitly.
  The natural number finrank represents dimension on the intended proper smooth curves;
  no arbitrary dimension or choice of a vector space replaces it.
- Invariant under algebraically closed extension: the new theorem binds
  `{k K : Type u} [Field k] [Field K] [IsAlgClosed k] [IsAlgClosed K] [Algebra k K]`.
  Its left side is the genus of
  `pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))`, the structure
  morphism of C_K, and its right side is `f.genus`. A field algebra map is injective,
  so this represents the specified field extension without an extra hypothesis.
  The statement uses no lets, extra geometric-integrality assumption, Jacobian datum,
  or hypothesis asking the caller to supply connectedness of the base change.
  All types and universes are explicitly bound. A common arbitrary universe accommodates
  k, K and C simultaneously, without bounding the extension's cardinality.

Dependencies used:

- `def-sc-curves`: module `WeilConjectures.AlgebraicGeometry.Curve`, declarations
  `AlgebraicGeometry.IsCurve` and `AlgebraicGeometry.IsConnectedCurve`. The recorded
  primary declaration is usable; the module gives the companion connected notion too.
- `def-sc-genus`: the same module, `AlgebraicGeometry.Scheme.Hom.genus`, whose full
  signature and construction were read. All three notions are listed in `lean.declarations`.
- Proof dependency `lem-sc-genus-invariant`: module
  `WeilConjectures.AlgebraicGeometry.GenusInvariant`, declaration
  `AlgebraicGeometry.genus_jacobian_invariant`. Its full signature and docstring were
  read. The new module imports it without `public`. The proof docstring follows the
  node's sole step: remove its three existential witnesses, take the first conjunct
  (genus equality), and discard the extra Jacobian conclusions. The remaining proof
  dependency `def-sc-genus` is already a public statement import.

Why a small new statement is needed: Curve.lean provides exactly all the definitions
but not the parenthetical. `genus_jacobian_invariant` states strictly more, with
existential geometric properties and Jacobian compatibility. The existing
`Scheme.Hom.genus_baseChangeField` in `Curve/BaseChange.lean` has a different interface,
assuming `SmoothOfRelativeDimension 1 f` and properness and allowing all field extensions.
It is not an exact statement with the unit's smooth-proper-connected hypotheses.
The new theorem adds no definition and states only the equality extracted by the
node's recorded proof plan, rather than silently replacing the unit by either
stronger theorem. Its own matching DAG node is this item.

Edge cases checked before writing:

- Empty schemes satisfy the dimensional inequality and are permitted as curves;
  the connected-curve hypotheses appropriately exclude them.
- Spec k and finite disjoint unions of points may be curves; dimension exactly one
  correctly excludes them from connected curves.
- A disconnected union of one-dimensional curves remains a curve but fails
  `ConnectedSpace`; no integrality assumption is put into the definitions.
- P1 has genus zero and smooth proper connected elliptic curves have genus one;
  the equality accommodates both, including characteristic p.
- The identity extension K = k and nontrivial algebraically closed extensions are
  both included. No degree-finiteness, separability or characteristic restriction
  was added. Nonproper smooth curves do not fall under this genus-invariance theorem.

Searches actually run:

- `msearch.py ... leanfinder` query: "curve separated scheme finite type dimension
  at most one genus global sections relative differentials invariant field extension".
  Eight results: standard-smooth relative dimensions, Weierstrass function fields,
  formally etale separable fields, differential fields, function-field class numbers.
  None defines this arbitrary-scheme curve/genus package.
- `msearch.py ... loogle` query:
  `AlgebraicGeometry.IsCurve, AlgebraicGeometry.IsConnectedCurve, AlgebraicGeometry.Scheme.Hom.genus`.
  Zero results, diagnostic unknown identifier `AlgebraicGeometry.IsCurve` in Mathlib.
- `msearch.py ... grep` query `IsCurve|IsConnectedCurve|def genus|genus.*pullback`,
  Mathlib subdirectory `AlgebraicGeometry`: zero results.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for curve, connected curve,
  genus declarations and genus base-change equalities found the Curve.lean definitions,
  `genus_jacobian_invariant`, `Scheme.Hom.genus_baseChangeField`, and a specialized
  smooth-projective-curve theorem. Their interfaces were inspected as described above.
- `grep -rn sk-def-curve lean/WeilConjectures` found the three definition docstrings
  in Curve.lean and downstream references in Curve/Estimate and Curve/RiemannRoch.
- `rg` for `genus_baseChange_of_isAlgClosed` in Mathlib, both project roots and
  `dag/lean_names_upstream.json` had no result; the new declaration name is unused.

## Validation

Resumed the saved packet on 2026-10-21 and ran the required dry run first. It
reproduced the saved upstream-path refusal for the proposed EulerChar import
repair. Re-read the current blueprint unit, the dependency records and their
full declarations and docstrings. The saved statement remains correct, so its
module and node record were retained unchanged.

Investigated the upstream per-file timeout through scompile.py. Tested an
explicitly typed base-change definition, cached sheaf category instances, and
ordinary definitions in place of action-map abbreviations. Also tested hiding
the generic Ext scalar-action and base-change construction bodies with
`@[no_expose]`, retaining their canonical data and adapting consumers to the
existing scalar-action and pure-tensor characterization lemmas. The generic
Ext module compiled; the complete experimental FlatBaseChange repair did not
pass the per-file limit. These are experiments under scratch, not delivered
library changes. No timeout was raised and no source file in the shared
repository or launcher tool was edited.

During this work, a later compile passed the unchanged CurveGenus module
against the server's then-current dependencies (3.1 seconds for its library
check). Retested the original statement packet alone, with the obsolete
EulerChar import repair preserved under scratch rather than in the packet.
The prescribed deliver2.py dry run then printed:

```
OK (dry run): commit 79f07faf39c passes the preflight and compiles; nothing pushed
```

Thus no upstream repair is required by the delivered statement packet. The
only delivered Lean file is Sheaf/AlgebraicGeometry/CurveGenus.lean. Its only
theorem proof is sorry; there are no new definitions, dependency modules or
node changes outside lean. A source-based self-check confirmed the signature
in lean.statement is verbatim, the node differs from the current shared node
only in lean, and every Lean line is at most 100 characters.

The scratch logs retain the unsuccessful upstream diagnostics and the
successful statement-only dry run. They are not included in the delivery.

## Second reading by Q84

No second reading by a worker: this worker was dispatched directly, with instructions
not to start other agents. The maintainer's independent review reads the delivery.

## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothProjectiveTorusInvariantAffineCover` states
`AlgebraicGeometry.smooth_projective_torus_invariant_affine_cover`. Its single theorem has
proof `sorry`; there are no new definitions or auxiliary theorems. The accepted eight-step
split and its source attribution are retained. The theorem docstring records all eight steps,
including the linearization step missing from Milne's linear-action lemma.

Source read: Milne, Algebraic Groups (2017), printed p.272, Definition 13.45 (locally affine
means an invariant affine open cover) and Lemma 13.46 (the eigenvector-chart proof for the
projective space of a representation). This lemma is not attributed the stronger general
statement: the DAG's agent-formulated proof supplies the reduction via linearization.
The inherited previous BLOCKED report concerned stage 1, not stage 2. The current queue
assigns this item to stage 2, and the current node has no Lean record. There is no released
repair note for this item.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Algebraically closed field F | `(F : Type u) [Field F] [IsAlgClosed F]` |
| Group scheme T | `T : Grp (Over (Spec (.of F)))`, whose `T.X` has `GrpObj` |
| T is isomorphic as group scheme to a finite split torus of rank r >= 0 | `(r : ℕ)` and `_hT : Nonempty (T ≅ MultiplicativeType.splitTorus F r)`; the isomorphism is in `Grp`, so it respects the group law |
| Y is an F-scheme | `Y : Over (Spec (.of F))` |
| Smooth and projective over F | `[Smooth Y.hom] [IsProjective Y.hom]`; this is the dependency's H-projective convention |
| Algebraic action a on Y | `a : ModObj T.X Y`; `a.smul` is a morphism from the fibre product to Y over F |
| Identity and associativity on all commutative test algebras | The `one_smul` and `mul_smul` fields of `ModObj` are identities of morphisms; evaluation on every affine F-scheme gives exactly these laws. Conversely affine test schemes detect the identities by the affine open cover of their domains |
| Finite family of open subschemes | `∃ (n : ℕ) (U : Fin n → Y.left.Opens)`; each `U j` is its actual restriction scheme, with inclusion `(U j).ι` |
| Cover Y | `(⨆ j, U j) = ⊤` in the lattice of opens |
| Each open is affine | `∀ j : Fin n, IsAffineOpen (U j)` |
| Action restricted to T times U_j factors through U_j | The displayed equality `aU.smul ≫ Over.homMk (U j).ι = (T.X ◁ Over.homMk (U j).ι) ≫ a.smul` |
| Each U_j carries the restricted algebraic T-action | `∃ aU : ModObj T.X (Over.mk ((U j).ι ≫ Y.hom))`; this includes both action laws, with the preceding equality pinning the action to the original one |
| Empty Y and trivial T allowed | `n = 0` is permitted; `r = 0` is permitted and `splitTorus F 0` is the tensor unit |

There is no assumption of an equivariant projective embedding, irreducibility, connectedness,
positive rank or characteristic zero. No condition is checked only on F-points. The restricted
actions are not arbitrary: their composites with the open immersions are fixed by the displayed
identity. Their laws are the restrictions of the original laws, since open immersions are monic.

Dependency declarations read and used:

- `Field`, Mathlib.Algebra.Field.Defs, lines 170-180: the field structure.
- `IsAlgClosed`, Mathlib.FieldTheory.IsAlgClosed.Basic, lines 57-65, and `exists_root`,
  lines 74-80: algebraic closedness (the dependency's match explicitly names this predicate).
- `CategoryTheory.GrpObj` and `Grp`, Mathlib.CategoryTheory.Monoidal.Grp, lines 40-49 and
  82-91: group schemes in the over-category; `Grp` is the bundled version of this record.
- `StandardGroupSchemes.multiplicative` and `multiplicativeGroup`,
  Sheaf.AlgebraicGeometry.StandardGroupSchemes, lines 79-88: Laurent-polynomial G_m and its
  group law, used by the recorded split-torus product.
- `MultiplicativeType.splitTorus`, Sheaf.AlgebraicGeometry.ToriMultiplicativeType, lines 34-39:
  finite product of that G_m, with the empty product equal to the trivial group. The landed
  node `def-sfb-tori-multiplicative-type` is added to stmt_deps to cite this existing notion.
- `AlgebraicGeometry.Scheme` and `Spec`/`Spec.map`, Mathlib.AlgebraicGeometry.Scheme,
  lines 35-47 and 469-480: schemes, affine spectra and their morphisms.
- `AlgebraicGeometry.Smooth`, Mathlib.AlgebraicGeometry.Morphisms.Smooth, lines 58-65:
  the dependency's affine-local smoothness notion.
- `AlgebraicGeometry.IsHProjective` and `IsProjective`,
  WeilConjectures.AlgebraicGeometry.Morphisms.Projective, lines 31-49: projectivity as a
  closed immersion in finite projective space plus quasi-compactness.
- `CategoryTheory.Limits.pullback`, Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback,
  lines 94-110: fibre products and projections. The cartesian tensor in `Over (Spec F)`
  is this fibre product (Mathlib.CategoryTheory.Monoidal.Cartesian.Over, public in Tori).
- `AlgebraicGeometry.IsOpenImmersion`, Mathlib.AlgebraicGeometry.OpenImmersion, lines 34-39,
  and `Scheme.Opens.toScheme`/`ι`, Mathlib.AlgebraicGeometry.Restrict, lines 44-58:
  actual open subschemes and their inclusion morphisms.
- `IsAffineOpen`, Mathlib.AlgebraicGeometry.AffineScheme, lines 250-252: affineness of the
  open restriction scheme.
- `CategoryTheory.ModObj`, Mathlib.CategoryTheory.Monoidal.Mod, lines 51-66: actual action
  morphism and the two action laws; the self-action forms at lines 153-164 confirm that
  these use the cartesian tensor. This is reused, not privately redefined.

Statement imports expose these notions. Plain proof imports are the currently recorded modules
of `sbc-lem-smooth-geometrically-reduced`, `def-pc-projective-space-twist`,
`def-pc-module-pullback`, `def-sc-invertible-module`,
`lem-sfb-relative-group-unit-axis-factorization`, `lem-pc-module-pullback-identity-composition`
and `lem-sfb-projective-polarization-section-algebra`. The recorded properness and finite-type
modules, projective space and smooth-flat instances are already imported by the statement
imports. Four proof nodes have no recorded Lean interface and are not imported:
`lem-trf-split-lattice-torus-projection`, `lem-sfb-split-torus-torsor-line-pullback`,
`lem-sfb-linearized-qcoherent-cohomology-coaction`,
`lem-sfb-split-torus-representation-weight-decomposition`. None is needed to type the statement.

Edge cases checked before writing:

- Empty scheme: take `n = 0`; the supremum of the empty family is bottom, equal to top
  on the empty space. There is no `Nonempty (Fin n)` condition.
- Trivial torus: `r = 0` is the empty product, and an ordinary finite affine cover gives
  the conclusion. No basis weight is assumed nontrivial.
- A point and disconnected smooth projective schemes: no integrality or connectedness
  binder, and the cover can contain opens from different components.
- Positive characteristic: neither the action laws nor the torus definition excludes it.
- Nonreduced commutative test algebras: equalities of morphisms in `Over (Spec F)` include
  them. No test-algebra universe is independently constrained or made vacuous.
- Universe: arbitrary `u`, with field, schemes and coordinate algebras in the same universe;
  the finite family uses `Fin n`, so its size is not restricted.

Searches actually run with msearch.py (Q37, this item):

- LeanFinder: `A smooth projective scheme with an action of a split torus admits a finite
  covering by invariant affine open subschemes`. Eight hits: ordinary Proj or affine
  covers, finite subcovers and an affine-transition auxiliary declaration. None states
  invariance for arbitrary algebraic actions.
- Loogle: `"IsAffineOpen", "invariant"`. Zero hits.
- Mathlib grep in AlgebraicGeometry: `Sumihiro|torus.*(affine|lineariz)|invariant.*affine`.
  Zero hits.
- LeanSearch: `Smooth projective torus action finite invariant affine open cover`. Eight
  hits, all ordinary affine covers, Proj covers or finite subcovers. None provides invariance.
- Local `rg` in `lean/WeilConjectures` and `lean/Sheaf` for split-torus and group-action
  names found the existing `MultiplicativeType.splitTorus` and use of Mathlib `ModObj`.
  Invariant affine descent modules concern descent transport, not torus invariance.
  The item-id search in `lean/WeilConjectures` returned no match. Name searches for
  `smooth_projective_torus_invariant_affine_cover` and its camel-case variant in Mathlib,
  WeilConjectures and Sheaf returned no match. `dag/lean_names_upstream.json` has no
  matching torus invariant-affine-cover declaration.

Validation: scompile.py compiled this file in sandbox mode and at its library module path,
with exit code 0 and no diagnostics (24.9 s and 9.8 s). The theorem remains `sorry` as required.
No statement correction or statement dispute.

## Second reading by Q37

This is the worker's second pass; the maintainer's independent review follows delivery,
as specified in the dispatch brief. No other agent was started.

Reopened the node and final Lean file and checked each binder and conclusion against the
correspondence table. `T ≅ splitTorus F r` is an isomorphism of group schemes, not of their
underlying schemes. `a : ModObj T.X Y` fixes a single algebraic action, and each restricted
`aU.smul` is required to agree with that same `a.smul` on `T × U_j`. `Over.mk` uses exactly
`(U j).ι ≫ Y.hom`, so no other F-structure on the open is chosen. The supremum equals top,
not just a dense open. `IsAffineOpen` is on each member, and `Fin 0` preserves the empty-cover
case. The two `ModObj` action laws are included in the existential restricted action. No
hypothesis or clause mismatch was found; no statement change was made. The sole node delta
outside `lean` adds the already landed split-torus definition to stmt_deps, under §5's rule
allowing landed definition dependencies.

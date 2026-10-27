## Worker report

The item is stated in `Sheaf.AlgebraicGeometry.RelativeSplitTorusInvariantAffines`, declaration
`AlgebraicGeometry.exists_relative_split_torus_invariant_affine_neighbourhood`. Its only postponed
proof is that named theorem. The accompanying definition module has real data and no `sorry`.
The item's statement, proof, proof dependencies, source, and status are unchanged; `stmt_deps`
only gains the new definition node `def-sfb-relative-split-torus`.

Hypotheses and conclusions, clause by clause:

- An arbitrary affine Noetherian base is `S : Scheme.{u}`, `[IsAffine S]`, and
  `[IsLocallyNoetherian S]`. Affine schemes are quasi-compact, so no additional compactness
  hypothesis is needed to express Noetherian here. No field, base normality, or regularity is assumed.
- Rank `r ≥ 0` is `r : ℕ`, including zero. The acting group is exactly
  `(relativeSplitTorus S r).X`, the canonical group over S whose coordinate algebra is
  `AddMonoidAlgebra Γ(S, ⊤) (Fin r → ℤ)`. Thus there is no nonsplit-torus case.
- The scheme X, its map to S, and its action are bundled in
  `X : CategoryTheory.Mod (Over S) (relativeSplitTorus S r).X`.
  Its underlying scheme is `X.X.left`, its structure map is `X.X.hom`, and the action
  map is `ModObj.smul`. Because it is a morphism in `Over S`, it is over S.
  `ModObj.one_smul` and `ModObj.mul_smul` are precisely the unit and associativity identities;
  the tensor product in this category is the fibre product over S. No inverse-action
  identity beyond these group-action laws is added.
- Separated finite type is `[IsSeparated X.X.hom]`, `[LocallyOfFiniteType X.X.hom]`, and
  `[QuasiCompact X.X.hom]`, precisely the convention recorded by the dependency node.
- Every local ring is a normal domain: `hnormal : ∀ p : X.X.left,
  IsDomain (X.X.left.presheaf.stalk p) ∧ IsIntegrallyClosed (X.X.left.presheaf.stalk p)`.
  This is the recorded inline normal-domain form, not an irreducibility hypothesis on X.
- An ample invertible module is `L : X.X.left.Modules`, `[L.IsInvertible]`, and
  `hL : Scheme.Modules.IsAmple X.X.left L`. Giving an arbitrary such L instead of an
  existentially quantified L is the ordinary curried form of the same conditional theorem.
- For every point, `x : X.X.left`, the conclusion supplies an action object U over the same
  S for the same group, and an equivariant morphism `i : U ⟶ X`. `IsOpenImmersion i.hom.left`
  makes its image an open subscheme of X, `IsAffine U.X.left` makes this open affine,
  and `x ∈ Set.range i.hom.left` makes it a neighbourhood of the specified point.
- Invariance is scheme-theoretic: `i.isModHom` says the action on U followed by i equals
  the action on X after the product inclusion. Thus the action restricts to the indicated
  open for every test scheme, including nonreduced test algebras. An equivariant open
  immersion carries exactly the restricted action; it is not extra arbitrary data.
  Since the point is arbitrary, these invariant affine opens cover X. This is the node's
  per-point covering assertion, without adding a chosen indexing set or requiring a finite cover.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom` and `Over S`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- The convention node `def-weil-pbc-scheme-conventions` has no declaration of its own;
  its separated and finite-type meanings are `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`, combined with
  `IsDomain` as explicitly required by `def-weil-pbc-normal-ring`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `Scheme.Modules.IsInvertible`,
  reexported by the recorded ampleness module.
- `WeilConjectures.AlgebraicGeometry.Ample`: `Scheme.Modules.IsAmple` (the full definition
  was read; absolute ampleness and its quasi-compactness condition are retained).
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: `StandardGroupSchemes.multiplicative`
  was read, with its `multiplicativeGroup`. Both have a field binder, so they cannot supply
  the acting group over this S. This recorded statement-dependency module remains imported;
  the new relative definition supplies the missing general-base notion without copying
  or changing any of that node's field-level declarations.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, its projections,
  and its functorial maps; `Over`'s existing cartesian tensor implements these fibre products.
- `Mathlib.CategoryTheory.Monoidal.Mod` and `.Cartesian.Mod`: `Mod`, `ModObj`, and
  `Mod.Hom` / `IsModHom`, supplying the action, its identities, and equivariance.
- The new definition uses `AlgebraicGeometry.hopfSpec` from
  `Mathlib.AlgebraicGeometry.Group.Affine`, `AddMonoidAlgebra.instHopfAlgebra` from
  `Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra`, and the finite-product-preserving
  `(Over.pullback S.toSpecΓ).mapGrp` from `.Monoidal.Cartesian.Over`.

Available proof dependencies are imported privately: `AmpleImmersionAffineBase` (upstream),
`ProjectiveClosedSubschemeHomogeneousIdeal` (Sheaf), Mathlib `Noetherian` (already public),
`ProjectiveSpectrum.Basic`, `Morphisms.ClosedImmersion`, and `OpenImmersion` (already public
because the conclusion uses it). The relative diagonal embedding and relative boundary lemmas
have no recorded Lean modules on the read base, so there is nothing to import for those two
proof-only nodes yet. Their uses remain in the proof docstring and the unchanged DAG proof.

Edge cases checked before writing: empty X makes the pointwise conclusion vacuous; empty S
and its zero global-section ring are permitted by the definition and hypotheses; rank zero
uses the group algebra of the zero group and is the trivial S-group. Disconnected S and
reducible normal X are allowed. Points need not be closed or rational. There is no
characteristic restriction, no flatness assumption on X/S, no faithful-action hypothesis,
and no extra finite-dimensional representation or linearization hypothesis. All schemes
use one arbitrary universe u; `Fin r → ℤ` has fixed finite rank and the algebra lies in u.
Every variable and universe is explicitly bound, with both auto-implicit options disabled.

Searches actually run:

1. `msearch.py ... leanfinder` for a normal ample scheme over an affine Noetherian base
   with a split-torus action and invariant affine neighbourhoods: 8 hits, including affine
   covers and projective basic opens, none stating this equivariant theorem.
2. `msearch.py ... loogle "AlgebraicGeometry.Scheme, AlgebraicGeometry.IsAffineOpen"`:
   12 hits, ordinary affine-open APIs only.
3. `msearch.py ... grep "splitTorus|invariant_affine|def.*[Gg]m|def.*multiplicative"
   AlgebraicGeometry`: 13 unrelated text matches, no relative split-torus definition or theorem.
4. Direct `rg` on `lean/WeilConjectures` and `lean/Sheaf` for split tori, torus actions,
   and invariant affines, and the requested item-id search on `lean/WeilConjectures`:
   existing field-only `MultiplicativeType.splitTorus`, field-only `diagonalizableGroup`,
   field-only Sumihiro neighbourhood theorem, and finite-flat-descent invariant-neighbourhood
   theorem. None says this node's general-base statement. Their signatures were read.
5. New-definition searches via `msearch.py`: LeanSearch for the arbitrary-base split torus
   as a group-algebra spectrum (8 hits, mostly unrelated base change); LeanFinder for the
   same construction (8 affine-space hits); grep of `AlgebraicGeometry/Group` for
   `splitTorus|relativeSplitTorus|hopfSpec` (5 hits, generic hopfSpec only).
   Exact returned outputs are preserved in the new node's `mathlib_searches`.
6. DAG filename and statement searches found no relative split-torus definition node.
   `python3 tools/blueprint_refs.py search 'split torus'` returned zero blueprint nodes.
   The existing split-torus frame model defines frames, not a relative torus.

Source reading: Stacks `groupoids.tex`, label `example-multiplicative-group`, Tag 022U,
explicitly gives the group over every scheme by base change, with t ↦ t ⊗ t. The rank-r
version uses the free abelian group ℤ^r and the existing group-algebra Hopf structure.
The primary Thomason article was read online at
https://www.researchgate.net/publication/243015730_Equivariant_resolution_linearization_and_Hilbert%27s_fourteenth_problem_over_arbitrary_base_schemes
(Theorem 3.3 and Corollary 3.4(3), printed p.32). The split reductive/ample-family case
allows an affine base without normality of that base. The affine-chart consequence is
precisely the boundary-avoiding argument already recorded in this node, not a claim that
Thomason states invariant affine charts verbatim. No statement correction or dispute is needed.

Validation: `scompile.py Q110 lem-sfb-relative-split-torus-invariant-affines` compiled each
of the two delivered files separately, including the main theorem in module mode against
the private overlay of the definition. Both returned successfully with no unexpected warnings.

## New nodes

`def-sfb-relative-split-torus` defines the actual group over an arbitrary scheme S:
base change of the Hopf spectrum of Γ(S,O_S)[ℤ^r] along S → Spec Γ(S,O_S). It owns
`AlgebraicGeometry.relativeSplitTorus` in `Sheaf.AlgebraicGeometry.RelativeSplitTorus`.
Its source is Stacks Tag 022U and finite products. Its searches are listed above and
recorded with exact msearch outputs in the node. Field-only `multiplicative`, `splitTorus`,
and `diagonalizableGroup` cannot supply this arbitrary-base construction. The generic
Hopf-spectrum and base-change machinery are reused, not redefined. This new notion
is cited directly by the item; no existing dependency node is changed.

## Second reading by Q110

This is a self-audit; the dispatcher explicitly forbids starting another agent, and
independent review is performed by the maintainer after delivery. Re-read both Lean files
against the unchanged item and the new definition node. The S binder retains an arbitrary
affine locally Noetherian base; the three morphism classes retain separated finite type;
`hnormal` retains normal domains at every point, without global integrality; L retains
both invertibility and absolute ampleness. `Mod` has exactly the action identities.
The conclusion retains an actual equivariant affine open neighbourhood at every point,
not only pointwise invariance on rational points. The relative group law is fixed by
Mathlib's Hopf structure and categorical base change, with no existentially chosen group.
The rank-zero, zero-ring and empty cases remain included. No mismatch or statement
change was found in this self-audit; no independent-worker review is claimed.

Dry-run repair: preflight required an explicit empty `import_flags` on the new node,
and the definition signature in `lean.statement` must start at `def`, excluding the
`noncomputable` modifier. Both record-only issues were corrected; Lean source unchanged.

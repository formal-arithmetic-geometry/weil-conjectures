## Worker report

The module Sheaf.AlgebraicGeometry.ReducedCurveNormalization states
AlgebraicGeometry.exists_finite_smooth_modification_of_reduced_curve with a sorry proof.
No definition is introduced and no node statement is changed.

Hypotheses and conclusions, in node order:

- An algebraically closed field k: `{k : Type u} [Field k] [IsAlgClosed k]`.
- A scheme X over k: `(X : Scheme.{u}) [X.Over (Spec (.of k))]`.
- Reduced: `[IsReduced X]`.
- Separated: `[IsSeparated (X ↘ Spec (.of k))]`.
- Finite type: `[LocallyOfFiniteType (X ↘ Spec (.of k))]` and
  `[QuasiCompact (X ↘ Spec (.of k))]`.
- Dimension at most one: `(h_dim : topologicalKrullDim X ≤ 1)`.
- A scheme X^nu and morphism nu: `∃ (Y : Scheme.{u}) (ν : Y ⟶ X)`.
  Its k-structure is the composite `ν ≫ (X ↘ Spec (.of k))`. Giving Y this
  structure makes nu a k-morphism by construction; no unconstrained second structure map
  or compatibility hypothesis is necessary.
- Y separated and finite type over k: `IsSeparated` and both
  `LocallyOfFiniteType` and `QuasiCompact` of that composite.
- Dimension at most one: `topologicalKrullDim Y ≤ 1`.
- Smooth over k: `Smooth (ν ≫ (X ↘ Spec (.of k)))`.
- Finite morphism: `IsFinite ν`.
- Dense open subscheme X': `∃ U : X.Opens, Dense (U : Set X)`.
  Mathlib gives U its canonical open subscheme structure.
- Isomorphism from the inverse image of X' to X': `IsIso (ν ∣_ U)`.
  `morphismRestrict` has precisely source `(ν ⁻¹ᵁ U).toScheme` and target U.
- The parenthetical choice of the normalization is the witness construction, rather than
  an additional property imposed on every modification. It is recorded in steps 2--6 of
  the theorem docstring: disjoint union of normalizations of reduced irreducible components,
  with zero-dimensional components identified with their normalization. The theorem states
  the existential assertion preceding the parenthesis, not uniqueness of the witness.

Dependencies read and used:

- def-weil-algebraic-closure: Mathlib.FieldTheory.IsAlgClosed.Basic, IsAlgClosed;
  its definition by splitting polynomials is equivalent to existence of roots of all
  nonconstant polynomials (the source docstring and exists_root/of_exists_root).
- def-kun-topological-krull-dimension: Mathlib.Topology.KrullDimension,
  topologicalKrullDim, valued in WithBot ℕ∞.
- def-sbc-smooth-morphisms: Mathlib.AlgebraicGeometry.Morphisms.Smooth,
  AlgebraicGeometry.Smooth (affine-locally smooth ring maps).
- def-weil-pbc-scheme-conventions is explicitly a convention node, with no declaration;
  use Mathlib.AlgebraicGeometry.Morphisms.Finite (IsFinite),
  Morphisms.Separated (IsSeparated), Morphisms.FiniteType (LocallyOfFiniteType),
  and Morphisms.QuasiCompact (QuasiCompact). Finite type is the conjunction of
  locally finite type and quasi-compact, as the convention node specifies.
- def-pc-reduced-scheme: Mathlib.AlgebraicGeometry.Properties, AlgebraicGeometry.IsReduced.
- def-sc-normalization: WeilConjectures.Mathlib.AlgebraicGeometry.Normalization,
  Scheme.normalization and Scheme.fromNormalization, read with `[IsIntegral X]`.
  These serve the proof construction, not the existential signature, so their module is
  not an unused import of the statement file.
- def-weil-irreducible-components: Mathlib.Topology.Irreducible,
  irreducibleComponents (maximal IsIrreducible subsets). Likewise proof-only here.

Edge cases checked before writing: empty X admits the empty witness and empty dense open;
WithBot dimension permits dimension minus infinity. Zero-dimensional integral components
are Spec k, hence already smooth; mixed zero- and one-dimensional components are allowed.
No Nonempty, integral, pure-dimensional, proper, characteristic-zero, or surjectivity
hypothesis/conclusion is added. Reducible crossing components are allowed: their intersection
is removed from the dense open. All schemes and the field share the standard universe u;
there is no quantified smaller-universe testing condition. All variables/universes are bound.

Searches performed using /home/ubuntu/weil-launcher/msearch.py (H1, this item):

- leanfinder: "A reduced separated finite type curve over an algebraically closed field
  admits a finite smooth modification isomorphic over a dense open": eight hits, on smooth
  charts and elliptic-curve reduction, none matching this statement.
- loogle: "AlgebraicGeometry.Smooth, AlgebraicGeometry.IsFinite": zero hits.
- grep: "normalization|smooth.*modification" in AlgebraicGeometry: relative normalization
  and Zariski main theorem hits, no matching reduced-curve modification statement.
- rg of WeilConjectures and lean/Sheaf for reduced curves, smooth modifications and smooth
  normalizations: Curve/Reductions.lean assumes an already supplied finite smooth map;
  it does not assert the existence required here. The integral normalization API supplies
  components only. No matching Sheaf declaration.
- rg of the item ID in WeilConjectures: no hits. rg of the proposed declaration name in
  Mathlib, WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json: no hits.

Source checked: local literature/stacks-project is absent on this machine, so the source
was read at https://stacks.math.columbia.edu/tag/0BXR,
https://stacks.math.columbia.edu/tag/0B8Y and https://stacks.math.columbia.edu/tag/0A3Q.
These give finite normalization, smooth normalized curves over a perfect field, and the
isomorphism over a dense open used in the cohomological reduction, respectively.
The docstring follows all six proof steps of the node and names their auxiliary DAG nodes.
No missing notions, unusable dependency records, or statement disputes were found.

## Second reading by H1

I reread the node statement against the Stacks source places (Varieties 0BXR and
0B8Y, and the use in Etale Cohomology 0A3Q), then matched every binder and
conclusion clause with the Lean theorem.

* The algebraically closed base is rendered by `{k : Type u} [Field k]
  [IsAlgClosed k]`; no characteristic or perfection assumption is added.
* The scheme over the base is `(X : Scheme.{u}) [X.Over (Spec (.of k))]`.
  Reducedness is `[IsReduced X]`, separatedness is `[IsSeparated (X ↘ Spec
  (.of k))]`, and finite type is exactly `[LocallyOfFiniteType (X ↘ Spec (.of
  k))] [QuasiCompact (X ↘ Spec (.of k))]`, matching the convention node.
* The dimension hypothesis is `(h_dim : topologicalKrullDim X ≤ 1)`.
* The witnesses are `∃ (Y : Scheme.{u}) (ν : Y ⟶ X)`. Their separated,
  locally finite type, and quasi-compact properties over `k` are respectively
  `IsSeparated (ν ≫ (X ↘ Spec (.of k)))`, `LocallyOfFiniteType (ν ≫ (X ↘
  Spec (.of k)))`, and `QuasiCompact (ν ≫ (X ↘ Spec (.of k)))`; the dimension,
  smoothness, and finiteness clauses are `topologicalKrullDim Y ≤ 1`, `Smooth
  (ν ≫ (X ↘ Spec (.of k)))`, and `IsFinite ν`.
* The final witness is `∃ U : X.Opens, Dense (U : Set X) ∧ IsIso (ν ∣_ U)`,
  which is the dense open and the isomorphism from its inverse image. The
  `morphismRestrict` notation has the required inverse-image source.

The conjunction order and quantifier order agree with the node. The parenthetical
component-normalization construction is proof documentation, not an extra
universal conclusion. Empty schemes and empty opens are allowed; dimension uses
`WithBot ℕ∞`, so the empty case is covered. Zero-dimensional components,
mixed-dimensional reduced curves, and positive characteristic algebraically
closed fields are all covered. No nonemptiness, integrality, properness,
surjectivity, or characteristic-zero hypothesis appears, and all schemes and
the field share universe `u` as in the node.

I repeated the searches recorded above with `rg` over `WeilConjectures`, the
repository `lean/Sheaf`, and Mathlib's algebraic-geometry modules, and with the
LeanFinder/Loogle searches in `searches.jsonl`. They found only relative
normalization APIs and no declaration of this existential reduced-curve
modification theorem; the recorded dependency declarations are the appropriate
ones. No missing definition node or unusable dependency was found.

No mismatch was found, so no source, statement, dependency, or module change was
needed. The module compiles cleanly with `scompile.py`; its only proof is the
required `sorry`.

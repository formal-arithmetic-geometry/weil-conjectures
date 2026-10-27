## Worker report

The module `Sheaf.AlgebraicGeometry.GeometricInvariantDescent` states
`AlgebraicGeometry.RationalRepresentation.geometric_invariant_descent`, with one
`sorry` and no new data definitions. Source read: Milne, Algebraic Groups (2017),
Section 4(i), printed pp.96--97, Propositions 4.31--4.33 and Corollary 4.34.
The full six-step DAG proof is in the theorem docstring. The source defines
invariants by all algebra-valued points, describes them as the universal coaction
kernel, and states base-field-extension compatibility. The DAG combines this with
geometric-point detection for a smooth group.

Hypothesis and conclusion matching:

- Field k: `{k : Type u} [Field k]`.
- Algebraic closure K of k: `{K : Type u} [Field K] [Algebra k K]
  [IsAlgClosure k K]`. In particular this records algebraicity, as well as algebraic
  closedness; it does not replace algebraic closure with an arbitrary extension.
- The k-group scheme: `(G : Scheme.{u}) [G.Over (Spec (.of k))]
  [GrpObj (G.asOver (Spec (.of k)))]`, using the dependency's internal-group notion.
- Affine, smooth and finite type: `[IsAffine G]`,
  `[Smooth (G ↘ Spec (.of k))]`, `[LocallyOfFiniteType (G ↘ Spec (.of k))]`
  and `[QuasiCompact (G ↘ Spec (.of k))]` respectively.
- Dimension d >= 0: `(d : ℕ)`; W is `(W : Type u) [AddCommGroup W] [Module k W]
  [FiniteDimensional k W]`, with `(hd : Module.finrank k W = d)` fixing its dimension.
- Rational action: `(r : NaturalRepresentation (k := k) G W)`. Its `action` field
  is a group homomorphism on every commutative k-algebra into R-linear equivalences
  of the actual `R ⊗[k] W`. Its `naturality` field requires the commuting square for
  every k-algebra homomorphism. No faithfulness or geometric-point-only substitute.
- Definition of W^G: the theorem supplies `∃ U : Submodule k W`; its first conjunct
  is exactly `∀ w, w ∈ U ↔ ∀ (R : Type u) [CommRing R] [Algebra k R] (g : ...),
  r.action R g (1 ⊗ₜ w) = 1 ⊗ₜ w`. Thus U is uniquely specified by membership,
  rather than assumed as extra data or replaced with invariance at k-points.
  Submodule existence is asserted together with all its requested properties;
  no definition chooses an arbitrary object from a postponed existence theorem.
- Scalar-extended inclusion: `U.subtype.lTensor K`, the Mathlib tensor map of the
  actual inclusion. On pure tensors it sends b tensor w to b tensor (w : W).
  `Function.Injective` is the requested injectivity.
- Identifies its source with exactly the displayed geometric fixed space:
  `Set.range (U.subtype.lTensor K) = {z : K ⊗[k] W | ∀ g : points ... K,
  r.action K g z = z}`. With injectivity this is exactly the identification.
- The final equivalence is `(∃ z, z ≠ 0 ∧ ∀ g, r.action K g z = z) ↔ U ≠ ⊥`.
- There is no `PerfectField` or connectedness hypothesis. No characteristic excluded.

Statement dependencies read and reused:

- `def-weil-field`: Mathlib `Field` (Algebra.Field.Defs).
- `def-weil-algebraic-closure`: `IsAlgClosure`, read in
  `Mathlib.FieldTheory.IsAlgClosed.Basic`, with `IsAlgClosed` and algebraicity fields.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`, read in
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`, read in
  `Mathlib.CategoryTheory.Monoidal.Grp`, specialized to `Over (Spec (.of k))` as
  documented in `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `def-weil-finite-type-morphism`: `LocallyOfFiniteType` and `QuasiCompact`, read in
  Mathlib's FiniteType and QuasiCompact modules. Both conjuncts are retained.
- `def-weil-pbc-module-tensor-product`: `TensorProduct` and `LinearMap.lTensor`, read
  in Mathlib's TensorProduct.Defs and TensorProduct.Map.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec`/`Spec.map`, read in Scheme.
- The new definition-only record reuses
  `AlgebraicGeometry.RationalRepresentation.NaturalRepresentation` from
  `Sheaf.AlgebraicGeometry.RationalRepresentationComoduleDictionary`. Its entire
  definition, action and naturality signatures, and generic-point helpers were read.

Proof-dependency imports are retained: `Mathlib.AlgebraicGeometry.Pullbacks`
(affine fibre product), `Mathlib.RingTheory.TensorProduct.Maps` (algebra tensor
pushout), `WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced`
(`Smooth.geometricallyReduced`), and
`WeilConjectures.Mathlib.RingTheory.Nullstellensatz`
(`eq_zero_of_forall_algHom_apply_eq_zero`). The finite-type and reducedness
Mathlib leaves are already publicly available through these imports. No unstated
proof dependency is given a guessed import.

Edge cases checked before writing and on rereading: d=0/W=0 gives U=0 and no
nonzero geometric fixed vector. The trivial group gives U=W and the identity
scalar-extension inclusion. Disconnected smooth groups and imperfect base fields
remain allowed. Test algebras can be zero or nonreduced, and all algebra structures
and all points are quantified. No empty-matrix convention is needed. The fixed
universe is the published NaturalRepresentation interface's convention: k, G,
W, K and all test algebras are in Type u; any particular input data can be placed
in such a common universe. Test algebras are not quantified in an independent
smaller universe. The families themselves live in the containing universe.

Searches actually run using msearch.py:

- LeanFinder: "For a smooth affine group scheme a rational representation has
  scheme invariants whose scalar extension to an algebraic closure is the geometric
  fixed subspace" returned abstract-group `Rep.invariantsFunctor` and related hits.
- Loogle: `"invariants", "baseChange"` returned no hits.
- Mathlib grep: `invariants.*(baseChange|tensor)|RationalRepresentation|rationalAction`
  returned abstract-group homology/coinvariant and induced-representation files.
- LeanSearch: "Invariants of rational group scheme representations commute with
  algebraic closure" returned `Representation.invariants` and Galois invariants,
  none comparing scheme invariants with geometric-point fixed vectors.
- For the natural-action definition node, LeanSearch and LeanFinder queries on
  natural algebra-valued linear group actions returned affine schemes or ordinary
  abstract-group actions; Mathlib AlgebraicGeometry grep
  `NaturalRepresentation|rational.*representation` returned zero hits.
- `rg` of WeilConjectures found matrix-based RationalHom/representation APIs;
  the exact item-id search returned no match. `rg` of Sheaf found the existing
  NaturalRepresentation in the dictionary module, reused here. Related invariants
  in RationalHighestWeightData use restricted coordinate coactions; none states
  this geometric descent theorem. No invariants definition is duplicated here.
- DAG searches and `tools/blueprint_refs.py search 'natural rational representation'`
  found no definition-only owner of the natural-family interface (0 blueprint hits).
  `def-sfb-rational-representation-gzero` is about comodule Grothendieck groups.
  `lem-sfb-rational-fixed-space-base-change` treats universal fixed vectors over
  every further algebra, not detection on K-valued points, and has no Lean record.

Validation: scompile.py compiled the delivered module in both sandbox and library
modes, cleanly (21.5 s and 7.5 s). The theorem's expected sorry is the only postponed
proof; there are no diagnostic commands or data definitions with sorry. No
STATEMENT-DISPUTED issue, statement correction or dependency-module repair.

## New nodes

`def-sfb-natural-rational-representation` gives the definition-only DAG owner of
natural actions on all scalar extensions (Milne, Chapter 4(a), printed p.83, and
Remark 4.1, printed p.84). It is `existing: true`, naming the already landed
`AlgebraicGeometry.RationalRepresentation.NaturalRepresentation`; no new module,
copy, interface change, or theorem dependency is introduced. Previously this
helper was attached only to the dictionary theorem node. The search results are
recorded verbatim in the new node. The item gains only this definition node in
stmt_deps. Its source notions are the existing field, group scheme, tensor and
spectrum nodes; its blueprint ancestor is null as printed by blueprint_refs.py.

## Second reading by Q46

I reread the node and the completed Lean signature in a separate pass in this
worker session; this is not an independent-agent review. The dispatch brief
forbids starting another agent and says the maintainer independently reviews the
delivery. The algebra-valued quantifier and naturality field, both finite-type
conditions, algebraicity of K/k, d=0, the actual tensor inclusion, exact range
rather than a one-sided containment, and the nonzero equivalence all match.
The existential U is fully pinned by its membership biconditional, so its use
adds neither an invariant-space hypothesis nor an arbitrary subspace choice.
The natural-action node records the exact existing structure and introduces
no duplicate declaration. No mismatch was found and no statement changed.

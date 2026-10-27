## Worker report

The item is stated in `Sheaf.AlgebraicGeometry.PerfectExponentPVectorGroup` as
`AlgebraicGeometry.perfect_exponent_p_vector_group`.  Its only proof is `sorry`.
The theorem uses the project's bundled group scheme `Grp (Over (Spec (.of k)))` and
concludes with an isomorphism in the category of group schemes over `Spec k`.
The item node's original statement, source, proof, proof dependencies, and statement
dependencies are unchanged; only its `lean` field was added.

The recorded proof dependency `lem-sfb-smooth-p-torsion-additive-embedding` had no
Lean declaration or Mathlib match.  Under the stage-2 dependency-module rule, I added
`Sheaf.AlgebraicGeometry.SmoothPTorsionAdditiveEmbedding` and changed only that
copied dependency node's `lean` field.  It states exactly the dependency node's
embedding conclusion; its proof is `sorry`.  The item imports this module privately,
as it is a proof dependency rather than a statement dependency.

Hypothesis and clause correspondence for the item:

- `{k : Type u} [Field k]` is the field in `def-weil-field`.
- `(p : ℕ) [CharP k p] (hp : 0 < p)` expresses characteristic `p > 0`.
- `hperfect : ∀ x : k, ∃ y : k, y ^ p = x` says every field element is a p-th power.
- `G : Grp (Over (Spec (.of k)))` is a k-group scheme.  The bundled group object
  supplies multiplication, identity, inverse, and their laws.
- `[IsAffine G.X.left]`, `[LocallyOfFiniteType G.X.hom]`, and
  `[QuasiCompact G.X.hom]` render affine and finite type over k, using the recorded
  Mathlib finite-type convention (finite type is locally finite type plus
  quasi-compactness).
- `[Smooth G.X.hom]` and `[ConnectedSpace G.X.left]` render smoothness and
  connectedness.  `ConnectedSpace` includes nonemptiness, as required by the
  recorded connected-scheme notion.
- `[IsCommMonObj G.X]` is commutativity of the group object.
- `hpG : 𝟙 G.X ^ p = 1` is `[p]_G = 0`: multiplication by `p` is the p-th power
  in the group of group-scheme endomorphisms, and `1` is the constant identity
  morphism.  This is the pointwise sum-of-p-copies condition from the node.
- The conclusion `∃ d : ℕ, Nonempty ((∏ᶜ (fun _ : Fin d ↦
  Grp.mk (StandardGroupSchemes.additive k))) ≅ G)` is an isomorphism
  `Ga^d ≅ G` in group schemes over k.  The categorical product is coordinatewise
  additive; `Fin 0` gives the trivial group scheme, so `d = 0` is included.

The dependency module renders its node as follows: `H : Grp (Over (Spec (.of k)))`
with `[IsAffine H.X.left]`, `[LocallyOfFiniteType H.X.hom]`,
`[QuasiCompact H.X.hom]`, `[Smooth H.X.hom]`, `[IsCommMonObj H.X]`, and
`hpH : 𝟙 H.X ^ p = 1`; its conclusion is
`∃ n, ∃ i : H.X ⟶ ((∏ᶜ fun _ : Fin n ↦ Grp.mk (StandardGroupSchemes.additive k)).X),
IsClosedSubgroupScheme i`.  `IsClosedSubgroupScheme` includes the group
homomorphism and closed-immersion clauses, and `n = 0` is allowed.

Declarations read and reused:

- `Field` from Mathlib (the `def-weil-field` Mathlib match).
- `CategoryTheory.GrpObj`, `CategoryTheory.Grp`, and `CategoryTheory.IsCommMonObj`
  from `Mathlib.CategoryTheory.Monoidal.Grp` and its Cartesian group-object imports;
  the full group-scheme conventions are documented in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact` from
  Mathlib's finite-type and quasi-compact morphism modules.
- `AlgebraicGeometry.Smooth` from `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- `TopologicalSpace.ConnectedSpace` from `Mathlib.Topology.Connected.Basic`.
- `AlgebraicGeometry.StandardGroupSchemes.additive` and its group instance from
  `Sheaf.AlgebraicGeometry.StandardGroupSchemes`.
- The proof imports the stated `additive_subgroup_perfect_decomposition` theorem
  from `Sheaf.AlgebraicGeometry.AdditiveSubgroupPerfectDecomposition` and the
  closed embedding theorem from the new dependency module.  The item also imports
  `WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced` transitively
  through the proof modules for the smooth-reducedness step; no duplicate notion is
  defined here.

Edge cases checked before writing:

- `d = 0` and `n = 0` are represented by empty categorical products and retain the
  trivial group scheme.
- The trivial group satisfies the conclusion; no nontriviality assumption was added.
- The field may be finite or infinite and may have any positive characteristic, with
  `hperfect` supplying exactly the stated perfection hypothesis.
- Smoothness is retained as a scheme-morphism property and connectedness retains the
  nonempty requirement of `ConnectedSpace`; no geometric connectedness or reducedness
  hypothesis was added.
- The exponent condition is imposed on all group-scheme endomorphisms via `𝟙 G.X ^ p
  = 1`, so it includes nonreduced test algebras and is not reduced to k-valued points.
- In the decomposition proof, infinitesimal `alpha` factors are excluded by smooth
  reducedness and finite étale factors by connectedness; no such exclusions were
  inserted as hypotheses into the statement.

Searches (2026-10-24):

- `msearch.py ... leanfinder` with “Smooth connected commutative affine group schemes
  killed by p over a perfect field are vector groups”: 8 hits about perfect rings,
  Witt vectors, and affine space; no group-scheme classification.
- `msearch.py ... leansearch` with “A smooth connected commutative group scheme killed
  by p over a perfect field is isomorphic to a power of the additive group”: 8 hits
  about abstract primary components, Witt vectors, and perfect closures; no match.
- `msearch.py ... loogle '"GrpObj"'`: 12 hits for generic group-object declarations;
  none states this theorem.
- `msearch.py ... grep 'perfect.*exponent|exponent.*p|vector.group|GroupScheme'
  AlgebraicGeometry`: zero hits.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for the theorem name and the
  classification keywords found no existing declaration.  The only related existing
  theorem is the characteristic-zero sibling, which has a different hypothesis.
- The node's pre-existing Mathlib search records were also read: all report no exact
  affine group-scheme classification match.

No statement correction, source error, or `STATEMENT-DISPUTED` flag is needed.

Validation: `scompile.py Q45 lem-sfb-perfect-exponent-p-vector-group` compiled the
new dependency module and the item module separately in dependency order with no
errors or warnings (apart from the expected `sorry` declaration warning, which the
wrapper suppresses in its clean result).  All declaration binders are explicit under
`set_option autoImplicit false`, and all Lean lines are at most 100 characters.

## Second reading by Q45

I reopened both final Lean modules and both sandbox node copies and checked each binder
against the corresponding node clause.  The item has exactly one field, one positive
characteristic binder, one perfectness hypothesis, the affine/finite-type/smooth/
connected/commutative group hypotheses, the endomorphism power equality, and the
finite additive-power isomorphism conclusion.  The empty product gives the required
trivial case.  The dependency module has exactly the embedding node's hypotheses and
closed-subgroup conclusion, with no connectedness or perfection added.  The imports
are public for the statement vocabulary and private for the two proof modules.  No
mismatch or correction was found.

## Dependency modules

`lem-sfb-smooth-p-torsion-additive-embedding`: its base node had no usable `lean` or
Mathlib record, while the item proof explicitly applies this theorem.  The added
module `Sheaf.AlgebraicGeometry.SmoothPTorsionAdditiveEmbedding` states the node's
smooth commutative affine finite-type p-torsion embedding exactly, with a real
categorical additive-power target and `IsClosedSubgroupScheme`; only its proof is
postponed.  The copied dependency node changes only `lean` and records why this
module is required.

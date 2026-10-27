## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.SmoothSubgroupTangentGeneration` states
`AlgebraicGeometry.GrpObj.isIso_of_iSup_range_differential_eq_top`, with proof `sorry`.
No definition, helper theorem, new node, dependency repair, or statement correction is needed.
The original node is preserved except for its `lean` record and the addition of the landed
`def-wf-lie-algebra-derivation` to `stmt_deps`, as required by the H2 return.

Source read: Milne, Algebraic Groups (2017), Proposition 10.15 and Corollary 10.17,
printed pp.190–191 (PDF pages 202–203). The corollary uses Lie-algebra generation;
the assigned node deliberately specializes to linear spanning. Its connected smooth H_i
also permit the stated reduction through the reduced identity component of an arbitrary K.
The six steps of the accepted DAG proof are reproduced in the theorem docstring, with
their dependencies. The theorem does not assert anything about a chosen generated subgroup.

Clause-by-clause correspondence:

- Algebraically closed field F: `(F : Type u) [Field F] [IsAlgClosed F]`.
- F-group scheme G and its group laws: `(G : Over (Spec (.of F))) [GrpObj G]`.
- Affine, smooth, connected, finite type: `[IsAffine G.left] [Smooth G.hom]
  [ConnectedSpace G.left] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`.
  The last two classes together are the recorded finite-type convention.
- A finite set I, possibly empty: `(I : Type v) [Finite I]`. The index universe is
  independent of the scheme universe, and there is no `Nonempty I` requirement.
- For each index a smooth connected closed subgroup: `H : I → Over (Spec (.of F))`,
  the family of `GrpObj (H i)` instances, inclusions `ι : ∀ i, H i ⟶ G`, and the
  instances `IsClosedSubgroupScheme (ι i)`, `Smooth (H i).hom`,
  `ConnectedSpace (H i).left`. No finite-type or affine hypothesis is added on H_i:
  these follow from being closed in the affine finite-type G.
- Lie(J) is the identity tangent space, not a characteristic-zero matrix construction.
  The existing `AlgebraicGeometry.GrpObj.Lie` is the dual of the cotangent sheaf pulled
  back along the unit. Its existing `lieIdentityTangentEquiv` and
  `lieCotangentDualEquiv` identify it with T_e J and the local cotangent dual. I read
  their full definitions, including the rational residue-field identification.
- The induced differential is the existing `GrpObj.differential (ι i)`, whose defining
  formula composes dual-number points with the homomorphism. The existing
  `tangentPoint_differential` states exactly this formula.
- Linear images span: `hspan : (⨆ i : I,
  LinearMap.range (differential (ι i)).toLinearMap) = ⊤`. Taking `toLinearMap` is
  essential: the supremum is in `Submodule F (Lie G)`, so it expresses linear span,
  rather than generation using brackets in a lattice of Lie subalgebras.
- Every containing closed subgroup: arbitrary `(K : Over (Spec (.of F))) [GrpObj K]`
  and `(j : K ⟶ G) [IsClosedSubgroupScheme j]` occur after `hspan`. There is no
  smoothness, reducedness, connectedness, or finite-type hypothesis on K.
- Every inclusion factors: `hfactor : ∀ i, ∃ f : H i ⟶ K, f ≫ j = ι i`.
  These are morphisms over F. Compatibility with group laws follows by cancelling the
  closed immersion j, since both j and ι_i are homomorphisms; adding a separate
  `IsMonHom f` requirement would be unnecessary.
- K equals G as a closed subgroup scheme: `IsIso j`. For a closed immersion, this
  says its defining closed subscheme is the entire ambient scheme. It expresses equality
  including the immersion, not an abstract isomorphism of the two group schemes.

Dependency declarations used, with defining modules read:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`.
- `def-weil-algebraic-closure`: `IsAlgClosed`, `Mathlib.FieldTheory.IsAlgClosed.Basic`.
  Only the algebraically-closed-field part of this node is used, not a chosen closure.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`,
  `Mathlib.CategoryTheory.Monoidal.Grp`; homomorphisms use `CategoryTheory.IsMonHom`
  from `Mathlib.CategoryTheory.Monoidal.Mon`.
- `def-sc-group-scheme-subgroup`: `AlgebraicGeometry.IsClosedSubgroupScheme`,
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`, extending the recorded
  `IsSubgroupScheme` with a closed immersion of underlying schemes.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- `def-weil-connected-scheme`: `ConnectedSpace`, `Mathlib.Topology.Connected.Basic`.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact`, respectively the Mathlib morphism modules
  `FiniteType` and `QuasiCompact`.
- `def-wf-lie-algebra-derivation`: the existing upstream `AlgebraicGeometry.GrpObj.Lie`,
  its `Module F` instance, and the identity tangent description, recorded by
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Bracket` with primary declaration
  `AlgebraicGeometry.GrpObj.lieEquivTangent`. The public import of
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Differential` publicly imports
  `Lie.Bracket` and supplies `AlgebraicGeometry.GrpObj.differential`, used in `hspan`.
  The recorded construction works over arbitrary fields, including characteristic p.

The additional statement interface is reused from
`WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Differential`:
`AlgebraicGeometry.GrpObj.differential`, returning a Lie homomorphism whose underlying
linear map is used. It imports the existing `Lie` and its F-module structure.
Every recorded module of a proof dependency is imported without `public` unless it
already provides one of the statement dependencies. In particular the identity-component,
smooth-algebra reducedness, reduced-source factorization, rational tangent duality, and
two identity dimension modules are present. The dimension-drop node currently records
`PrimeSpectrum.isDomain_of_irreducibleSpace`; its recorded module is imported as instructed.
That record supplies a reducedness/irreducibility input, not the full dimension-drop
theorem. This does not alter the present statement or require an interface repair for it;
the accepted natural-language proof still specifies the dimension-drop step for stage 3.

Edge cases checked before writing:

- Empty I: the supremum is bottom, so `hspan` forces Lie(G) = 0. Smooth connected
  finite-type G over an algebraically closed field is then the trivial group; the result
  includes every K containing its identity. No choice of an index occurs in the signature.
- Trivial G: every closed subgroup is the whole trivial group, including for empty I.
- Positive characteristic: neither `CharZero` nor a separability restriction is present.
  The Lie/differential interfaces are over arbitrary fields. Non-smooth alpha_p cannot
  be one of the H_i, but an arbitrary non-smooth K remains admitted.
- Disconnected G is excluded exactly as in the node. ConnectedSpace includes nonemptiness;
  an empty scheme is also impossible for a group scheme over a nonzero field.
- The supremum uses linear subspaces and includes every image, without requiring any
  individual differential to be surjective.

Searches actually run through msearch.py for this group and item:

- LeanFinder: “A smooth connected affine algebraic group is generated by smooth connected
  subgroups whose tangent spaces span the tangent space at identity”. Eight hits concern
  manifold Lie groups and their Lie algebras; none states this algebraic-group result.
- Loogle: `"tangent", "Subgroup"`. Zero hits.
- Mathlib grep: `tangent.*(generat|subgroup)|Lie.*generat.*[Gg]roup`. Fourteen hits,
  concerning Euclidean tangent spaces and algebraic cotangent presentations, not this result.
- LeanSearch: “A connected smooth affine group scheme equals every closed subgroup
  containing smooth connected subgroups whose tangent spaces at identity span its Lie
  algebra”. Eight hits concern topological closed subgroups and manifold Lie groups.
- Local rg in `lean/WeilConjectures` and `lean/Sheaf` for
  `tangent.*generat|Lie.*generat.*[Gg]roup|subgroup.*tangent`, and the exact node id:
  no existing theorem matches. Existing consumers only mention this node in proof comments.
  Existing Lie and differential APIs were found and reused. A name search for
  `isIso_of_iSup_range_differential_eq_top` in Mathlib, both project roots and the upstream
  name index found no declaration.

Validation: scompile.py compiled both the sandbox and final library module names cleanly.
The final module sets `autoImplicit false` and explicitly binds universes u and v.
The only postponed result is the named theorem in this node.
No mathematical statement dispute or correction was found.

## Second reading by Q60

This is the dispatcher's single-worker delivery; no independent agent was started, as the
brief expressly forbids starting agents. This section records a second self-check, not an
independent review. The maintainer's independent review remains required.

I reread the node and final signature. All eight statement-dependency notions are reused, including the newly cited landed
`def-wf-lie-algebra-derivation` owning the Lie module and differential interface.
I checked the finite empty index type, each of the three hypotheses on H_i, all four
geometric hypotheses on G plus finite type, the linear rather than Lie supremum, and the
arbitrary closed K quantifier against the clause mapping above. Factorizations are over F;
their homomorphism property follows from the fixed subgroup inclusions. `IsIso j` preserves
the closed-subscheme meaning of equality. No extra regularity property of K is inferred
or requested as a hypothesis. The H2 return identified a missing dependency edge, now repaired as described below.
No mathematical statement text or Lean signature was changed.

## Repair of return on 49e9c5610e7b

H2: added the existing, landed `def-wf-lie-algebra-derivation` to the item’s `stmt_deps`
and named its owning module and declarations in the dependency list above. I read its
current node record, the recorded `lieEquivTangent` declaration, the base-field module
instance in `Lie.Ring`, and the public import and definition of `differential` in
`Lie.Differential`. This supplies the missing DAG edge for the actual Lie module and
differential used in the signature. The existing public `Lie.Differential` import already
provides the recorded `Lie.Bracket` interface, so the Lean file is unchanged.

Compared with the returned delivery, the only changes are this dependency edge and report
updates. Compared with current main, the item differs only in `lean` and that added
`stmt_deps` entry; no dependency node or mathematical statement was edited. The delivery
wrapper refreshes its base and rebases the repair through its normal isolated worktree.

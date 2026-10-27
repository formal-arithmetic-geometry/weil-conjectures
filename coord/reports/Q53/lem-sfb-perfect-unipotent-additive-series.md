## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.PerfectUnipotentAdditiveSeries`
states `AlgebraicGeometry.perfect_unipotent_additive_series`, with its single
proof postponed by `sorry`. It adds no definitions or other theorems. The source
was read directly in Milne, Algebraic Groups (2017), printed p.331:
Corollary 16.24, first assertion, and Corollaries 16.22 and 16.23. The latter
supply smooth connected terms and a central additive subgroup for the induction.
The node's five proof steps are reproduced in the declaration docstring.

Hypothesis and clause correspondence:

- The field is `{k : Type u} [Field k]`. Perfectness is `[PerfectField k]`,
  Mathlib's equivalent irreducible-polynomial separability definition. In
  particular it does not require algebraic closedness or characteristic zero.
- The group scheme is `U : Grp (Over (Spec (.of k)))`. Bundled `Grp` uses the
  recorded `CategoryTheory.GrpObj` and its group homomorphisms.
- Affineness is `haff : IsAffine U.X.left`; finite type is the conjunction of
  `hft : LocallyOfFiniteType U.X.hom` and `hqc : QuasiCompact U.X.hom`.
- Smoothness is `hsm : Smooth U.X.hom`; connectedness, including nonemptiness,
  is `hconn : ConnectedSpace U.X.left`.
- The geometric faithful-matrix unipotence hypothesis is
  `hunip : SolvableGroupStructure.IsUnipotent U`. Its full existing definition
  was read: it includes smoothness, a closed faithful representation into GL_n,
  every algebraically closed extension F, every F-point, and a positive nilpotence
  exponent of the represented matrix minus the identity. Because smoothness is
  already an explicit hypothesis, this is precisely the node's notion.
- A nonnegative integer length and all terms are `m : ℕ` and
  `S : Fin (m + 1) → Grp (Over (Spec (.of k)))`. The actual subgroup embeddings
  are `i : ∀ j, S j ⟶ U`.
- Every term is closed, normal in U, smooth, and connected by the four clauses
  quantified over `j : Fin (m + 1)`. Closed subgroup scheme and normal subgroup
  scheme are the recorded upstream predicates on `(i j).hom.hom`.
- `U = U_0` is `IsIso (i 0)`: the first embedded subgroup is all of U, not
  merely an abstract subgroup isomorphic to U. The last term is the trivial
  group by `Nonempty (S (Fin.last m) ≅ Grp.trivial _)`.
- For `j : Fin m`, the map `a : S j.succ ⟶ S j.castSucc` and equation
  `a ≫ i j.castSucc = i j.succ` express the descending inclusions as actual
  factorizations of the fixed ambient embeddings. They are closed inclusions:
  a map between closed subgroups with that factorization is the induced closed
  subgroup inclusion.
- `q : S j.castSucc ⟶ Grp.mk (StandardGroupSchemes.additive k)` and
  `IsFppfGroupQuotient a q` identify the represented successive fppf quotient
  with the standard G_a itself, equivalently giving the required isomorphism
  of group schemes. This quotient predicate uses the coset presheaf, actual
  fppf local surjectivity, and the sheafification universal property.
- `Q`, `p : U ⟶ Q`, and `IsFppfGroupQuotient (i j.succ) p` give the represented
  ambient quotient U/U_{j+1}. The map `b : G_a ⟶ Q` with
  `q ≫ b = i j.castSucc ≫ p` is the induced map of the successive quotient into
  the ambient quotient. It is the canonical map, determined by that equation
  since q is an epimorphism of fppf sheaves. Its image is U_j/U_{j+1}; it is
  automatically a monomorphism since both quotient kernels are U_{j+1}.
- Centrality is `(x ≫ b.hom.hom) * y = y * (x ≫ b.hom.hom)` for every
  `T : Over (Spec (.of k))`, every G_a-section x, and every Q-section y.
  Testing all such T also tests every section after any base change: a section
  over any further base-changed scheme is the corresponding morphism over k.
- The explicit clause `Nonempty (U ≅ Grp.trivial _) → m = 0` records that the
  trivial group admits the zero-length series. For a nontrivial U its premise
  is false, so it imposes no restriction on the length.

Recorded dependency declarations used, read with their signatures/docstrings:

- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, bundled `Grp`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `IsSubgroupScheme`, `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`; the imported QuasiCompact module's
  `AlgebraicGeometry.QuasiCompact` supplies the other finite-type clause.
- `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.Topology.Connected.Basic`:
  `ConnectedSpace`. These mathlib leaves need no added lean record.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`:
  `StandardGroupSchemes.additive` and its `additiveGroup` instance. The underlying
  affine scheme is Spec k[y] and its actual operations use the displayed
  comultiplication, counit and antipode of the recorded dependency.
- `Sheaf.AlgebraicGeometry.SolvableGroupStructure`:
  `SolvableGroupStructure.IsUnipotent`, recorded by the already landed
  `def-sfb-solvable-group-structure`. Added this existing node to `stmt_deps`.
- `Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry`:
  `IsFppfGroupQuotient`, recorded by the already landed
  `def-sfb-fppf-group-quotient-presentation`. Added this existing node to
  `stmt_deps`. It explicitly uses `Scheme.fppfTopology.over` and the coset
  sheafification universal property, hence implements the originally cited
  fppf-site and sheafification dependencies without a private replacement.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfTopology`;
  `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf` and the
  `sheafificationAdjunction`, read as the existing universal-property interface.
- `Mathlib.FieldTheory.Perfect`: `PerfectField`.

Already stated proof dependencies are imported: the above affine quotient
module, `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`
(`AffineSpace.smoothOfRelativeDimension_over` and
`topologicalKrullDim_eq_of_smoothOfRelativeDimension`),
`WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected`
(`GeometricallyConnected.of_connectedSpace_of_section`), and
`Mathlib.AlgebraicGeometry.Morphisms.Separated` (the two separatedness instances).
The homogeneous quotient dimension, central additive subgroup, normal quotient
image, and unipotent-to-multiplicative nodes currently have no recorded Lean
module, so no import can yet be named for those proof-only dependencies.

Edge cases checked before writing:

- U = 1: m = 0, the sole term is U, its embedding is the identity, the endpoint
  is trivial, and `Fin 0` makes every quotient and centrality condition empty.
- U = G_a: m = 1, with identity and trivial subgroup, successive quotient G_a;
  the ambient quotient is also G_a and commutation follows from its addition.
- Noncommutative upper-unitriangular 3-by-3 group: refine its central subgroup
  and its two-dimensional additive quotient into one-dimensional quotients;
  centrality is imposed in the ambient quotient, not merely within each term.
- Nonreduced test schemes are included by unrestricted `T : Over (Spec k)`.
  The group alpha_p is excluded by smoothness, not wrongly treated as split.
- Positive characteristic perfect fields are included. No separable-closure,
  algebraically closed, characteristic-zero, or positive-dimension restriction
  was introduced. Imperfect forms of G_a are excluded by the required perfectness.
- The field, groups, test schemes, and geometric fields all have common size u,
  as in the recorded definitions; no independently smaller test universe occurs.

Searches actually run using the prescribed msearch wrapper:

- leanfinder: `Smooth connected unipotent algebraic group over perfect field has
  a central normal series with additive group quotients`: eight hits, including
  `upperCentralSeriesAux`, nilpotence and abstract-group central series. None
  provides algebraic subgroup schemes or additive fppf quotients.
- loogle: `"unipotent", "series"`: zero hits.
- grep of Mathlib: `unipotent.*[Ss]eries|[Cc]entral.*[Ss]eries.*[Ss]cheme`:
  zero hits.
- leansearch: `Smooth connected unipotent algebraic group over perfect field
  has a central series with additive group scheme quotients`: eight abstract
  nilpotent-group central-series hits, no algebraic-group scheme theorem.
- rg of `lean/WeilConjectures` and `lean/Sheaf` for the item ID and
  `unipotent.*[Ss]eries|[Cc]entral.*[Ss]eries`: the split solvable and affine
  quotient modules cite this item in proof plans but do not state it. Existing
  `nilpotent_connected_central_series` has no additive quotients and assumes a
  nilpotent series. `SplitUnipotentLength` gives no ambient centrality, so neither
  is an exact match. The upstream tree has only unrelated complex unipotents.
- rg of `dag/lean_names_upstream.json`, Mathlib, upstream and Sheaf for
  `perfect_unipotent_additive_series`: no declaration already has this name.
- DAG and project searches for `IsUnipotent` and `IsFppfGroupQuotient` located
  the existing two notion nodes cited above; neither notion was redefined.

No statement correction, disputed mathematical claim, dependency repair, or new
node was needed. Only `lean` and addition of the two landed notion nodes to
`stmt_deps` change in the item JSON.

## Second reading by Q53

A separate second pass read the source paragraph, original node, current full
signatures of the two added dependencies, and the finished Lean declaration.
The first subgroup is identified through its actual embedding (`IsIso (i 0)`),
not only by an unrelated isomorphism. Every S_j is normal in U, including the
endpoints. The terminal trivial group, length-zero case, and all index bounds
were checked: `castSucc` is j and `succ` is j+1. Each successive quotient is the
standard additive group with its recorded group structure. The equation for b
makes the image in Q the required successive quotient, rather than an arbitrary
central additive map. Both quotient presentations retain the actual quotient
maps, kernels, and fppf sheafification property. Centrality quantifies over all
sections of Q, including sections with no global lift to U; thus it avoids the
weaker condition of commuting only with globally lifted sections. The field
and smoothness hypotheses coincide with the source, and no torus-equivariance
clause from the second assertion of Corollary 16.24 is inadvertently asserted.
No mismatch requiring a statement change was found. The maintainer performs
the independent review of this self-delivered worker item.

Validation: `scompile.py Q53 lem-sfb-perfect-unipotent-additive-series` compiled
both the sandbox probe and the actual module cleanly. The prescribed
`deliver2.py ... --no-push` printed `OK (dry run)` after its preflight and compile.

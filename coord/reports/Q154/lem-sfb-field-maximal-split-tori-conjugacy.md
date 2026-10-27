## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.FieldMaximalSplitToriConjugacy`
states `AlgebraicGeometry.field_maximal_split_tori_conjugacy`, with its sole proof
`sorry`. It adds no definitions and proves nothing. The statement and accepted
four-step proof in the DAG are unchanged. The declaration docstring carries all
four steps, including the central case, minimality of the parabolic, the inverse
in h_i^(-1) S_i h_i, and the final conjugator h_2 u h_1^(-1).

Source read: Milne, Algebraic Groups (2017), Section 25(a), printed pp.544–546
(PDF pp.556–558), especially Theorem 25.10 and the surrounding hypotheses. The
section assumes G reductive over k, with no infinitude or perfection assumption.
The accepted DAG already repairs the two omissions in the source proof; this
delivery preserves those repairs.

Clause-by-clause comparison:

- Any field k is `{k : Type u} [Field k]`, without other field instances.
- G, S₁ and S₂ are `Grp (Over (Spec (.of k)))`: genuine group objects in
  k-schemes with group-scheme homomorphisms. This uses the recorded
  `CategoryTheory.GrpObj` notion through its existing bundle `CategoryTheory.Grp`.
- Smooth affine finite type, geometric connectedness and reductivity are
  `_hG : ReductiveTorusCentralizer.IsReductive G`. I read its full definition.
  `SolvableGroupStructure.IsAlgebraic G` expands to `IsAffine G.X.left ∧
  LocallyOfFiniteType G.X.hom ∧ QuasiCompact G.X.hom`; the next conjunct is
  `Smooth G.X.hom`. Connectedness is tested after scalar extension to
  `AlgebraicClosure k`. For a finite-type k-scheme this is equivalent to
  connectedness after every field extension, exactly the node's geometric
  connectedness. Its final universal clause excludes every nontrivial connected
  closed normal smooth unipotent subgroup over the algebraic closure. The
  additional affine finite-type predicate on such a subgroup is automatic for a
  closed subgroup of this affine finite-type G. The reused unipotence predicate
  includes smoothness and a faithful closed representation into GL_n, with
  `(r(x)-1)^N = 0`, N > 0, at every geometric point. Thus it does not impose a
  characteristic or splitness condition on G.
- The two inclusions are `i₁ : S₁ ⟶ G` and `i₂ : S₂ ⟶ G`, with
  `[IsClosedImmersion i₁.hom.hom.left]` and the analogous instance for i₂.
  Group compatibility is already part of morphisms in `Grp`.
- `_hS₁` and `_hS₂` assert a group-scheme isomorphism over k to
  `MultiplicativeType.splitTorus k r` for some `r : ℕ`. This is the existing
  product of `StandardGroupSchemes.multiplicative k`, the Laurent spectrum
  Spec k[z,z⁻¹] with its Hopf multiplication. The empty product is the trivial
  group. These are split tori over k, rather than tori split only geometrically.
- `_hmax₁` and `_hmax₂` quantify over every closed split torus `j : T ⟶ G`
  defined over k. If `a : S_i ⟶ T` factors its inclusion (`a ≫ j = i_i`),
  it must be an isomorphism. This is maximality under subgroup inclusion, with
  inclusion expressed scheme-theoretically by factorization. Since both maps
  into G are closed subgroup inclusions, any such factorization is the subgroup
  inclusion in question. The target class is explicitly split over k; the
  existing `IsMaximalTorus` would instead quantify over all k-tori and is not used.
- The conclusion provides `g : 𝟙_ (Over (Spec (.of k))) ⟶ G.X`, a k-rational
  point, and `e : S₁ ≅ S₂`, an isomorphism of k-group schemes.
- The displayed equality says that postcomposition of the inclusion i₁ with
  conjugation by g is `e.hom.hom.hom ≫ i₂.hom.hom`. Multiplication and inverse
  take place in the existing group of morphisms into G.X. Precomposing with any
  B-point x gives `g_B * i₁(x) * g_B⁻¹ = i₂(e(x))`. Here `toUnit S₁.X ≫ g`
  is the constant morphism with value g. Thus this is the restriction of the
  canonical conjugation morphism, an equality of scheme morphisms, not merely
  an equality on k-points. No arbitrary map or comparison datum is assumed.

Recorded dependency declarations used and read:

- `Mathlib.Algebra.Field.Defs`: `Field` (line 180).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj` (line 43), `Grp` (line 81).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`
  (line 62).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`
  (line 43); `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`:
  `QuasiCompact` (line 43).
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace` (line 705).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`
  (line 45).
- `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`:
  `AlgebraicGeometry.ReductiveTorusCentralizer.IsReductive`, including its full
  signature and the full definitions of `SolvableGroupStructure.IsAlgebraic`
  and `SolvableGroupStructure.IsUnipotent` from its public imports.
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`:
  `AlgebraicGeometry.MultiplicativeType.splitTorus`, `baseChange`;
  `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: `multiplicative` and its
  canonical Laurent Hopf group structure.

The last two existing definition nodes were added to `stmt_deps`, as allowed by
brief-stage2 §5. Their existing declarations are reused without copying them.
The only stated proof prerequisite is imported privately:
`Sheaf.AlgebraicGeometry.GroupScheme.AffineHomomorphismFlatImage`.
The other six theorem prerequisites have no Lean record in the read repository;
they are preserved in the proof plan. The group-scheme dependency is already
publicly available through the statement imports.

Edge cases checked before drafting:

- Rank zero is permitted by `r : ℕ` and the empty-product definition. If G has
  no nontrivial split torus, both maximal split tori are trivial; g = 1 works.
- G itself a split torus: every maximal split torus inclusion is an isomorphism;
  conjugation is trivial, and the corresponding isomorphism satisfies the display.
- A central positive-rank split torus does not imply a proper parabolic. The
  preserved proof plan treats the all-central case before choosing P.
- Finite and imperfect fields are included. No `Infinite`, `PerfectField`,
  `IsAlgClosed`, or characteristic instance is bound for k.
- Nonreduced test algebras are included because the conclusion is a scheme
  morphism equality; no condition on B is hidden in the signature.
- Empty G is impossible for a group object over a field (it has a unit section).
- The common universe u supports k and its schemes and does not introduce a
  smaller independently quantified universe of test algebras.

Searches actually run with msearch.py (Q154, this item):

- LeanFinder: `Maximal split tori of a connected reductive group scheme over an
  arbitrary field are rationally conjugate`. Eight hits on Lie Cartan subalgebras,
  root-pairing constructions and abstract group-extension splittings; none gives
  rational conjugacy of maximal split torus subgroup schemes.
- Loogle: `"torus", "conj"`. Zero hits.
- Mathlib grep: `IsMaximalSplitTorus|split.?tor.*conjug|maximal.?split.?tor`.
  Zero hits.
- LeanSearch: `Two maximal split tori of a reductive algebraic group over a
  field are conjugate by a rational point`. Eight hits on abstract group
  extensions, Iwasawa structures and conjugate polynomial roots; no match.
- rg over the exact live `lean/WeilConjectures` and `lean/Sheaf` directories:
  `maximal.*split|IsMaximalSplit|field_maximal_split|split.*conjug`.
  No matching theorem. The parent FieldSplitTorusRationalContainment uses this
  node in its proof and has an inline maximal-split predicate; I read its full
  declaration and matched that same predicate. The general reductivity and
  split-torus searches found the existing definitions listed above.
- Search by this exact node id in `lean/WeilConjectures`: no declaration.
  Search in `dag/lean_names_upstream.json`: no matching theorem name.

No statement correction, new node, dependency repair, or STATEMENT-DISPUTED flag.

Validation: scompile.py compiled the file both as a sandbox module and at its
library module name, cleanly (1.9 s and 1.7 s). No diagnostic commands remain.

## Second reading by Q154

This is a second pass by the assigned worker; the brief prohibits starting
another agent, and the maintainer supplies the independent delivery review.
I reopened the node, source and final signature and compared each clause above.
In particular the quantifier in each maximality hypothesis ranges over split
tori over k, not all geometric tori; no perfection, infinitude, algebraic
closedness, or positive-rank assumption was introduced. The existence conclusion
contains a group-scheme isomorphism e, and the direction of the equality is
conjugation by g taking S₁ to S₂, not by g⁻¹. The morphism equality retains all
algebra points, including nonreduced algebras. The IsReductive definition is the
already recorded geometric predicate and agrees with all the hypotheses. The
statement uses exactly the parent's maximal-split interface, so the parent can
apply this theorem to its chosen maximal containing torus M and prescribed S.
No mismatch was found and no signature revision was needed.

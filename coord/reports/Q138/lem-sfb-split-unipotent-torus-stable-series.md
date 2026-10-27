## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.SplitUnipotentTorusStableSeries`
states `AlgebraicGeometry.splitUnipotent_exists_torusStableSeries`, with exactly
one postponed proof (`sorry`). It introduces no definitions and proves nothing.
The original natural-language statement, proof, proof dependencies, source and
all other node fields are preserved. The statement dependencies gain three
already landed definition nodes (solvable-group vocabulary, the split additive
series, and split tori) and the new definition node for the existing coordinate
projections. The frame-geometry theorem is not a statement dependency.

Source read: Milne, *Algebraic Groups* (2017), printed pp.333–334 (Summary 16.29,
especially (d)) and pp.343–344 (split solvable groups and Proposition 16.54).
The current blueprint's direct-images proof in
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`
was read. This node is a supporting structural input, not that blueprint unit's
statement. Its four-step proof is transcribed into the theorem docstring, including
the arbitrary-field central vector-subgroup and linearization prerequisites;
perfect-field Corollary 16.24 is not substituted. Those three newer structural
proof dependencies have no Lean records at the time of writing and therefore no
module import is invented for them.

Hypotheses, one by one:

- `k : Type u`, `[Field k]` is an arbitrary field, with no characteristic,
  perfectness, infinitude or algebraic-closure assumption.
- `U : Grp (Over (Spec (.of k)))` is the group scheme over precisely this field.
  `_halg : SolvableGroupStructure.IsAlgebraic U` unfolds to affineness and the
  two finite-type conditions `LocallyOfFiniteType U.X.hom` and
  `QuasiCompact U.X.hom`.
- `_hunip : SolvableGroupStructure.IsUnipotent U` is the existing smooth geometric
  matrix-unipotence predicate. Its full definition supplies `Smooth U.X.hom`, a
  finite-dimensional faithful representation as a closed subgroup of GL, and
  nilpotence of matrix-minus-identity at every algebraically closed field point.
  Faithfulness is scheme-theoretic, not injectivity on rational points only.
- `_hgeom : GeometricallyConnected U.X.hom` is Mathlib's connectedness after all
  field-valued base changes. This uses nonempty `ConnectedSpace`, as required.
- `_hsplit : ∃ n : ℕ, SplitUnipotentLength U n` reuses the landed split-series
  definition. It supplies smooth connected closed subnormal terms and actual
  fppf quotient homomorphisms to G_a, ending in the trivial group. Connectedness
  here is equivalent to the requested geometric connectedness: every group term
  has its rational unit section, so
  `GeometricallyConnected.of_connectedSpace_of_section` applies. The latter
  declaration and docstring were read in
  `WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected` (Tag 04KV).
  Conversely geometric connectedness implies connectedness, so no case is added.
- `s : ℕ` includes zero, and the acting group is exactly the existing
  `MultiplicativeType.splitTorus k s`, the recursively chosen product of G_m.
- `act` is a morphism of k-schemes from this torus times U to U. `_hone` and
  `_hassoc` state its unit and associativity identities on every commutative
  k-algebra. `_hhom` states the group-homomorphism identity in the U argument.
  These are precisely an action by group automorphisms: the inverse torus element
  acts inversely by the first two identities. Compatibility with identity and
  inverse in U follows from multiplicativity for maps between groups.
  All algebra variables and their structures are explicitly bound.

Conclusion, clause by clause:

- `∃ m : ℕ` allows length zero. `V : Fin (m+1) → Grp (Over (Spec (.of k)))`
  and `a i : V i ⟶ U` describe the actual subgroup schemes in U.
- `IsIso (a 0)` says the top subgroup is U, with its inclusion being the
  identification, not just an unrelated abstract isomorphism.
  `Nonempty (V (Fin.last m) ≅ Grp.trivial _)` identifies the last subgroup with 1.
- For **every** index i, the four conjuncts require its inclusion to be closed,
  normal **in U**, and its structure morphism smooth and geometrically connected.
  Affineness and finite type for every term follow from its closed inclusion in U;
  no extra hypothesis on the output groups is required.
- `j i : V i.succ ⟶ V i.castSucc` and `j i ≫ a i.castSucc = a i.succ` give the
  descending chain with compatible inclusions. The next two conjuncts explicitly
  require these successive inclusions to be closed normal subgroup inclusions.
- For each `i : Fin m`, `actᵢ` is an actual morphism on E times V_i.
  The equality
  `E.X ◁ (a i.castSucc).hom.hom ≫ act = actᵢ ≫ (a i.castSucc).hom.hom`
  states that the original action restricts to V_i. Its action and homomorphism
  identities are inherited by the closed monomorphism. The last term is trivial
  and hence automatically stable, including when m=0.
- `q : V i.castSucc ⟶ Grp.mk (StandardGroupSchemes.additive k)` is a genuine
  group-scheme homomorphism. `SolvableGroupStructure.IsFppfQuotient (j i).hom.hom q`
  requires flatness, surjectivity, local finite presentation, and an isomorphism
  from V_(i+1) to the scheme-theoretic kernel **commuting with the inclusion**.
  For affine groups of finite type, this exactly represents the fppf coset
  sheafification: lift sections fppf locally and compare two lifts by their
  difference in the specified kernel. A quotient with an isomorphism b_i to G_a
  can equivalently be represented by its composite quotient homomorphism q_i to
  G_a; this is the representative used here, with b_i the identity. Thus the
  quotient identification and the explicit scheme-theoretic kernel clause are
  retained, rather than replaced by a pointwise-surjectivity hypothesis.
- `n : Fin s → ℤ` is the integer tuple n_i. `SplitTorusFrames.coordinate k s l`
  is the existing l-th coordinate character. Group powers of its composite
  with e implement positive and negative integer powers **in G_m(R)**; they
  do not try to invert a nonunit in R. `List.ofFn ... |>.prod` is the finite
  product in increasing coordinate order, and gives 1 for the empty product.
- The final equality pulls the standard additive coordinate `Polynomial.X`
  back along `e⋅x` and along x, and pulls the Laurent coordinate `T 1` back along
  the product character. The equality is written in `Γ(Spec R, ⊤)`, canonically
  isomorphic to R by `Scheme.ΓSpecIso`. It is exactly
  `q_i(e⋅x) = (∏ e_l^(n_i l)) q_i(x)` on every commutative k-algebra R.
  Because q_i is the specified represented fppf quotient, this is precisely the
  required induced-action identity on the quotient; equality of sheaf maps is
  checked after the local lifts along q_i. It does not assume surjectivity of
  q_i on raw R-points.

Dependency declarations used (full definitions/signatures/docstrings read):

- `Mathlib.Algebra.Field.Defs`: `Field` (the Mathlib match of def-weil-field).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`, `Grp`; group homomorphisms and
  isomorphisms use this bundled category, with underlying `IsMonHom`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme`, and the underlying
  `IsSubgroupScheme` and kernel declarations; imported through the vocabulary.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace` (the recorded Mathlib match
  of def-weil-connected-scheme); `Mathlib.AlgebraicGeometry.Geometrically.Connected`:
  `GeometricallyConnected` (connected after every field-valued base change).
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: `additive`, `additiveGroup`,
  `multiplicative`, `multiplicativeGroup` with their actual polynomial/Laurent
  Hopf laws. No separate G_a or G_m is introduced.
- `Sheaf.AlgebraicGeometry.SolvableGroupStructure`: `IsAlgebraic`, `IsUnipotent`,
  `IsFppfQuotient`.
- `Sheaf.AlgebraicGeometry.GroupScheme.SplitUnipotentSeries`: `SplitUnipotentLength`.
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`: `MultiplicativeType.splitTorus`.
- `Sheaf.AlgebraicGeometry.SplitTorusTorsorFrameGeometry`: `SplitTorusFrames.coordinate`.
- Proof imports: `Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry`
  (`affine_normal_quotient_geometry`); `Mathlib.AlgebraicGeometry.Morphisms.Separated`
  (the two existing affine-source separatedness instances recorded by the leaf);
  `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`
  (`AffineSpace.smoothOfRelativeDimension_over`). All stated proof dependencies
  have their imports. The other four proof dependency nodes have no recorded
  declaration, and no downstream waiting or extra postponed theorem was added.

Searches before writing:

- `msearch.py leanfinder`: “A split unipotent algebraic group with split torus
  action has a stable normal series with additive character quotients”. Eight
  hits, including upper/lower central series and abstract nilpotence; none is a
  statement about smooth subgroup schemes and represented character quotients.
- `msearch.py loogle`: `"GrpObj", "IsUnipotent"`: zero hits.
- `msearch.py grep`: `split.*unipotent|torus.*series|torus.*filtration` in
  Mathlib/AlgebraicGeometry: zero hits.
- `msearch.py leansearch`: “A split unipotent group with split torus action admits
  an invariant normal series with additive quotients acted on by characters”.
  Eight hits concerning abstract central series and abstract extension splittings;
  none is the desired algebraic-group statement.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf`, including the node id,
  split/unipotent names, fppf quotient predicates, actions, torus coordinates and
  `dag/lean_names_upstream.json`: no existing theorem stating this node. Found
  and reused the existing split series, matrix-unipotence, quotient, split-torus
  and coordinate interfaces listed above.
- `tools/blueprint_refs.py search 'split unipotent torus'`: zero blueprint matches.
  Existing DAG definition nodes and their Lean records were read. The returned
  delivery exposed missing definition-node ownership for the existing coordinate
  characters; the repair below supplies it. Read-only dependency traversal
  confirmed that the added statement dependencies have no path back to this item.

Edge cases checked before writing: U=1 permits m=0 (Fin 0 makes all quotient
clauses empty); s=0 gives the trivial acting group and the empty character product
is 1; length one is an additive character quotient with trivial next subgroup;
zero or negative weights use the G_m group law; finite/imperfect fields and every
positive characteristic remain covered. Test algebras are arbitrary commutative
k-algebras, including nonreduced and zero algebras. All universe and variable
binders are explicit and `autoImplicit` and `relaxedAutoImplicit` are false.
No statement dispute or statement correction was found.

Validation: scompile.py compiled the delivered module both as an isolated sandbox
file and at its library module path, with no errors or non-sorry warnings. The
first elaboration exposed a missing commutative-group instance for the chosen
G_m model when using Finset products; the equivalent ordered `List.ofFn` product
uses its existing group instance and retains exactly the same finite character
product. No type-class hypothesis or auxiliary theorem was added to bypass it.
The source has no lines above 100 characters.

## New nodes

`def-sfb-split-torus-coordinate-characters` records the ordered projection
characters of `MultiplicativeType.splitTorus k r`. Its source is Milne,
*Algebraic Groups*, Definition 12.14 and Example 12.15, printed p.236, read in
the local PDF. The split torus is the recursive ordered product already used by
the item. The empty family is implemented by `Fin.elim0`; the first character is
`fst`; the remaining characters are `snd` followed by recursive coordinates.
Thus rank zero, arbitrary fields and all commutative test algebras are included.
The full recursive definition and docstring of
`AlgebraicGeometry.SplitTorusFrames.coordinate` were read at
`Sheaf.AlgebraicGeometry.SplitTorusTorsorFrameGeometry:91`. This declaration
already gives exactly the required data, so the new node has `existing: true`
and adds no module or duplicate definition. No definition node previously owned
it. Its definition dependencies are the recorded field, group scheme, G_m and
split-torus definitions.

The new node records the actual search outputs: LeanSearch for ordered split
torus coordinate characters returned eight unrelated coordinate/analytic-torus
hits; Loogle for `"splitTorus", "coordinate"` and Mathlib grep for
`splitTorus|SplitTorus|torus.*coordinate` returned zero hits. Project searches
found the existing coordinate construction and split torus; exact declaration
ownership checks found no definition node. `blueprint_refs.py search
'coordinate characters'` returned zero blueprint matches.

## Repair of returned delivery

H2 of the independent review of `2de00f0fc4cf` requested definition ownership
for the coordinate characters. Added the definition node above and replaced
`lem-sfb-split-torus-torsor-frame-geometry` in the item's `stmt_deps` with
`def-sfb-split-torus-coordinate-characters`. The theorem module already imports
`Sheaf.AlgebraicGeometry.SplitTorusTorsorFrameGeometry`, which is the new
definition node's recorded module. The statement uses only its coordinate
definition, without using the frame-geometry theorem. The theorem signature and
all approved hypotheses and conclusion clauses are preserved. The retained
sandbox was compared against current main: only `lean` and `stmt_deps` differed;
the repaired node was rebuilt from current main with those authorized changes.

## Second reading by Q138

The maintainer's independent review approved the theorem's mathematical
statement and identified H2, repaired above. This dispatched single-worker
repair adds the definition-node binding to the existing recursive construction.
Independent review of this repaired delivery remains with the maintainer.

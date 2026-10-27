## Worker report

The module `Sheaf.AlgebraicGeometry.AffineGroupCentreBaseChange` states
`AlgebraicGeometry.exists_affine_group_centre_baseChange`, with one postponed theorem
and no new definitions. The node's mathematical statement is unchanged. Four already
landed definition nodes are added to `stmt_deps` to cite the existing interfaces used.
No dependency is redefined or repaired, and no new node is needed.

Source read: the local Milne Algebraic Groups (2017) PDF, printed pp.33--35,
Proposition 1.92 and the following paragraph. The source explicitly tests all R-algebras
R', defines Z(G) as C_G(G), and states compatibility with extension of the base field.
The source also warns that Z(SL_p) can be the nonreduced group mu_p.

Hypotheses and clauses, read against the node:

- A field k is `{k : Type u} [Field k]`.
- A k-group scheme is `G : Grp (Over (Spec (.of k)))`: the bundled recorded `GrpObj`.
- Affineness and finite type are exactly `hG : SolvableGroupStructure.IsAlgebraic G`:
  its body is `IsAffine G.X.left ∧ LocallyOfFiniteType G.X.hom ∧ QuasiCompact G.X.hom`.
- The introductory references to smoothness, connectedness and geometric connectedness
  are terminology, not assertions that G is smooth or connected. The theorem adds
  neither such hypothesis. Their recorded modules remain public statement imports.
- Representability is the existential `Z : Grp (Over (Spec (.of k)))`, `i : Z ⟶ G`,
  followed by `IsClosedSubgroupScheme i.hom.hom` and the equality of image subfunctors.
  Closedness gives injectivity on every A-point by the recorded subgroup definition;
  image equality therefore gives the representing bijection, naturally by composition.
  `SolvableGroupStructure.IsAlgebraic Z` records the ambient affine finite-type convention
  for the representing centre as well.
- Closed subgroup scheme is the recorded `IsClosedSubgroupScheme i.hom.hom`, with the
  actual group-scheme homomorphism i, rather than an arbitrary scheme map.
- Normality is the recorded `IsNormalSubgroupScheme i.hom.hom`.
- Commutativity is the recorded `IsCommMonObj Z.X`, i.e. multiplication is invariant
  under the interchange of factors as morphisms, including on nonreduced test rings.
- The scheme-theoretic centre functor is
  `ReductiveTorusCentralizer.centralizerPoints (𝟙 G) A`. Its existing definition tests
  every `B : Type u`, `[CommRing B]`, `[Algebra k B]`, every `f : A →ₐ[k] B`, and every
  `t : StandardGroupSchemes.affine k B ⟶ G.X`, and requires
  `Commute (StandardGroupSchemes.map k f ≫ g) (t ≫ (𝟙 G).hom.hom)`.
  This is precisely every A-algebra extension and every point over it: an A-algebra
  structure supplies such a k-algebra map and conversely. There is no injectivity,
  fieldness, finite-generation or reducedness restriction on these algebra maps.
- The first equality, for every commutative k-algebra A, identifies that set with
  `Set.range (fun z : StandardGroupSchemes.affine k A ⟶ Z.X ↦ z ≫ i.hom.hom)`.
  Thus it uses the inclusion's actual image, not an unrelated abstract bijection.
- Every field extension K/k is `∀ (K : Type u) [Field K] [Algebra k K]`. This includes
  the identity extension and inseparable or transcendental extensions, in any universe
  containing the input field and the extensions. No algebraicity or separability is added.
- Z(G)_K and its inclusion are literally
  `(MultiplicativeType.baseChange (K := K)).obj Z` and
  `(MultiplicativeType.baseChange (K := K)).map i`. That existing functor is
  `(Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).mapGrp`, so both
  underlying schemes and group operations are the canonical scalar extensions.
- The base-change clause asserts that this very inclusion is a closed normal subgroup
  and its domain is commutative, and identifies its image on every commutative K-algebra
  A with `centralizerPoints (𝟙 ((MultiplicativeType.baseChange (K := K)).obj G)) A`.
  This is the natural equality Z(G)_K = Z(G_K) as closed subgroup schemes of G_K:
  closed subschemes are identified by their image subfunctors on all affine tests.
  In affine coordinates, testing C/I and C/J recovers both ideal containments, so this
  equality retains the scheme structures and not merely their point sets over fields.
  No chosen representative or choice of isomorphism changes the comparison map.

Dependency declarations used, with their source modules and signatures read:

- `Mathlib.Algebra.Field.Defs`: `Field` (def-weil-field).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.Grp`, `GrpObj`;
  `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`: `CategoryTheory.Hom.group`; `Mathlib.CategoryTheory.Monoidal.Mon`:
  `IsMonHom` and `IsCommMonObj` (def-sc-group-scheme).
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `AlgebraicGeometry.IsSubgroupScheme`, `IsClosedSubgroupScheme`,
  `IsNormalSubgroupScheme` (def-sc-group-scheme-subgroup).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`
  (def-weil-finite-type-morphism), used through the existing IsAlgebraic body.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth` and
  `SmoothOfRelativeDimension`; `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`
  (def-sbc-smooth-morphisms and def-weil-connected-scheme), the contextual terminology.
- `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`:
  `AlgebraicGeometry.ReductiveTorusCentralizer.centralizerPoints`, specialized to
  `i = 𝟙 G` (def-sfb-reductive-torus-centralizer-terminology).
- `Sheaf.AlgebraicGeometry.SolvableGroupStructure`:
  `AlgebraicGeometry.SolvableGroupStructure.IsAlgebraic`
  (def-sfb-solvable-group-structure).
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`:
  `AlgebraicGeometry.MultiplicativeType.baseChange`
  (def-sfb-tori-multiplicative-type).
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`:
  `AlgebraicGeometry.StandardGroupSchemes.affine` and `map` (def-sc-gm-ga).

Available proof interfaces are imported: GammaSpecAdjunction, Proper (including
separatedness), the subgroup module, and the public imports providing Spec, pullbacks,
finite type and closed immersions. The existing DAG proof dependency
`lem-sfb-constant-source-closed-factorization-locus` has no Lean or mathlib declaration
recorded in this read checkout, so no module import can yet be added for it. It is
preserved in `proof_deps` and explicitly cited in the complete five-step proof docstring.
It is only a proof dependency: the statement above uses no missing declaration from it.

Edge cases checked before writing: the trivial group (centre all of it); arbitrary
commutative groups; constant nonabelian finite groups; mu_p and the centre of SL_p in
characteristic p; nonreduced test algebras; the zero test algebra (permitted by CommRing);
identity, inseparable and transcendental field extensions. A group scheme cannot be
empty because of its unit section, so no Nonempty or connectedness hypothesis is needed.
The shared universe is the existing small-algebra convention of the recorded interfaces;
it may be increased to accommodate any given field extension, and never quantifies only
in a universe smaller than the base field. The all-algebra condition distinguishes the
scheme-theoretic centre from a reduced centre or the abstract centre of G(k).

Searches actually run (logged by msearch.py for this item):

- LeanFinder: "The scheme theoretic center of an affine finite type group scheme is a
  closed normal commutative subgroup scheme and commutes with field base change".
  Eight abstract-group hits, including Subgroup.center and Subgroup.instNormalCenter;
  no group-scheme representability or scalar-extension statement.
- Loogle: `"GrpObj", "center"`: zero hits.
- Mathlib grep: `center|centre|centralizer`, subdirectory `AlgebraicGeometry`: zero hits.
- LeanSearch: "scheme theoretic centre affine algebraic group closed subgroup extension
  of scalars": eight hits, including Subgroup.center, SpecialLinearGroup.mem_center_iff,
  Algebra.IsCentral and AffineScheme; none is the required statement.
- `rg` of project WeilConjectures and Sheaf for centre/center/centralizer, and the exact
  item-id `grep` in WeilConjectures: no existing theorem for this item. The upstream
  GeneralLinear/ClosedSubgroup centre concerns reduced groups with radical ideals over
  algebraically closed fields; it cannot replace this arbitrary-characteristic,
  possibly nonreduced centre. Project search found the reusable centralizerPoints,
  IsAlgebraic and baseChange declarations above, so no duplicate definition is created.
- DAG search of the six original statement dependencies, the four added definition nodes,
  and dag/lean_names_upstream.json confirmed ownership and absence of an exact theorem.
  No new mathematical notion or new node was introduced, so no new-node searches apply.

No statement correction, disputed assertion, hollow definition or extra axiom is present.
The only postponed proof is `AlgebraicGeometry.exists_affine_group_centre_baseChange`.
Initial scompile.py validation passed both sandbox and library compilations without
errors or warnings; final compilation and delivery preflight follow below.

## Second reading by Q58

Author's separate second reading for dispatcher delivery; this is not an independent
review. Reopened the node and full file after the first compile. Matched Field k, the
bundled group structure, affine finite type, all-algebra centre condition, closedness,
normality, commutative multiplication, and every field extension against their Lean
clauses. Checked that the second range uses the mapped inclusion, not a freshly chosen
map, and that its centre condition is over K, not over k. The all-algebra quantification
in centralizerPoints includes arbitrary maps and nilpotents, so testing only geometric
points has not slipped in. Smoothness and connectedness are not imposed. Added the
explicit `IsAlgebraic Z` conclusion to record the ambient affine finite-type convention
for the represented centre. No mathematical statement changed, and no other mismatch
was found. The unchanged five proof steps are carried in the theorem's docstring.
The maintainer's independent review remains the independent reading of this delivery.

Final validation: scompile.py compiled the final module in both sandbox and library
modes, exit 0 with no diagnostics. The sandbox request took 146.4 seconds wall time
including slot acquisition; the wrapper reported success, not a compiler timeout.
The library compile took 6.3 seconds. No time limit was changed. Read the current
latest blueprint direct-images statement and proof (3); this auxiliary centre lemma
remains a supporting input through its recorded ancestry, not the unit's own assertion.

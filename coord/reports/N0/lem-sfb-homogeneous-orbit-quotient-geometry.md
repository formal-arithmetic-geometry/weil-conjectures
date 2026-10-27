## Worker report

Item: lem-sfb-homogeneous-orbit-quotient-geometry, group N0, stage 2.
The new module is
`Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousOrbitQuotientGeometry`.
Its two named theorems state the quotient geometry and the canonical orbit
identification. Both proofs are exactly `by sorry`; there are no new definitions,
instances, axioms, or chosen objects. The node is unchanged except for `lean`.
No statement correction, disputed statement, new node or dependency repair is needed.

Source read: Milne, Algebraic Groups (2017), Definition 5.20, Propositions
5.24--5.25, Corollary 5.27, Propositions 7.11--7.12 and 7.17 and Theorem 7.18.
Theorem 7.18 is on printed p.143, as the existing stage-1 review already records;
the inherited source metadata says p.142. No source metadata was edited.
Also read the current blueprint's direct-images proof (3), the item's recorded
auxiliary route toward the Borel quotient, the full item proof and all statement
dependency nodes and their recorded source declarations.

### Hypotheses and clauses

`exists_homogeneous_fppf_quotient` renders the first and last parts of the node:

- Algebraically closed field F: `{F : Type u} [Field F] [IsAlgClosed F]`.
  No characteristic restriction and no selected algebraic closure is imposed.
- Group schemes: `G H : Over (Spec (.of F))` with `[GrpObj G] [GrpObj H]`.
  These are the dependency's actual internal group objects, not abstract groups
  of rational points.
- Affine and finite type, for both groups: `[IsAffine _.left]`,
  `[LocallyOfFiniteType _.hom]`, `[QuasiCompact _.hom]`.
- G smooth and connected: `[Smooth G.hom] [ConnectedSpace G.left]`.
- H any closed subgroup: `(i : H ⟶ G) [IsClosedSubgroupScheme i]`.
  This uses the upstream subgroup notion and supplies its homomorphism and closed
  immersion. There is no normality, smoothness, reducedness or connectedness on H.
- Representing separated finite-type F-scheme: `∃ (Q : Over (Spec (.of F)))
  (q : G ⟶ Q), IsSeparated Q.hom ∧ LocallyOfFiniteType Q.hom ∧
  QuasiCompact Q.hom ∧ ...`.
- q faithfully flat: `Flat q.left ∧ Surjective q.left` is the scheme meaning
  of faithful flatness; it does not incorrectly require q to be affine.
- q(gh)=q(g): the equality between `fst G H ≫ q` and
  `lift (fst G H) (snd G H ≫ i) ≫ μ[G] ≫ q` is an equality of scheme maps.
- The specified torsor isomorphism: `∃ e : G ⊗ H ≅ pullback q q` with
  `e.hom ≫ pullback.fst q q = fst G H` and second projection equal to
  `lift (fst G H) (snd G H ≫ i) ≫ μ[G]`.
  Both projections are fixed, so this is exactly (g,h) ↦ (g,gh).
- The coset presheaf is the existing categorical `coequalizer` of `yoneda.map`
  of projection and right multiplication. Colimits of Type-valued functors are
  pointwise: its value on T is G(T)/H(T), with right multiplication by H.
  No normality is required to form this quotient of sets.
- Sheafification and representability: `Presheaf.IsSheaf ... (yoneda.obj Q)`,
  an arrow `ηq` from that coequalizer, its equation
  `coequalizer.π _ _ ≫ ηq = yoneda.map q`, and bijectivity of precomposition
  with `ηq` for every `Z : Sheaf ... (Type u)`. This is precisely the universal
  property in def-weil-pbc-sheafification, including the canonical map from G.
  The actual topology is `Scheme.fppfTopology.over (Spec (.of F))`.
  Restricting this big-site presentation to affine F-schemes gives exactly the
  stated faithfully flat finitely presented algebra coverings: affine source
  and target give quasi-compactness and quasi-separatedness, so lfp is fp.
  Conversely affine fppf refinement extends the affine sheaf presentation to
  this one. Thus the site expression does not change the quotient notion.
- Every F-point lifts: `Function.Surjective (fun g : 𝟙_ (Over ...) ⟶ G ↦ g ≫ q)`.
- (G/H)(F)=G(F)/H(F): the final iff says two rational points have equal images
  exactly when `∃ h, g₂ = g₁ * (h ≫ i)`. Together with surjectivity this is
  the canonical bijection, not an arbitrary bijection of underlying sets.
  The tensor unit of Over is Spec F with identity structure morphism, so these
  hom types are exactly F-points.

`exists_orbit_stabilizer_quotient_iso` renders the intervening action clauses:

- The same field and G hypotheses occur verbatim.
- X is an F-scheme: `X : Over (Spec (.of F))`; separated finite type is
  `[IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]`.
- The action is the existing Mathlib `[ModObj G X]`. Its morphism is `γ[G, X]`,
  and its fields are the unit and multiplication identities, not an arbitrary
  map of points. `x : 𝟙_ (Over ...) ⟶ X` is the specified F-point.
- The stabilizer is `∃ (K : Grp (Over ...)) (i : K.X ⟶ G)` with
  `IsClosedSubgroupScheme i` and the affine finite-type properties. For every
  `T : Over ...` and `g : T ⟶ G`, the equivalence
  `(∃ h : T ⟶ K.X, h ≫ i = g) ↔ g • (toUnit T ≫ x) = toUnit T ≫ x`
  is exactly the full scheme-theoretic fixing condition. Taking T=Spec A gives
  the node's displayed formula for every commutative F-algebra, including
  nonreduced algebras. The closed subgroup inclusion makes h unique.
- Reduced orbit: `∃ (O : Over ...) (j : O ⟶ X) (a : G ⟶ O)` with
  `IsReduced O.left ∧ IsImmersion j.left`, equality of the range of j with
  the range of the actual orbit map, and `a ≫ j =` that orbit map.
  A reduced locally closed immersion with this range specifies precisely the
  reduced subscheme structure on the orbit, uniquely up to its unique isomorphism
  over X. No reducedness of X or K is assumed.
- The orbit map in those formulas is
  `lift (𝟙 G) (toUnit G ≫ x) ≫ γ[G, X]`, i.e. g ↦ gx.
- Canonical G/K ≅ O: for every Q,q with the same sheafification presentation
  as in the first theorem, `∃! e : Q ≅ O, q ≫ e.hom = a`.
  This fixes gK ↦ gx as a scheme map. It is not merely an isomorphism of
  F-points or an unspecified `Nonempty (Q ≅ O)`. The first theorem applied
  to K, whose needed properties are supplied above, guarantees such quotient
  presentations exist, so the comparison clause is not vacuous.

All universes and variables are explicitly bound; `autoImplicit` is false.
The site is the category of all schemes at the fixed scheme universe, and the
hom sets, coset sets and sheaf values live in Type u. There is no independent
smaller test-algebra universe and no restriction to finite or reduced algebras.

### Dependency declarations used

- def-weil-field: Mathlib.Algebra.Field.Defs, `Field`.
- def-weil-algebraic-closure: Mathlib.FieldTheory.IsAlgClosed.Basic,
  `IsAlgClosed`, as identified in the dependency's mathlib_match; no closure
  extension is part of this node's hypotheses.
- def-sc-group-scheme: Mathlib.CategoryTheory.Monoidal.Grp, `GrpObj`, `Grp`;
  Cartesian.Grp supplies `Hom.group`, and Cartesian.Mon supplies the induced
  multiplication on Hom. The importing upstream GroupScheme.Defs documents
  exactly this specialization to Over (Spec F).
- def-sc-group-scheme-subgroup:
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs,
  `AlgebraicGeometry.IsClosedSubgroupScheme`, extending `IsSubgroupScheme`.
- def-sbc-smooth-morphisms: Mathlib.AlgebraicGeometry.Morphisms.Smooth, `Smooth`.
- def-weil-connected-scheme: Mathlib.Topology.Connected.Basic, `ConnectedSpace`.
- def-pc-morphism-conventions is a convention record, not a declaration. Its
  named Mathlib notions `IsAffine`, `IsSeparated`, `LocallyOfFiniteType`,
  `QuasiCompact`, `Flat`, `Surjective`, `IsImmersion` are used directly.
- def-pc-fppf-site: Mathlib.AlgebraicGeometry.Sites.Fpqc,
  `Scheme.fppfTopology`, induced on Over by
  Mathlib.CategoryTheory.Sites.Over, `GrothendieckTopology.over`.
- def-weil-pbc-sheafification: Mathlib.CategoryTheory.Sites.Sheafification,
  `presheafToSheaf`, `toSheafify`, `sheafificationAdjunction` are imported;
  its equivalent defining universal property is stated explicitly. This avoids
  introducing a new sheafification definition or a HasSheafify assumption.
- def-pc-fibre-product:
  Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback, `pullback`,
  `pullback.fst`, `pullback.snd`; categorical products in Over use the same
  scheme fibre products. These definitions are exported by the other imports.
- Existing additional infrastructure: Mathlib.CategoryTheory.Monoidal.Cartesian.Mod,
  `ModObj`, `Hom.mulAction`; Mathlib.AlgebraicGeometry.Properties, `IsReduced`;
  Mathlib.AlgebraicGeometry.Morphisms.Immersion, `IsImmersion`;
  Mathlib.CategoryTheory.Limits.Types.Colimits and FunctorCategory.Basic,
  the existing pointwise coequalizer construction.

The stated proof dependencies' project modules are imported plainly:
GroupScheme.Separated (`GrpObj.isSeparated_hom`), FppfAffineRefinement
(`Scheme.exists_finite_fppf_affine_open_refinement`) and
AlgebraicSpaceFppfFiniteAffineRefinement
(`AlgebraicSpace.exists_finite_affine_fppf_refinement`). Mathlib proof inputs
are provided by Fpqc, FiniteType, FinitePresentation, QuasiSeparated, Proper,
AlgClosed.Basic and the pullback imports. The two group-geometric proof
prerequisites, lem-sfb-algebraic-group-homogeneous-quotient and
lem-sfb-smooth-group-orbit-geometry, have no recorded declaration on the read
base, so there is no module for them to import yet. They are proof prerequisites
only; the statement does not posit them as extra assumptions or copy them.

### Edge cases checked

- H=1 gives Q=G and the diagonal kernel pair; H=G gives Q=Spec F.
- GL₂/B gives the usual P¹ quotient, so no normality or affine quotient
  requirement can be imposed. The quotient here is only separated finite type.
- In characteristic p, G_m/μ_p is covered: H may be nonreduced, the quotient
  map need not be smooth, and the rational-point map is still surjective.
- The same inseparable phenomenon in an action must use the full stabilizer,
  not its reduction (Milne Remark 7.14). The formula on all test schemes retains it.
- Trivial action gives K=G and O=the reduced rational point. Nonreduced X is
  allowed, for example a trivial action on a scheme with nilpotents.
- X empty has no x, as the source requires; G empty is excluded by the group
  identity and by connectedness. The trivial connected group is included.
- Nonreduced and disconnected H, positive characteristic, and zero-dimensional
  groups/subgroups are not silently excluded by any binder.

### Searches

All msearch calls used the prescribed wrapper and are logged in searches.jsonl.

- leanfinder: "The fppf quotient of a smooth affine algebraic group by any closed
  subgroup is represented by a separated finite type scheme and identifies reduced
  orbits with quotients by stabilizers". Eight hits concerned Galois categories,
  abstract/topological group quotients and invariant rings; none states this result.
- loogle: "CategoryTheory.GrpObj, AlgebraicGeometry.IsClosedSubgroupScheme".
  No hits; the second identifier is upstream-only and unknown to Loogle.
- leansearch: "The quotient of an affine group scheme by a closed subgroup in the
  fppf topology is representable and is isomorphic to the reduced orbit for a
  stabilizer". Eight abstract group-action/coset hits, including
  MulAction.orbitEquivQuotientStabilizer; none is a scheme statement.
- msearch grep: "homogeneous|stabilizer|coset", AlgebraicGeometry. The first
  25 hits concern homogeneous ideals/projective spectrum, not this statement.
- Direct rg in WeilConjectures and Sheaf for homogeneous, orbit/quotient,
  stabilizer, coset and action definitions: inspected GroupScheme.Defs,
  GroupScheme.AffineNormalQuotientGeometry, SolvableHomogeneousProperSubschemes,
  TorusCentralizerBorelIntersection and SchemeActionTorsorGroupoids. The normal
  quotient predicate requires a group target and a normal kernel, so it cannot
  express this quotient by an arbitrary subgroup. The action module confirms
  that Mathlib ModObj is already the shared action notion. No duplicate notion
  is introduced: cosets, the sheafification universal property, and the reduced
  locally closed orbit are expressed directly using existing categorical and
  scheme notions, with no helper definition.
- Exact item-ID search in WeilConjectures found no declaration; Sheaf hits are
  proof-plan citations only. Exact proposed theorem-name search in WeilConjectures,
  Sheaf and dag/lean_names_upstream.json found no existing declaration.
- DAG definition-statement scan for group scheme actions, homogeneous spaces,
  coset presheaves and scheme-theoretic stabilizers found no separate applicable
  definition beyond the existing group/subgroup and categorical notions used here.

### Validation

scompile.py compiled both sandbox and final module successfully (11.6 s and
7.9 s respectively), with no errors or non-sorry warnings. An initial compile
reported an incorrect Mathlib.AlgebraicGeometry.Reduced import; it was corrected
to the existing Mathlib.AlgebraicGeometry.Properties before the successful compile.
The module has no diagnostic commands, local notation, private definitions or
file-local instances. The JSON signature is extracted verbatim from the first
theorem, and lean.declarations records both theorem statements.

## Second reading by N0

I reopened the node and the final module for a second self-reading. No other
agent was started, in accordance with the dispatcher's instruction; independent
review is the maintainer's delivery review.

Matched the field, affine/finite-type groups, smooth connected G, arbitrary
closed H, separated finite-type quotient, flat surjection, right invariance,
and both torsor projections against the first theorem. Its canonical unit and
universal bijection express the actual coset sheafification; its rational-point
surjectivity and fibre criterion express exactly the final equality of cosets.
Matched separated finite-type X, its genuine internal action and rational x
against the second theorem. Its full fixing condition specifies the closed
stabilizer; reducedness, immersion and exact range specify O. The unique
isomorphism equation fixes the orbit map. In particular neither H nor K is
assumed normal/smooth/connected/reduced, and X need not be reduced.
The two statements jointly cover every original clause. No mathematical
mismatch or node correction was found. The incorrect import path was the only
repair found during compilation and is fixed in the final file.

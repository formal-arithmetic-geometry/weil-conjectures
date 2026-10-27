## Worker report

The module `Sheaf.AlgebraicGeometry.PointedTorsorLineCharacterDescent` states
`AlgebraicGeometry.PointedTorsor.classification` with `sorry`. Its helper definitions belong
to the canonical classification notion explicitly introduced by this node: the rigidified
pairs, their quotient K_q(T), and the tensor, pullback and character-multiplier formulas.
All helpers contain actual data or explicit predicates; no data is chosen from an existence
statement. `Classification` bundles the conclusions and is not a hypothesis of the theorem.
The theorem asserts its nonemptiness; it does not choose a classification from that assertion.
There are no new DAG nodes, dependency repairs or statement corrections.

Source read: `literature/stacks-project/descent.tex`,
`proposition-fpqc-descent-quasi-coherent` (023T, lines 1583 onward), states effectivity and
full faithfulness for quasi-coherent modules under an fpqc cover. The same file's
`lemma-finite-locally-free-descends` (05B2, lines 2004 onward) states descent of finite local
freeness. The additional normalized-frame, character, tensor and naturality calculations
are the eight proof steps in this node, which were read and are included in the theorem's
docstring. The source explicitly identifies this as an agent-derived specialization;
it is not claimed that 023T itself states the character classification.

Hypothesis-by-hypothesis rendering:

- `k : Type u` with `[Field k]` is the arbitrary base field. `X Y G : Over (Spec (.of k))`
  are the specified k-schemes; the slice-category morphism `q` is a k-morphism.
- `[GrpObj G] [IsCommMonObj G]` are the recorded finite commutative group-scheme notions;
  `hfinite : IsFinite G.hom` is finiteness over k.
- `hqfinite`, `hqflat`, `hqsurj` use exactly `IsFinite q.left`, `Flat q.left` and
  `Surjective q.left`, respectively, with no smoothness or etaleness assumption.
- `a : X ⊗ G ⟶ X` is the actual right action, not a set action on geometric points.
  `hunit` and `hassoc` state its unit and right associativity on every scheme-valued
  point. Yoneda makes these exactly the two action diagrams.
- `hquot` says q is invariant; this is the well-definedness of the displayed map into
  the fibre product. `htorsor` says that every pair of scheme-valued points with equal
  q-image has a unique g carrying the first to the second. Together these say exactly
  that `(x,g) ↦ (x,xg)` induces the displayed isomorphism, by Yoneda. The tests use all
  schemes over k, rather than only fields or rational/geometric points.
- `x₀ : 𝟙_ (Over (Spec (.of k))) ⟶ X` is the k-point. `axis x₀ T` is x₀ × id_T.
  The composite `(axis x₀ T).left ≫ (q ▷ T).left` is y₀,T, so y₀ is not an independent
  point or an additional hypothesis.
- `hfunctions` is bijectivity of the actual ring map `(snd X S).left.appTop` for
  every k-scheme S. Bijectivity of a ring hom is equivalent to its being the stated
  ring isomorphism. This is the structure-induced map on functions, not an arbitrary
  abstract isomorphism of its source and target.

Conclusion-by-conclusion rendering:

- `Pair q x₀` contains the actual module `L`, its `IsInvertible` proof, and an actual
  isomorphism `r : (tensorPullback (x₀ ≫ q)).obj L ≅ 𝟙_ S.Modules`.
  Its `trivial` field is existence of a frame τ whose restriction is exactly r.
  `frameAt` uses the recorded section-normalized compositor and unit multiplication.
- `Pair.Isomorphic` is existence of an isomorphism L ≅ L' satisfying precisely the
  rigidification-preservation equation. `Classes` is `Quot` of that relation, and `K`
  specializes it to q_T and x₀,T. Since being isomorphic is an equivalence relation,
  this quotient is exactly the set of isomorphism classes, without choosing a skeleton
  or adding a frame to the data of a class.
- Tensor is the actual scheme-module tensor. `IsTensor P Q R` requires an isomorphism
  R.L ≅ P.L ⊗ Q.L that preserves the tensor rigidification, using the canonical
  tensor-pullback comparison and unit unitor. `IsUnit P` identifies the actual unit
  module and its canonical rigidification.
- `Classification.group` supplies the commutative group on each K_q(T).
  Its `tensor` field is an iff: a representative R has product class if and only if
  it is this tensor pair. Thus the group operation cannot be an unrelated operation.
  Its `unit` field similarly pins the identity class. The tensor existence assertion
  is included: every element of `Quot` has a representative; applying that fact to
  the group product and the iff supplies an R with the stated tensor graph.
- `Characters G T` is the actual Hom type between the two group objects obtained by
  the Mathlib slice pullback functor's `mapGrp`: G_T and the pullback of the recorded
  Laurent-polynomial multiplicative group G_m,k. It is not a Hom group of abstract
  rational-point groups. `characterGroup` and `character_mul` pin its group law to
  multiplication of the Laurent coordinate on every scheme-valued point. Yoneda
  and the coordinate identification make this exactly the usual character group.
- `equivalence T` is a `MulEquiv` with these exact group laws. It gives bijectivity,
  preserves products and consequently units and inverses.
- `unique_frame` is `∃! τ` satisfying the actual normalization equation, for every
  pair. It neither assumes uniqueness nor forgets the specified rigidification.
- `HasMultiplier` compares the pulled-back frames at x and xg on their common
  pulled-back line. If h expresses equality of their q-images, its `eqToIso`
  transports a section of the common pullback. The equation is
  τ_(xg)(c(m)) = χ(g) • τ_x(m). Consequently τ_(xg) c τ_x⁻¹ is multiplication by χ,
  exactly the node's convention; it is not multiplication by χ⁻¹. The scalar is the
  actual Laurent coordinate, pulled back along g. Quantifying over S and x,g detects
  the full overlap morphism, including nilpotents.
- `multiplier` is an iff between equality with the classifying character and existence
  of this normalized frame with this multiplier. Surjectivity of `equivalence`, and
  representability of quotient classes by pairs, therefore supplies the converse:
  for every character, a descended pair with exactly that trivial-line descent datum.
  Injectivity supplies uniqueness up to rigidification-preserving isomorphism.
- `IsPullback` spells out the actual tensor pullback of L along the parameter map on
  Y, with its specified pulled-back rigidification. `pullback_exists` ensures this
  pair is available for every base map; no preservation theorem is assumed as input.
- `frame_naturality` explicitly says that pulling a normalized frame back gives a
  normalized frame for any rigidification-compatible identification of the pulled
  line. The two square equalities are bound as equality witnesses only to form the
  canonical comparison terms. They are universally quantified, not extra restrictions
  on the theorem's data. `unique_frame` then identifies this with the normalized frame.
- `naturality` identifies the resulting character values on every scheme-valued point
  after every parameter map. This is the equality of base-changed characters by Yoneda.
  The multiplier iff in both directions and uniqueness give base-change compatibility
  for the inverse descent construction as well.

Dependency declarations used, with their source declarations and docstrings inspected:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, its morphisms, `Spec` and `Spec.map`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`; `Monoidal.Mon` supplies `IsCommMonObj`
  and `IsMonHom`. The upstream `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`
  documents this exact slice-category interpretation of the dependency node.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, its
  projections and universal morphisms. The tensor on the slice category is this
  chosen fibre product. `Monoidal.Cartesian.Over` provides the actual group base change.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible`, the scheme-module tensor and its unit.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullback`, `tensorPullbackSectionComp`; the former is publicly
  imported from `WeilConjectures.AlgebraicGeometry.TensorPullback` and has the actual
  inverse-image/change-of-rings/sheafification construction.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, exposing the existing localization tensor;
  no alternative tensor product is defined here.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`:
  `StandardGroupSchemes.multiplicative` and `multiplicativeGroup`, namely the actual
  Spec of the Laurent ring with its Hopf group law. `value` evaluates its coordinate t.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`, `.Flat`, `.UnderlyingMap`:
  `IsFinite`, `Flat`, `Surjective`.
- `WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons`:
  `boundaryPullbackComparison` and `boundaryPullbackTensorIso` are general canonical
  comparisons, despite the module's name: their full signatures have no closed
  immersion or square-zero hypothesis. They are used without restating them.
- Proof imports: `Mathlib.AlgebraicGeometry.Sites.Fpqc` supplies `fpqcPrecoverage` and
  its base-change stability; `WeilConjectures.AlgebraicGeometry.Descent` supplies
  fpqc effectivity/full faithfulness and descent of invertibility;
  `WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor` supplies
  `Scheme.Modules.invertible_pullback_tensor` and its tensor/section compatibilities.

Edge cases checked before and after drafting:

- Empty T and empty test S are admitted. The point x₀ excludes empty X, as in the node,
  but no global nonempty hypothesis excludes empty parameter schemes or opens.
- Nonreduced T, S and infinitesimal finite G are admitted: no reducedness, smoothness,
  separability or geometric-point test replaces an all-scheme test.
- The trivial group and identity torsor remain in scope. Universal constancy plus the
  specified point makes normalized frames unique in this case as well.
- All characteristics are allowed. No order is inverted, and no characteristic-zero
  or prime-to-order condition is imposed.
- Trivial lines and the identity character satisfy the specified unit normalization.
  The multiplier equation was checked by composing τ₂ c τ₁⁻¹, which fixes the sign.
- Every scheme, ring, module, test morphism and universe is explicitly bound;
  `autoImplicit` and `relaxedAutoImplicit` are false. Test schemes use the same
  ambient scheme universe as the base, not an independently smaller universe.

Searches actually performed:

- msearch LeanFinder: `Pointed finite flat group scheme torsor rigidified line bundles
  characters descent`. Eight hits, chiefly `PreGaloisCategory.AutGalois` and
  `AffineSpace.homOverEquiv`; none states pointed torsor line descent.
- msearch Loogle: `"IsMonHom", "Over"`. Two hits,
  `Over.isMonHom_pullbackFst_id_right` and the affine-group pullback instance;
  these provide group-base-change infrastructure, not this classification.
- msearch LeanSearch: `Rigidified line bundles trivialized by finite flat group scheme
  torsor correspond to characters`. Eight hits in `CharacterModule` and `MulChar`;
  these are abstract module duals/arithmetic characters, not group-scheme characters.
- msearch Mathlib grep: `rigidif.*torsor|torsor.*line|character.*descent`. Four hits
  about affine-space lines and normed modules; no scheme descent classification.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for rigidification, torsor, line,
  character and pullback comparison names; `grep -rn` for this item id in
  `lean/WeilConjectures` found no existing statement. Related project results include
  `CharacterPicardIsogenySequence` (different hypotheses and Picard exact sequence)
  and `GroupScheme/AssociatedCharacterLineBundle` (homogeneous quotient presentation).
  `RigidifiedLines` is on algebraic spaces with the different etale module category;
  it is not the scheme Zariski-module pairs explicitly used by this node.
- `rg` of the upstream name table and of Mathlib/upstream/project for the proposed
  `AlgebraicGeometry.PointedTorsor` namespace and `classification` found no clash.
- The suggested example `CompactObject.lean` was opened; its current local source is
  withdrawn and contains no declarations. The delivered file follows the required
  module-mode header, public statement imports and exposed public section.

Validation: the complete module was compiled through the prescribed `scompile.py`
against the live library. The only postponed proof is `PointedTorsor.classification`.
No `STATEMENT-DISPUTED` flag or node fault was found.

## Second reading by Q46

This is the author's second reading, not an independent review; the maintainer supplies
that review. I reopened the node and the completed module. The field, slice schemes,
finite/flat/surjective hypotheses, genuine right-action laws and all-scheme torsor test
match the first paragraph. The universal function map is the actual second-projection
map on global sections. The pair has L, its invertibility, r, and existence of a frame
restricting to r; it does not remember an extra frame. The quotient relation remembers
rigidifications. The group laws are pinned to tensor and unit by iff graphs, and the
character group uses actual base-changed group objects with pointwise multiplication.
The unique-frame field and multiplier iff include both directions of the classification;
computing τ₂ c τ₁⁻¹ confirms the requested positive-character convention. The base-change
fields quantify over arbitrary morphisms and all test schemes. On this reading I added
an explicit `frame_naturality` field so compatibility of the normalized frame itself is
visible, as well as compatibility of character values. All helpers have the owning
node's source/blueprint docstrings, no definitions have postponed data, and the only
theorem proof is `sorry`. The node's original statement and dependency fields are unchanged.

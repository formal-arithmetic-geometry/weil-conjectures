## Worker report

The module `Sheaf.AlgebraicGeometry.AdditiveAffineTorsorSection` states
`AlgebraicGeometry.additive_affine_torsor_section`, with its entire proof `sorry`.
It introduces no definitions. The statement is unchanged; its statement dependencies gain
the already landed node `def-sfb-split-solvable-right-torsors`, whose existing torsor
structure packages exactly the hypotheses. No new nodes or dependency repairs are needed.

Hypothesis and conclusion correspondence:

- The field k is `{k : Type u} [Field k]`.
- An arbitrary commutative k-algebra A is `(A : Type u) [CommRing A] [Algebra k A]`.
  The single ambient universe is the convention of the recorded scheme/group interfaces;
  it is arbitrary and introduces no cardinality, Noetherian, or finite type hypothesis.
- S = Spec A as a k-scheme is `StandardGroupSchemes.affine k A`, defined by `algSpec`
  on `CommAlgCat.of k A`, so its map to Spec k is the algebra structure map.
- The specified additive group scheme is `Grp.mk (StandardGroupSchemes.additive k)`.
  Its underlying scheme is Spec (Polynomial k), and its registered `additiveGroup` uses
  the coordinate substitutions y -> y tensor 1 + 1 tensor y, y -> 0, and y -> -y.
- P and its map to S are `P.space` and `P.projection` in the existing structure
  `RepresentedRightTorsor ... (StandardGroupSchemes.affine k A)`.
- Faithful flatness and surjectivity are exactly `P.flat` and `P.surjective`, using
  Mathlib `Flat P.projection.left` and `Surjective P.projection.left`.
- Finite presentation is `P.lfp`, `P.qc`, `P.qs`: locally finite presentation,
  quasi-compactness, quasi-separatedness. This is the comparison clause in the recorded
  dependency `def-sbc-locally-finite-presentation`, not an extra assumption.
- The right action is `P.action : P.space ⊗ G_a ⟶ P.space`, a morphism of k-schemes.
  `P.one_action` and `P.mul_action` give the right action laws on every test k-scheme.
- The canonical map (p,a) -> (p,p+a) being an isomorphism is exactly `P.torsor :
  IsPullback (fst P.space G_a) P.action P.projection P.projection`. Its commutative
  square also states that the action is over S. This retains the specified action;
  it does not merely assume some abstract isomorphism of the two schemes.
- The conclusion is `∃ e : StandardGroupSchemes.affine k A ⟶ P.space,
  e ≫ P.projection = 𝟙 (StandardGroupSchemes.affine k A)`. The arrow is over k,
  and the equation makes it a section over S. It does not assert uniqueness.
- No reducedness, Noetherian, finite-type-over-k, characteristic, perfectness, or
  nontriviality assumption on A appears.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: `affine`, `additive`, `additiveComul`,
  `additiveCounit`, `additiveAntipode`, `additiveGroup` in `AlgebraicGeometry.StandardGroupSchemes`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat` (equivalent to
  flat stalk maps), and `flat_iff` for the proof plan.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `AlgebraicGeometry.Surjective`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`; the existing torsor structure uses their universal
  property as `CategoryTheory.IsPullback` from its Defs module.
- `Sheaf.AlgebraicGeometry.SplitSolvableTorsorDefinitions`:
  `AlgebraicGeometry.RepresentedRightTorsor`, read in full including every field.

Plain imports record the already stated proof dependencies: `Scheme.fppfPrecoverage`,
`Scheme.fppfPrecoverage_le_fpqcPrecoverage` and fpqc subcanonicity in
`Mathlib.AlgebraicGeometry.Sites.Fpqc`;
`Scheme.exists_fpqc_singleton_affine_refinement` in
`WeilConjectures.AlgebraicGeometry.FpqcSingletonAffineRefinement`;
`Module.FaithfullyFlat.of_comap_surjective` in
`Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`;
`AlgebraicGeometry.pullbackSpecIso` in `Mathlib.AlgebraicGeometry.Pullbacks`;
`Module.FaithfullyFlat.exact_amitsurComplex` in
`WeilConjectures.RingTheory.FaithfullyFlat.Amitsur`. The theorem docstring carries
all four proof steps, the cocycle sign, descent, and verification of the section equation.

Source checked directly with pdftotext: Milne, Algebraic Groups (2017), Definition 2.66,
Example 2.67 and Example 2.72, printed pp.60--61. Example 2.72 explicitly treats an
arbitrary k-algebra R_0 and says its additive torsors are trivial by exactness of the
faithfully flat additive Cech complex. No source-based statement correction was needed.

Edge cases checked before writing: the zero algebra A (empty Spec, hence the unique empty
section); a trivial torsor (its zero section); nonreduced algebras such as k[epsilon]/epsilon²
(the scheme-theoretic square and cocycle identities still apply); arbitrary characteristic
and imperfect k; A of infinite type or non-Noetherian. A is not required to be a field or
nontrivial. P need not be assumed affine: its affineness is not a hypothesis here.
The correction t=h-b has t_2=h_1+c-b_2=h_1-b_1 for c=b_2-b_1.

Searches performed through msearch.py:

- leanfinder: `An additive group scheme torsor over the spectrum of a commutative algebra
  over a field has a section`: eight hits about `AffineSpace`, its structure morphism,
  coordinates and maps; no section theorem for scheme torsors.
- loogle: `AddTorsor, AlgebraicGeometry, IsTorsor`: zero hits, unknown identifier
  `AlgebraicGeometry` in this query.
- grep: `torsor|Torsor|RightAction`, subdirectory `AlgebraicGeometry`: zero Mathlib hits.
- leansearch: `Every additive group scheme torsor over an affine scheme has a section`:
  eight hits including `AddTorsor`, group-extension sections and an affine-limit lemma;
  none is the scheme torsor theorem.
- rg of `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` for
  additive/affine torsor sections: related etale torsors and stabilizer sections, no exact
  theorem. The node id has no upstream hit. Broader scheme-torsor/action search found
  `SplitSolvableTorsorDefinitions`, whose represented right torsor is reused.
  `SchemeActionTorsorGroupoids` uses a distinct left action interface and is unnecessary.

No STATEMENT-DISPUTED issue or node fault was found.

## Second reading by Q94

A second pass by this same dispatcher worker checked the node against the finished signature
and unfolded `RepresentedRightTorsor` field by field: flatness, surjectivity, all three
finite-presentation requirements, right action laws, its cartesian square, and the section
equation are retained. The cartesian square has the order (first projection, action), so it
specifies precisely (p,a) -> (p,p+a). No hypothesis or clause was added or omitted.
No independent subagent was started, as explicitly required by the dispatcher's brief;
the maintainer performs the independent review of this delivery.

Validation: scompile.py checked the delivered file in both sandbox and library module
modes successfully, with no errors or unexpected warnings.

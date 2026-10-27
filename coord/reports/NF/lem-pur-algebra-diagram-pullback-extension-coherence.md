## Worker report

The module `Sheaf.CategoryTheory.AlgebraDiagramPullbackExtensionCoherence` states
`CategoryTheory.AlgebraDiagramPullback.algebraDiagramPullbackExtensionCoherence`.
Its sole postponed proof is the theorem's `sorry`; the docstring reproduces all
six proof steps and their dependencies. Helper records package the normalized
maps of this node, on the existing categories, tensor and coefficient functors.
Every helper definition has actual data and a source/blueprint docstring. The mathematical statement is unchanged. The repair adds a definition-node record
for the already published tensor-normalization definitions, using `existing: true`. The live stage-1 split/review is not a stage-2 Lean delivery: the node had
no `lean` field when read.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The small index category J is `I : Type u` with `[SmallCategory I]`; the sites
  presenting X and Y are `X`, `Y`, `KX`, `KY`, small in the module universe `u`.
  Coefficients are `A : Type u` with `[CommRing A]`. The derived Hom universe `w`
  is independent of `u`, with the four explicit `HasDerivedCategory.{w}` binders.
  Larger ambient sites are represented by the small sites stipulated by the node.
- A geometric morphism is the sheaf adjunction `adj : F ⊣ G` with
  `[PreservesFiniteLimits F]`. `hInv`, `hDir`, `hAdj` identify its induced geometric
  morphism on entire diagram sites with componentwise inverse/direct images and
  their adjunction, written inline through `diagramSiteSheafEquivalence`,
  `Functor.whiskeringRight`, `Adjunction.whiskerRight`, and `Adjunction.comp`.
  Their parenthesization is exactly the previous helper definitions.
- `diagramConstantRing I Y KY A` and its X version are the actual `constantSheaf`
  on `diagramSiteTopology I _ _`. Vertical sheafification identifies them with
  the diagonal constant ring sheaf. `HasCanonicalConstants` fixes the structural
  identification on every constant scalar; it excludes an unintended twist by
  an automorphism of A. `[IsIso g.coefficient]` expresses the canonical constant
  ring identification, not flatness of the algebra extension.
- `d : CoefficientSquare g` supplies the commutative algebra sheaf `d.R'` on the
  Y diagram site, its algebra structure `d.sourceMap`, the X sheaf `d.S'`, and
  `d.targetMap`. Its inverse-image graph and square equations retain the actual
  compatible algebra structures. `[IsIso d.coefficient']` states
  `B_X = u^{-1} B_Y` up to its specified ring isomorphism. The structural maps
  `d.sourceMap`, `d.targetMap` have no invertibility or flatness hypothesis.
- A sheaf of modules over `d.R'` or `d.S'` on this product site is the semilinear
  strict module diagram: the horizontal restrictions use the actual algebra
  transitions. `Modules` is the dependencies' abbreviation for the recorded
  `ringedSiteModules`, hence Mathlib `SheafOfModules`; no module category is
  redeclared. Complexes are indexed by all integers, and the derived categories
  are the ordinary `DerivedCategory`, with no boundedness restriction.
- `Result` returns `ExactPullback` for g and its changed-coefficient pullback and
  `ExactRestriction` for both algebra structure maps. These exactness facts are
  conclusions, not additional input assumptions. Thus `mapDerivedCategory` is
  the canonical exact localization representing G_A, G_B and U_Y, U_X. The
  ordinary inverse/direct adjunctions are part of the existing `RingedPullback`
  input; the equations concern their canonical derived left adjoints.
- `ScalarDerivedPresentation.model` is the existing
  `DerivedChangeOfRingsCochainModel`. It includes the genuine left-derived
  universal property and K-flat counit. `ordinary` and `ordinary_hom` identify
  its ordinary functor with the existing `extensionFunctor` on the specified
  objects. `tensor.iso`, normalized by `tensor.pure`, is the actual ordinary
  underlying tensor/scalar-extension identification. `tensor.total` is built
  from Mathlib's termwise lift and the published single-factor total comparison.
  `underlyingIso` and `tensor_model` identify this same derived extension with
  the published derived tensor by B[0], resolving both factors before comparison.
  The coefficient resolution Q is allowed to map to a nonflat B[0].
- The scalar-extension unit i is `ScalarDerivedPresentation.adj.unit`;
  `unit_model` fixes it on every flat-term K-flat representative to the termwise
  ordinary `extensionAdjunction.unit`, with the explicit identity/composition
  comparisons for functors on complexes. No assertion makes this unit invertible.
- `Coherence.ordinaryRestriction`, `restriction_generators` specify the scalar
  unit map on all generalized inverse-image generators. Linearity and the
  invertible structural ring maps give the multiplication inverse. The derived
  `restriction` is the natural isomorphism b; `restriction_model` fixes it as
  the localization of that ordinary map on every complex.
- `Coherence.extension` is the natural isomorphism c. `extension_model` fixes its
  representative through the existing `kappa g kg d kd`, the balanced scalar
  association of the cochain-coherence dependency. The model is imposed on every
  flat-term K-flat complex and uses the actual derived counits and exact
  factorization maps. It is not an arbitrary isomorphism of abstract endpoints.
- `Coherence.ambient` and `ambient_model` use the dependency's `Phi`, `Psi` and
  `IsNormalized` for the actual pullback/tensor comparison, independently on
  simultaneous resolving factors. `beta_generators` fixes the coefficient
  comparison G_A B_Y = B_X on all generators. `derivedCoefficientIso` constructs
  its degree-zero derived comparison using exact factorization and `single`.
  `theta_ambient` defines the intended identification of `theta`: first identify
  underlying scalar extension with tensor, then the normalized ambient tensor
  comparison, then this coefficient isomorphism, then the target tensor/scalar
  identification.
- The first displayed equation is exactly `Coherence.tensor_coherence`:
  `restriction.hom.app (source.model.T.obj M)` followed by
  `U_X.map (extension.hom.app M)` equals `theta.hom.app M`.
  The second is exactly `Coherence.unit_coherence`: G_A applied to the source
  adjunction unit followed by theta equals the target adjunction unit at G_A M.
  Both are morphism equalities in the derived category of the entire diagram
  site, not pointwise cohomology statements.
- All comparisons are natural isomorphisms, so naturality in every derived M is
  part of their types. `CoefficientNaturality` quantifies over every compatible
  second algebra square and every compatible pair of ring maps. The maps hY,hX
  are fixed sectionwise to those actual ring maps. `scalarUnderlyingMap` is
  constructed by applying the existing derived tensor to their B[0] maps,
  conjugating by the normalized underlying tensor isomorphisms. The theta square
  and both unit equalities express compatibility with these maps; combined with
  `tensor_coherence` these also give compatibility of the displayed composite.
  No coefficient-change map is left arbitrary.
- No boundedness, flatness of B/A, perfectness, quotient, or completeness predicate
  occurs. Flatness predicates only select representatives in normalization
  equations, whose availability is the K-flat-resolution dependency.

Dependency declarations used (all signatures and docstrings read):

- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`
  and `constantCommuteCompose`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`.
- `Sheaf.CategoryTheory.DiagramSiteRealization`:
  `CategoryTheory.exists_diagramSite_realization`, `diagramSiteTopology` and the
  retained actual horizontal maps of its sheaf equivalence.
- `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`:
  `CategoryTheory.CochainPullback.cochainPullbackTensorCoherence`, and its public
  `RingedPullback`, `Comparison`, `CoefficientSquare`, `changed`, `Modules`,
  `Complex`, `restrictionFunctor`, `extensionFunctor`, `extensionTmul`,
  `extensionAdjunction`, `generator`, `pull`, `extend`, `restrictComplex`, `kappa`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and its existence theorem.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`;
  its retained `SheafOfModules.PullbackTensorCanonical.canonicalDerivedTensor`,
  `canonicalRepresentativeIso`, `Phi`, `Psi`, `IsNormalized` use the published
  K-flat-derived tensor, without selecting a new tensor.
- `Sheaf.Paper.PullbackTensorCanonicalShiftUnit`: the plain definitions
  `SheafOfModules.PullbackTensorCanonical.canonicalDerivedTensor`,
  `canonicalRepresentativeIso`, `Phi`, `Psi`, and `IsNormalized`, now recorded by
  `def-pur-derived-tensor-pullback-normalization`, supply the representative
  characterization used in `ambient_model`. No consequence of the shift-unit
  theorem is used to state this item.
- `Sheaf.Algebra.Homology.ExactPullbackSignedComparison` remains a plain proof
  import, corresponding to the unchanged proof dependency. No `ExactPullbackSigned`
  declaration occurs in the signature.
- `Sheaf.CategoryTheory.DiagramSiteSheafEquivalence`:
  `CategoryTheory.diagramSiteSheafEquivalence` gives the actual diagram-site
  equivalences used inline in the three componentwise geometric binders.
  `Mathlib.CategoryTheory.Adjunction.Whiskering` supplies `Adjunction.whiskerRight`.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `CategoryTheory.Functor.mapDerivedCategory`, `mapDerivedCategoryFactors`.
- `Mathlib.Algebra.Homology.Additive`: termwise natural-isomorphism and
  identity/composition comparison constructions. The dependency
  `WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle` supplies
  `CochainComplex.mapBifunctorSingle₂Iso`.
- All node proof-dependency modules with Lean records are imported. The
  localization leaf uses Mathlib's `CategoryTheory.Localization.lift` and
  natural-transformation uniqueness. The metatheoretic size convention is
  rendered by the explicit universes, smallness, and localization instances.

The returned packet's two inappropriate theorem statement dependencies are removed:
`lem-pur-diagram-ring-restriction-pushforward` is no longer imported, because its
three plain geometric helpers are expanded inline; and
`lem-pur-exact-pullback-signed-comparison` is kept only in `proof_deps`, with a
plain import. The only added statement dependency is the definition node
`def-pur-derived-tensor-pullback-normalization`, whose existing declarations are
used directly. All original statement dependencies and all proof dependencies
remain. No mathematical statement correction is made.

Edge cases checked before writing: I empty; I terminal; identity geometric
morphism with B=A; zero complexes; zero coefficient ring; point-site
A=Z, B=Z/2, M=Z/2, where derived tensor retains its nonzero Tor term. None is
excluded by the signature. The unit is never required to be a quasi-isomorphism.
The independent derived Hom universe w is retained. Horizontal arrows need not be
isomorphisms: all morphisms are morphisms of the actual module sheaves on the
whole diagram site. The normalization of constants excludes noncanonical
coefficient automorphisms while allowing every geometric morphism in the node.

Searches for an exact existing statement:

- `msearch.py ... leanfinder "Derived scalar extension of strict diagrams commutes
  with inverse image of sheaves and preserves the scalar extension unit"`:
  ordinary sheaf pullback/scalar-extension declarations, no normalized unbounded
  strict-diagram statement with the two equations.
- `msearch.py ... loogle "SheafOfModules.restrictScalars,
  CategoryTheory.CochainPullback.scalarAssociation"`: no result; the project
  scalar-association name is not in that Mathlib search service.
- `msearch.py ... grep
  "pullback.*[Ee]xtendScalars|[Ee]xtendScalars.*pullback|pullback.*[Rr]estrictScalars"`:
  no result.
- `msearch.py ... leansearch "Derived extension of scalars and pullback of ring
  sheaf module diagrams commute with the canonical tensor comparison and scalar
  units"`: ordinary `ModuleCat.extendScalars`, `ExtendScalars.obj'`, sheaf
  pullback and pseudofunctor comparisons; none is this statement.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for algebra-diagram
  pullback/extension names and related scalar normalization; no exact match.
  `grep -rn` for this node id in `lean/WeilConjectures` had no match. The nearby
  pro-etale scalar normalization is a narrower scheme/coefficient statement.
- The recorded dependency sources were read locally; current server source was
  checked with `scompile.py --source` when local reducibility attributes differed.

Source checked: `literature/stacks-project/sites-cohomology.tex`, Tags 07A4
(`lemma-pullback-tensor-product`) and 0G7E (`lemma-pullback-K-flat`), together with
all six node proof steps and the cochain/scalar interfaces. No disputed statement
or source fault was found.

Elaboration helpers `scalarTensorFunctor` and `scalarTensorComparison` are exactly
specialization of the published bifunctor and its identity identification.
`scalarCochainUnit` composes the existing identity, lifted unit and composition
comparisons. `IsNormalizedScalarUnit` and `IsNormalizedScalarTensor` name the two
representative equations used in the presentation record. Separating their
signatures avoids repeated expansion of localization/tensor data in dependent
record elaboration; it changes no mathematical construction.

`ExtensionComparison` only names the type of c between the specified derived
functors; `IsNormalizedExtension` is its balanced-representative equation.
These belong to the same canonical comparison data and add no mathematical
hypothesis or independent notion.

## Repair of return C1/H2

1. `lem-pur-diagram-ring-restriction-pushforward` was cited for plain definitions,
   not for its theorem. The permitted inline alternative is implemented:
   `hInv` is `(E_Y.functor ⋙ whisker F) ⋙ E_X.inverse`, `hDir` is
   `E_X.functor ⋙ (whisker G ⋙ E_Y.inverse)`, and `hAdj` is
   `(E_Y.toAdjunction.comp (adj.whiskerRight I)).comp E_X.symm.toAdjunction`.
   This is verbatim expansion of the three existing helpers, with the same
   parentheses; no new comparison or adjunction is chosen. The inappropriate
   statement dependency and public import are removed.
2. `lem-pur-exact-pullback-signed-comparison` is removed from `stmt_deps`, retained
   unchanged in `proof_deps`, and its import is plain. The five definitions really
   used in the statement now have the definition-node owner named below. Their
   already published module is directly public-imported. Under §1(A)/§5's
   explicit `existing: true` option, the new definition node records the existing
   definitions instead of copying or reimplementing them. Its primary declaration
   is `IsNormalized`, not the shift-unit theorem or a `.choose` from that theorem.

## New nodes

`def-pur-derived-tensor-pullback-normalization` records the existing stable tensor
and representative aliases, the actual composites `Phi` and `Psi`, and the
predicate `IsNormalized` from `Sheaf.Paper.PullbackTensorCanonicalShiftUnit`.
The source is Stacks 07A4 and its simultaneous K-flat representative square.
The definition's inputs are arbitrary `L`, `epsilon` and `tau`; its assertion is
exactly the universal representative equation, including the four target
resolving witnesses. It makes no existence, uniqueness, shift or invertibility
assertion. `canonicalDerivedTensor` is exactly `KFlatFixedTensor.derivedTensor`,
and `canonicalRepresentativeIso` returns its existing `representativeIso`.
The full explicit site and coefficient universes remain those of the published
source. The node is `existing: true`, as §5 requires for already existing project
definitions, so it needs no duplicate Lean module. Its dependencies name the
existing cochain presentation and derived-tensor representative definition nodes.
Searches (also recorded in the node): LeanSearch returned eight unrelated
pullback/flatness results; LeanFinder returned eight cartesian/over-category
results; Mathlib grep returned zero hits. The project/DAG grep found these five
plain definitions only in the existing shift-unit module and its theorem's helper
inventory, with no separate definition node for the normalization predicate.
`blueprint_refs.py search "normalized derived tensor pullback"` returned zero.
Thus no duplicate mathematical construction or theorem node is introduced.

## Self-check by NF

This dispatcher worker is explicitly instructed not to start other agents; the
maintainer's independent review supplies the independent reading. This self-check
re-read the current node and file, and compared the inline binders against all
three helper bodies in `DiagramRingRestrictionPushforward`. Both functor
parenthesizations and the composed adjunction are identical after unfolding.
All other hypothesis and clause correspondences above are unchanged. In
particular, `ambient_model` uses the definition `IsNormalized` with exactly the
existing flat-term K-flat representative equation; it never uses a consequence
of `ExactPullbackSigned` or the shift-unit theorem. Its target resolving witnesses
and its canonical cochain map are retained. The new definition node is a predicate,
so the zero-complex, nonexact `L`, and noninvertible `tau` cases are valid inputs;
the predicate can be false, and no existence conclusion is silently imposed.
All original edge cases remain included. No new `sorry` or data choice was added.

Validation: the repaired module passed `scompile.py` in sandbox form (38.4 s)
and under its final library module name (40.2 s), with no errors or non-sorry
warnings. `deliver2.py --no-push` then checked both the existing-declaration
record and the repaired module, and passed preflight and compilation at dry-run
commit `04474d7eeff`. The item node changes only `lean` and `stmt_deps`; its
statement, proof and proof dependencies are byte-for-byte unchanged as JSON
values. All original statement dependencies remain. The module has no line over
100 characters and its only `sorry` is the main theorem's proof.

## Second reading by NF

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

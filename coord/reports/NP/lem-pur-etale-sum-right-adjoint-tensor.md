## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleSumRightAdjointTensor` states the counit-normalized
etale tensor-transpose identity and its naturality, refinement and Cartesian open restriction
clauses. Every theorem has proof `sorry`; the auxiliary maps are constructed from existing
canonical graph, projection, pullback and conjugacy maps. No statement correction is needed.

Hypotheses and objects:

- Finite commutative coefficients are `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  The site is `Scheme.{u}` with coefficient modules in universe `u + 1`, exactly the
  already recorded ordinary-small-etale framework; no pro-etale or constructible category occurs.
- `U X : Scheme.{u}` and `[IsNoetherian U] [IsNoetherian X]` express the two Noetherian
  schemes. Mathlib's Noetherian scheme condition is equivalent to the node's finite affine
  Noetherian cover (`isNoetherian_iff_of_finite_affine_openCover`).
- `(e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]` expresses separated etale
  finite type. Etaleness already supplies locally finite presentation, hence locally finite
  type; quasi-compactness gives finite type. This does not assume finiteness of e.
- `(c : Compactification e)` is the arbitrary chosen compactification, without a finiteness
  hypothesis on its proper part.
- `DerivedCategoryModule A X` and `DerivedCategoryModule A U` are the ordinary unbounded
  derived categories of sheaves of constant-A modules. All objects K and all morphisms f
  are quantified in these whole categories, without boundedness or constructibility.
- `G` and `adj : rightDerivedLowerShriekOfCompactification ... c ⊣ G` are exactly the
  chosen exceptional right adjoint and adjunction. Quantification makes the statement
  independent of a choice of Brown right adjoint and adds no existence assumption:
  `thm-amb-etale-exceptional-adjoint` supplies such an adjunction.
- `F_e` is `rightDerivedLowerShriekOfCompactification ... c`, `S_e` is
  `(etaleLowerShriek ... e inferInstance).mapDerivedCategory`, and exact e-star is
  `(upperStar ... e).mapDerivedCategory`. Its sum/evaluation adjunction is
  `derivedEtaleLowerShriekUpperStarAdjunction`.

Conclusions and their normalizations:

- The existing `canonicalEtaleCompactSupportComparison A e c` is d, the inverse of the
  explicit derived graph comparison. It is the proper-support-to-sum comparison of the
  cited quasi-finite theorem, with the support-map dependency's graph normalization.
- `etaleTensorRho` is `conjugateIsoEquiv adj sumAdj d.symm`: it constructs the natural
  isomorphism rho from the inverse specified d, rather than choosing an unrelated iso.
- `constantComplex A X` is A_X. Thus `G.obj (constantComplex A X)` is W_e.
  `etaleTensorEta` composes rho at A_X with the existing coefficient pullback unit iso
  `etaleSumPullbackUnitIso A e` and hence is exactly eta.
- The first conjunct of `etaleSumRightAdjointTensor` says, for every natural transformation
  r, that `d.app (G.obj K) ≫ S.map (r.app K) ≫ sumAdj.counit.app K = adj.counit.app K`
  for every K iff r is rho. This includes both the specified counit equation and uniqueness.
- `etaleTensorProjection` is precisely `projectionMapOfCompactification` followed by
  F of tensor with the canonical left-derived-to-exact pullback comparison, the same
  expression used in support-map compatibility (2). `isIso_etaleTensorProjection` records
  invertibility so its inverse is well-defined as an actual inverse, without arbitrary data.
- `etaleTensorInverseTranspose` constructs F of the canonical signed symmetry,
  inverse specified projection, counit at A_X tensored with identity of K, and the left
  unitor. `etaleTensorTau` applies `adj.homEquiv` to that composite. This is the displayed inverse-transpose definition, with no altered projection.
- The second conjunct is tau followed by rho equals tensoring eta in the second
  variable of `derivedTensor`, followed by `derivedTensorRightUnitor`. Lean's composition
  is left-to-right; this is exactly rho composed after tau, and the right unitor after
  identity tensor eta, as in the node. The wrapper is the existing right unitor, with
  no new choice of monoidal structure.
- The third conjunct is the naturality equation for tau under every K ⟶ L. Rho and eta
  already come as natural iso/component constructions, so the equality is of derived
  natural transformations rather than merely of cohomology maps.
- `etaleSumRightAdjointTensor_refinement` uses the canonical left comparison
  `rightDerivedLowerShriekOfCompactificationIso A c d` and its inverse conjugate r.
  Its three clauses are r rho' = rho, r_unit eta' = eta, and tau r = (1 tensor r_unit) tau'.
  It quantifies over every pair c,d, hence in particular every proper refinement and the
  canonical common-refinement comparisons; the result is stronger only in indexing, not
  in mathematical content, since these are the canonical comparisons named by the node.
- `etaleTensorPullbackSquare` composes the exact pullback compositors with the equality
  of the square's boundary (`sq.w`); `etaleTensorRestrictionIso` is exactly the formula
  chi = rho' inverse after square pullback comparison after h-star rho from proof step 8.
- `etaleSumRightAdjointTensor_openRestriction` quantifies over Cartesian open subsquares
  and arbitrary compactifications c,d, including the pulled-back compactification.
  The first conjunct spells out eta' chi_unit = h-star eta with the coefficient-unit
  transport H(g-star A_X ≅ A_X'). The second is h-star tau then chi equals tensor-pullback
  comparison, square comparison tensor identity, identity tensor chi_unit (with that same
  coefficient transport), then tau' at g-star K. Thus the specified tensor equality is
  preserved by restriction, with all suppressed unit identifications supplied explicitly.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`; scheme Noetherian structure
  and finite-cover equivalence from `Mathlib.AlgebraicGeometry.Noetherian`.
- `def-weil-scheme-morphism-properties` is explicitly a collection, not a new notion;
  its finite-type and separation clauses use the existing Mathlib morphism classes.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `WeilConjectures.Compactification.RefinementCategory`: `Compactification.Refinement`,
  with `Compactification` from its existing definitions module.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`: `DerivedCategoryModule`,
  `constantComplex`; the torsion predicate recorded on the broad derived-category node
  is not used to restrict its ordinary ambient category.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`:
  `etaleInverseImageModulesExact`; the existing exact `upperStar` is used in its
  constant-coefficient `Sheaf ... (ModuleCat A)` encoding already used by the dependencies.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`: `derivedTensor`;
  `WeilConjectures.SixFunctors.Etale.Derived.TensorStructure`:
  `derivedTensorLeftUnitor`, `derivedTensorRightUnitor`. These generic wrappers avoid
  the documented expensive kernel comparison between two concrete monoidal instance terms.
  Every tensor morphism in the final module uses the same `derivedTensor` bifunctor.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `rightDerivedLowerShriekOfCompactification`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`:
  `isLeftAdjoint_rightDerivedLowerShriekOfCompactification`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`: `etaleLowerShriek` and
  `etaleLowerShriekUpperStarAdjunction`.
- `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`:
  `derivedEtaleLowerShriekUpperStarAdjunction` (existing degreewise derived adjunction).
- `Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact`: `quasifiniteCompactSupportExact`,
  for the canonical comparison and its normalization and coherence, not a bare chosen iso.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `conjugateEquiv`, `conjugateIsoEquiv`,
  `conjugateEquiv_counit` (the node is a Mathlib leaf, whose `mathlib_match` is its binding).
- `Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility`:
  `etaleSupportMapCompatibility`, `etaleSupportExactUpperTensorIso`; its specified
  compactification projection is reused verbatim, including the exact-pullback transport.
- Added statement dependencies: `lem-asd-compact-support-graph-derived-isomorphism`
  supplies `canonicalEtaleCompactSupportComparison`, whose construction needs its isomorphism
  theorem; `lem-kun-tensor-sym` owns `derivedTensorSymmetry`. The new definition node
  `def-pur-etale-exact-pullback-unit-composition-comparisons` owns the unchanged
  `etaleSumPullbackUnitIso` and `unboundedEtaleUpperStarCompIso`. The coherence and
  unbounded-comparisons theorems are not statement dependencies. Canonical refinement
  comparison is already available through the compact-support dependencies.

Edge cases checked before writing: e = identity (rho and eta give the canonical unit
normalization and tau becomes the unitor); U empty (the source category and all maps are
zero, with the zero object's identity invertible); U = X disjoint union X (evaluation folds
summands and rho is componentwise restriction); zero complex K; arbitrary shifts of K
(the symmetry is the existing signed one and W is normalized to the coefficient unit in
degree zero); open immersions (sum extension is extension by zero); nonfinite proper parts
of compactifications (projection remains the specified proper/open composite); the zero
finite ring (module categories trivial; no nontriviality hypothesis excludes it).

Searches for an existing statement:

- `msearch.py ... leanfinder "etale compact support exceptional right adjoint tensor counit
  sum evaluation"`: eight unrelated condensed-category adjunction results; no match.
- `msearch.py ... loogle "CategoryTheory.conjugateEquiv, CategoryTheory.conjugateIsoEquiv"`:
  four conjugate-iso component lemmas in Mathlib; they provide the generic mate API,
  not this normalized geometric tensor identity.
- `msearch.py ... grep "etale.*(RightAdjoint|rightAdjoint|Tensor)|sumRightAdjoint"`:
  four ring-theoretic etale tensor descent results, no geometric statement.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  `etaleSumRightAdjoint|sumRightAdjoint`: no existing item; the coherence module supplies
  related unit/coherence maps, not tau or this equality, so those existing helpers are reused.
- Read the entire current blueprint locality proof Step 1 and Stacks more-etale.tex
  `lemma-f-shriek-projection` (Tag 0GKF), including its pure-tensor rule. These agree with
  the node; there is no source error or STATEMENT-DISPUTED claim.

Validation: the prescribed server-only `scompile.py` compiled the whole module in its
sandbox and library locations. The final `deliver2.py --no-push` passed server preflight
and clean per-file compilation (dry-run commit `0d1b55bc71a`). There are four postponed
theorems, all with matching blueprint docstrings and natural-language proofs; every data
definition is implemented. No diagnostic `#check`, temporary option, or overlong line remains.
The earlier concrete-monoidal-instance timeout was repaired with the documented existing
tensor/unitor wrappers; the default 60-second limit was never increased.

## Repair of independent return H2

The returned immutable head was `f15896b1ba03`. The saved packet first passed the required
`deliver2.py --no-push` (commit `a799716d62e`). The review nevertheless identified a semantic
dependency ownership defect that the mechanical preflight does not detect. Dropped
`lem-pur-etale-sum-right-adjoint-coherence` and
`lem-amb-unbounded-compact-support-comparisons` from the item's added `stmt_deps`, and
replaced them by the new definition node below. Retained the graph-derived-isomorphism
and tensor-symmetry edges: their recorded declarations are genuine statement ingredients.
No existing dependency node or source module was edited, and the item's Lean file is
byte-identical to the saved returned packet (SHA256: fae2b548de026a14c0c211ad0901ac8062b211818241cfecbda158327727bbfc). Compared
the item with the current shared main snapshot: only `lean` and the authorized added
`stmt_deps` differ. No mathematical statement, hypothesis or conclusion changed.

## New nodes

`def-pur-etale-exact-pullback-unit-composition-comparisons` records the two canonical plain
definitions with `existing: true` in their unchanged published modules. Clause (1) is exactly
`etaleSumPullbackUnitIso`: inverse exact/left-derived comparison at the coefficient unit,
then `leftDerivedUpperStarUnitIso`. Clause (2) is exactly
`unboundedEtaleUpperStarCompIso`: `mapDerivedCategoryNatIso upperStarComp`, then
`mapDerivedCategoryCompIso`. These are the coefficient-unit and pullback-composition
identifications used in blueprint locality Step 1, not assertions of right-adjoint coherence
or compact-support exchange. Both definitions work for arbitrary scheme morphisms and
commutative A; no finite-ring or Noetherian hypothesis was added. The units are the degree-zero
constant complexes. Identity morphisms, empty schemes, zero rings, and unbounded shifted
complexes are allowed.

Searches ran through msearch.py (raw results copied verbatim to `mathlib_searches`): LeanSearch
returned eight generic sheaf/pullback comparisons; LeanFinder returned generic sheafification
comparisons; Loogle did not know `Functor.mapDerivedCategory`, recorded as unavailable for
that identifier; Mathlib grep returned zero matches for the exact unit/compositor names.
Direct rg of WeilConjectures, Sheaf and the DAG found the two definitions in the theorem
modules and no definition node owning this pair. Blueprint searches for `pullback unit` and
`pullback composition` found zero and eight matches respectively, none this definition.
The existing `def-pur-derived-constant-pullback-comparison` concerns the full constant functor
with left-derived pullback, rather than these exact unit and composition comparisons.

## Second reading by NP

This is an explicit self-check: the dispatcher prohibits starting another agent; the
maintainer supplies independent review. Read the saved Lean and the current item node.
Finite A, Noetherian U/X, separated quasi-compact etale e, an arbitrary compactification,
and every unbounded K remain quantified. The conjugate uses d inverse; the iff is the counit
characterization. The projection is support-map (2), and tau's inverse transpose uses signed
symmetry, inverse P, the counit tensored with identity, then the left unitor. The main
equality composes tau with rho and matches identity tensor eta then the right unitor.
The remaining conjunct is naturality in K; the other theorems state all three refinement
identities and both open-restriction clauses including coefficient-unit transport. The
returned review already checked these clauses; this repair changes only ownership of
the two plain definitions. Each clause of the new node matches the complete signature and
body of its named published definition. Both source modules and all theorem proofs stay
unchanged; no extra theorem is assumed through the new definition node.

Repair validation: `scompile.py` compiled the delivered module cleanly in both sandbox
and library locations (15.0 s and 15.9 s). The first repaired dry run identified the new
node's grouped citation formatting as invalid for its field check; separated the two
reference brackets. Its existing-declaration check expects the signature starting at
`def`, so the new node record omits the `noncomputable` modifier exactly as that check
requests. The item signature remains verbatim and unchanged.

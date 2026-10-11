## Worker report

The module `lean/Sheaf/AlgebraicGeometry/EtaleMayerVietoris.lean` states
`AlgebraicGeometry.Etale.etale_mayerVietoris`, with one `sorry` and no definitions.
The node is unchanged except for `lean`.

Hypothesis and clause correspondence:

- A scheme X: `(X : Scheme.{u})`; no finiteness, separation, or characteristic hypothesis.
- Open subschemes U and V: `(U V : X.Opens)`. Their intersection is `U ⊓ V`, their schemes
  are `.toScheme`, and their open immersions are `.ι`.
- X = U ∪ V: `(hcover : U ⊔ V = ⊤)`.
- Abelian étale sheaf F: `∀ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}`.
  The connecting transformations are chosen before F, so the result is functorial in F.
- F restricted to W is `(upperStar AddCommGrpCat.{u + 1} W.ι).obj F`, exactly the recorded
  inverse-image functor. `upperStarIsoLocalizationRestriction` identifies this with literal
  restriction. This comparison, and its adjunction description, were read in full.
- H^n(W_et,F|W): `(cohomology AddCommGrpCat.{u + 1} W.toScheme n).obj
  ((DerivedCategory.singleFunctor _ 0).obj ((upperStar _ W.ι).obj F))`.
  The main sequence uses R^n of evaluation at W on Ab(X_et), the alternate spelling
  explicitly included in the node's final parenthesis and used in Stacks 0A50.
  Evaluation is `sheafToPresheaf ... ⋙ (evaluation _ _).obj (op (Scheme.Etale.mk W.ι))`.
  `Functor.rightDerived n` computes its cohomology from an injective resolution.
- Identification of the evaluation terms with restricted-site cohomology (03F3 (2)):
  the four `Nonempty (∀ n : ℕ, ... ≅ ...)` conjuncts are natural isomorphisms of functors
  on coefficient sheaves, for X, U, V and U ∩ V respectively. For X the coefficient
  sheaf is unchanged. Transport of the following sequence gives the displayed
  sequence in the restricted-site spelling.
- 0 → H^0(X,F): `Function.Injective` of the pair of degree-zero restrictions.
- The pair (ρ_U,ρ_V): the pair-valued lambdas, formed from the right derived maps of
  section restriction along `MorphismProperty.Over.homMk U.ι` and the analogous V map.
  The two-term direct sum of abelian groups is represented by their product.
- The difference ρ−ρ: the difference-valued lambdas on the product, using
  `X.homOfLE inf_le_left` and `X.homOfLE inf_le_right` to the intersection.
  The equality witnesses are `X.homOfLE_ι`; these specify the actual inclusions over X.
- Connecting maps: `∃ δ : ∀ n : ℕ, ... ⟶ ...`, from intersection cohomology in degree n
  to X cohomology in degree n+1, as natural transformations of sheaf functors.
- Long exactness: for every n, the three `Function.Exact` conjuncts state exactness
  at the product in degree n, the intersection in degree n, and X in degree n+1.
  Together with the initial injection, this includes every term of the long sequence.
- Functoriality: `NatTrans.rightDerived` of the section maps and `δ n` are natural
  transformations. The four comparison isomorphisms are natural as well.
- Vanishing consequence: the last universally quantified implication is on the actual
  `cohomology` objects on U, V, the intersection, and X. Zero is `Subsingleton` of the
  underlying abelian group. For q > 0 the predecessor is expressed by
  `∃ m : ℕ, n = m + 1 ∧ ...`, avoiding truncated subtraction. At q = 0 the left term
  is zero, as the node's proof states, so the `n = 0` alternative imposes no additional
  hypothesis.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`, `Scheme.Etale`.
- `Mathlib.CategoryTheory.Sites.Sheaf`: `CategoryTheory.Sheaf` (the full subcategory of
  presheaves satisfying the sheaf condition) and `sheafToPresheaf`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.upperStar`, and the
  `upperStarLowerStarAdjunction` specifying inverse image.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`: `Etale.cohomology` and
  `Etale.rightDerivedGlobalSections`; the former is RΓ followed by derived homology.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `Etale.upperStarIsoLocalizationRestriction` and
  `Etale.localizationRestrictionLowerStarAdjunction`, used for interpreting inverse image
  as literal restriction in the comparison clauses and in the proof docstring.
- Mathlib `Functor.rightDerived`, `NatTrans.rightDerived` and
  `InjectiveResolution.isoRightDerivedObj` in `CategoryTheory.Abelian.RightDerived` were
  read to check the resolution-based evaluation terms and their maps.
  These are existing generic constructions; no new notion or private copy is needed.

Edge cases: U or V empty; U = V = X; disjoint U and V; the empty scheme; F = 0;
degree zero; all nonnegative degrees; arbitrary scheme universe and arbitrary
characteristic. Empty opens are permitted. The disjoint case has zero intersection
cohomology, as expected. At degree zero, injectivity gives the asserted vanishing.
Negative cohomology is represented by the initial zero rather than a natural-number
subtraction. No extra geometric hypothesis or boundedness of F is imposed.

Searches (2026-10-11):

- msearch leanfinder, `Mayer Vietoris long exact sequence etale sheaf cohomology open cover`:
  eight hits, including generic MayerVietorisSquare short complexes and exactness;
  none supplies the étale restriction comparison required here.
- msearch loogle, `MayerVietorisSquare.sequence_exact`: no hits; unknown identifier
  on that service. The pinned local declaration was read directly instead.
- msearch grep, `MayerVietoris|cohomologyPresheaf` in
  `CategoryTheory/Sites/SheafCohomology`: ten hits, including the general sequence
  and the explicit TODO for comparing evaluation with restricted-site cohomology.
- msearch leansearch, `cohomology presheaf restriction slice site comparison`:
  unavailable (Internal Server Error); no mathematical verdict based on that service.
- rg of `MayerVietoris` and étale cohomology/restriction names in Mathlib, WeilConjectures,
  and lean/Sheaf: generic site and topological sequences, a pro-étale adic sequence,
  and unrelated module cohomology. No exact existing statement for this node.
- rg of the item id in WeilConjectures: no declaration. rg of
  `etale_mayerVietoris|etaleMayerVietoris` in Mathlib, WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json: no collision.

The local literature checkout lacks the Stacks TeX files. Sources were read at
https://stacks.math.columbia.edu/tag/0A50 and https://stacks.math.columbia.edu/tag/03F3.
The eight-step node proof is included in the declaration docstring. No statement
correction, disputed statement, new node or dependency replacement is needed.

Validation: server compilation is clean. `deliver2.py --no-push` printed OK: compilation
and preflight passed except for the second reading, which the independent reader supplies.
Nothing was pushed.

## Second reading by C1

I read the node statement, its source (Stacks Tags 0A50 and 03F3), all six
statement dependencies, and the Lean declaration
`AlgebraicGeometry.Etale.etale_mayerVietoris`.

The correspondence is as follows. The scheme is `(X : Scheme.{u})`; the two
open subschemes are `(U V : X.Opens)` and the cover is `hcover : U ⊔ V = ⊤`.
The four site-cohomology terms are rendered by the four `Nonempty (∀ n, ... ≅
...)` comparison clauses: evaluation at `𝟙 X`, `U.ι`, `V.ι`, and
`(U ⊓ V).ι`, respectively, compared with `cohomology` after `singleFunctor`
and, for an open, `upperStar`. The connecting maps are the existential family
`δ : ∀ n, ...rightDerived n ⟶ ...rightDerived (n + 1)`, natural in the sheaf.
For each coefficient sheaf `F`, the initial `Function.Injective` is the
degree-zero restriction map; the three `Function.Exact` clauses are exactness
at the product, at the intersection, and at the next `X` term. The maps are
the right-derived evaluation maps for `U`, `V`, and the inclusions
`U ⊓ V ≤ U,V`, with the difference map formed in the abelian group product.
The final implication gives the stated vanishing, using `n = 0` or an explicit
predecessor `n = m + 1` rather than subtraction. Thus every object,
hypothesis, quantifier, and conclusion clause of the node is present, with no
extra geometric, finiteness, separation, characteristic, or boundedness
hypothesis.

Edge cases checked: empty opens and empty schemes, `U = V = X`, disjoint
opens, the zero sheaf, degree zero, arbitrary natural degree, and arbitrary
scheme universe. The predecessor disjunction makes the degree-zero case
vacuous exactly as in the source.

I searched Mathlib, the source repository, and `lean/Sheaf` (LeanSearch,
LeanFinder/Loogle, and `rg`) for Mayer–Vietoris and étale cohomology
declarations. Only the generic site Mayer–Vietoris constructions occur; none
states this étale comparison and sequence. No mismatch was found, so no Lean
or node change was required. The module compiles with its single named
`sorry`, and the declaration has no unbound variables or universes.

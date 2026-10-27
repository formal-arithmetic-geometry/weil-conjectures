## Worker report

Item: `lem-pd-open-module-balanced-projection`, stage 2, group O1.
Module: `Sheaf.PoincareDuality.OpenModuleBalancedProjection`.
Primary declaration: `AlgebraicGeometry.ProEtale.CondensedRing.openModuleBalancedProjection`.
The six supporting definitions name the canonical maps of this same node; none replaces
an existing notion. All have real data, from existing isomorphisms and functorial operations.
The only postponed proof is the main theorem, whose eight-step proof is in its docstring.
No node correction, new node, dependency repair, or disputed statement is needed.

Hypothesis-by-hypothesis and clause-by-clause comparison:

- Prime ell: `(ℓ : ℕ) [Fact ℓ.Prime]`. Field k of positive characteristic different
  from ell: `(k : Type u) [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]`. This is exactly the setting's upstream convention:
  positive characteristic of a field is prime, and conversely prime ringChar is positive.
- Separated finite-type k-schemes U,Z: `U Z : Scheme.{u}`, their `Over (Spec (.of k))`
  instances, and `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` on each structure map.
  The latter two express finite type. The morphism is `j : U ⟶ Z` with `j.IsOver`
  and `IsOpenImmersion j`. No quasi-compactness assumption on j was added.
- Arbitrary commutative condensed coefficients: the section variable
  `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}` with `MonObj Λ` and
  `IsCommMonObj Λ`. These are the underlying object and structures of the recorded
  `Profinite.CondensedRing = Mon (...)` encoding; no topological presentation is required.
- Sites are exactly `Scheme.ProEt.topology` in the recorded upstream size convention,
  with abelian group values `Ab.{u+1}`. There is no equality between the site object
  universe and morphism universe, and no extra smallness assumption. The existing
  functors determine the small representatives via the source framework.
- Coefficients Lambda_T are `condensedRingObj Λ T`, i.e. `upperStarFromPoint T` applied
  to Λ, the same underlying object as the recorded bundled `coefficientRing T (Mon.mk Λ)`.
- Internal module categories are `supportModules Λ T`, the existing transparent
  abbreviation for `Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u+1}) (condensedRingObj Λ T)`.
  Module tensor `⊗` uses the recorded `Mod.monoidalCategory` coequalizer construction;
  `Mod.tensorObjπ` is its specified quotient projection.
- E and R are precisely `openImmersionLowerShriek Λ j` and `upperStar Λ j`.
  The adjunction is `openImmersionLowerShriekUpperStarAdjunction Λ j`, not an arbitrary
  adjunction. Its `unit`, `counit` and `homEquiv` occur explicitly.
- The map nu is `openModuleTensorComparison Λ j A B`. Its body conjugates
  `(supportTensorComparison Λ j A B).inv` by the components of the specified
  `supportPullbackIsoUpperStar`. Thus this uses exactly the inverse of the ordinary
  comparison named in the dependency, and never an arbitrary monoidal structure on R.
- Both functors additive and exact: the first six conjuncts assert `Additive`,
  `PreservesFiniteLimits` and `PreservesFiniteColimits` for E and R, respectively.
- The unit is invertible for every M: an isomorphism `e : M ≅ R.obj (E.obj M)`
  with `e.hom = adj.unit.app M`. Its underlying map, composed with
  `openModulePullbackUnderlyingIso`, equals the actual abelian adjunction unit.
  That underlying comparison is the forgetful image of the inverse of
  `supportPullbackIsoUpperStar`, hence is the canonical alpha coefficient identification.
  The third conjunct explicitly gives the action equation for `e.inv.hom`.
  Moreover `e.inv` itself is a morphism in `Mod`, so linearity is also encoded structurally.
- The displayed theta is the data-defined `openModuleBalancedProjectionMap`: E of
  `unit ▷ R N ≫ nu`, followed by the specified counit at `E M ⊗ N`.
  Functoriality of E identifies this with the node's three-arrow displayed formula.
  The next clause asserts `IsIso` of this very morphism for every M,N.
- Its transpose is exactly `unit ▷ R N ≫ nu`: the following equality uses the
  specified adjunction's `homEquiv`, with no mere existence of an unnamed isomorphism.
- Naturality in both variables is the joint equation for every a:M→M' and b:N→N':
  `E.map (a ⊗ₘ R.map b) ≫ theta M' N' = theta M N ≫ (E.map a ⊗ₘ b)`.
- The canonical abelian projection in the order M tensor S L is
  `openModuleAbelianProjectionIso`: P applied to the braiding, the recorded adjunction
  projection formula in the opposite factor order, then the target braiding.
- `openModuleBalanceTargetIso` is H0: first the canonical underlying-pullback
  identification in the second factor, then that abelian projection iso.
- `openModuleBalanceSourceIso` is H1: re-associate `(M ⊗ Lambda_U) ⊗ R N`, use
  alpha inverse on the coefficient and the underlying-pullback comparison on N, apply
  the abelian inverse-image tensorator to the last two factors, project against
  `Lambda_Z ⊗ N`, and re-associate back. Thus it includes the required additional
  coefficient factor, and its choices are fixed data, not existential diagram isos.
- The first of the final three equations is `P(d1) ≫ H0.hom = H1.hom ≫ e1`,
  where d1/e1 are explicitly the right actions `(braiding ≫ action) ▷ object`.
- The second is `P(d2) ≫ H0.hom = H1.hom ≫ e2`, where d2/e2 are explicitly
  `(associator).hom ≫ object ◁ left_action`. The two arrows are never interchanged.
- The last equation is `P(q_U) ≫ theta.hom = H0.hom ≫ q_Z`, with both q's the
  recorded `Mod.tensorObjπ`. Since P preserves these coequalizers, this says exactly
  that theta is the induced map on their coequalizers. All maps in these three equations
  are abelian-sheaf tensor maps; their quotients are the internal relative tensors.
- No derived, K-flat, or constructibility conclusion is asserted. The setting and tensor
  comparison dependency modules happen to export derived interfaces; only their ordinary
  declarations are used by this theorem.

Dependency declarations read and used (full names below have the indicated namespaces):

- `sk-def-sfb-dc-setting`: public import
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`.
  Read `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField` and the
  setting documentation, including its prime-characteristic/Over/finite-type convention.
  The node's setting is expressed by the binders above, rather than invoking its unused
  chosen compactification.
- `sk-def-sfb-condensed-ring`: public import `Sheaf.Topology.ProfiniteCondensedRing`;
  read `Profinite.CondensedRing`, a transparent `Mon` abbreviation. Our unbundled
  coefficient uses the same sheaf/monoid-object data as the ordinary functor interfaces.
- `def-weil-pbc-proetale-site`: read Mathlib `AlgebraicGeometry.Scheme.ProEt` and
  `Scheme.ProEt.topology`, from `Mathlib.AlgebraicGeometry.Sites.Proetale`.
- `sk-def-sfb-pulled-back-coefficients`: read
  `AlgebraicGeometry.ProEtale.coefficientRing`, `coefficientRing_X`, `condensedRingObj`
  and `upperStarFromPoint` in
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`.
- `sk-def-sfb-module-objects`: read Mathlib `CategoryTheory.Mod`, `Mod.Hom`,
  `Mod.forget`, `Mod.regular`, `ModObj`, and `IsModHom`, in
  `Mathlib.CategoryTheory.Monoidal.Mod`.
- `def-sfb-modobj-relative-tensor`: read `CategoryTheory.Mod.monoidalCategory`,
  `tensorObj_X`, `tensorObjπ`, `isColimitTensorπ` and both action arrows in
  `WeilConjectures.CategoryTheory.ModuleObjects.Monoidal`.
- `def-sfb-module-open-lower-shriek` and its specified adjunction: public import
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`, using
  `AlgebraicGeometry.ProEtale.CondensedRing.openImmersionLowerShriek` and
  `openImmersionLowerShriekUpperStarAdjunction`; read their actual scalar-restriction,
  linearized-action, scalar-coextension and Ext/Coext identification bodies.
- `def-sfb-module-upper-star`: `AlgebraicGeometry.ProEtale.CondensedRing.upperStar`
  in `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`;
  read its `mapMod` then `extendScalars` construction and exactness interfaces.
- `def-sfb-condensed-pullback-tensor-comparison`: public import
  `Sheaf.AlgebraicGeometry.CondensedPullbackTensorComparison`; read
  `supportPullbackIsoUpperStar`, `existsUnique_supportTensorComparison`,
  `supportTensorComparison`. The comparison is chosen from its unique balanced-generator
  characterization, and the transport is `extendScalarsIsoComapInv`.
- Other canonical data: `AlgebraicGeometry.ProEtale.openImmersionLowerShriek`,
  `openImmersionLowerShriekUpperStarAdjunction` on abelian sheaves; and
  `CategoryTheory.Adjunction.projectionFormula` in
  `WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula`.
- Public imports expose the statement dependencies. Plain proof imports include
  `Sheaf.CategoryTheory.SitePullbackAbelianExact`, `Sheaf.CategoryTheory.SheafTensor`,
  `Sheaf.CategoryTheory.ModuleObjects.LiftExact`, and the upstream finite-coefficient
  lower-shriek Proper and Open.Projection modules. Other stated proof prerequisites
  are already in their import closures (scalar change, projection coherences,
  braidedness, left-adjoint colimit preservation, enough injectives, Hom adjunction).

Edge cases checked against the formulas:

- Empty U, empty Z, identity j, zero coefficient ring, and zero M or N remain allowed.
  The canonical units, tensorators, projection isomorphisms and coequalizers still make
  sense, including when the categories are zero. No nonemptiness/nonzero binder was added.
- j need not be declared quasi-compact; no complement, Noetherian structure, derived
  category, constructibility, flatness or finite-generation hypothesis is introduced.
- The generic universe u and fixed Ab.{u+1} match the actual upstream functor signatures;
  no artificial equality of universes or restriction to topologically presented Λ appears.
- For j the identity, the actual specified unit and coefficient transport are retained;
  neither is silently replaced by a definitionally equal identity morphism.
- The associators in H1 take the balancing domain `(M ⊗ B_U) ⊗ R N` to the exact
  target `(E M ⊗ B_Z) ⊗ N`. The first/second balancing arrows and quotient equation
  have been individually checked for these source/target objects by compilation.

Searches for an existing declaration:

- `msearch.py ... leanfinder "Extension by zero of internal sheaf modules open immersion
  balanced relative tensor projection formula normalized adjunction unit"`: eight hits,
  on scheme structure-sheaf module restriction adjunctions and general pullback-unit maps.
  None treats these internal condensed-coefficient modules or both balancing arrows.
- `msearch.py ... loogle "CategoryTheory.Mod.tensorObjπ, CategoryTheory.Adjunction"`:
  zero hits; the service does not index the project's tensorObjπ name.
- `msearch.py ... grep "openImmersionLowerShriek|balancedProjection"`: zero Mathlib hits.
- `msearch.py ... leansearch "Extension by zero of internal module objects satisfies the
  balanced relative tensor projection formula"`: eight elementary algebraic tensor and
  projection hits, no match.
- `rg` of `open.*[Bb]alanc|balanced.*[Pp]rojection|openModuleBalanced|<item id>` in
  `lean/WeilConjectures` and `lean/Sheaf`, and a final name search for all seven declarations:
  no hits. Existing OpenImmersionTensorProjection is a derived object-isomorphism statement;
  it does not give the specified underived unit, normalized mate or balancing equations.
- Read the current blueprint at `literature/blueprint/latest/blueprint/` only:
  `sec-six-functors-basics/sk-lem-int-tensor/det-lem-int-tensor-projection.proof.md`.
  The open sheaf paragraph defines the adjunct of the identity under j-star j-shriek,
  exactly the normalized map retained here. The DAG's proof supplies its explicit
  coefficient-linear and balanced-coequalizer refinement.

Validation: scompile.py compiled both sandbox and actual module-name forms cleanly,
5.3 s and 7.4 s respectively (60 s limit); no errors or unexpected warnings.
The initial parse error came from opening the wrong gamma notation scope and was repaired
by using the existing `CategoryTheory.MonObj` scope. No global build was run.

## Second reading by O1

Author's separate rereading, with the node statement, full eight-step proof and completed
module open; independent review is reserved for the maintainer as specified by the brief.
I checked the signature clause by clause against the node. The tuple has exactly the
six additivity/exactness assertions, then the unit isomorphism and underlying normalization,
then inverse linearity, pointwise invertibility plus exact transpose, joint naturality,
and all three coequalizer equations. The helper nu transports the inverse of the recorded
support comparison rather than using the possibly differently presented monoidal-upperStar
instance. H1 includes alpha inverse and the extra coefficient tensorator, and preserves the
ordered balancing arrows; H0 uses the matching alpha identification on R N. The unit
isomorphism e has its hom fixed to the specified unit, and its inverse is linear in the
same coefficient action. Every theorem proof is sorry, every helper has constructed data,
and all variables/universes are bound explicitly. No mathematical mismatch or node change
was found. The gamma-scope parsing correction was the only implementation repair.

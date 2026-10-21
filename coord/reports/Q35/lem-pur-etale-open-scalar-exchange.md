## Worker report

The module `Sheaf.Paper.EtaleOpenScalarExchange` states
`AlgebraicGeometry.Etale.etaleOpenScalarExchange`, with proof `sorry`.
It is exactly the displayed ordinary small-etale scalar/open base-change equation,
using the already published canonical functors and comparisons. No definition,
helper theorem, dependency repair, new node, or statement correction is introduced.
The item's other fields are unchanged.

Source read: `literature/stacks-project/etale-cohomology.tex`,
`lemma-shriek-base-change`, Tag 03S6, lines 11492 onward. This gives the natural
open exchange via equality of right adjoints. The node's six-step coefficient/unit
calculation supplies the additional scalar compatibility and is transcribed into
the theorem docstring, including the inverse-mate normalization and the square
identity obtained from scalar pullback composition.

Hypothesis and clause correspondence:

- Finite commutative unital rings A and B are `{A B : Type (u + 1)}`,
  `[CommRing A] [CommRing B] [Finite A] [Finite B]`. The unital map is
  `(φ : A →+* B)`. No algebra structure or flatness is assumed.
- Arbitrary schemes U, T, T' are `{U T T' : Scheme.{u}}`. The maps are
  `(j : U ⟶ T) [IsOpenImmersion j]` and `(g : T' ⟶ T)`.
- Ordinary unbounded D_A(U) is `DerivedCategoryModule A U`; `(M : ... )` is
  arbitrary, with no boundedness or constructibility predicate.
- Q_S is `scalarExtension φ S`, the published abbreviation for
  `ProEtale.pbcFixedScalarExtension S.smallEtaleTopology φ`. It is the
  ordinary small-etale specialization of derived change of rings, not a newly
  chosen functor on ringed-site module categories.
- Exact u_R^* is `(upperStar (ModuleCat.{u + 1} R) u).mapDerivedCategory`.
  Exact j_!,R is `(openImmersionLowerShriek (ModuleCat.{u + 1} R) j).
  mapDerivedCategory`; `derivedExtension` in the open tensor API abbreviates it.
- The chosen U' is literally `pullback g j`. Its h is `pullback.snd g j`,
  and its j' is `pullback.fst g j`. The square supplied to the exchange
  construction is `(IsPullback.of_hasPullback g j).flip`; hence its source
  and projections are the specified fibre product, rather than arbitrary maps.
  The open-immersion instance on j' follows from stability under base change.
- Lambda_u is `(properOpenCoefficientPullbackIso φ u).hom.app ...`.
  Its definition is exactly the existing K-flat comparison `scalarPullbackIso`,
  conjugated by `leftDerivedUpperStarIsoMapDerivedCategory` for B and A, as in
  `def-pur-open-coefficient-normalizations`. Nothing is supplied as an
  unconstrained comparison parameter.
- Beta_j is `(openScalarExtension φ j).hom.app M`, the balancing comparison
  used by `etaleOpenTensorComparisons`. Its inverse is the canonical open mate.
  The definition by uniqueness of the composite scalar/open left adjoints,
  together with the restriction/scalar mate, gives precisely the transpose
  Q_U(eta_A) followed by lambda_j inverse. The plain definition
  `properOpenCoefficientOpenInverse` in the recorded normalization module
  expresses this same transpose directly. We use the published balancing
  comparison itself, rather than introduce a second beta definition or assume
  a normalization on an arbitrary isomorphism. Both open adjunctions are the
  published degreewise-normalized derived adjunctions.
- E_R is the `.inv` of `mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
  (ModuleCat.{u + 1} R) (IsPullback.of_hasPullback g j).flip`.
  This is exactly the inverse of the degreewise descent of
  `openImmersionLowerShriekBaseChangeMap`; its inverse has transpose H_R(eta_R)
  followed by the canonical square identification. This follows directly from
  `unit_map_openImmersionLowerShriekBaseChangeMap_app` and descent of the
  exact adjunction. In particular the direction is g_R^* j_!,R to j'_!,R h_R^*.
- The left composite, in Lean's left-to-right composition order, is
  `g_B^*.map beta_j`, then `e_B.app (Q_U.obj M)`, then `j'_!,B.map lambda_h`.
- The right composite is `lambda_g.app (j_!,A.obj M)`, then `Q_T'.map e_A`,
  then `beta_j'.app (h_A^*.obj M)`. Thus both have source
  g_B^* Q_T j_!,A M and target j'_!,B Q_U' h_A^* M, exactly as in the node.
- Naturality on the entire derived category is retained: every factor is a
  component or functorial image of a fixed natural transformation, and the
  theorem quantifies over every M. Componentwise equality is equivalent to
  equality of the corresponding natural transformations. No extra naturality
  hypothesis is imposed.

Dependency declarations read and used (all names below are already published):

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `def-weil-pbc-derived-categories`:
  `WeilConjectures.AlgebraicGeometry.DerivedCategories`, with the actual
  `AlgebraicGeometry.Etale.DerivedCategoryModule` signature in
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`.
- `lem-pur-derived-change-of-rings`:
  `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`,
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and
  `nonempty_derivedChangeOfRingsCochainModel`. The already published
  small-etale realization used here is `AlgebraicGeometry.Etale.scalarExtension`
  in `Sheaf.Paper.EtaleDerivedScalarTensor`, carrying this node's blueprint tag.
- `prop-weil-pbc-inverse-image-modules-exact`:
  `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`,
  `AlgebraicGeometry.etaleInverseImageModulesExact`. Its constant-module
  inverse image is the existing `upperStar` used in the six-functor encoding.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`:
  `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`,
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.
  ringedTopoiCanonicalDerivedTensorPullback`. The canonical small-etale
  scalar specialization is `scalarPullbackIso` in
  `Sheaf.Paper.PurEtaleScalarMateProjection`, characterized uniquely by its
  K-flat representative equation; it is transported by the recorded exact
  comparison below. We do not choose data from the general existence theorem.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`.
- `def-weil-pbc-extension-by-zero` and
  `lem-weil-pbc-extension-by-zero-adjunction`:
  `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`,
  `openImmersionLowerShriek`, `openImmersionLowerShriekUpperStarAdjunction`.
  Derived extension and its adjunction are in
  `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek`.
- `lem-coef-etale-open-tensor`: `Sheaf.SixFunctors.EtaleOpenTensor`,
  `EtaleOpenTensorComparisons`, `etaleOpenTensorComparisons`, and the canonical
  `openScalarExtension` from its public import
  `Sheaf.SixFunctors.EtaleOpenTensorDefs`.
- `def-pur-open-coefficient-normalizations`:
  `Sheaf.Paper.ProperOpenCoefficientRefinement`,
  `properOpenCoefficientPullbackIso`, `properOpenCoefficientOpenInverse`.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `pullback`,
  `pullback.fst`, `pullback.snd`.
- `lem-cbc-extension-zero-base-change`:
  `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare`,
  `isIso_openImmersionLowerShriekBaseChangeMap`,
  `openImmersionLowerShriekBaseChangeMap`,
  `unit_map_openImmersionLowerShriekBaseChangeMap_app`. Its existing derived
  descent is `mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso` in
  `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange`.
- Proof dependency `lem-sf-scalar-pullback-composition`:
  `Sheaf.Paper.ScalarPullbackComposition`, `scalarPullback_composition`,
  imported without `public`; its full statement permits arbitrary unbounded N.

The first three public imports expose the actual functors and comparisons used
in the signature. General ringed-module existence interfaces are read as requested;
the statement reuses their published six-functor specializations and does not
construct alternative realizations or impose universe identifications.

Edge cases checked: U empty (both composites between zero extensions); g the
identity (the canonical identity/composition comparisons remain present); j the
identity; M zero; zero coefficient rings; and nonflat coefficient reduction such
as Z/4 to Z/2. There is no nontrivial-ring assumption, no cohomological bound,
no quasi-compactness, separatedness, properness or flatness restriction on g.
The site size convention is the existing `Scheme.{u}` with coefficients and
module carriers in `u + 1`. All finite rings are available at this size by the
usual universe lift. The square is canonical for every g, including empty T'.
No suspected false statement or node fault was found.

Searches (all run via the prescribed wrapper or read-only source search):

- LeanFinder: "Extension by zero open base change isomorphism commutes with
  derived scalar extension". Eight hits, chiefly `ModuleCat.extendScalarsComp`
  and ordinary scalar-adjunction lemmas; no matching derived open square identity.
- Loogle: `AlgebraicGeometry.Etale.openImmersionLowerShriekBaseChangeMap,
  AlgebraicGeometry.Etale.scalarExtension`. Zero hits; the former identifier
  is unknown to the Mathlib-only search service.
- Mathlib grep, CategoryTheory:
  `openImmersionLowerShriekBaseChange|scalar.*[Bb]ase[Cc]hange|[Bb]ase[Cc]hange.*[Ss]calar`.
  Zero hits.
- LeanSearch: "Derived scalar extension commutes with open immersion extension
  by zero base change". Eight hits on algebra extensions and stability of open
  immersions under base change; no matching statement.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for
  `open.*[Ss]calar.*[Ee]xchange|[Ss]calar.*[Oo]pen.*[Bb]ase[Cc]hange|
  lem-pur-etale-open-scalar-exchange` finds only the separate pro-etale statement
  `openScalarExchange` in `Sheaf.SecSmoothPurity.OpenScalarExchange` and its
  supporting pro-etale modules. They use pro-etale categories, hence are not
  this ordinary etale statement.
- The requested `grep -rn` for the item id in `lean/WeilConjectures` has no hit.
  `rg` for `etaleOpenScalarExchange` in both source trees also has no hit.

Validation: `scompile.py Q35 lem-pur-etale-open-scalar-exchange
.../lean/Sheaf/Paper/EtaleOpenScalarExchange.lean` compiled the sandbox and library
forms cleanly (35.1 s and 21.3 s). The sole new proof is `sorry`, as required.
All universe and variable binders are explicit under `set_option autoImplicit false`.

## Second reading by Q35

A second pass in this single-worker session reread the node, the complete new
signature, the open scalar definitions, the exact scalar/pullback transport, and
the source/target of the derived base-change isomorphism. This is not a claim
of another agent's independent review; the maintainer supplies that review.
The only direction requiring care was the published base-change isomorphism:
its hom is j'_! h^* to g^* j_!, so the signature uses `.inv` on both sides.
The `.flip` of the chosen pullback square was checked to have h = snd and
j' = fst. The three left factors and three right factors were matched in order
with every factor in the node. Both scalar/open maps use the same published
balancing construction, while both lambdas use the exactness transport specified
by the normalization dependency. Finite coefficients, arbitrary g and arbitrary
unbounded M are all bound explicitly; there is no additional hypothesis.
No mismatch requiring a change was found in this reading.

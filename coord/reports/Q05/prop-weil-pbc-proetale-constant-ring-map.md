## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap` states
`AlgebraicGeometry.ProEtale.finiteCoefficientInverseImageMap_isIso`, with the
constant-sheaf normalization and the empty-source clause as additional theorems.
All theorem proofs are `sorry`. All map definitions contain real constructions.
No statement correction, new node, or dependency-module repair was needed.

The source blueprint markdown named by the node is absent from this read-only
checkout. I read the node's complete statement and six-step corrected proof and
opened the three primary-source places that proof cites:
[Stacks 04B3](https://stacks.math.columbia.edu/tag/04B3) (empty covering),
[Stacks 0H7J](https://stacks.math.columbia.edu/tag/0H7J) (constant-sheaf
sheafification and its universal property), and
[Stacks 09A5](https://stacks.math.columbia.edu/tag/09A5) (base-change functor on
small pro-etale sites). The ring-valued version is used with the ring operations,
exactly as the node's corrected proof explains; the set-valued example alone is
not asserted to be the complete ring-sheaf comparison theorem.

Hypotheses and clauses, in the order of the node:

- The finite discrete ring, without commutativity, is `(Λ : Type (u + 1))
  [Ring Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ]`. These are
  the exact binders of the recorded coefficient construction. The only theorem
  requiring `[CommRing Λ]` is the final constant-structure-map comparison.
- An arbitrary scheme morphism is `{U V : Scheme.{u}} (f : U ⟶ V)`.
  No properness, quasi-compactness, separatedness, or nonemptiness is imposed.
- The small sites are `Scheme.ProEt.topology U` and `Scheme.ProEt.topology V`
  on the recorded `U.ProEt` and `V.ProEt`. Their object universe is `u+1`
  and morphism universe is `u`; neither is forced equal to the other.
- The coefficient sheaves are precisely `finiteCoefficientRingSheaf U Λ`
  and `finiteCoefficientRingSheaf V Λ`. They are the recorded sheafifications
  of `finiteCoefficientPresheaf`, whose sections are continuous functions on
  `ConnectedComponents` with the quotient topology. No new coefficient notion
  is defined here.
- The inverse image, direct image, and their adjunction are
  `Scheme.proEtaleSheafInverseImage f RingCat.{u+1}`,
  `Scheme.proEtaleSheafDirectImage f RingCat.{u+1}`, and
  `Scheme.proEtaleSheafAdjunction f RingCat.{u+1}`. In particular the inverse
  image uses ring-valued Kan extension and sheafification.
- The node's `η_T(a)` is the component of the recorded
  `finiteCoefficientScalarMap T Λ` applied to `a`: a constant continuous
  function followed by the sheafification unit. No injectivity is assumed.
- `finiteCoefficientDirectImageApp f Λ W` precomposes a continuous function
  with the map on connected components induced by
  `pullback.fst W.unop.hom f`, then applies `toSheafify` at the base-changed
  object. The recorded base-change convention is `W ×[V] U`, so this first
  projection maps to W. On an open fibre with value a the pullback is the
  constant function a, followed by exactly the prescribed `η_U(a)`.
  The sheafified section therefore agrees with gluing those sections on the
  inverse-image fibre cover. This constructs the specified map, without an
  arbitrary map or an existence choice.
- `finiteCoefficientDirectImageApp_naturality` states the needed naturality
  equation, with its own proof plan. `finiteCoefficientDirectImagePresheafMap`
  uses that equation as its structure proof.
- The extension by sheafification is
  `finiteCoefficientDirectImageMap f Λ`, defined by the inverse hom equivalence
  of `sheafificationAdjunction`. Thus this is precisely rho.
- `finiteCoefficientInverseImageMap f Λ` is the inverse hom equivalence of
  the recorded ring-sheaf adjunction applied to rho. Thus it is precisely c_f,
  rather than an unrelated map with the same source and target.
- The main theorem concludes `IsIso (finiteCoefficientInverseImageMap f Λ)`.
  Its docstring follows all six steps of the node's corrected proof: empty
  cover, open fibres, the ring-Hom/gluing characterization, constant-sheaf
  identification, adjunction and terminal evaluation, and the two inverse
  identities in one ring-sheaf category.
- The canonical constant-preserving identification is
  `finiteCoefficientConstantComparison Λ T`, defined by sheafification from
  `finiteCoefficientScalarMap T Λ`. Its theorem states that this map is an
  isomorphism and is the unique sheaf map preserving the scalar sections.
  The normalization equation uses the constant-presheaf `toSheafify` unit.
- For commutative Λ, `finiteCoefficientInverseImageMap_constant` states the
  commuting square
  `f⁻¹(comparison_V) ≫ c_f = c^f_Λ ≫ comparison_U`.
  Here `c^f_Λ` is exactly the recorded
  `Scheme.proEtaleConstantInverseImageMap f RingCat.{u+1} (RingCat.of Λ)`:
  the generic value-category declaration of the dependency, specialized to
  ring sheaves. This is the ring-sheaf formulation in the node, with no
  comparison of module categories or replacement by an abstract isomorphism.
- The empty clause is `finiteCoefficientInverseImageMap_empty`, with
  `[IsEmpty U]`: at every object both ring sheaves have subsingleton section
  rings, and every map between the two sheaves equals the canonical map.
  A subsingleton unital ring is the zero ring; combined with the unrestricted
  isomorphism theorem this says exactly that c_f is the unique isomorphism.

Recorded dependencies read and used:

- `def-weil-pbc-scheme-conventions` is explicitly a convention node with no
  owning declaration. The scheme and arrow binders use Mathlib's `Scheme`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`:
  `finiteCoefficientPresheaf`, `finiteCoefficientRingSheaf`,
  `finiteCoefficientConstants`, and `finiteCoefficientScalarMap` in
  `AlgebraicGeometry.ProEtale`. I read the full definitions and the module's
  coefficient-identification proof docstring; `scompile.py --source` also
  confirmed the current published module.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory` supplies the recorded
  small-site convention; `Scheme.ProEt` and `Scheme.ProEt.topology` themselves
  are Mathlib's existing definitions. No derived category is introduced here.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `Scheme.proEtaleBaseChange`, `proEtaleSheafDirectImage`,
  `proEtaleSheafInverseImage`, `proEtaleSheafAdjunction`,
  `proEtaleConstantDirectImageMap`, and `proEtaleConstantInverseImageMap`.
  I read their full declarations and docstrings, including the orientation
  of the fibre product.
- `Mathlib.CategoryTheory.Sites.Sheafification`:
  `CategoryTheory.presheafToSheaf`, `toSheafify`, and
  `sheafificationAdjunction`; source definitions read around lines 72–100.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`:
  `CategoryTheory.constantSheaf`; source definition and docstring read around
  lines 63–72, including its constant-presheaf sheafification formula.
- The proof-only import
  `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization` corresponds to
  `lem-weil-proetale-weakly-etale-localization`. Its statement and proof
  docstring were read; the proof uses its geometric localization clause
  with auxiliary commutative ring Z, not with the possibly noncommutative Λ.

Edge cases checked: U empty, V empty (which forces U empty), the empty test
object even when the base is nonempty, Λ the zero ring, noncommutative finite
rings, disconnected schemes, identity morphisms, and arbitrary morphisms.
On the empty test object the function ring on connected components already
has one element; after sheafification both sides obey the empty-cover axiom.
No step asserts that different constants remain different on empty objects.
Open fibres are used, not connected components as purported open subschemes.
All constructions preserve pointwise addition, multiplication, zero and one,
without using commutativity. Universes and variables are explicitly bound,
with `set_option autoImplicit false` enforced in the delivered module.

Searches actually run (the four wrapper searches are in `searches.jsonl`):

- `msearch.py ... leanfinder "inverse image of a finite discrete constant ring
  sheaf on a pro-etale site is canonically isomorphic to the constant ring
  sheaf"`: eight hits for condensed/light condensed locally constant
  functors; none is the requested pro-etale ring-sheaf comparison.
- `msearch.py ... loogle "CategoryTheory.constantSheaf, CategoryTheory.IsIso"`:
  three generic constant-sheaf counit/constantness results, not this map.
- `msearch.py ... leansearch "inverse image constant sheaf of rings is
  isomorphic to constant sheaf"`: service unavailable, Internal Server Error.
  This is recorded as unavailable, not as evidence of no match.
- `msearch.py ... grep
  "constantSheaf.*[Ii]so|[Ii]so.*constantSheaf|constant.*[Pp]ullback"
  CategoryTheory/Sites`: eight hits, generic constantness and local-site
  coconstant functors. Read `constantSheaf` and its adjunction definitions.
- `rg` of constant-ring, coefficient-map and item-id patterns in the upstream
  `WeilConjectures/SixFunctors/ProEtale` and project `lean/Sheaf/AlgebraicGeometry`:
  existing adic rings and the coefficient/inverse-image definitions, no exact
  theorem for the specified finite continuous-function coefficient sheaves.
- `grep -rn "prop-weil-pbc-proetale-constant-ring-map"` in upstream
  `WeilConjectures`: no hit.
- `rg` of the new declaration prefixes
  `finiteCoefficient(DirectImageApp|DirectImagePresheafMap|DirectImageMap|InverseImageMap|ConstantComparison)`
  across Mathlib, upstream `WeilConjectures`, and project `lean/Sheaf`: no hit.
- The upstream-name index `dag/lean_names_upstream.json` was searched for
  constant/ring declarations; its existing constant-sheaf match was reused.

Validation: `scompile.py Q05 prop-weil-pbc-proetale-constant-ring-map
<module>` passed with no errors or unexpected warnings, under the prescribed
60-second limit. The source record changes only `lean`; the delivery has no
new DAG nodes or dependency repairs. All supporting declarations belong to
this node and are listed in `lean.declarations`. Every postponed theorem has
its source and natural-language proof in its own docstring.

## Second reading by Q05

I read the complete item record in
`dag/nodes/sec-proper-base-change/prop-weil-pbc-proetale-constant-ring-map.json`,
the recorded signatures of every statement dependency, and the module
`lean/Sheaf/AlgebraicGeometry/ProEtaleConstantRingMap.lean`. The source places
used by the node are Stacks Tags 04B3 (the empty-cover sheaf condition), 0H7J
(constant sheaf as sheafification and its universal property), and 09A5
(functoriality of the small pro-etale site). The source gives an arbitrary
scheme morphism; it does not add properness, quasi-compactness, separatedness,
or nonemptiness hypotheses.

The item statement matches the Lean as follows, in order.

* The finite discrete, possibly noncommutative ring is
  `Λ : Type (u + 1)` with `[Ring Λ] [Finite Λ] [TopologicalSpace Λ]`
  `[DiscreteTopology Λ]`; these are exactly the module variables.
* The schemes and morphism are `{U V : Scheme.{u}}` and `f : U ⟶ V`, with no
  additional geometric hypotheses. The pro-etale sites are
  `Scheme.ProEt.topology U` and `Scheme.ProEt.topology V`, using the recorded
  object/morphism universe convention.
* The coefficient sheaves are exactly `finiteCoefficientRingSheaf U Λ` and
  `finiteCoefficientRingSheaf V Λ`, namely the recorded sheafifications of
  `finiteCoefficientPresheaf`; no duplicate coefficient definition occurs.
* The direct image, inverse image, and ring-sheaf adjunction are respectively
  `Scheme.proEtaleSheafDirectImage`, `Scheme.proEtaleSheafInverseImage`, and
  `Scheme.proEtaleSheafAdjunction`, all in `RingCat.{u + 1}`. The definitions
  `finiteCoefficientDirectImageApp`,
  `finiteCoefficientDirectImagePresheafMap`, and
  `finiteCoefficientDirectImageMap` implement the stated pullback-on-functions,
  open-fibre gluing, and sheafification extension of `rho`.
* `finiteCoefficientInverseImageMap` is defined as the adjoint of that exact
  direct-image map, so it is the node's `c_u`, rather than an unrelated map.
  The declaration `finiteCoefficientInverseImageMap_isIso` states the node's
  principal conclusion `IsIso ...`.
* The constant-sheaf comparison is
  `finiteCoefficientConstantComparison`; its supporting theorem states the
  isomorphism and uniqueness preserving the scalar sections. For commutative
  `Λ`, `finiteCoefficientInverseImageMap_constant` gives the node's commuting
  square with the recorded `Scheme.proEtaleConstantInverseImageMap` structure
  map. `finiteCoefficientInverseImageMap_empty` records the stated empty-source
  zero-sheaf and uniqueness clause.

No mismatch was found, so no Lean or node field was changed in this second
reading. In particular, the ring-valued construction does not silently impose
commutativity, and the commutative comparison theorem is restricted to
`[CommRing Λ]` exactly where the source requires it.

Edge cases checked explicitly: `U = ∅` (including the empty-cover and zero-ring
section argument), `V = ∅` (which forces the source empty), an empty test object
over a nonempty base, the zero ring, noncommutative finite rings, disconnected
schemes, identity and arbitrary morphisms, and all constant values coinciding
on an empty object. The module keeps the full site universe and does not add a
universe equality or a nonemptiness assumption.

Searches were rerun/read from `searches.jsonl` and the upstream/project trees:
LeanFinder and Loogle searches found only generic constant-sheaf results;
LeanSearch was unavailable and is recorded as unavailable; grep searches of
Mathlib `CategoryTheory/Sites`, upstream `WeilConjectures`, and project
`lean/Sheaf` found no exact pro-etale finite-coefficient ring comparison or
duplicate declaration. The existing `CategoryTheory.constantSheaf` match is
used through the dependency node. The exact Stacks pages were opened at
`https://stacks.math.columbia.edu/tag/04B3`,
`https://stacks.math.columbia.edu/tag/0H7J`, and
`https://stacks.math.columbia.edu/tag/09A5`.

The required compile was rerun with
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q05
prop-weil-pbc-proetale-constant-ring-map
lean/Sheaf/AlgebraicGeometry/ProEtaleConstantRingMap.lean`; it completed cleanly
within the 60-second limit.

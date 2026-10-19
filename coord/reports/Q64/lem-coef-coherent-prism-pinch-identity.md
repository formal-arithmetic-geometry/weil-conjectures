## Worker report

The module `Sheaf.CategoryTheory.CoherentPrismPinchIdentity` states
`CategoryTheory.CoherentNerve.coherent_prism_pinch_identity`, with `sorry` as its
entire proof. Its conclusion is nonemptiness of `PrismPinchIdentityData c d`:
a family of the canonical maps with their complete characterizations and the
asserted identity. The helper definitions contain actual data and no sorry.
No new DAG node, dependency repair, or statement correction is needed.

Sources read: Arakawa, Remark 2.5 and Proposition 3.2, printed pp.34--36,
https://cahierstgdc.com/wp-content/uploads/2025/10/CTGDC_LXVI-4.pdf (the predecessor
formula in Remark 2.5 at the 0-to-1 switch is exactly the displayed maximum
formula); Kerodon https://kerodon.net/tag/01L5, Proposition the project server; and the
five recorded dependency source modules and their full statement signatures.
The right-pinch degreewise convention is the existing dependency's
`rightPinchPrism`, which interchanges prism factors for internal hom.
The item already identifies its pointwise equality as an agent refinement;
its four proof steps are reproduced in the theorem docstring.

Hypotheses and clauses, individually:

* The coherent nerve and its identification of objects with vertices are
  `nerveFunctor` and `c : CoherentNerveComparisonStatement.{u}`. No alternative
  nerve is introduced. The supplied `d : PinchedAdjunctionData c` is precisely
  the recorded right-mapping identification, normalized on simplex generators.
* Small simplicial categories are the dependency's `SCat.{u}`. In the `prism`
  and `pinch` fields, `A : SCat.{u}` and `IsLocallyKan A` express exactly the
  hypothesis on A. The universe u is arbitrary and explicitly bound.
* Objects are `x y : A`, with no distinctness assumption. P is the literal
  `nerveFunctor.obj A`; T is the literal `hom A x y`.
* The right mapping space is the existing `SSet.Enhanced.mappingSpace`, with
  endpoints `c.vertex A x` and `c.vertex A y`. The fixed-endpoint arrow space
  is the existing `SSet.Enhanced.arrowMappingSpace` at those same endpoints.
* The maximum map `q` has domain `SSet.Pinched.resolution` and codomain
  `SSet.stdSimplex`. Its `q_generators` field fixes it on every coherent-cone
  mapping set from every initial i to the final vertex. The map to Q is
  required by HEq to be the actual mapping map of `prismConeGenerator`.
  The latter is explicitly the coherent-simplex inclusion followed by
  rigidification of the existing pinched quotient. For every subset chain B,
  the ordinal alpha is characterized by membership in B and being at least
  every initial member of B; the output is exactly that ordinal simplex.
  Thus this is the maximum map from the canonical quotient description in
  `lem-coef-pinched-cube-latching`, on the resolution actually used by Phi.
  It does not posit an unnormalized isomorphism between two presentations.
* `prismMaximum e b B` is the finite supremum of b(k) over path members k
  with e(k)=0, literally max{b_k : k in S, epsilon_k=0}. A mixed path
  contains its initial endpoint, so the finite supremum is a maximum of a
  nonempty set. It requires neither injectivity of b nor strict chains.
* `PrismSimplexFormula` first fixes the object at every position to x or y
  according to epsilon. Its second clause fixes every equal-epsilon mapping
  set to the constant identity map, via `toUnit` followed by `eId`.
* Its third clause fixes every mixed mapping map on every nerve simplex:
  for any chain B of subsets and ordinal alpha giving the maxima, the value
  is `(hom A x y).map alpha.op a`. This is precisely the composite of a with
  the nerve of the monotone maximum function. It covers all subset inclusions,
  rather than just vertices of a mapping set. Alpha exists since the sets are
  finite nonempty and the maxima are monotone under inclusion.
* `prism_formula` applies this predicate after uncurrying the image of a
  under `prism`, at every pair of ordinal simplices e and b. These pairs
  are every chain in [1] times [n]. `prism` lands in the actual fixed-endpoint
  arrow space, so its two whole ends, not just their vertices, are constant.
  The maps are simplicial morphisms, which includes every face and degeneracy.
* `tau : identityFunctor SSet -> Pinched.singular` is natural in T, and
  `tau_formula` is exactly tau_n(a)=q^n followed by a. The `.down` only removes
  the canonical universe-preserving ULift in the recorded singular object.
* `pinch_formula` characterizes the right-pinch map on every mapping simplex
  by the identical equation used in `right_pinch_comparison`: uncurrying its
  inclusion is `rightPinchPrism` followed by that simplex. Thus `pinch` is
  the canonical j from that node; it is not a new arbitrary comparison map.
* `identity` is literally
  `prism A hA x y = tau.app (hom A x y) >> (d.identification A x y).inv >>
  pinch A hA x y`, with Lean's composition symbol in the actual source.
  This is equality in the Hom set of simplicial sets, not equality up to
  homotopy and not merely equality on vertices.
* `naturality` gives equality after the existing arrow-space inclusions for
  every enriched functor F between locally Kan categories. The right-hand
  side precomposes with `F.map x y`, and the left-hand side postcomposes the
  internal functor with `nerveFunctor.map F`. The inclusions are monos, so
  this is the usual naturality square with the transported endpoints.
  Functors identifying objects are permitted. The equality and naturality
  also give naturality of the displayed factorization.

Dependency declarations used (all source modules opened and read):

* `Sheaf.CategoryTheory.CoherentNerveComparison`:
  `CategoryTheory.CoherentNerveComparisonStatement`, its `vertex` and
  `locally_kan_quasicategory` convention, and the recorded
  `CategoryTheory.coherent_nerve_comparison` existence interface.
  Its infrastructure supplies `SCat`, `hom`, `IsLocallyKan`, `nerveFunctor`.
* `Sheaf.CategoryTheory.CoherentNervePinchedAdjunction`:
  `CategoryTheory.CoherentNerve.PinchedAdjunctionData`, especially its actual
  `identification`, normalized `simplex_formula`, and forward/inverse formulas;
  `coherent_nerve_pinched_adjunction` supplies this datum.
* `Sheaf.CategoryTheory.PinchedRigidificationResolution`:
  `SSet.Pinched.resolution`, `singular`, `coherentSimplex`,
  `coherentSimplexInclusion`, `rigidification`, `simplex`, `quotient`;
  `pinched_rigidification_resolution` is the corresponding existence and
  weak-equivalence theorem, imported as the node's recorded interface.
* `Sheaf.AlgebraicTopology.PinchedCubeLatching`:
  `SSet.PinchedCube.pinched_cube_latching` supplies the quotient description
  and maximum descent used by the proof plan. The statement normalizes q on
  its generators without replacing the other dependency's resolution by its
  independently constructed colimit. This import is retained for stage 3.
* `Sheaf.CategoryTheory.RightPinchComparison`:
  `SSet.Enhanced.arrowMappingSpace`, `arrowMappingSpaceInclusion`,
  `rightPinchPrism`, and the characterization of `right_pinch_comparison`.

Edge cases checked before writing and again after compilation: n=0 gives one
mixed edge and maximum 0; r=0 only has equal-side objects and identity maps;
repeated vertices and noninjective b retain the maximum formula; i=j is an
equal-side identity; a reversed 1-to-0 pair has empty path nerve and the unique
map; x=y still retains the side labels, so a mixed map need not become an
identity. Empty categories make the family over objects vacuous, appropriately;
empty Hom spaces contribute no input simplex. No characteristic, nonemptiness,
object-distinctness, or finite category hypothesis is imposed.

Searches actually run:

* `msearch.py ... leansearch 'The coherent nerve maximum coordinate prism
  equals the right pinch comparison map'`: eight hits, including ordinary nerve,
  right_edge, and Cech-conerve maps. None states this identity.
* `msearch.py ... leanfinder` with that same query: eight hits, including
  `SSet.prodStdSimplex.isoNerve`, `stdSimplex.isoNerve_hom_app_apply`, and
  `nerve.right_edge`; none gives the prism-pinch identity.
* An earlier leanfinder query, 'The coherent nerve prism on an enriched mapping
  simplex equals right pinch composed with the pinched simplex maximum map',
  lost its process handle during the provider interruption. I do not claim a
  result for that interrupted search; the completed query above replaces it.
* `msearch.py ... loogle 'CategoryTheory.SimplicialThickening'`: twelve hits
  describing thickening, its path category, functor maps and category laws.
  These are the Mathlib definitions used by the dependencies, not this identity.
* `msearch.py ... grep 'coherent.*prism|prism.*pinch|pinch.*maximum'
  AlgebraicTopology`: zero hits.
* `rg` for coherent/prism/pinch and the proposed declaration names in the
  upstream WeilConjectures source, Mathlib, and `lean/Sheaf`: no declaration
  states this identity. Nearby `SpacePointCoconeCriterion` concerns only the
  category of Kan complexes and its family-of-points comparison;
  `DiagonalCoherentNerveComparison` states the global diagonal comparison,
  not its explicit mapping-fiber identity. Their source was read.
* The prescribed upstream grep for the full item id returned no hits; the
  proposed names also have no hit in `dag/lean_names_upstream.json`.

Validation: `scompile.py Q64 lem-coef-coherent-prism-pinch-identity <module>`
compiled the module at both its sandbox and final library module paths with
exit code 0 and no warnings. The first compile identified an unopened
`CartesianMonoidalCategory.toUnit`; opening its owning namespace repaired it.
All universes and variables are explicit; every line is at most 100 characters.
Only the item's `lean` field changes. No statement dispute or node fault found.

## Second reading by Q64

This is the author's separate second pass; the maintainer performs the
independent delivery review under the dispatched brief. I reopened the node,
its five dependency signatures, and the completed module, and matched the
clauses as listed above. In particular I checked the often-lost clauses:
whole fixed endpoints, x=y, every subset-inclusion chain, noninjective simplex
operators, the q-normalization for every initial endpoint rather than only zero,
actual simplicial-map equality, and functors identifying objects. All are
present. The finite supremum is used only on nonempty mixed subsets, and the
conditional ordinal formulas are not vacuous because their maxima are monotone.
The only code correction after the first compile was opening the namespace for
`toUnit`; it changed no statement or mathematical clause. No data is selected
from an unconstrained existence theorem. The q, tau, prism, and pinch outputs
are fixed by their complete formulas; only the named main theorem is postponed.

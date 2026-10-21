## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteRootSiteComparison` states
`AlgebraicGeometry.Scheme.finiteRootSiteComparison`. Its complete assertion is the
exposed proposition `FiniteRootSiteComparisonSpec A`: there are comparison
isomorphisms sigma and canonical root-induced arrows d, satisfying twelve groups
of normalization and coherence clauses. The theorem alone is postponed with
`sorry`. Its docstring gives all six proof steps of the DAG node. Definitions
have real data and no postponed proof or arbitrary witness choice.

The node's mathematical statement, proof and proof dependencies are unchanged.
The statement dependency list additionally names two already landed nodes:
`def-sfb-cartier-reduction-data`, whose recorded declarations include the canonical
root comparison, and `def-sfb-constant-ring-module-restriction`, which owns the plain
scalar-restriction definition retaining the original root groups in fixed coefficients.
No new node or dependency repair is needed.

Hypotheses and objects, clause by clause:

- A finite commutative ring is `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  The theorem assembles all exponents and schemes simultaneously so the power
  squares compare the very same chosen sigma family. Positive m is `hm : 0 < m`;
  annihilation is `hA : (m : A) = 0`. This is equivalent to mA=0 by multiplication
  with each element, including when A is the zero ring.
- An arbitrary scheme is `T : Scheme.{u}`; invertibility is
  `hT : IsUnit (m : Γ(T, ⊤))`. Local inverses glue uniquely, so this says exactly
  that m is invertible on T. There is no affine, Noetherian, qcqs or finite-type
  assumption. Test schemes are the original `T.ProEt`, with object universe u+1
  and morphism universe u. No universe equality is imposed.
- The etale root sheaf is the recorded `T.rootsOfUnitySheaf m`. The pro-etale
  root sheaf is exactly the recorded `proEtaleRootsOfUnitySheaf T m`.
  The canonical root isomorphism c is the existing
  `ProEtale.cartierRootsIso T m hm hT`, which is the kernel comparison induced
  by the existing canonical units comparison. It is not restated or copied.
  This is an additive isomorphism between m-torsion sheaves. By the unique
  normalized constant Z/m-module structures in the recorded torsion lemma,
  every such additive map is Z/m-linear; there is no weaker set-only comparison.
- E is exactly `finiteEtaleTateLine T m A hA`. It sheafifies the sectionwise
  extension along `finiteEtaleTwistScalar m A hA`, using the already recorded
  `finiteEtaleMuModulePresheaf`. This equals `finiteEtaleTateSheaf A m T hA 1`
  by unfolding the published definition, so the published pullback maps apply.
- D is `finiteRootProTensor A m hm hA T`, the sheafification of the sectionwise
  scalar extension of `finiteRootProModule T m hm`. The latter restricts the
  RECORDED `proEtaleRootsOfUnityModule T m hm` along the constant-ring
  sheafification unit and the canonical ULift ring equivalence. Its underlying
  group at W is definitionally the original pro-etale root group. Thus this
  is the actual balanced Z/m tensor, with A acting on its A factor, not the
  comparison inverse image used as a surrogate for the target tensor.
  Tensor factors are written a tensor z, as in the dependency's E construction;
  commutative tensor symmetry identifies this with the source's z tensor a.
- sigma has type `comparisonUpperStar (ModuleCat A) T |>.obj E ≅ D`.
  Its morphisms are A-linear, equivalently linear for the corresponding constant
  sheaf. The canonical module-valued Kan/sheafification inverse image is the
  coefficient specialization of the recorded geometric comparison.
- The `root_sections` conjunct supplies an ADDITIVE equivalence from the
  comparison inverse-image sections at every W to the global sections of
  `Etale.upperStar AddCommGrpCat W.hom` of the etale roots, evaluated at
  `op (Etale.mk (𝟙 W.left))`. Composing it with the recorded normalized etale
  root pullback and kernel inclusion yields exactly the unit obtained from c.
  The kernel inclusion is monic, so this determines the equivalence and the
  same-root identification uniquely. It is the precise Gamma(W_et, f^-1 mu)
  intermediate identification of the node, without assuming W affine.
- `root_unit` evaluates the comparison unit at an etale U and restricts along
  an arbitrary T-map `f : W.unop ⟶ (toProEt T).obj U.unop`. After c, the actual
  unit is `Units.map f.left.appTop.hom.toMonoidHom` of the original unit, which
  is f-sharp(z), with no arbitrary root lifts.
- `tensor_unit` gives the node's stated equivalent normalization of the
  canonical balanced-tensor comparison: sigma of the comparison unit on
  `finiteEtaleTateOneGenerator ... a z`, restricted along f, is
  `finiteRootProGenerator ... a` of that root transported by c. Combined with
  `root_unit`, this is exactly f-sharp(z) tensor a, for EVERY a and every
  etale/pro-etale test pair. Locally constant scalar sections are locally
  constants, and tensor/sheafification universal properties uniquely determine
  the complete sheaf morphism from this formula. Hence the scalar and balanced
  tensor normalization is part of the assertion.
- `d_unit` determines d under the RECORDED `proEtaleSheafAdjunction`: its
  adjunct sends a tensor z to a tensor the image of z under the RECORDED
  `proEtaleRootsOfUnityDirectImageMap v m`. This map is precisely projection
  pullback on units. Since the scalar is the very same a and local tensors
  generate after sheafification, d is the canonical root-induced tensor map,
  rather than an arbitrary map merely assumed to satisfy a square.
- The etale e is the degree-one component
  `(finiteEtaleTwistPullbackData A m hm hA).c v hT hT' 1`.
  `scheme_square` is exactly
  `proPull.map sigma.hom ≫ d = kappa ≫ comparison.map e.hom ≫ sigma'.hom`.
  kappa is the `.inv` of the recorded `comparisonCoefficientPullbackIso`,
  whose forward orientation is nu'_star after etale pullback to pro pullback
  after nu_star. Its normalization is the adjunction mate of the sectionwise
  direct-image identification, not a separately chosen natural isomorphism.
  `d_isIso` asserts invertibility for every v with m invertible on its target.
  An additional hT' in the displayed square simply supplies the corresponding
  pulled-back invertibility proof used by the published etale interface; it
  follows from hT by pulling back an inverse.
- `root_square` is the same equation before scalar extension, using precisely
  `proEtaleRootsOfUnityInverseImageMap v m` and the recorded etale root
  comparison `.r`. This also implies invertibility of this pro-etale root map.
- `d_id`, `d_comp`, `root_id`, `root_comp` use the canonical inverse-image
  identity and composition isomorphisms, not strict identifications of chosen
  fibre products. They are restricted to the positive invertible exponents of
  the source statement. Together with the existing etale and comparison-square
  coherence and the two scheme squares, these give the asserted identity and
  composite compatibility of c and sigma's squares.
- `powers` quantifies over positive m,m' with `hdiv : m ∣ m'`, the same A,
  the two annihilation proofs, and schemes on which both are invertible.
  The second annihilation proof follows from the first and divisibility;
  invertibility of m follows from that of m'. Neither is a new restriction.
  It supplies q,tE,tP. The equation of q followed by kernel inclusion says
  exactly q(z)=z^(m'/m). The tE and tP equations say a tensor z goes to the
  SAME a tensor that power of z. The last two equalities are exactly the root
  and scalar-extension comparison power squares. All maps are thereby fixed
  by their normalized generators, including the evident reduction of the
  constant scalar rings. Powers commute with projection pullback of units;
  hence these normalized maps also commute with the scheme squares.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`; the recorded
  root modules and coefficient extensions use its constant-ring sheafification.
- `Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf`:
  `proEtaleRootsOfUnitySheaf`, `proEtaleRootsOfUnityModule`,
  `proEtaleRootsOfUnityInclusion`, `proEtaleRootsOfUnityTransition`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: the recorded
  independent-universe sheaf tensor API, with its public sectionwise tensor
  and scalar-extension foundation. D uses Mathlib `ModuleCat.extendScalars`
  and `presheafToSheaf`, the fixed-coefficient presentation of that tensor.
- `Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnityInverseImage`:
  `proEtaleRootsOfUnityDirectImageMap`, `proEtaleRootsOfUnityInverseImageMap`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `proEtaleBaseChange`,
  `proEtaleSheafInverseImage`, `proEtaleSheafAdjunction`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: `proEtaleSiteComparison`,
  `proEtaleSiteComparisonModules`; its upstream foundation provides the same
  comparison as `ProEtale.comparisonUpperStar` and `comparisonAdjunction`.
- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`:
  `finiteEtaleTwistPullbackData`, with `.r` and `.c`; its public foundations
  provide `finiteEtaleTateLine`, `finiteEtaleTateOneGenerator`,
  `finiteEtaleTwistScalar` and the etale root sheaf.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `Etale.upperStar`, `Etale.upperStarLowerStarAdjunction`.
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`: its recorded
  support interface publicly reuses `comparisonCoefficientPullbackIso`,
  `proEtaleComparisonId`, `proEtaleComparisonComp` from
  `Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence`. These are the SAME
  canonical constructions as the support-prefixed abbreviations.
- `Sheaf.AlgebraicGeometry.CartierReductionData`:
  `ProEtale.cartierRootsIso`, built from `cartierRootsComparison` and the
  normalized units comparison. The whole source signature and construction
  were read; it is available for every positive invertible m, without divisors,
  prime-power, finiteness or support assumptions.
- `Sheaf.CategoryTheory.ConstantRingModuleSheaves`:
  `CategoryTheory.constantRingModuleRestriction`, recorded by
  `def-sfb-constant-ring-module-restriction`; this restricts scalars along
  `toSheafify`, retaining exactly the original underlying abelian presheaf.
  The equivalence theorem `constant_ring_module_sheaves` is not used.

All stated proof dependencies are imported (possibly publicly as statement
foundations). The two Mathlib proof dependencies with no lean record are
`Adjunction.comp` in `Mathlib.CategoryTheory.Adjunction.Basic` and
`unit_conjugateEquiv_symm` in `Mathlib.CategoryTheory.Adjunction.Mates`; their
full source signatures and unit equations were read. No module is available
for an unstated dependency and none is invented.

Searches actually run with msearch.py (Q19 and this item):

- leanfinder: "Etale proetale comparison roots of unity sheaf tensor coefficients
  canonical scheme pullback" returned eight ring/etale/pullback results,
  including `StandardEtalePair.hasMap_X` and `Scheme.Pullback.ofPointTensor_SpecTensorTo`;
  no complete comparison/coherence statement.
- loogle: `"rootsOfUnitySheaf", "comparison"` returned zero results.
- grep, AlgebraicGeometry: `rootsOfUnitySheaf|finiteRootSite|finiteEtaleTateLine`
  returned zero Mathlib hits.
- leansearch: "Canonical etale proetale roots of unity tensor finite coefficients
  comparison isomorphism coherent under scheme pullback" returned eight general
  etale algebra/base-change/module pullback results; no full match.
- rg over project `lean/WeilConjectures` and `lean/Sheaf` for rootsOfUnity,
  finiteEtaleTateLine, root/module/tensor and comparison names found the etale
  tensor construction and canonical `cartierRootsIso`, both reused here.
  The root-comparison portion already exists, but no declaration states all
  scalar, arbitrary-test section, scheme and power clauses of this item.
  The upstream grep for this blueprint id returned no result.
- The added two landed node ids were checked against the whole DAG; traversing
  their statement/proof dependencies reaches no path back to this item.

Sources read: `literature/stacks-project/proetale.tex`,
`lemma-describe-pullback-from-etale` (0GLZ), including its unit/counit construction;
`literature/stacks-project/sites-modules.tex`,
`lemma-tensor-product-pullback` (03EL), with the adjunction/bilinear-Hom proof;
and the current blueprint's vector-bundle-purity statement. No node correction
or STATEMENT-DISPUTED issue was found.

Edge cases checked before formalizing: m=1 forces A to be the zero ring and
both tensor sheaves to be zero; the root groups are trivial and all formulas
still apply. A may be the zero ring for any positive m. The empty scheme and
empty covering families are permitted by the sheafification and kernel
constructions. No nontrivial-ring instance, primitive-root choice, affine-test
restriction, flatness of A over Z/m, or relation on the site universes was
added. Identity maps, arbitrary composites, m=m', and arbitrary divisible
positive exponents occur in the quantified laws.

Compilation uses only scompile.py. The construction and complete assertion
compiled locally against the published server library in 30.0 and 39.1 seconds
on the first complete pass. Its only warnings were two overlong comments;
these were wrapped. The final dry run recompiles the final source and performs
server preflight before delivery. A temporary structure encoding was replaced
by the equivalent explicit existential proposition, avoiding generated
recursors and exposing all laws without choosing data from a bare Nonempty.

## Second reading by Q19

I reopened the node and final source for a separate clause-by-clause pass in
this single-worker session; the dispatcher explicitly prohibits starting
another agent, so this is not claimed as an independent worker review. The
maintainer supplies the independent review of the delivery.

I checked the exact E and D definitions, the actual c construction, the
intermediate etale-global-section equivalence on EVERY weakly etale test,
and the comparison-unit formula after arbitrary W-to-U restriction. The
tensor scalar remains the same a, both in sigma's formula and d's adjunct.
I checked the orientation of kappa: the `.inv.app` is essential, because the
recorded comparison has the opposite orientation to the square in this node.
I also checked the order of categorical composition, the `.c ... 1` etale
map, the root-only square, all identity/composite maps, and the two power
squares against the original statement. I restricted the explicit identity
and composite laws to positive invertible exponents, so they do not add a
zero-exponent assertion outside the source. The scalar module and all
sectionwise tensor data are fully constructed; there is only one sorry,
the named theorem with this node's complete proof docstring. All variable
and universe binders are explicit, and every delivered declaration carries
the source and blueprint marker. No mathematical mismatch remains from this
pass. Final compile and dry-run results are obtained by the prescribed tools.

Final validation: `deliver2.py Q19 lem-amb-finite-root-site-comparison --no-push`
returned `OK (dry run)` at commit `61519eeadd2`: server preflight and final
per-file compilation passed, with no remaining warnings.


## Returned-delivery repair (2026-10-21)

H2, immutable reviewed head `7fcd82765c8d`: replaced the added statement-dependency
citation `lem-cbc-constant-ring-module-sheaves` by the existing definition owner
`def-sfb-constant-ring-module-restriction`, exactly as the return requests. I read
that node's statement, its `existing: true` record and the full signature,
docstring and body of `CategoryTheory.constantRingModuleRestriction` in
`Sheaf.CategoryTheory.ConstantRingModuleSheaves`. The use in
`finiteRootProModule` is the plain restriction functor along `toSheafify`, not a
choice from the equivalence theorem. The module import already provides this
same declaration, so the Lean source and all mathematical clauses are unchanged.
Updated `lean.note` and the dependency explanations above. No new node,
dependency module or mathematical statement correction is involved.

The initial prescribed dry run of the retained packet passed at `09b7afa9908`.
That mechanical pass did not remove the independent review's H2 fault, which is
repaired here. The repair self-check reread the owning definition and its use,
verified the dependency replacement and checked the unchanged Lean source hash
`597db5af26cf0c675f994c546638a38a45d06645057f55cdd86bd809c567a43c`.
Fresh compile and dry-run results follow below.

Repair validation: the explicit `scompile.py` run passed both sandbox and library
checks in 32.0 s and 37.4 s, with no warnings or errors. The repaired packet's
`deliver2.py --no-push` returned `OK (dry run)` at `1fbea631abd`, passing server
preflight and per-file compilation. The self-check also verified the verbatim
recorded signature, exactly one named theorem with `sorry`, unchanged non-owned
node fields and the two intended existing-definition dependencies.

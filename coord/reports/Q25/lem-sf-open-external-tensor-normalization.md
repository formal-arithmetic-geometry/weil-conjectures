## Worker report

Delivered `Sheaf.SixFunctors.OpenExternalTensorNormalization`, main declaration
`AlgebraicGeometry.ProEtale.OpenExternalTensor.finite_open_external_tensor_normalization`.
The theorem has `sorry`; every definition has actual data. Its docstring retains all eight
steps of the DAG proof. The module contains the geometric and comparison helpers needed
to express every equation, listed in `lean.declarations`. No mathematical statement correction,
dependency module, or disputed statement is needed. The H2 repair adds a definition
node recording the existing finite open operation helpers, without adding Lean definitions.

The statement dependencies were read in full, including their recorded interfaces and
source docstrings. The example CompactObject module is withdrawn; its node now records
the identical upstream `WeilConjectures.CategoryTheory.CompactObject`, which was read.
The current blueprint symmetry paragraph and Stacks sites-cohomology.tex,
`lemma-j-shriek-and-tensor` (0GL1), were read directly.

### Hypotheses and coefficient presentations

* `D : FiniteFieldDatum` carries p, a, q and the specified algebraic closure k;
  `C : D.CoefficientDatum` carries the distinct prime ell and algebraic closure of
  its coefficient field. `E`, its field/algebra/finite-dimensional instances, and
  `n`, `hn : 1 ≤ n` give the specified finite extension and positive quotient.
  The ring is exactly `Padic.coefficientExtensionRing C.l E n`, with its recorded
  valuation-ring/uniformizer construction. Its standard `ULift.{u+1,u}` is the
  same coefficient presentation used by the existing finite operations.
* `S : SixFunctorDatum D C E n hn` retains the complete prescribed datum, including
  completed integral, rationalized and common-finite-stage operations. The conclusion
  concerns only its finite stage, as does the source. It does not impose extra
  identities between coefficient universes.
* `B X₀ Y₀ Xb₀ Yb₀ : SixFunctorSpace D` are finite-type schemes over k.
  The five `IsSeparated ...obj.hom` instances impose separatedness over k.
  `f`, `g` are morphisms over k to B; their `IsSeparated`, `LocallyOfFiniteType`
  and `QuasiCompact` instances give precisely separated finite type.
* `j₀`, `k₀` are morphisms over k with their `IsOpenImmersion ...hom.left` instances.
  Since these schemes are finite type over a field, their opens are quasi-compact;
  no arbitrary non-quasi-compact open case is being added to the finite-type setting.
* `d : Diagram ... T₀ Tb₀` retains the projections, product open u, two intermediate
  products, four Cartesian open base-change squares, factorization equations, and
  projection equations. `_barProduct` and `_product` specify the two outer product
  cones by their actual universal properties. This expresses the source's choices
  of products without unfolding Mathlib's scheme constructions during kernel checking.
  All such choices are quantified; the additional diagram fields are the canonical
  geometric factorizations, not new mathematical assumptions on j or k.
* `K`, `L : finiteTorConstructibleCategory ...` are exactly the recorded D^b_ctf
  objects. `FiniteAssertion` applies the inverse of
  `sixFunctorFiniteRealization D C E n hn X₀` (and Y₀) to their underlying objects.
  This is the existing equivalence from the intrinsic ring-sheaf presentation to
  constant-scalar pro-etale module sheaves; it is not a newly chosen category or map.
  The operations are therefore stated in the same finite fixed-scalar coordinates
  as the normalization dependency.

### Every conclusion clause

* `ambient A d K L` is the tensor of the ambient projection pullbacks of j!K and k!L.
  `inside A d K L` is D = p*K tensor q*L.
* `comparison A d K L` is the actual prescribed composite: beta for the square
  `d.first`, gamma for j₁, canonical pullback composition along `j₁_qb`, beta for
  `d.second`, rho for k₁, canonical pullback composition along `k₁_r`, and the
  unit-normalized open compositor followed by the geometric equality `factor`.
  `FiniteOpenProduct.rho` is the signed symmetry, gamma, extension of signed
  symmetry. No arbitrary comparison arrow or Nonempty choice is supplied.
* `BinaryAssertion` asserts `IsIso comparison`. The simultaneous naturality equation
  in `FiniteAssertion` uses `ambientMap` and `insideMap` for every pair of morphisms
  K→K', L→L'. Thus these components form the asserted natural isomorphism.
* `restriction` has direction D → u*H, built only from the two open units and
  canonical projection/tensor comparisons. The equation
  `restriction ≫ u*.map comparison = adj.unit.app D` says exactly that restriction
  of e is the identity, after the specified section-normalized identifications.
  It does not define the restriction identification by using e itself.
* `oppositeComparison` uses `d.swap`: its first square is `first'`, its second is
  `second'`, and its normalized compositor is the other factorization. The outer
  and inner signed symmetries put the factors back in X,Y order. The second
  `IsIso` and equality conjuncts assert invertibility and agreement of this map.
* The last `BinaryAssertion` equation is
  e ≫ u!(signed symmetry) = (signed ambient symmetry) ≫ reversed e.
  Here `d.swap` describes the swapped cones after their canonical transport back
  to the same products: the two projections are exchanged, and all four squares
  and both intermediate factorizations are exchanged. This is the usual typed
  common-cone formulation of the source's swap square; it retains Koszul signs
  via the existing `FiniteOpenProduct.sigma`, descended from cochain braiding.
* The final forall in `FiniteAssertion` includes arbitrary third finite-type
  separated schemes W₀,Wb₀, an open l₀ over B, a separated finite-type h:Wb₀→B,
  and M in its recorded D^b_ctf. It quantifies every choice of the four binary
  product diagrams for the two bracketings and their actual product universal
  properties. `Triple` records their canonical projection equations and equality
  of the two resulting triple product opens. These are exactly the identifications
  made when transporting both bracketings to the same triple product cone.
* `tripleLeft` first applies the (j,k) comparison, then the (j×k,l) comparison;
  `tripleRight` first applies (k,l), then (j,k×l). `outerAssociator` and
  `innerAssociator` contain only canonical pullback composition and the existing
  derived tensor associator. `shriekCongr` transports only the equality of the
  geometric open maps, while the actual open compositors occur in every comparison.
* `TripleAssertion` equates these two composites. Its two further equations say
  separately that their restrictions are identity via the single independently
  defined `tripleRestriction`. This identification is built from the binary
  restriction identification, the third open unit, pullback composition and tensor
  comparison, and contains neither triple composite. Thus the source's final
  assertion about both identity restrictions is explicitly retained.

All intermediate binary comparisons are defined on arbitrary ambient unbounded
complexes; there is no additional constructibility or Tor-amplitude assumption on
an intermediate external tensor. All isomorphism assertions live in the derived
category, not only on cohomology.

### Dependency declarations used

* `Sheaf.Paper.SixFunctorDatum`: `WeilConjectures.SixFunctorDatum`, its inherited
  operation datum and coefficient setting; `SixFunctorSpace` and
  `sixFunctorFiniteRealization` are its publicly imported recorded definitions.
* `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage`, with its
  actual supplied open comparisons, is the recorded exchange dependency. Its
  finite specialization is the canonical open maps below; the construction uses
  those actual finite maps, not freely supplied stage fields.
* `Sheaf.Paper.SixFunctorDualNotation`: the recorded projection convention and
  `SixFunctorDatum.finiteCoefficientDual` are publicly imported. No dual object is
  needed in this theorem; its relevant projection convention is the existing
  open gamma in direction j!K tensor L → j!(K tensor j*L).
* `Sheaf.SixFunctors.OpenTensorNormalization` and its public data module:
  `openTensorNormalization`, `FiniteD`, `finiteShriek`, `finiteGamma`; and
  `AlgebraicGeometry.ProEtale.ordinaryOpenExtensionBaseChangeIso`.
* `Sheaf.Paper.FiniteOpenProductSwap`: existing `FiniteOpenProduct` helpers
  `pull`, `pullComp`, `square`, `tensor`, `tensorMap`, `tensorIsoMap`,
  `tensorPullIso`, `adj`, `comp`, `gamma`, `rho`, `sigma`. The new definition node
  `def-sf-finite-open-tensor-operations` owns these existing helpers and is cited in
  stmt_deps. The theorem node is not a statement dependency. Its theorem covers the binary result on arbitrary
  ambient complexes; it does not contain triple associativity or the present
  six-functor finite-Tor specialization, so it is not an exact existing match.
* Proof imports retain the recorded open normalization, generic independent-
  coefficient tensor descent, and Mathlib adjunction mates/uniqueness machinery.
  The ringed tensor-pullback and total-complex dependencies are already exposed
  through the recorded normalization imports. Composite adjunction is Mathlib
  `Adjunction.comp`; its normalized comparison is `Adjunction.leftAdjointUniq`,
  with `unit_conjugateEquiv_symm` expressing the required unit equation.

### Edge cases checked

Empty schemes and empty opens are allowed: no Nonempty or inhabited scheme binder
occurs. Identity opens are allowed, including all three being identities; the
formulas then use the actual open units and canonical pullback identities. Zero
objects and zero morphisms are allowed in both inputs and the third factor.
The smallest coefficient exponent n=1 is retained. No invertibility of arbitrary
coefficient transition maps, completion, or extra properness is imposed. Objects
of odd cohomological degree use the existing descended signed symmetry; the two
signs in rho cancel as (-1)^(ij+ji). The third-factor clause retains arbitrary
intermediate external products in ambient categories. Site objects and morphisms
retain their respective u+1 and u universes, and coefficients use the existing
canonical lift, with no new universe equality.

### Searches and validation

Searches used the prescribed msearch wrapper (the exact output is in searches.jsonl):

* LeanFinder: “Extension by zero along a product of open immersions commutes with
  external derived tensor product with normalized symmetry and associativity”.
  Eight hits about gluing/restriction; no exact comparison with all coherence clauses.
* Loogle: `Functor.prod, Adjunction.leftAdjointUniq`; returned no hit, unknown
  unqualified Functor.prod. Source inspection then located the actual adjunction
  composition and unique-left-adjoint declarations in Mathlib.
* Mathlib grep: `extensionByZero|externalTensor|externalProduct`, CategoryTheory.
  Hits describe external products of functors and Kan extensions, not this result
  on product pro-etale sites.
* LeanSearch: “The external product of two extensions by zero is extension by zero
  along the product open immersion and the comparisons are associative”. Eight hits
  include Ext composition and external-functor-product units; none is this theorem.
* rg of `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`:
  `externalTensor|ExternalTensor|openExternal|external_tensor`, plus the item id.
  Upstream hits concern affine quasi-coherent external coefficients, not open
  derived extension. A broader search of finite open helpers found the recently
  landed `FiniteOpenProductSwap`, which is reused as noted above.

Every compile used scompile.py. Initial timeouts came from coefficient-specialized
monoidal-instance elaboration and were repaired by using the existing named tensor
helpers and evaluating the existing associator before specializing its coefficient
category. The complete delivered file then compiled cleanly in about nine seconds,
without increasing the 60-second file limit. No global build or repository write
was performed. The delivery wrapper performs the authorized preflight and push.

## Second reading by Q25

This is the worker's second pass, not a claim that another agent performed an
independent review: the dispatcher explicitly prohibits starting other agents, and
the maintainer performs the independent review after delivery. I reopened the node
and final file together. The pass checked all finite-field/coefficient hypotheses,
separated finite-type domains, open/product squares, finite-Tor inputs, the explicit
beta/gamma/rho order and normalized compositor, the direction of the unit equation,
naturality, the swapped projections and signed symmetries, the two triple composites,
and both separate triple restriction identities. I corrected the diagram's field
binders, the direction descriptions of restriction identifications, and removed
expensive duplicate specializations of existing operation helpers. No source
statement was changed and no clause was dropped.

## New nodes

`def-sf-finite-open-tensor-operations` records the existing plain definitions in
`Sheaf.Paper.FiniteOpenProductSwap` with `existing: true`. Its `lean.declarations`
lists tensor, the two tensor actions, pullback and its composition/equality/tensor
comparisons, open adjunction, normalized compositor, base change, gamma, signed
braiding, and rho, together with their coefficient/unspecialized-braiding helpers.
The primary declaration is `WeilConjectures.FiniteOpenProduct.tensor`; the full
coefficient context is the source's explicit `A : Type (u + 1)` with `[CommRing A]`
and `[Finite A]`. No theorem, including `finiteOpenProductSwap`, is listed.
The source is the blueprint symmetry paragraph used by the item and Stacks 0GL1,
03DI and 07A4. The existing source docstrings name these places and the original
blueprint theorem node; the reviewer explicitly permitted ownership by an
existing:true record on this unchanged module. No module is copied or rewritten.

For each definition clause: `tensor`, `tensorMap`, `tensorIsoMap` evaluate and map
the published derived bifunctor; `pull` is exact inverse image localized termwise;
`pullComp`, `pullCongr`, `square`, `composeEq` are its composition/equality
identifications; `tensorPullIso` uses the canonical exact/K-flat comparison; `adj`
is the existing open adjunction; `comp` is exactly the `leftAdjointUniq` composite
in source lines 167-171; `beta` uses ordinaryOpenExtensionBaseChangeIso; `gamma`
is finiteGamma followed by the exact pullback identification; `sigma` evaluates
`proetSigma`, the descent of signed cochain braiding; `rho` is sigma, gamma,
then j!-of-sigma; `coefficientNoetherian` is the finite-ring instance. The node
claims no coherence or external-product theorem. Empty schemes, empty and identity
opens, zero objects, and arbitrary unbounded complexes remain allowed; all
operations retain the existing site and coefficient universes.

The new-node searches are recorded verbatim as returned summary records in its
mathlib_searches: LeanSearch returned eight generic inverse-image/adjunction hits;
LeanFinder returned eight unrelated polynomial-tensor hits; Mathlib grep returned
sixteen generic leftAdjointUniq hits. DAG/blueprint and source searches found the
existing helpers in FiniteOpenProductSwap and their list under its theorem node,
but no definition node owning them. This is a record of existing constructions,
not a second implementation.

## Repair of returned delivery d79810dff23d

H2: removed `lem-pur-finite-open-product-swap` from the packet's statement
dependencies and added `def-sf-finite-open-tensor-operations`. Relative to the
current base, which never had the extra theorem dependency, the only dependency
change is addition of the new definition node. The theorem and every helper in
OpenExternalTensorNormalization are retained from the checked packet.

For the comparison advisory, the item's `comparison` is the chosen-cone interface
to the same canonical chain as FiniteOpenProduct.comparison. In the latter's
chosen pullbacks, `leftComparison` expands to beta, gamma and projection
composition; its extended `rightComparison` expands to beta, rho and projection
composition; `compTo` expands to comp and geometric equality transport. These are
exactly the six factors of the item comparison in source lines 162-185. The item
accepts arbitrary product cones and their canonical squares so that all four
binary products in the triple clause can use a common triple cone. It reuses the
operations, rather than choosing another e; changing chosen cones transports this
same chain by their unique cone isomorphisms. No equality of unrelated arbitrary
maps is assumed.

The swap advisory is retained as an advisory: Diagram.swap exchanges projections
on the common cones after canonical geometric swap transport, and BinaryAssertion
writes the resulting signed square on those cones. The independent review
explicitly checked this clause and accepted the equations; the repair changes
ownership records only.

### Repair self-check by Q25

Reopened both node records and source lines 83-223 alongside the retained item
module. Every FiniteOpenProduct name used by the item is now listed in the new
definition node; none depends on finiteOpenProductSwap. Rechecked the new node's
explicit finite-ring context, unbounded categories, directions of pullComp, comp,
tensorPullIso, gamma and rho against their bodies. The saved Lean statement and
all clauses accepted by the independent reviewer are unchanged. The first saved
packet dry run passed (73189f5aaae); that mechanical pass did not resolve H2,
which the new node and dependency replacement now repair.

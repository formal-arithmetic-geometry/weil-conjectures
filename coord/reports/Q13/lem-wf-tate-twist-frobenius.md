## Worker report

The delivery states `WeilConjectures.wfTateTwist_closedFrobenius` in
`Sheaf.Paper.WeilTateTwistFrobenius`. It also repairs the unusable recorded
interface of `def-wf-tate-twist` in `Sheaf.Paper.WeilTateTwistsFinite` under §1(B).
The item's mathematical statement, statement dependencies, proof and proof dependencies
are unchanged. The dependency copy changes only `lean`. No new node is created.
All newly stated theorems have `sorry` proofs; definitions contain real constructions.

Sources read: the main-20261015 statement and proof of
`sec-algebraic-groups-lie-algebras/sk-p-cyclotomic/lem-wf-tate-twist-frobenius`,
the eight expanded proof steps of the DAG node, and the main-20261015 definition
`sk-d-ab-cyclotomic/def-wf-tate-twist`. The dependency's earlier stage-1 review
explicitly warns that the upstream Qbar construction and the framework signed
sheaf construction are not interchangeable without comparison. This delivery
retains that comparison and verifies the derived tensor/Hom characterizations.
There is no statement correction or mathematical dispute.

Hypothesis and clause correspondence for the item:

* `D : FiniteFieldDatum.{u}` supplies the prime `p`, exponent `a ≥ 1`,
  `q = p^a`, arbitrary finite base field `D.k₀` with that cardinality, and
  the chosen algebraic closure `D.k`. It does not fix a particular closure.
* `c : D.CoefficientDatum` supplies the prime `c.l`, its primality instance,
  `c.different : c.l ≠ D.p`, and the chosen coefficient algebraic closure.
* `E : Padic.FiniteCoefficientFields c.l c.Qbar` is the required finite
  intermediate extension. The local API is used over
  `pbcFiniteField.{u} c.l c.Qbar E`, the published `Shrink` of `E.val`, not a
  replacement extension. Its field and Q_l algebra structures are transported
  by the fixed equivalence `Shrink.algEquiv`; natural-number casts and integer
  powers are preserved. Every finite intermediate field is covered.
* `X₀ : Over (Spec (.of D.k₀))` binds the actual scheme and structure map.
  `[IsSeparated X₀.hom]` is separatedness. `[LocallyOfFiniteType X₀.hom]`
  and `[QuasiCompact X₀.hom]` together say finite type. Every twist and local
  operator uses the existing geometric base change `D.geometricFiber X₀`.
* `m : ℤ` covers every signed exponent, without a positivity assumption.
* `x : {x : X₀.left // x ∈ closedPoints X₀.left}` is every closed point.
  The embedding `ι` and equation `hι` specify the chosen geometric lift,
  as the local-operator dependency requires. They express a k₀-embedding of
  the actual residue field, not a fixed-point equation for scheme maps.
  Such embeddings exist for every finite residue extension. The theorem is
  universal in the embedding, so no preferred embedding restricts the claim.
* `wfTateTwist D c X₀ E m` is the actual signed object in `WeilD`. Its
  construction uses completed root lattices and rationalization. Its Weil map
  uses the published root maps and normalized coefficient comparison.
  `wfTateTwistLocalModel` applies the inverse of that same equivalence to this
  constructed PBC object; it does not substitute an unrelated framework line.
* `localClosedFrobeniusCohomology ... (wfTateTwistLocalModel ...) x ι hι 0`
  is the existing geometric Frobenius on H^0 of the derived point complex.
  The twist is a degree-zero rank-one sheaf, so this is exactly its sheaf stalk
  under the convention in `def-weil-local-frobenius-trace`. The dependency's
  residue-degree iteration, composition comparisons and point transport are
  used unchanged; the operator is not independently defined in this delivery.
* `(Nat.card (X₀.left.residueField x.val) : pbcFiniteField ... E) ^ (-m)`
  is exactly `Q_x^{-m}` in the chosen coefficient presentation. It uses the
  residue-field cardinality itself, not merely `q` or an assumed degree.
* Equality with that scalar times `𝟙 _` is equality of E-linear stalk
  endomorphisms. It is not just an equality of traces or eigenvalue sets.

Dependency declarations read and used:

* `def-wf-tate-twist`: the old record names
  `WeilConjectures.WeilSheaf.TateTwist`, notably
  `AlgebraicGeometry.WeilSheaf.cyclotomicUnit`, `tateTwistSheafNat`,
  `tateTwistSheaf` and `AlgebraicGeometry.WeilComplex.tateTwist`.
  Their full source uses `PadicAlgCl`, constant Weil twists and its own stalk
  model. It cannot instantiate the finite-E local operator required here.
  The replacement record names the full finite-coefficient construction below.
* `def-wf-tensor-product`: `Sheaf.Paper.WeilTensorProduct`,
  `wfTensor`, `wfWeilCarrier`, `wfWeilStructure`, `wfTensorFrobenius`,
  and `wfConstructibleInclusion`. These are the actual completed derived
  tensor and its Weil map used in the dependency's positive/functor comparisons.
* `def-wf-internal-hom`: `Sheaf.Paper.WeilInternalHom`,
  `wfInternalHom` and `wfInternalHomFrobenius`. The negative-power comparison
  is an isomorphism of pairs for this exact map, including its inverse first
  structure map in the contravariant argument.
* `def-weil-local-frobenius-trace`: `Sheaf.Paper.LocalFrobeniusTrace`,
  `localClosedFrobeniusCohomology`, `localPointComplex`, `localClosedPoint`,
  `localClosedPointDegree` and `localClosedPoint_return`, including the
  iteration and the semilinear return used in their definitions.
* The real root-line data and normalized sheaf maps are the existing
  `FrobeniusCoefficientTwists.rationalWeilLine`, `rationalWeilTwistingFunctor`,
  `rootTowerMap`, `rootLineMap`, `positiveLineMaps`, `signedLineMaps`,
  `completedToOrdinary`, `integralDerivedLineMap` and `rationalDerivedLineMap`
  in `Sheaf.Paper.FrobeniusCoefficientTwistsCanonical`. Positive maps are fixed
  on scalar/root tensors; negative maps are fixed by evaluation. These objects
  are constructed before and independently of the scalar-action theorem.
* `Sheaf.Paper.RationalCoefficientCategoryComparison`,
  `rationalCoefficientCategoryComparison` and `FdFrobeniusComparison`, supply
  the normalized comparison system. `FdRationalStageComparison` fixes integral
  objects and localized pure tensors; the finite pullback comparison is fixed
  on the entire strict quotient diagram and its augmentation.
* `Sheaf.Paper.PbcAutomorphismTransport`,
  `pbcIsoOrdinaryDerivedComparison` and `pbcIsoIntegralPullback`, and
  `Sheaf.Paper.PbcCompletedPullbackActual`, `pbcActualCompletedPullUnit`, supply
  the actual ordinary/complete maps used in the additional adapter.
* Other source-defined components are the published `purTwistZlOne`,
  `purTwistIntegralModule`, `coefficientTwistPower`, `coefficientTwistLine`,
  `sfIntegralTwistingCoefficient`, `sfRationalTwistingCoefficient`, and
  the canonical small finite-field presentation `pbcFiniteField`.

Proof imports include the primitive-root theorem, Frobenius construction, root
inverse-image map, finite closed-point field theorem, point fibre, point transport,
and its naturality. `lem-wf-tate-twist-compatibility` currently has no recorded Lean
module and is a proof dependency only: its root-normalization content is retained
by the existing canonical root-line maps. It is not assumed in the statement.
The unstated `lem-wf-internal-hom-weil` does not obstruct this definition: the
negative line is actually constructed from its ordinary locally free lattice,
and `wfTateTwist_negative` identifies its derived internal Hom and exact Weil map.

Searches actually run for this item:

* msearch LeanFinder: "Geometric Frobenius on the stalk of an integer Tate twist
  E(m) equals residue field cardinality to the power minus m". Eight hits included
  Witt-vector isocrystals, arithmetic Frobenius and untilts. None states this
  finite-E adic stalk identity.
* msearch Loogle: `cyclotomicCharacter`. Four hits: the character, continuity,
  `spec`, and `toZModPow`. These concern roots/characters, not the required stalk.
* msearch grep: `TateTwist|tateTwist|cyclotomicCharacter_frobenius`. Zero Mathlib hits.
* msearch LeanSearch: "Frobenius on roots of unity and on integer Tate twists of
  l adic sheaves". Eight hits concern ring Frobenius, isocrystals, arithmetic
  root action and finite-field Frobenius. None is the desired adic stalk statement.
* `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for Tate twists,
  `wfTate`, `cyclotomicUnit` and the node id. Read the exact upstream
  `WeilSheaf.StalkTateTwist.stalk_frobenius_tateTwistSheaf`: it concerns
  `PadicAlgCl` and a different Weil-sheaf/stalk construction, so it is not an
  exact existing attachment for the finite-E node. The search found the real
  signed coefficient maps in `FrobeniusCoefficientTwistsCanonical`, which are
  reused rather than rewritten. Searches for the new full declaration name in
  Mathlib, `WeilConjectures`, and `Sheaf` gave no collision.

Edge cases checked before writing: `m = 0` gives the coefficient unit and scalar
one; `m = 1` gives inverse residue cardinality; `m = -1` gives residue cardinality
because the first Hom argument is contravariant. Positive powers are left-associated.
The degree-zero case uses the actual unit even on an empty scheme. An empty scheme
has no closed points, making the final assertion vacuous. A closed point of degree
greater than one uses the residue cardinality and degree iteration, not one-step q.
No rational-point hypothesis, chosen root basis, nonempty-scheme hypothesis, lattice
for arbitrary Weil complexes, unramified-extension hypothesis, or equality of site
and coefficient universes is added. The coefficient prime differs from p, so every
residue cardinality is nonzero and invertible in the characteristic-zero field.
Ramified finite E and E = Q_l are included; the construction uses the existing
completed coefficient comparison between ell-power roots and uniformizer-power
coefficients. All universe and variable binders are explicit; auto-implicits are off.

## Dependency modules

`def-wf-tate-twist` is repaired in `Sheaf.Paper.WeilTateTwistsFinite`. The replacement
is necessary because its former declaration only gives Qbar constant Weil twists.
The repair does not duplicate roots, inverse limits, coefficient lattices, tensor,
internal Hom, scalar localization, or the framework signed maps.

The module constructs the source notion as follows. `wfTateComparisonSystem` selects
the published normalized coefficient system; its integral, fraction and quotient
formulas fix its functors. `wfTateFrobeniusComparison` obtains its specified fixed-pair
equivalences. The resulting completed-pullback finite pair category is not definitionally
`WeilD`: the latter uses exact automorphism coefficient transport. This mismatch is
repaired explicitly, rather than cast away. `wfTatePullbackUnit_isIso` is the named
well-definedness theorem for the actual completion unit. The integral comparison
`wfTateIntegralPullbackComparison` is its inverse followed by the published ordinary
derived comparison, which is fixed by the universal counit on every complex.
`wfTatePullbackComparison_exists` characterizes the rational natural isomorphism by
this very map on every integral representative. `wfTatePairTransport` transports
fixed pairs through its inverse. Its equivalence theorem only supplies invertibility
of this already specified functor; the inverse is determined up to the usual unique
isomorphism. No arbitrary line, Weil arrow or unnormalized natural isomorphism is chosen.

`wfTateCoefficientEquivalence` composes these two prescribed equivalences.
`wfTateTwist` applies its forward functor to the existing real signed root-line pair.
Zero is the completed coefficient unit, one is the completed root lattice, positives
are the left-associated tensor powers, and negatives the evaluation duals. Placement
in degree zero and raw rationalization precede this comparison, as in the node.
`wfTateTwistLocalModel` is the inverse image of this very PBC object. The equivalence
unit identifies it with the original framework root-line pair, intertwining its Weil
structure. Consequently the main theorem is about the node's object and local operator.

`wfTateTwist_positive` and `wfTateTwist_negative` express their derived characterizations
as isomorphisms in the category of ambient Weil pairs. The right-hand structures are
literally `wfTensorFrobenius` and `wfInternalHomFrobenius`; an isomorphism of plain
underlying objects would not suffice. These theorems supply no data to any definition.
They are the well-definedness/comparison properties of this definition's real flat-line
construction, with their complete proof plans in docstrings. No replacement of the
source's derived maps by discrete sheaf maps is assumed without these comparisons.

`wfTateTwistingFunctor` conjugates the existing normalized framework tensor twist by
the coefficient equivalence. `wfTateTwistingFunctor_spec` gives its natural family
of ambient Weil-pair isomorphisms with tensor by `wfTateTwist`, including the explicit
underlying map equation for `u tensor id`. This includes all m and arbitrary K,
not merely the Tate lines themselves. All postponed theorems in this dependency module
are the membership, canonical-comparison and derived-characterization obligations
of `def-wf-tate-twist` itself, tagged with that node. No independent notion is added.

Validation uses only scompile.py on the server for each file separately, including
both modules in dependency order. The mandated deliver2.py dry run and final delivery
perform preflight and their own per-file compilation. No live source or build was modified.

## Second reading by Q13

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

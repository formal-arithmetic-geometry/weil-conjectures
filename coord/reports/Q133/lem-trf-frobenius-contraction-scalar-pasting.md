## Worker report

Stage 2, Q133, 2026-10-22. The module
`Sheaf.AlgebraicGeometry.FrobeniusContractionScalarPasting` defines
`AlgebraicGeometry.Scheme.frobeniusContraction` by composing existing canonical
isomorphisms, and states
`AlgebraicGeometry.Scheme.frobenius_contraction_scalar_pasting` with `sorry`.
This is the only postponed theorem. The definition has real data and no proof holes.
The mathematical statement is unchanged. This repair adds one existing-definition ownership
node; it adds no module or declaration for that node and no dependency module.

This repairs the returned immutable head a549075167eb. The retained packet was
inspected and passed through the prescribed initial dry run before repair. The two
returned faults concern ownership and direct dependency imports, not the mathematics.

Source read: the complete current main-20261015
`sec-trace-formula/sk-p-trace-coeff/thm-trf-finite-coefficient-map.proof.md`, especially its
final coefficient-naturality sentence, and
`sec-six-functors-basics/sk-prop-sf-rf-shriek-preservation/prop-trf-scheme-galois-comparison.proof.md`,
which constructs kappa from pullback composition followed by the specified Frobenius
trivialization. The live node and all its statement dependencies and recorded Lean
interfaces were read, including the already landed coefficient-naturality theorem.

Hypotheses and clauses, matched individually:

- Prime p is `(p : ℕ) (hp : p.Prime)`. The scheme and its characteristic are
  `(Y : Scheme.{u}) (hY : Y.IsCharacteristic p)`. The latter is the recorded predicate,
  including vanishing of p in every ring of sections. `hY.2 ⊤` supplies the global
  section vanishing required by the recorded absolute-Frobenius construction.
- Arbitrary scheme endomorphism is `(v : Y ⟶ Y)`. There is no invertibility instance.
- Integer b at least zero is encoded by `(b : ℕ)`; every nonnegative integer occurs,
  including zero. H is exactly `Y.iterateFrobenius hp (hY.2 ⊤) b`.
- Finite commutative coefficient rings are `{A B : Type u} [CommRing A] [CommRing B]
  [Finite A] [Finite B]`. The unital map u is `(φ : A →+* B)`; a Lean ring homomorphism
  preserves one, including the zero-ring case.
- The ordinary unbounded constant-coefficient category is the existing
  `proEtaleDerivedCategory Y A`, and `(K : proEtaleDerivedCategory Y A)` is arbitrary.
  This uses the same ordinary presentation as the recorded coefficient-naturality
  theorem, without completing or restricting the category.
- T is exactly `AlgebraicGeometry.ProEtale.directImageScalarExtension φ Y`, the
  canonical derived extension along the actual map of constant ring sheaves.
- Each c_h is `(AlgebraicGeometry.ProEtale.directImageScalarPullbackIso φ h).hom.app K`.
  Its direction is h_B^*(T K) to T(h_A^* K), so it is the inverse comparison required
  by the node, with the existing constant-section and tensor-balancing normalization.
  The finite discrete ring identifications and the condensed comparison are imported;
  no arbitrary isomorphism is supplied as an assumption.
- V_R is `proEtaleConstantRingDerivedPullback R v`, P_R is the same functor at H,
  and S_R is the functor at `H ≫ v`, Lean's order for v composed with H.
- d_R is `(proEtaleConstantRingPullbackComposition H v R).symm`. Its target is
  `V_R ⋙ P_R`, meaning P_R after V_R. This is the existing general canonical
  ring-sheaf compositor, specialized and transported along the published equality
  identifying composite constant coefficient comparisons.
- t_R is the existing `coefficientFrobeniusTrivialization p hp Y hY R b`, fixed by
  relative Frobenius and the section-unit normalization, as in the recorded site
  theorem. No new trivialization is chosen.
- e_R is the real definition `frobeniusContraction`: d_R, then
  `Functor.isoWhiskerLeft V_R t_R`, then `Functor.rightUnitor V_R`. Thus its component
  is precisely t_R at V_R K after d_R at K; the functor unitor has identity components.
- The left side in Lean is `c_(vH).hom.app K ≫ T.map (e_A.hom.app K)`.
  The right side is `e_B.hom.app (T.obj K) ≫ c_v.hom.app K`.
  Since Lean writes composition left to right, this is exactly the displayed equation
  T(e_A) composed with c_(vH) = c_v composed with e_B, with source S_B(T K) and
  target T(V_A K) in D_B.
- There are no hypotheses about annihilators, flatness, Tor amplitude, boundedness,
  or constructibility. The definition retains unitors rather than treating pullback
  by the identity as a literal equality of functors.

Dependency declarations reused (module and name):

- `Sheaf.AlgebraicGeometry.SchemeCharacteristic`:
  `AlgebraicGeometry.Scheme.IsCharacteristic`.
- `WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius`:
  `AlgebraicGeometry.Scheme.iterateFrobenius`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `FiniteCoefficientModules` and
  `FiniteCoefficientDerivedCategory` in `AlgebraicGeometry.ProEtale`; its ordinary
  constant-ring presentation is the imported `Scheme.proEtaleDerivedCategory` used
  in the existing coefficient-naturality statement.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and
  `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel`, the ordinary universal
  derived-extension interface. The concrete functor is the existing specialization
  `AlgebraicGeometry.ProEtale.directImageScalarExtension` below.
- `Sheaf.SixFunctors.ScalarSixPullback`:
  `AlgebraicGeometry.ProEtale.CondensedRing.scalarSixPullback`, especially its
  normalized `scalarSixPullHom` and composition clause.
- `Sheaf.Paper.FiniteDiscreteCondensedRing`:
  `Profinite.finiteDiscreteCondensedRing_constant`.
- `Sheaf.Paper.FiniteDiscreteSchemeRing`:
  `AlgebraicGeometry.ProEtale.finiteDiscreteSchemeRing_constant`.
- `Sheaf.SecSmoothPurity.DirectImageScalarOperations`:
  `AlgebraicGeometry.ProEtale.directImageScalarExtension` and
  `AlgebraicGeometry.ProEtale.directImageScalarPullbackIso`.
- `Sheaf.Paper.IntegralFinitePullbackComposition`:
  `WeilConjectures.integralTowerGeneralPullbackComposition`, the recorded general
  ring-sheaf compositor of `lem-weil-pbc-proetale-derived-pullback-composition`.
  This is retained as a proof-plan import.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison`:
  `AlgebraicGeometry.Scheme.proEtaleConstantRingPullbackComposition`, owned by
  `pur713-def-pullback-comparison`, now added to stmt_deps and directly publicly
  imported. Its definition specializes the general canonical compositor and
  transports the coefficient identification along
  `proEtaleConstantRingCompositeCoefficients_eq`. This is the actual d_R constructor;
  the integral finite-level module is not its owner.
- `Sheaf.AlgebraicGeometry.AbsoluteFrobeniusSite`:
  `AlgebraicGeometry.Scheme.absoluteFrobenius_proEtale_trivialization` and
  `proEtaleFrobeniusDerivedIso`.
- `Sheaf.AlgebraicGeometry.FrobeniusTrivializationPullback`:
  `AlgebraicGeometry.Scheme.absoluteFrobenius_proEtale_trivialization_pullback`,
  the projection- and section-unit-normalized module trivialization package used
  by the unchanged finite-coefficient constructor.
- `Sheaf.AlgebraicGeometry.AbsoluteFrobeniusCoefficientNaturality`:
  `AlgebraicGeometry.Scheme.coefficientFrobeniusTrivialization`, now owned by
  `def-trf-coefficient-frobenius-trivialization` with existing: true.
  The module also contains `absoluteFrobenius_coefficient_naturality`, which is
  a proof dependency only: its conclusion is not needed to define t_R or e_R.
  The public import is needed for the existing definition, even though the
  theorem from the same file is only used in the future proof.

Edge cases checked before writing: b=0 retains the canonical identity-pullback unitor
and reduces to the same coefficient comparison on both sides; v=id is Frobenius
coefficient naturality, with its unitors; a noninvertible v needs no cancellation or
inverse; the empty scheme satisfies the characteristic predicate and the site
constructions; B=0 is permitted by CommRing and finite coefficients; the nonflat
map Z/p² to F_p is allowed because T is derived and no flatness instance is used.
K may be unbounded or zero. The ordinary categories use the standard size convention
already fixed by the dependency theorem; no new equality of site universes is imposed.

Searches made through the prescribed msearch.py Q133/item wrapper:

- LeanFinder: `Derived scalar extension commutes with canonical contraction of pullback
  along an arbitrary scheme endomorphism composed with absolute Frobenius`.
  Eight hits were ordinary scheme pullback projection identities, not this equality.
- Loogle: `"frobenius", "pullback"`. The sole hit was
  `CategoryTheory.Regular.frobeniusMorphism_isPullback`. I opened its Mathlib source:
  it concerns intersections and images of subobjects in a regular category, rather
  than absolute Frobenius or coefficient change.
- Mathlib grep in AlgebraicGeometry:
  `(frobenius|Frobenius).*(scalar|coeff|tensor|pullback)|(scalar|coeff|tensor|pullback).*(frobenius|Frobenius)`.
  Zero hits.
- LeanSearch: `Derived coefficient extension respects contraction of an absolute
  Frobenius pullback factor`. Eight hits concerned polynomial contraction and
  coefficients of perfection; none is a sheaf-theoretic statement.
- Project rg in both `lean/WeilConjectures` and `lean/Sheaf`:
  `frobeniusContraction|frobenius_contraction|contraction_scalar|lem-trf-frobenius-contraction-scalar-pasting`.
  Zero hits. The existing Frobenius coefficient-naturality theorem was read in full;
  it states only the H-comparison and has no arbitrary v-contraction equality.
- Local reads of the existing constant-ring compositor and scalar operations found
  every needed constructor, so no duplicate definition of any prerequisite was made.

No STATEMENT-DISPUTED issue or mathematical node fault was found. The retained
module had already compiled; this repair changes its imports and the DAG ownership
records, and reruns scompile.py and deliver2.py below.

## New nodes

`def-trf-coefficient-frobenius-trivialization` is an existing: true ownership record
for `AlgebraicGeometry.Scheme.coefficientFrobeniusTrivialization` in
`Sheaf.AlgebraicGeometry.AbsoluteFrobeniusCoefficientNaturality` (line 50). It creates
no second definition. Its statement names the prime p, characteristic-p scheme X,
finite commutative ring A, and every b in ℕ, matching the existing binders exactly.
Its isomorphism `L(F_X^b)^* ≅ id` is exactly the result type. Its construction is
`proEtaleFrobeniusDerivedIso A` applied to the module trivialization selected from
`absoluteFrobenius_proEtale_trivialization_pullback p hp A`; the two projections of
relative Frobenius and the section-unit equation determine this map uniquely.
Thus it does not choose arbitrary data from an unconstrained existence statement.
The definition adds the canonical derived identity comparison, as specified in
its new node statement. The existing declaration's entire signature is recorded
verbatim, and the module is left unchanged.

The source's final paragraph constructs the site isomorphisms from relative
Frobenius, takes the adjoint module trivialization, and descends it exactly to
complexes. The zero iterate is the normalized identity-base-change isomorphism;
empty X and A=0 remain allowed. There is no prime-to-p or flatness restriction.
The new node cites the characteristic, absolute-Frobenius, site, operations,
site-trivialization and arbitrary-pullback-trivialization nodes; no naturality
in the coefficient ring is used as an input.

Searches for the new ownership node (all recorded in mathlib_searches):

- LeanSearch, `Canonical trivialization of derived pullback by an iterate of
  absolute Frobenius on the small pro etale site with finite constant coefficients`:
  eight hits (fiber-bundle trivializations, iterated ring Frobenius and Witt-vector
  coefficients); no derived-site match.
- Loogle, `"frobenius", "pullback"`: only
  `CategoryTheory.Regular.frobeniusMorphism_isPullback`, unrelated subobject result.
- Mathlib grep, `(coefficientFrobeniusTrivialization|Frobenius.*trivialization|
  frobenius.*trivialization)` in AlgebraicGeometry: zero hits.
- Project rg in lean/WeilConjectures and lean/Sheaf found the unique existing
  definition in AbsoluteFrobeniusCoefficientNaturality.lean:50 and its consumers.
  DAG rg found only the coefficient-naturality theorem node; blueprint_refs.py
  search `coefficientFrobeniusTrivialization` found zero blueprint nodes. Thus the
  return's requested new definition ownership does not duplicate a definition node.

## Returned faults repaired

F1: removed `lem-trf-absolute-frobenius-coefficient-naturality` from stmt_deps,
retaining it in proof_deps. Added `def-trf-coefficient-frobenius-trivialization`
as an existing: true ownership record for the unchanged plain definition. The
new node depends on the actual site/pullback trivialization inputs and absolute
Frobenius; its definition uses no coefficient-naturality conclusion.

F2: added the landed `pur713-def-pullback-comparison` to stmt_deps and directly
publicly imported `Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison`.
The dependency list above now identifies this as the owner of d_R, rather than
attributing it to IntegralFinitePullbackComposition. The latter remains a normal
proof-plan import for the general compositor. No statement, proof step, or
proof_deps field was changed, and no dependency node was edited.

## Second reading by Q133

This is an in-session second pass, not an independent worker's review: the dispatch
explicitly forbids starting other agents and says the maintainer reviews independently.
I reopened the complete node and the completed module. The definition's compositor
has domain pullback along H followed by v and codomain V_R followed by P_R in functor
notation; whiskering t_R on the left by V_R therefore evaluates it on V_R K, rather
than incorrectly evaluating it on K before V_R. Its right unitor ends in V_R exactly.
The theorem's first map is c_(vH), its next map is T(e_A); the other path first
contracts over B at T K and then uses c_v. Both paths end at T(V_A K). These are
the exact four maps in the node's square, with no extra compatibility hypothesis.
All parameters p, hp, Y, hY, v, A, B, φ, b and K are explicitly bound; only u is
a declared universe. Finite does not exclude zero rings, v has no IsIso assumption,
and b has no positivity assumption. No statement correction was necessary.
The repair changes only the compositor import in Lean. F1 is repaired by the new
existing-definition owner and the item dependency replacement; F2 is repaired by
the landed compositor dependency, its direct import, and the corrected attribution.
I rechecked both constructor signatures against their owning source modules.
The natural-language proof docstring retains the three live DAG proof steps and
their named inputs. Definitions have actual canonical data; only the main theorem
uses sorry. The maintainer's independent reading remains the external review.

Validation after repair: scompile.py compiled the sandbox module in 14.4 seconds
and the library-named module in 8.4 seconds, with no errors or unexpected warnings.
The initial saved-packet dry run returned OK at 788b9cf9b4a; the repaired packet
is separately checked by the required final dry run and delivery.

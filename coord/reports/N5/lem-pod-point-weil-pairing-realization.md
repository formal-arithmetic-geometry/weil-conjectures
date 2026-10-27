## Worker report

Item: lem-pod-point-weil-pairing-realization. Group: N5. Stage: statements only.
Module: Sheaf.Paper.PointWeilPairingRealization.
Namespace: WeilConjectures.PointWeilPairing.

The module renders the point-Hom realization, its actual transport and Frobenius
formulas, the inverse coefficient-unit tensor equation, and both pairing equations.
The final scheme clause is `compact_ordinary_specialization`, at the derived level;
applying any cohomology functor gives the degreewise actions. Its parameter R is the
recorded SupportModel. Instantiate it with frobeniusCohomologyCompactModel for K,
and separately with frobeniusCohomologyDirectModel for L. These constructors retain
the compactification and ordinary cartesian square separately.

Every theorem is postponed with sorry. All definition data is constructed. Choices
of maps or shift structures are only from named uniqueness theorems with explicit
normalization equations. In particular, neither the unit nor the tensor comparison
is chosen from a bare Nonempty assertion. The support exchange is the actual
recorded exchange; its inverse is obtained from the named exchange_isIso theorem.

Hypothesis and clause correspondence:

- The finite-field data, p prime, a positive, q = p^a, finite k0 and its algebraic
  closure k are exactly `D : FiniteFieldDatum.{u}`. The coefficient prime is
  `l : ℕ`, `[Fact l.Prime]`, `hl : l ≠ D.p`. Prime invertibility at s is supplied
  by the existing frobeniusPointPrimeInvertible construction, not an extra premise.
- `E : Type u`, `[Field E]`, `[Algebra (Padic l) E]` and
  `[FiniteDimensional (Padic l) E]` are the finite rational coefficient field.
  No embedding into an algebraic closure affects this rational statement. The
  tensor-normalization theorem tests the recorded canonical comparisons over
  every algebraic closure; it does not add a closure hypothesis to the result.
- `C D l E` is exactly sfRationalConstructibleCategory at Spec D.k, so all A and
  D1 are bounded constructible rational point complexes. Here D1 denotes the
  node's second complex D, to distinguish it from the finite-field datum D.
- `P` is rationalDerivedPullback along the recorded frobeniusPointIso, hence
  geometric Frobenius. `thetaA : P.obj A ≅ A` and `thetaD : P.obj D1 ≅ D1`
  unbundle precisely the IsoAlgebra datum used in sfWeilComplex. They are rational
  arrows, with no integral Weil datum or stable lattice among the hypotheses.
- `F` is pointRationalFibre followed by its actual full-subcategory inclusion.
  `iota` is frobeniusPointTransportRational followed by the prescribed object
  equality frobeniusPointRationalPullbackEq. It is not an arbitrary comparison.
- `frobenius N theta` is iota_N followed by F(theta.hom). `shiftedTheta` is the
  induced datum on N[r], using fieldRationalPullShift through `pShift`.
- `U` is the recorded rationalLine at m = 0. `c` is rationalDerivedLineMap at
  m = 0. The first conjunct of point_weil_pairing_realization says its actual
  point Frobenius is identity on the whole derived unit, not just a scalar.
- `n : ℤ`, and `B : T.obj (A, D1[n]) ⟶ U`, are exactly the displayed pairing.
  `mu` is canonicalRationalPullbackTensor. The arrow equality before the final
  implication is exactly mu followed by thetaA tensor thetaD[n], then B, equal
  to P(B) followed by c. No nondegeneracy or perfectness assumption was added.
- `realize` sends a representative U → N[i] to F(x), after the normalized point
  unit and shift comparison, and evaluates at 1. `realize_bijective` and
  `realization` give the canonical equivalence for every N and every integer i.
  They apply to A, D1, PN and U. `scalar_bijective` records End(U) = E through
  the actual scalar map, not an independently chosen equivalence.
- The second conjunct of the main theorem identifies the cohomology of iota_N
  with `transportRep N r x`: c.inv, then P(x), then the canonical pullback shift.
  The third identifies the cohomology of Frobenius with `frobeniusRep`: that
  transport followed by theta.hom shifted by r. Thus both A and D formulas hold.
- `j` is the inverse unit tensor constraint, reflected through the normalized
  fully faithful point equivalence from the actual E[0] multiplication unitor.
  The fourth conjunct states exactly c.inv followed by P(j) followed by mu equals
  j followed by the tensor of the two c.inv factors. This is the explicit unit
  equation requested by the node.
- `tensorShift` reflects the normalized field derived-tensor shifts, extracting
  the second factor first and then the first. This order has the source's sign
  (-1)^(j*p) in first shifted degree p. It does not exchange the ordered factors.
  `pairingEnd` sends y to (D1[n])[-i] by shiftFunctorAdd', tensors x and y after
  j, applies tensorShift at (i,-i), cancels i + -i, and composes with B.
- `pairing` uses the two inverse realization equivalences and applies `scalar`
  to pairingEnd. The final two clauses of the main theorem state the equality
  with c.inv followed by P(pairingEnd) followed by c, and the scalar equality
  b_i(F_A x,F_D y) = b_i(x,y). scalar_bijective identifies the scalar statement
  with the corresponding statement in End(U).
- All i,n,r are unrestricted integers. No positivity condition, nonzero object,
  integral model for theta, or stable-lattice condition occurs.
- In the scheme specialization `Y0 : Over (Spec k0)`, the typeclasses
  LocallyOfFiniteType, QuasiCompact and IsSeparated on Y0.hom say precisely
  separated finite type. `operation` is the actual modelRationalFunctor for R;
  `exchange` is its modelRationalExchange, and `operationTheta` is exchange
  followed by operation(theta). The specialization identifies the derived
  Frobenius with frobeniusTransportRational followed by F(operation(theta)).
  Its compact and direct instances are the two node formulas; no properness
  or equality between the two support operations is assumed.

Canonical construction details:

The larger point-unit comparison uses PointTateFiber.rationalSizeNormalization
at twist zero, ConstantGeometricStalkUnit.integralSectionsUnit (the existing
canonical inverse section coordinates), the exact scalar-extension/single
comparison, and rationalRegular (the actual tensor multiplication). It descends uniquely
through the carrier lift. The rational fibre shift is characterized on all
localized integral objects by fShift_existsUnique. This uses the actual
pointIntegralRationalFibre and the fixed size equivalence. The tensor comparison
is characterized against PointFibreDerivedTensorCanonical, including its full
representative normalization, rather than a bare monoidal structure. These are
helpers owned by this pairing statement, not replacement coefficient categories,
pullback operations, derived tensors, or point fibre functors.

Dependency declarations used:

- Sheaf.Paper.FiniteFieldFiber: FiniteFieldDatum, geometricFiber.
- Sheaf.AlgebraicGeometry.FrobeniusDetailed: geometricFrobenius.
- Sheaf.Paper.DerivedPullbackTensorHom: rationalDerivedPullback,
  rationalDerivedTensor and the specified localization constructions.
- Sheaf.Paper.SfWeilSheafComplex: the rational IsoAlgebra Weil convention,
  unbundled as an object together with theta : P.obj N ≅ N.
- Sheaf.Paper.FiniteCoefficientPoint: pointRationalFibre,
  pointIntegralRationalFibre, pointRationalFibre_existsUnique, pointFibreSizeLift,
  pointFibreSizeDescent, and the coefficient/carrier normalization functors.
- Sheaf.SixFunctors.FrobeniusPointTransport: frobeniusPointIso,
  frobeniusPointTransportRational and frobeniusPointPrimeInvertible.
- Sheaf.SixFunctors.FrobeniusPointTransportNatural:
  frobeniusPointRationalPullbackEq (the actual equality used in iota).
- Sheaf.Paper.FrobeniusCoefficientTwistsCanonical:
  FrobeniusCoefficientTwists.rationalLine and rationalDerivedLineMap.
- Sheaf.Paper.PointFibreEquivalence: point_fibre_equivalence, specifically its
  rational equivalence and shift-compatible exactness components.
- Sheaf.SixFunctors.FrobeniusCohomologyTransport: SupportModel recipes,
  frobeniusTransportRational, frobeniusCohomologyCompactModel and DirectModel;
  FrobeniusExchange.modelRationalFunctor and modelRationalExchange are reused.
- Sheaf.Paper.CompletedPullbackTensorComparison:
  canonicalRationalPullbackTensor, owned by
  def-pur-completed-pullback-tensor-comparison; no conclusion of
  lem-pur-derived-pullback-tensor-iso is required by a statement.
- Sheaf.Paper.FieldWeilShriekShiftData: fieldRationalPullShift.
- Sheaf.Paper.ConstantGeometricStalkUnit: integralSectionsUnit and
  rationalRegular, now definition-owned by
  def-pod-point-coefficient-unit-coordinates. unitLarge no longer refers to
  section_isIso; the already defined canonical iso supplies the inverse.
- Sheaf.Paper.PointTateFiberCoefficientComparisons: rationalSizeNormalization,
  definition-owned by def-pod-point-tate-fibre-size-coordinates. Its
  rawRationalSingle is also recorded as part of the same degree-zero interface;
  unitLarge now uses integralSectionsUnit directly through derived scalar extension.
- Sheaf.Paper.PointFibreDerivedTensor: PointFibreDerivedTensorCanonical,
  now definition-owned by def-pod-point-fibre-tensor-canonical.
  tensor_existsUnique quantifies over this normalization data; it does not use
  the existence theorem pointFibreDerivedTensor in its signature.
- Mathlib/upstream derived-category APIs: homSingleToHomology,
  homSingleEquivOfProjective, singleFunctorCompHomologyFunctorIso,
  singleFunctorObjUnitIso, canonical curried-tensor shifts, and preimageIso.

The original proof dependency records are unchanged. Their constructions remain
available where used. The direct DerivedPullbackTensorIso import is replaced
by the smaller actual comparison owner. The four returned theorem stmt_deps
are removed; the three missing definition owners are supplied below, while
canonicalRationalPullbackTensor uses its already landed definition owner.
The original field-shift definition dependency remains. No existing dependency
record, mathematical statement, proof, or proof dependency has changed.

Edge cases checked before and during writing:

The degrees zero, negative degrees and cancellation n-i = n+(-i) use the same
integer shift operations; no use of Nat subtraction occurs. The coefficient
object is twist zero, so no roots of unity choice is required. Zero A or D1
has zero represented Hom groups and zero pairing; nothing requires a nonzero
object or representative. n=0 and i=0 use the actual shift-zero constraints.
The finite field may have a=1. The only characteristic constraint is l≠p.
The scheme can be empty, and the compact support model is kept even when the
scheme is not proper. Arbitrary rational theta maps are never lifted to lattices.
The coefficient/carrier universes are transported through their explicit lift
and descent functors; no equality between site object and morphism universes
has been imposed.

Searches for an existing statement (recorded also in searches.jsonl):

- msearch.py leanfinder: "Canonical point transport realizes shifted Weil
  pairings as Frobenius invariant cohomology pairings". Eight unrelated
  RootPairing hits; no exact result.
- msearch.py leansearch: "Frobenius equivariant derived pairing yields
  invariant cohomology pairing". Eight unrelated Witt/RootPairing hits;
  no exact result.
- msearch.py loogle: "Functor.map_comp, CategoryTheory.MonoidalCategory".
  No hits (Functor.map_comp was not a recognized Loogle identifier).
- msearch.py grep: "Weil.*pairing|frobenius.*pairing|point.*realization"
  under Mathlib CategoryTheory. No matches.
- rg in lean/WeilConjectures and lean/Sheaf for the item id and point/Weil
  pairing names: no existing exact statement. Further targeted searches found
  PointFibreDerivedTensor, PointTateFiberCoefficientComparisons,
  ConstantGeometricStalkUnit and the normalized pullback shifts, which are
  reused rather than redefined.
- Local Mathlib and upstream searches for homSingle/projective homology,
  shiftFunctorAdd, curried tensor shifts and preimageIso located the APIs
  used by the real definitions.

Current source read: literature/blueprint/latest/blueprint/sec-poincare-duality/
sk-thm-frobenius/prop-weil-operations.proof.md, final two sentences, together
with the node's retained seven-step rational proof. The own statement was not
corrected or weakened. There is no STATEMENT-DISPUTED flag.

Validation uses scompile.py only. The full module (including the scheme clause)
has compiled on the server against the live library. Delivery dry-run and final
push results are recorded by the prescribed delivery wrapper.

## Repair of returned delivery

The sandbox was compared field by field with the current shared main node.
The returned file's mathematical statement and signature agree with main; the
pending differences are statement dependency ownership and lean metadata.
The delivery wrapper rebases the repaired packet on the current live branch.

H2(1): `mu` now imports Sheaf.Paper.CompletedPullbackTensorComparison and cites
its owner def-pur-completed-pullback-tensor-comparison. The theorem
lem-pur-derived-pullback-tensor-iso remains only a proof dependency.
H2(2): tensor_existsUnique's PointFibreDerivedTensorCanonical is now carried
by def-pod-point-fibre-tensor-canonical with an exact existing:true binding.
H2(3): unitLarge now consumes integralSectionsUnit directly through derived
scalar extension and its single comparison. Thus no section_isIso theorem
conclusion is used there; the canonical unit coordinates and rationalRegular
are carried by def-pod-point-coefficient-unit-coordinates.
H2(4): rationalSizeNormalization and the associated rawRationalSingle have
an exact existing:true definition owner def-pod-point-tate-fibre-size-coordinates.
All four returned theorem ids have been dropped from stmt_deps.

H4 advisory: DerivedPullbackTensorIso.pullbackTensorRationalUnit is localization
of pullbackTensorIntegralUnit, the reconstructed coherent coefficient-system
unit. Its rational LeftUnitor and RightUnitor have that chosen object as their
literal endpoint. Our U is FrobeniusCoefficientTwists.rationalLine at twist zero,
the localized strict signed-line representative. The recorded module provides
no normalized identification between those chosen objects, so its unitors
cannot be substituted at U directly. The module supplies no tensor-shift API.
Consequently j and tensorShift retain the already accepted reflection through
the fully faithful point fibre, normalized by the actual constant section,
regular-module multiplication, canonical field unitors, and signed field shifts.
The definitions are fixed by their actual normalization equations, not arbitrary
choices. No alternate tensor or unit notion has been introduced.

## New nodes

`def-pod-point-fibre-tensor-canonical` records the exact existing structure
WeilConjectures.PointFibreDerivedTensorCanonical in
Sheaf.Paper.PointFibreDerivedTensor. It collects all 17 finite, integral,
rational and closed-coefficient representative normalizations, units,
localization counits and scalar-extension squares. Its dependencies are the
already landed definition owners of each component, including finite source
constraints and integral scalar squares. The retained point-pairing proof uses
this normalization data to fix its tensor comparison. No prior definition node
owns the assembled structure; the prior theorem only listed it as a helper.
The new record is existing:true, so it duplicates neither declaration nor module.

`def-pod-point-coefficient-unit-coordinates` records the exact existing
integralSection, integralSectionsUnit and rationalRegular definitions in
Sheaf.Paper.ConstantGeometricStalkUnit. They give constant completed sections,
their degree-zero canonical inverse, and tensor multiplication after scalar
extension, as used in the retained point-unit realization. The inverse is
already determined by its actual section map; it is not a new existence choice.
No prior definition node owns these coordinates. This existing:true record
avoids reproducing them or adding a theorem conclusion as a statement dependency.

`def-pod-point-tate-fibre-size-coordinates` records exact existing
rationalSizeNormalization and rawRationalSingle in
Sheaf.Paper.PointTateFiberCoefficientComparisons. They are the actual carrier
lift/descent composite and the two exact-functor degree-zero comparisons for
every signed twist. Their source is the point-fibre normalization used in the
retained rational proof. No prior definition node carries these comparisons.
This is existing:true, with no new construction or replacement fibre.

For each new node, msearch.py LeanSearch queried "canonical geometric point
derived tensor fibre finite integral rational scalar normalization" (eight
unrelated normalization results); Loogle queried "PointFibreDerivedTensorCanonical,
integralSectionsUnit, rationalSizeNormalization" (zero hits, unknown identifier);
LeanFinder queried "integral coefficient unit geometric point sections regular
module rational coefficient normalization" (eight unrelated normalization hits);
msearch grep queried "point.*(tensor|unit)|rationalSizeNormalization" under
Algebra/Category (zero hits). The actual response records are copied into each
node's mathlib_searches. Local rg searches of dag/nodes, lean/WeilConjectures,
and lean/Sheaf found the exact source declarations and no definition owner.
blueprint_refs.py search "point tensor" found one unrelated Poincare-trace
definition, and searches "section unit" and "size normalization" found none.
The new records use existing:true in accordance with brief-stage2 section 1(A),
not fresh copies of the source declarations.

## Second reading by N5

Independent reader: N5 second_reader, a separately dispatched read-only review.
I opened the complete item JSON, the full Lean module, all three new definition
nodes, their recorded source declarations, the current blueprint final
smooth-pairing passage, and the retained seven-step rational proof. This review
compared the mathematical clauses rather than relying on the earlier acceptance
or compiler result.

1. `D : FiniteFieldDatum.{u}` supplies prime p, a>=1, q=p^a, k0 of cardinality q
   and its specified algebraic closure k. `l`, `[Fact l.Prime]`, `hl : l != D.p`,
   and the field/algebra/finite-dimensional instances on E give exactly the stated
   coefficient hypotheses. There is no new stable-lattice or integral Weil datum.
   Working without an explicit embedding E into Qbar does not alter these rational
   constructions: the tensor characterization quantifies over every closure, and
   the result never depends on a chosen embedding.
2. `C`, `P`, `T` and `F` use the existing rational constructible category,
   geometric-Frobenius pullback, derived tensor, and actual point fibre followed
   by ambient inclusion. `thetaA` and `thetaD` are arbitrary rational Weil
   isomorphisms. `iota` uses the recorded point transport with its pullback-object
   equality; `frobenius` is iota followed by F(theta). `pShift` and `shiftedTheta`
   provide exactly the induced shift datum.
3. `U` and `c` are the canonical coefficient line and coefficient map at twist
   zero. The first main conjunct is identity of the whole derived point Frobenius
   of U. `unitLarge`, uniquely descended `unit`, and the normalized `fShift` fix
   the Hom/cohomology identification. `realize` applies F, the unit and shift
   comparisons, then evaluation at 1; `realize_bijective` gives the claimed
   identification for every N and integer degree, including A, D1, PN and U.
   The repair composes the existing `integralSectionsUnit` under derived scalar
   extension and then `rationalRegular`; it preserves the former inverse constant
   section normalization while removing the direct use of `section_isIso`.
4. `transportRep` is diagrammatically c.inv >> P(x) >> pShift.hom, and
   `frobeniusRep` postcomposes with theta[r]. The second and third main conjuncts
   identify their realizations with H^r(iota) and H^r(Frobenius), respectively.
   Their universal N includes both input complexes. No shift or inverse is reversed.
5. The B binder is exactly A tensor D1[n] -> U. The antecedent is mu followed by
   thetaA tensor shiftedThetaD, then B, equal to P(B) followed by c: precisely
   the stipulated Weil equation. No perfectness, nondegeneracy, properness or
   finite-Tor premise was added.
6. `j` is the inverse coefficient-unit constraint reflected through the normalized
   point equivalence. The fourth conjunct is c.inv >> P(j) >> mu =
   j >> (c.inv tensor c.inv), the node's required unit equation. `tensorShift`
   extracts the second shift before the first, preserving the specified
   (-1)^(j*p) signed total-tensor convention without exchanging factors.
   `pairingEnd` places y in D1[n][-i], tensors both representatives after j,
   cancels shifts i and -i, then composes B. Thus it is the specified
   End(U)-valued pairing.
7. `scalar` identifies End(U) with E by the same normalized unit and evaluation
   at 1; `scalar_bijective` records this identification. `pairing` applies scalar
   to pairingEnd on the two inverse realization maps. The last two main clauses
   are exactly conjugation c.inv >> P(pairingEnd) >> c and scalar Frobenius
   invariance. Diagrammatic composition translates that conjugation to
   c P(h) c^{-1} in the node's mathematical order.
8. In the scheme clause, `Over (Spec k0)` with LocallyOfFiniteType, QuasiCompact
   and IsSeparated is precisely separated finite type. `operation` and `exchange`
   are the recorded support-model functor and actual exchange, and
   `operationTheta` is exchange then operation(theta).
   `compact_ordinary_specialization` identifies its derived Frobenius with the
   recorded transport followed by F(operation(theta)); applying cohomology yields
   the requested actions. Instantiating SupportModel separately with the compact
   model for K and direct model for L gives the two clauses, without identifying
   support conventions or assuming properness.
9. All indices i,n,r are integers; n-i uses integer subtraction. Zero complexes,
   zero representatives, n=0, i=0, negative shifts, a=1 and empty schemes remain
   admitted. The explicit coefficient/carrier lift and descent do not impose equal
   site universes. Every new definition has actual construction data; choices are
   pinned by uniqueness or invertibility, and the delivered theorem proofs remain
   sorry as stage 2 requires.
10. H2 repair: mu now imports and cites
    `def-pur-completed-pullback-tensor-comparison`, which owns
    `canonicalRationalPullbackTensor`. The three new existing:true nodes own the
    exact existing canonical tensor structure, point-unit section coordinates,
    and Tate carrier/single coordinates. Their signatures and declaration lists
    match the source. The canonical structure statement covers all 17 fields,
    including normalized localization/field/stage counits and rational/qbar units.
    I found one prose mismatch during review: lift data quantify over every field,
    not only finite coefficient extensions; field (6) was corrected explicitly.
    No duplicate definitions or theorem conclusions occur in the new definition
    statements.
11. H4 advisory: the available rational unitors have `pullbackTensorRationalUnit`
    as endpoint, the localization of a reconstructed coherent ring unit. U is
    the localized strict twist-zero representative, and that API supplies no
    normalized comparison between these chosen objects. It also supplies no signed
    two-shift interface. The existing normalized point reflection therefore gives
    j and tensorShift at the correct endpoints without arbitrary choices. This is
    why retaining those constructions is appropriate.

After the field-(6) wording correction and the report's module-attribution
correction (`frobeniusPointRationalPullbackEq` is in FrobeniusPointTransportNatural),
I found no remaining mathematical mismatch. The change repairs definition ownership
and unit-coordinate usage; it does not alter the accepted main mathematical signature.

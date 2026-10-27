## Worker report

The module `Sheaf.Paper.OrientedDoubleHomCancellation` states
`WeilConjectures.sixFunctor_orientedDoubleHomCancellation`, with one `sorry`.
Every other declaration is a real definition of the specified maps or a spelling-out
of this same node's conclusion. No theorem is proved, and no statement is corrected.

Hypothesis and clause correspondence:

- `D : FiniteFieldDatum` contains the prime p, positive a, q=p^a, finite field k0
  of cardinality q, and its specified algebraic closure k. `C : D.CoefficientDatum`
  contains the prime ell, ell different from p, and the coefficient algebraic closure.
  `E`, its field/algebra/finite-dimensional instances, and the published Padic
  coefficient constructions give the finite extension, O_E, uniformizer and quotient.
  The level is `n+1` for arbitrary `n : Nat`, covering exactly every positive level.
- `S : SixFunctorDatum D C E (n+1) (Nat.succ_pos n)` is the recorded six-functor datum.
  `X : SixFunctorSpace D` is precisely a finite-type scheme over its k, with its given
  structure map. There is no separatedness hypothesis on X.
- The four conjuncts use `S.finiteClosed X`, `S.integralClosed X`,
  `S.rationalClosed X`, and `S.commonClosed X`, including their `.closed` and
  `.symmetric` fields. These are the recorded closed structures on the actual
  finite-Tor domains, formed from `sixFunctorDomainHom`, not an abstract substitute
  category or ordinary discrete E-sheaves. The unit is `.closed.monoidal.tensorUnit`.
  Thus completed tensor and unit, raw rationalization, and common finite-stage
  operations are inherited verbatim. All U,V below range over the selected closed
  coefficient category, including all its objects, without a perfectness restriction.
- `m r : Int` are unrestricted. `L` and `I` have underlying objects equal to the
  existing coefficient twists shifted by `2*r` and `-(2*r)`, respectively. The two
  equalities specify the aliases L=Lambda(m)[2r] and I=Lambda(-m)[-2r], rather than
  imposing new geometric hypotheses. Full-subcategory membership witnesses are
  bundled with L,I. `orientedFiniteTateObject`, `orientedIntegralTateObject`,
  `orientedRationalTateObject`, and `orientedCommonTateObject` apply only the recorded
  signed-line constructions, supplying their source-implied residue inverses through
  the existing `dlAdicGeometricResidueInvertible`. No extra inverse is assumed.
- `OrientedDoubleHomCancellation` is a transparent Prop definition expanding the
  remaining clauses of the statement, not an assumed package of its conclusion.
  Its `_a` and `_b` quantify over the supplied opposite-line identifications
  L tensor I isomorphic to 1 and I tensor L isomorphic to 1. No compatibility between
  them is required. The quantified W and `gamma : L isomorphic to W` are arbitrary.
- P ranges over the same finite-Tor domain and `@IsDualizable ... T.monoidal P`
  is exactly the recorded definition of perfectness from sk-def-perfect.
  The typeclass `IsIso (ringedSiteDualEvaluationLeft T s unit (Iso.refl _) P L)`
  is the explicit invertibility hypothesis on c_{P,L}.
- `ringedSiteDualEvaluationLeft` is the existing comparison c: the transpose of
  coefficient evaluation after moving the coefficient past P by the actual symmetry.
  `orientedHomThetaInverse` is c followed by H(P,gamma), hence precisely theta inverse;
  its inverse is the stated theta=c inverse H(P,gamma inverse). `asIso` uses the
  explicit comparison-invertibility hypothesis and introduces no arbitrary map.
- `orientedHomTensorBoth T U Y L` is the transpose s_{U,Y,L} of evaluation tensor 1_L,
  with the associator included. It is the same normalized transpose as the dependency's
  `ihomTensorBoth`, expressed directly in the datum's right-tensor adjunction rather
  than a private copy of internal Hom. `orientedHomCancellationInverse` is this s
  followed by H(1,lambda_L). Consequently the first conjunct of the Prop definition,
  `(q U).inv = orientedHomCancellationInverse T L U`, uniquely fixes q as
  H(1,lambda inverse) followed by s inverse, exactly in the order in the node.
- q is a family of actual `Iso`s. The second conjunct is its contravariant naturality
  in U: H(f tensor 1,1) followed by q equals q followed by H(f,1).
- The third conjunct gives the inverse-transpose formula on every test object V and
  every `v : V tensor U -> 1`: after transposing v and composing with q inverse,
  uncurrying equals associator inverse followed by `v tensor 1_L` and lambda_L.
  The fourth conjunct explicitly states that this map of the displayed Hom sets
  is bijective. In particular it also supplies the claimed evaluation normalization
  by taking V=H(U,1) and v=coefficient evaluation.
- `orientedHomDoubleIso` is constructed as `H.mapIso` of the product of
  `orientedHomThetaInverse ... .op` and `gamma.symm`. It is exactly the specified
  t=H(theta inverse,gamma inverse), including the two variances.
- `ringedSiteBidual T s W P` and `ringedSiteBidual T s unit P` are the existing
  transposes of evaluation after the symmetry, namely delta^W_P and j_P. The final
  conjunct says `delta >> t.hom >> (q Pdual).hom = j`, precisely q t delta=j.
  Every symmetry is the supplied signed derived symmetry; no cohomology-level
  replacement appears. No smooth map, orientation, absolute dualizing object,
  exceptional-adjoint existence hypothesis or geometric biduality theorem is used.

Dependency declarations read and used:

- `Sheaf.Paper.SixFunctorOperationDatum`: `SixFunctorOperationDatum`, its actual
  finite/integral finite-Tor predicates and operation interfaces, reexported by the datum.
- `Sheaf.Paper.SixFunctorDatum`: `SixFunctorDatum`, `SixFunctorClosedDomain`,
  `sixFunctorDomainHom`, the four closed structures, and `SixFunctorSpace` from the
  publicly imported stage construction.
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic`:
  `CategoryTheory.IsDualizable`, the exact recorded Prop of sk-def-perfect.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`: the reexported
  `finiteCoefficientTwist`, `sfIntegralTwistingObject`, `sfRationalTwistingCoefficient`,
  and `sfQbarTwistingCoefficient`. Read also CoefficientTwistsDetailed for the signed
  finite powers and duals, and IntrinsicCoefficientTwists for the intrinsic categories.
- `Sheaf.CategoryTheory.InvertibleFactorHomCancellation`:
  `CategoryTheory.MonoidalClosed.ihomTensorBoth` and
  `CategoryTheory.MonoidalClosed.invertibleFactorHomCancellation`, imported as a proof
  dependency. Its evaluation-normalized s is spelled out in the existing actual Hom
  presentation so that the statement does not assume an unrelated closed instance.
- The existing maps `CategoryTheory.ringedSiteBidual` and
  `CategoryTheory.ringedSiteDualEvaluationLeft` from
  `Sheaf.CategoryTheory.RingedSiteDualityMaps`, publicly reexported by SixFunctorDatum.
  Their owning node is `lem-sfb-ringed-site-duality-maps`; the existing reexported
  maps are retained, with no additional theorem conclusion assumed.
- Landed definition dependency `def-dl-a1-locally-constructible-adic-heart`, module
  `Sheaf.Paper.DlLocallyConstructibleAdicHeart`:
  `WeilConjectures.dlAdicGeometricResidueInvertible D C X.obj.left` supplies the
  residue-field inverses by transporting the coefficient-prime unit through k0, k,
  and the scheme structure map. The only requirements are the standing finite-field
  and coefficient data and the given k-scheme structure. The returned theorem
  dependency `lem-coef-completed-tensor-hom-transpose` and its import are removed.
- `lem-sf-coefficient-evaluation-naturality` has no current Lean record; its five-step
  mathematical argument is cited in the theorem docstring, while its explicitly
  assumed c invertibility and the evaluation maps themselves are already available.
  There is no unstated object missing from this statement and no additional proof
  theorem or duplicate dependency module is required.

Edge cases checked before writing and on rereading: P=0; m=r=0 and gamma identity;
negative m and r; odd shifts of P (the two actual crossings cancel by the symmetry
axiom, retaining Koszul signs); level one (`n=0` in Lean); every coefficient stage;
the empty scheme; arbitrary inverse-line isomorphisms and arbitrary gamma, with
no scalar normalization silently imposed. `U,V : B` have independent object and
morphism universes `a,b`, not a small test universe. All variables and universes are
explicit, with both autoImplicit options disabled. There are no local instances,
local notation, private helpers or hollow definitions in the statement interface.

Searches (2026-10-22, logs in sandbox searches.jsonl):

- leanfinder: "Canonical double dual evaluation into an invertible line agrees with
  coefficient biduality under internal Hom tensor cancellation". Eight ordinary
  module/FGModule dual-evaluation hits; none states the canonical equality here.
- loogle: "CategoryTheory.MonoidalClosed.curry, CategoryTheory.ihom". Twelve curry,
  uncurry and naturality declarations; useful adjunction API, no target statement.
- grep through msearch: "toIhomIhom|ihomTensorBoth|compTranspose", in
  CategoryTheory/Monoidal/Closed. Five compTranspose hits, no matching cancellation.
- leansearch: "Internal Hom double duality twisted by an invertible object agrees
  with coefficient biduality after canonical tensor cancellation". Eight rigid-duality
  or module-duality declarations; none gives this identity with its normalization.
- rg in project Sheaf, upstream WeilConjectures and dag/lean_names_upstream.json for
  orientedDouble, doubleHom, coefficientEvaluation, ihomTensorBoth, and the new names.
  Existing ringed-site bidual and dual-evaluation maps are reused; the generic
  invertible-factor cancellation is reused in the proof plan. No declaration states
  the whole item. `grep -rn` for the item id under WeilConjectures returns no match.

Validation: the prescribed scompile.py compiled the sandbox probe and full module
cleanly (14.8s and 15.2s after slot acquisition). The initial compiler errors were
repaired: the product iso constructor is `Iso.prod`, and all four twist wrappers
supply the already existing residue inverses instead of adding a binder.
The only postponed declaration is sixFunctor_orientedDoubleHomCancellation.

## Second reading by O4

Reread the node, its five proof steps and the module together. This was a second pass
by the same dispatched worker; the dispatcher explicitly forbids starting other
agents, and the maintainer supplies the independent review after delivery.

Checked every quantifier and the four stages against the correspondence above.
In particular, q inverse has source H(U,1), not H(U tensor L,L); the target unitor
is lambda hom; t uses theta inverse contravariantly and gamma inverse covariantly;
the final composition order is delta then t then q. Test objects and U are entirely
unrestricted in each selected closed domain. Perfectness and the c-isomorphism
hypothesis are both retained. The two twists use opposite integers and opposite
shifts, and no positivity was imposed on either. The original draft's missing
residue inverses were repaired by wrappers around the published constructions; no
extra hypothesis was retained. No other mismatch or statement dispute was found.


## Repair of return L (H2)

The saved packet first passed the required dry run at `44e5ff09e81`; that mechanical
pass did not resolve the independent review's H2 finding. Compared the saved node
with current main: the only non-Lean field difference was its added theorem
statement dependency. Removed `lem-coef-completed-tensor-hom-transpose` and the
`CompletedTensorHomTranspose` import. Added the landed definition node
`def-dl-a1-locally-constructible-adic-heart`, imported its recorded module
`Sheaf.Paper.DlLocallyConstructibleAdicHeart`, and replaced the instance supplied
in each of the four `oriented*TateObject` wrappers with
`dlAdicGeometricResidueInvertible D C X.obj.left`. Read its full signature,
construction and source docstring and the matching usage in
`Sheaf.Paper.OrientationCoefficientTwists` (the recorded module of
`def-sf-orientation-scalar-line-comparisons`). No new node or dependency module
is needed, and the theorem signature and all canonical maps are retained.

Repair self-check: the finite wrapper still forms the degree-zero derived image
of the signed finite twist; the integral, rational and common wrappers still use
their respective signed published coefficient objects. The supplied instance needs
only the existing k-scheme structure, hence adds neither separatedness nor any
other hypothesis. Residue-field `Invertible` is a subsingleton, so replacing its
construction preserves these objects. Reread the four stage clauses, arbitrary
m,r and inverse-line isomorphisms, q inverse and naturality, all test-object
transposes and bijectivity, dualizability, explicit comparison invertibility, and
`delta >> t >> q = j`: none of those clauses changed. The maps' owner noted in the
advisory is identified above. This self-check was performed by the same worker,
as required by the dispatcher's prohibition on starting other agents; independent
review remains with the maintainer.

Repair validation (2026-10-22): scompile.py compiled both the sandbox probe and
the library module cleanly, 16.7 seconds each, with no unexpected warnings.
The recorded theorem signature occurs verbatim in the module.

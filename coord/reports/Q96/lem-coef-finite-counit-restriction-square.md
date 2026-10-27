## Worker report

Q96 states `WeilConjectures.FiniteCounitRestriction.finiteCounitRestrictionSquare` in
`Sheaf.SixFunctors.FiniteCounitRestrictionSquare`. The only postponed proof is this
node's theorem. Its docstring gives the six-step natural-language proof from the
DAG. Every helper has real data and a source/blueprint docstring. The node's
natural-language statement, dependencies, proof, and other fields are unchanged.

Source read: current `literature/blueprint/latest/blueprint/sec-smooth-purity/`
`sk-lem-sp-tower/prop-coef-integral-dualizing.proof.md`, paragraph 2, especially
its last sentences identifying the specified natural maps by their counits.
Also read the entire node statement and proof and its statement dependencies,
including their recorded Lean signatures and docstrings.

Hypotheses and objects, clause by clause:

- The fixed geometric finite-field datum is `D : FiniteFieldDatum.{u}`. Its
  characteristic is `D.p`, and its geometric point is `Spec (.of D.k)`.
- The coefficient prime is `l : ℕ`, `[Fact l.Prime]`, with theorem hypothesis
  `_hl : l ≠ D.p`. The coefficient extension is `E : Type u`, `[Field E]`,
  `[Algebra (Padic l) E]`, `[FiniteDimensional (Padic l) E]`.
- The valuation ring, chosen uniformizer, and its powers are those of the
  recorded `Padic.coefficientExtensionIntegers`, `coefficientExtensionIdeal`,
  and `coefficientExtensionRing`. `finiteDualizingCoeff l E n` is the recorded
  lifted coefficient ring at exponent `n+1`; thus every positive level occurs,
  including exponent one at index zero. No exponent-zero quotient is added.
- `X : Scheme.{u}` with `[X.Over (Spec (.of D.k))]` supplies the structure map.
  Named hypotheses `hft`, `hqc`, `hsep` are respectively `LocallyOfFiniteType`,
  `QuasiCompact`, and `IsSeparated` of that map. `include hft hqc hsep` retains
  all these hypotheses on the theorem even where a helper is more general.
- `c : Compactification (X ↘ Spec (.of D.k))` is an arbitrary fixed
  compactification, not the library's globally chosen one.
- `omega` is precisely `ProEtale.sfFiniteExceptionalFixed` at the regular
  coefficient unit. `value` is `ProEtale.sfFixedCompactSupport ... c` applied
  to `omega`, namely the ordinary small pro-etale `Rp_* j_!` value.
- `etaleAdjunction` transports the actual exceptional adjunction by
  `Etale.rightDerivedLowerShriekIso ... c`. This retains arbitrary `c`.
  `etaleCounit` is its counit at the regular coefficient complex.
- `comparison` is the counit-defined `u`: the actual exceptional hom-equivalence
  is applied to inverse coefficient comparison, scalar extension of the counit,
  and the canonical scalar-unit map. `compactComparison` is precisely `c`
  followed by compact support of this `u`.
- `etaleTransition` uses the hom-equivalence of scalar extension/restriction,
  so it is exactly `eta` followed by restriction of `compactComparison`.
  `etaleUnitTransition` is the same transpose of the scalar-unit isomorphism.
- `omegaOrigin`, `valueOrigin`, `unitOrigin`, and
  `pbcDerivedComparisonRestrict` transport these constructions by the specified
  comparison realizations to the actual pro-etale objects. This defines
  `counit`, `transition` (d), and `unitTransition` (v). There is no independently
  selected pro-etale adjunction and no unconstrained map.
- The first conjunct is `transition ≫ Res.map counit = counit ≫ unitTransition`,
  exactly the sheaf-level restriction counit square, with all `n ≤ m` allowed.
- The next four conjuncts give the sheaf-level identities and successive
  quotient laws for both d and v. `restrictionUnit` and `restrictionComp` are
  the canonical normalized restriction isomorphisms; the latter uses the
  recorded `finiteDualizingQuotient_comp` equality. These are the needed
  associativity transports, not strict identifications of unequal categories.
- `integralRing` is `ULift` of the recorded valuation ring, solely the same
  standard size transport already used for finite coefficients. It is ring
  equivalent to R and introduces no hypothesis equating site universes.
  `integralQuotient` is the actual lifted residue-class map from that ring.
- `sections` evaluates ordinary constant-R-module sheaves at the terminal
  pro-etale object. Its published algebraically closed point colimit theorem
  and evaluation limit preservation provide the exact derived sections functor.
  `finiteSections` first restricts along R -> A_n and applies these derived
  sections. Evaluation commutes with scalar restriction objectwise, so this is
  the specified constant-R restriction of derived point sections.
- `quotientModule` is the regular finite coefficient module with its actual
  R-action. `quotientMap h` is `finiteDualizingQuotient l E h` on elements,
  as an R-linear morphism; its data is not a chosen map.
- `ordinaryUnitIso`, `constantSections`, and `targetSingleIso` define the
  regular coefficient's actual constant-section map, in degree zero.
  `targetConstantMap` is that map into the derived sections of the regular unit.
- The existential family `ι` consists of isomorphisms from precisely those
  targets to `quotientModule[0]`. The equation
  `targetConstantMap n ≫ (ι n).hom = 𝟙 _` fixes each uniquely as the inverse
  of the actual regular constant-section map; this is the specified canonical
  target normalization, not a mere arbitrary isomorphism.
- The following conjunct identifies `sectionUnitTransition` under `ι` with
  `singleFunctor.map (quotientMap h)`, namely the actual quotient q[0].
- The next conjunct is the requested equation in D(R):
  `sectionTransition ≫ finiteSections.map counit ≫ ι_n =
  finiteSections.map counit ≫ ι_m ≫ singleFunctor.map quotientMap`.
- The final four conjuncts give identities and successive quotient compositions
  of d and v after sections. `integralRestrictionComp` inserts the canonical
  composite restriction isomorphism before applying the common sections functor.
- No strict dualizing tower, arbitrary test object, finite-Tor assumption,
  flatness hypothesis, or ambient exceptional right adjoint is assumed.

Dependency interfaces used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its public imports:
  `Padic.coefficientExtensionIntegers`, `coefficientExtensionIdeal`,
  `coefficientExtensionRing`, and the finite-ring instances.
- The scheme-property convention uses Mathlib's `LocallyOfFiniteType`,
  `QuasiCompact`, `IsSeparated` (finite type = locally finite type plus qc).
- `Sheaf.Paper.NormalizedDVRTower`, publicly imported by `FiniteDualizing`:
  the canonical restriction/tensor adjunction and identity/composite conventions;
  the ordinary fixed-module implementation uses
  `Sheaf.derivedRestrictScalars`, `derivedRestrictScalarsCompIso`,
  `ProEtale.normalizedOriginRestrictionUnit`, and `Adjunction.ofIsRightAdjoint`.
- `Sheaf.SixFunctors.FiniteDualizing`: `finiteDualizingCoeff`,
  `finiteDualizingQuotient`, `finiteDualizingQuotient_id`,
  `finiteDualizingQuotient_comp`, and its published site-size instance (reexported by `siteSmall` to fix
  elaboration at the explicit standard universe);
  `finiteDualizingCoefficientComparisons` supplies the proof route.
- `Sheaf.Paper.QcqsCompactSupportRealization` publicly exposes the recorded
  compact-support implementations; `ProEtale.sfFixedCompactSupport` is used.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` publicly exposes
  the recorded finite exceptional construction; `sfFiniteExceptionalFixed` is
  the constant-module coordinate realization of that same exceptional functor.
- `Sheaf.Paper.FiniteCoefficientPoint`: `pointFibreBaseIsAlgClosed`; its finite
  point functor is the intrinsic-module coordinate version of exact evaluation.
  Here fixed-module evaluation is used directly, with canonical R restriction.
- `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`:
  `ProEtale.compactSupportSiteComparison` at the bounded-below exceptional origin.
- `Sheaf.Paper.ExceptionalCoefficientComparison` (public via FiniteDualizing):
  `Etale.ExceptionalCoefficients.compactSupportMap`, `comparisonInverse`,
  `unitIso`, and `Etale.scalarExtension`.
- `Sheaf.Paper.BoundaryDualizingComposition` and
  `Sheaf.Paper.NormalizedEtaleOriginWitnesses` (public via FiniteDualizing):
  `boundaryDualizingComparisonIso`, `boundaryCoefficientPlus`,
  `pbcDerivedComparisonRestrict`, and the scalar normalizations.
- Proof dependencies `Sheaf.Paper.PointExactExtensionSections`,
  `Sheaf.SixFunctors.CoefDualizingConstruction`, and
  `Sheaf.Paper.EtaleCompactSupportCoefficientChange` give respectively exact
  constant point normalization, finite-Tor dualizing construction, and coefficient
  comparison composition. The proof docstring explicitly explains their use.
- `WeilConjectures.SixFunctors.ProEtale.AlgClosedFieldSiteColimits`:
  `ProEtale.preservesColimitsOfShape_sheafSections_of_iso` supplies actual
  exactness data for the point sections construction. No new postponed lemma
  or independent definition node is required for these owning-node helpers.

Edge cases checked against both signatures and the formulas: index zero is the
positive exponent-one coefficient; m=n uses normalized identity restrictions;
r=m and m=n are included in the cocycle clauses; the quotient A_2 -> A_1 need
not be flat (all scalar extensions are derived); empty X and X=s are allowed;
no smoothness or nonemptiness of X is assumed. The regular module calculation
uses its freeness, not false flatness of the quotient ring over its predecessor.
All scheme sites retain their object/morphism sizes, with coefficient ULift only.

Searches for an existing exact statement:

- `msearch.py ... leanfinder` query: "Finite exceptional counits commute with
  restriction of quotient coefficients and derived point sections identify
  target maps with the actual quotient ring maps". Eight hits on quotient
  ideals, cotangents and scheme restrictions, no exact statement.
- `msearch.py ... loogle` query `CategoryTheory.Adjunction.unit_naturality`:
  three hits, including abstract unit naturality; this is an ingredient only.
- `msearch.py ... grep` query `counit.*quotient|quotient.*counit`:
  eight hits on coalgebra quotients and skeletal categories, no match.
- `msearch.py ... leansearch` query "Finite exceptional counits commute with
  coefficient restriction and point sections give quotient maps": eight hits
  on module adjunction counits and coalgebras, no exact statement.
- `rg` on both `lean/WeilConjectures` and `lean/Sheaf` for exceptional counits,
  point sections, quotient maps and coefficient comparisons; grep of the item
  id in upstream sources found no existing attachment. The related
  `Sheaf.SixFunctors.CoefTowerTraceRectification` depends on this item in the
  DAG and concerns a chosen compactification/tower; importing it would reverse
  the dependency. It is not used. The module here retains arbitrary c and the
  actual finite pro-etale counit objects.
- Rechecked the proposed namespace in both source trees: no declaration clash.

No disputed statement or node fault was found. The additional declarations are
canonical maps and coordinate transports belonging to this node's own notion,
as allowed by the missing-helper rule; there are no new or repaired DAG nodes.

## Second reading by Q96

This dispatcher assignment expressly forbids starting other agents; this is an
honest second pass by Q96, not a claim of an independent reader. The maintainer's
independent delivery review remains to be performed.

Reopened the node and module together and checked all hypotheses and conclusions
listed above. The second pass found and fixed: Lean would omit unused finite-type
and separated instances, so they are now explicitly included on the theorem;
the selected library compactification could not replace arbitrary c, so the
adjunction is explicitly transported by the canonical compactification iso;
and the targets must be actual regular constant sections, so their normalization
is imposed using `targetConstantMap`, with `quotientMap` defined on residue
classes. The identity and both cocycles are stated at sheaf and section levels.
The same point-sections functor is used for the two counits and both transitions.
The ULift of R and A_n only transports sizes; no field, site, or coefficient case
is excluded. The single theorem retains `sorry`, while helper data is complete.
No natural-language correction or dependency-record replacement was necessary.

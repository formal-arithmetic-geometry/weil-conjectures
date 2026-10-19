## Worker report

This is a substantive replacement of the returned smooth, quotient-only etale
restatement. The delivered module is now
`Sheaf.Paper.FiniteCoefficientAdjointComparisons`, with main declaration
`AlgebraicGeometry.FiniteCoefficientAdjoints.finite_coefficient_adjoint_comparisons`.
It states the original general finite-type pro-etale adjunction and its entire
finite coefficient system. It does not invoke the existing smooth comparison
theorem as a substitute for this item.

The item's statement, statement dependencies, proof, proof dependencies and
source are retained from current main. There is no statement correction and no
`statement_change`. The former report's proposed smooth correction and its
unsupported eight-citer audit are withdrawn. No citer is changed.

Hypotheses and coefficient objects, read against the node:

* `k`, `[Field k]`, `[CharP k p]`, `hp : 0 < p`, `[Fact l.Prime]`, and
  `hlp : l ≠ p` render exactly the arbitrary positive-characteristic field and
  distinct coefficient prime. There is no perfectness, finite-field, closure,
  or smoothness assumption.
* `X.Over`, `Y.Over`, the local-finite-type and quasi-compact structure maps,
  and their separatedness render separated finite-type k-schemes.
  `f.IsOver` renders a k-morphism. The auxiliary theorem
  `finiteTypeMorphismProperties` derives its separatedness, local finite type
  and quasi-compactness; they are not additional hypotheses of the main theorem.
  `finiteTypeNoetherian` similarly derives the Noetherian instances.
* `E`, its field structure, `Algebra (Padic l) E`, and finite dimension render
  the fixed finite extension of Q_l. The coefficient universe is u+1, the
  required coefficient universe for schemes of universe u, with no equality
  imposed between the site's object and morphism universes.
* `Stage l E` indexes finite extensions F of E and positive exponents. Its
  integer ring is exactly `Padic.coefficientExtensionIntegers`; its parameter
  is the image of `Padic.coefficientExtensionUniformizer l E` under the actual
  restricted field embedding `strictEtaleIntegerMap`. Its coefficient ring is
  the actual quotient S/(t)^n, including ramified stages. Taking F=E and the
  identity inclusion gives the node's A_n. `baseStage` and the identity-on-residues
  `baseCoefficientEquiv` expose this identification with the recorded
  `Padic.coefficientExtensionRing`. `stageFinite` states finiteness.
* `Arrow` retains an actual field embedding over E and the exponent inequality.
  `Arrow.ringMap` is `Ideal.quotientMap`, using the image of the source ideal
  inside the target ideal. Identity field embeddings give all quotient maps;
  equal levels give all finite-free extension maps. A general arrow is their
  composite. Thus the interface covers mixed coefficient diagrams as well.
  `Arrow.IsFiniteFree` uses actual `Module.Finite` and `Module.Free`, and the
  main theorem asserts this property for every equal-level arrow.

The categories and each asserted clause:

* `D A T` is the ordinary derived category of pro-etale sheaves of A-modules.
  `ctf A T` abbreviates the existing upstream
  `ProEtale.DerivedCategory.constructibleFiniteTor (ModuleCat A) T` from the
  finite-coefficient framework: bounded constructible cohomology and finite
  Tor amplitude. Its constructibility condition is the essential image of
  bounded constructible etale objects. `System.origin_X` and `origin_Y`
  explicitly retain the recorded `Scheme.FixedEtaleOriginWitness` for each
  input, without changing the full-subcategory morphisms. All normalization
  equations hold for every retained witness, not just one arbitrary witness.
* `lower A c` is the recorded
  `ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat A) c`.
  `etaleUpper` and `etaleAdjunction` use the ordinary etale right adjoint for
  precisely that same compactification, obtained from the recorded ambient
  adjoint-existence theorem. `upper A c` is explicitly
  `rnu A Y ⋙ etaleUpper A c ⋙ nu A X`, hence G_A in the node.
* `AdjointDatum.lower_preserves` and `upper_preserves` are the two preservation
  clauses. `adjunction` is an actual Lean `Adjunction` on the existing full
  ctf subcategories. Its `counit_normalization` is the composite of the
  specified `compactSupportSiteComparison`, the etale counit and the derived
  comparison counit. Consequently its unit is the transported geometric unit;
  an unrelated adjunction does not meet this normalization.
* `tensor` is the actual published left adjoint to derived restriction of
  scalars, `pbcFixedScalarExtension`, i.e. derived coefficient tensor. Every
  `Change` asserts its preservation on X and Y.
* `Change.projection` is a natural isomorphism T_Y F_A -> F_B T_X on the full
  X ctf subcategory. `projectionAtWitness` is a real composite of the etale
  canonical compact-support coefficient map and the recorded coefficient/site
  and compact-support/site comparisons, transported by the witness. The
  `projection_normalization` equation identifies q with that precise map.
* `Change.mate` is a natural isomorphism T_X G_A -> G_B T_Y on the full Y ctf
  subcategory. `counit_equation` is exactly F_B(b_K);epsilon_B =
  q_(G_A K)^(-1);T_Y(epsilon_A), with Lean composition written left to right.
  Since `dB.adjunction` is an actual adjunction, this equation says exactly
  that b is the specified transpose, not an arbitrary isomorphism.
* `Change.unit_equation` is exactly
  T_X(eta_A);b_(F_A K);G_B(q_K) = eta_B. It uses the same adjunctions and maps.
* `System.projection_comp` and `mate_comp` state the two composite equations
  under `pbcFixedScalarExtensionComp`; `Arrow.ringMap_comp` provides the
  equality of the actual induced quotient maps. `projection_id` and `mate_id`
  use the published scalar unitor `normalizedOriginScalarUnit` and the actual
  identity quotient map. They are universally quantified component equations
  of specified natural transformations, equivalently equality of natural
  transformations by extensionality. Naturality itself is part of NatIso.
* `RefinementDatum.lower_normalization` identifies the refinement isomorphism
  with the published etale refinement comparison transported along the exact
  site comparison and an arbitrary retained witness. Its inverse is used
  where required by that published comparison's orientation.
  `upper_normalization` fixes the right-adjoint conjugate by its counit.
  `System.projection_refinement` and `mate_refinement` are the corresponding
  commuting squares for q and b, respectively. Arbitrary composites of
  permitted coefficient arrows include the mixed diagrams in the node.
* The last main-theorem clause writes the image of t as a unit times v^e,
  with e positive, identifies every power ideal with the recorded (v)^(en),
  and states cofinality of en among the positive exponents. Thus the finite
  quotient systems are exactly the cofinal systems in the node. There is no
  assertion about inverse-limit, rational or condensed adjunctions.

Dependency declarations used directly include:

* `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer` and
  `coefficientExtensionIdeal` from `Sheaf.NumberTheory.Padics.CoefficientExtension`
  and the finite-quotient interfaces imported by `CoefficientExtensionFinite`.
* `Compactification` and `Compactification.Refinement` from
  `WeilConjectures.Compactification.Refinement`.
* `ProEtale.rightDerivedLowerShriekOfCompactification` from the published
  finite-coefficient derived lower-shriek framework.
* `Scheme.FixedEtaleOriginWitness` from
  `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`.
* `ProEtale.comparisonUpperStar`, `comparisonLowerStar` and
  `derivedComparisonAdjunction` from the finite-coefficient comparison framework;
  `ProEtale.compactSupportSiteComparison` from
  `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison` and its
  site-unit interface `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`.
* `Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification` from
  `Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint`.
* `Etale.ExceptionalCoefficients.compactSupportMap` from
  `Sheaf.Paper.ExceptionalCoefficientComparison`, used only to normalize the
  etale projection map, not its restricted smooth theorem.
* `ProEtale.pbcFixedScalarExtension`, `pbcFixedScalarExtensionComp` and
  `pbcComparisonReduction` from `Sheaf.Paper.WitnessCompatibility`;
  `normalizedOriginScalarUnit` from `Sheaf.Paper.NormalizedEtaleOriginWitnesses`.
* `strictEtaleIntegerMap` from `Sheaf.Paper.EtaleCoefficientSystemAdjoint`,
  used solely for the restriction of a finite field embedding to its integers.
  None of that module's adjoint-on-towers or semilinear-section theorems is used.
* The canonical etale compactification-refinement isomorphism imported through
  `Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons`.

The module bundles these clauses as `AdjointDatum`, `Change`, `RefinementDatum`
and `System`, with concrete fields, not unconstrained propositions. These are
helper interfaces for this node's already stated data, listed in
`lean.declarations`; they introduce no alternative definition of the mathematical
operations. Definitions have real data. Theorem helpers and the main theorem
have named `sorry` proofs and source/proof docstrings. The main docstring contains
all fifteen proof steps from current main in full, including each dependency
list. The lecture-notes diagonal/DNC route supplies the smooth factor; the
ordinary K-injective closed-support argument supplies the general morphism.

Edge cases checked by reading the types: arbitrary imperfect k; identity f;
empty schemes and zero derived objects; exponent 1; equal coefficient levels;
identity coefficient embeddings; non-flat quotient maps; ramified extensions
(e greater than 1); and successive quotient/extension composites. No global
pro-etale ambient right adjoint or smoothness assumption is introduced. All
universes and binders are explicit, with auto-implicit elaboration disabled.

Searches: the retained msearch log contains the earlier leanfinder search for
finite coefficient exceptional adjunction/mates (generic mate results), loogle
search (no exact match), and upstream grep (no exact match). Fresh searches in
this repair used leanfinder "ordinary derived pro-etale exceptional adjunction
finite coefficient quotient finite free counit unit compatibility" (eight
unrelated condensed/standard-etale results), loogle
"CategoryTheory.mateEquiv, CategoryTheory.Adjunction.leftAdjointCompIso" (zero
hits), and grep "finite_coefficient_adjoint_comparisons|FiniteCoefficientAdjoints"
(zero hits). Direct rg in WeilConjectures and lean/Sheaf found only the existing
`exceptional_coefficient_comparison`, whose extra smoothness, ZMod coefficients
and assumed cocycle make it different from this node. The existing canonical
maps and general categorical scalar/unit interfaces were read and reused.
There is no STATEMENT-DISPUTED finding and no correction to audit.

## Second reading by NS

A separate agent was prohibited by the dispatcher, so this section records a
second pass by the same worker, not a claim of independent-agent review.
I checked the node against the replacement type clause by clause. The returned
H3 omission is repaired by the pro-etale G formula, actual normalized adjunction,
invertible mate, unit equation, finite-free changes, coherence, refinements and
cofinality clauses above. H4 is repaired by replacing the duplicate theorem,
while retaining only its reusable canonical etale projection definition.
H7/H7b and H11 are repaired by retaining the original statement and removing the
unsupported correction and invalid citer audit. H8 is repaired by including the
complete current fifteen-step proof in the theorem docstring. The compiler's
refinement-orientation diagnostic was resolved using the inverse canonical map.

## Repair of returned H3

The returned theorem was rejected because its conclusion exposed only `Nonempty (FiniteTypeSystem ...)`, finite-free arrows, and ideal/cofinality facts. The theorem signature now explicitly concludes, for a witnessed `S : FiniteTypeSystem l E k f`, every omitted clause: preservation of the ctf domains by lower and upper exceptional functors; the actual normalized adjunction (as a `Nonempty` subtype whose element is definitionally `S.datum s c).adjunction`); the etale bound and its counit normalization; preservation under every coefficient arrow; the projection and mate natural isomorphism interfaces (again with subtype witnesses equal to the actual `S.change` fields); the witness-level canonical projection formula; counit and unit equations; retained origin witnesses; projection and mate composition for arbitrary composable arrows; identity scalar-unit equations; refinement data; projection and mate refinement squares; then the finite-free and ramified cofinality clauses. The `Nonempty` subtypes are used only to express propositions whose categorical records live in `Type`; each equality pins the witness to the canonical field in `S`, so arbitrary replacement maps or adjunctions cannot satisfy the conclusion.

The five explicit `letI` bindings in the signature install the Noetherian and morphism-property instances derived from the finite-type hypotheses before any `lower`, `upper`, `AdjointDatum`, or `System` expression is elaborated. The signature was compiled verbatim with all binders explicit. The final `lean.statement` field is synchronized byte-for-byte with the declaration through its colon and conclusion (before `:= by`).

## Worker report

This is a stage-2 delivery of `lem-sfb-complete-norm-open-test`, in
`lean/Sheaf/Paper/CompleteNormOpenTest.lean`. The live node has an accepted stage-1
split by Q120, and no Lean record. The 2026-10-22 stage-handoff rule in
`coord/brief-stage2.md` explicitly permits recording this statement. The inherited
stage-1 BLOCKED ending is not applicable to this stage-2 assignment. No repair note
exists. The accepted statement, proof, dependencies and stage-1 review are unchanged;
only the node's `lean` field is filled.

The main declaration is `AlgebraicGeometry.ProEtale.completeNorm_open_test`.
Its helpers construct the actual maps and diagrams of this same notion; all data
are real. Every theorem has proof `by sorry`; structural naturality lemmas needed
for these maps have source and mathematical proof docstrings and are listed in
`lean.declarations`. No new independent notion or dependency repair is required.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`. The coefficient field is
  `(B : Type u) [NormedField B] [IsUltrametricDist B] [CompleteSpace B]`.
  Mathlib's normed-field distance is `dist x y = ‖x-y‖`, so `CompleteSpace B`
  is precisely the required metric completeness. `[Algebra ℚ_[ℓ] B]` and
  `hB : ∀ x, ‖algebraMap ℚ_[ℓ] B x‖ = ‖x‖` specify an isometric extension,
  with its supplied norm, rather than choosing an unrelated valuation.
- The unit ball O is `(NormedField.valuation (K := B)).integer`.
  The valuation is defined as `nnnorm`, so its integer subring is exactly
  `{b | ‖b‖ ≤ 1}`; its topology is the induced subspace topology.
  `normOpenQuotient ℓ B n` is O modulo `(Ideal.span {(ℓ : O)}) ^ (n+1)`.
  This equals O/ell^(n+1)O. Index zero thus represents the first positive level;
  no level is omitted. The quotient has its quotient topology, and the first
  conjunct asserts `DiscreteTopology` at every level, rather than assuming it.
- `(V : Scheme.{u}) [IsAffine V] (f : Γ(V, ⊤))` supplies the affine scheme and
  global function. T is always `(V.basicOpen f).toScheme`, with actual inclusion
  `(V.basicOpen f).ι`. `hV` uses the recorded
  `GrothendieckTopology.IsWeaklyContractible` on `Scheme.ProEt.mk (𝟙 V)`;
  weak contractibility of T is never assumed.
- `htorsion` quantifies over every positive n and every
  `M : AddCommGrpCat.{u+1}` with `∀ x : M, ℓ^n • x = 0`. In particular M need
  not be finite, finitely generated, or a quotient of a finite coefficient ring.
  `normOpenConstantSheaf` is the recorded `constantSheaf` functor with only its
  sheafification instance and site universe fixed explicitly; no second constant
  sheaf construction is used.
- `NormOpenRestrictionIso V f F` means `QuasiIso` of the actual section-restriction
  morphism on the existing `CochainComplex.kInjectiveResolutionFunctor` applied
  to `F[0]`. The arrow in `normOpenComplexRestriction` is induced by the actual
  site morphism `Scheme.ProEt.mk (V.basicOpen f).ι ⟶ Scheme.ProEt.mk (𝟙 V)`.
  It is therefore the displayed restriction in D(Ab), not an unspecified
  isomorphism or an arbitrary map taken as a hypothesis. Localization of the
  ambient site at this open object is the small pro-etale site of T, and
  evaluation of a K-injective resolution on that object computes its derived
  sections. This is the usual ambient-site computation of the actual restriction.
- `normOpenFunctions X R` reuses `continuousCoefficientRingSheaf X R`, forgetting
  to abelian groups. Its sections are all continuous functions, lifted by `ULift`
  to the standard coefficient universe. `normOpenRealization X R` has source
  `(upperStarFromPoint X).obj (Profinite.continuousMapRingObjOfUniverse R)`.
  Thus its source is exactly the recorded p_X^* C_R. It is defined by the
  point-pullback adjunction and the test formula b ↦ b composed with the
  relative profinite projection. It is not a choice from an unspecified
  existence theorem. The `IsIso` clauses for B and O canonically identify the
  source with the function-sheaf model used in all subsequent clauses.
- For each Z=V,T, `Mono (normOpenRationalInsertion ℓ B Z 0)` is the subsheaf
  assertion: insertion at stage zero is the actual O-inclusion into B.
  `normOpenRealization_natural` identifies it with p_Z^* of the inclusion.
  The same naturality applies to quotient maps and multiplication maps.
- `IsIso (normOpenConstants Z (normOpenQuotient ℓ B n))` identifies the quotient
  function sheaf with the recorded constant sheaf on the discrete additive
  quotient. It is the actual constant-function map, extended by sheafification.
  `Epi (normOpenQuotientStep ℓ B Z n)` is the asserted quotient transition.
  The map uses `Ideal.Quotient.factor` of the actual power-ideal inclusion.
- The existential natural transformation π has its components specified by
  `π.app (op n) = normOpenQuotientProjection ℓ B Z n`. Those projections are
  induced by `Ideal.Quotient.mk`. `Nonempty (IsLimit (Cone.mk _ π))` says this
  very cone is a limit; the quantifier does not allow arbitrary projections.
  Combined with the constant-function isomorphisms this is precisely
  L_Z ≅ lim underline(O_n)_Z with the displayed quotient maps.
- The `QuasiIso` clause is the composite of the degree-zero map induced by
  `limit.lift` from that normalized cone and the recorded canonical
  `milnorLimitComparison`. Its target is the existing Roos complex, not a new
  completion category or an arbitrary homotopy-limit object. Hence it says the
  canonical L_Z[0] → Rlim underline(O_n)_Z[0] is an isomorphism in the ordinary
  derived category of abelian sheaves. The Roos triangle uses the recorded
  `IsDerivedLimit` convention; the concrete representative is the existing
  `WeilConjectures.integralOperationsRoos`.
- The existential κ is a cocone on `Functor.ofSequence` of multiplication by
  ell, starting at m=0. Its components are required to equal
  `normOpenRationalInsertion ℓ B Z m`, explicitly the additive map
  x ↦ `(ℓ : B)⁻¹ ^ m * (x : B)`. `Nonempty (IsColimit (Cocone.mk _ κ))`
  is exactly the displayed rationalization with those stage insertions.
- The two final `NormOpenRestrictionIso` clauses state actual restriction
  invertibility for O-valued functions and B-valued functions respectively.
  The last clause quantifies over all integer q>0 and asserts `IsZero` of
  degree-q homology of `normOpenSectionsComplex` at the principal-open object.
  This is H^q(T,C_B)=0 computed with the same existing K-injective replacement.
- Restriction compatibility is retained, not replaced by existence of abstract
  isomorphisms. Every displayed cone/cocone component is a sheaf morphism,
  hence commutes with object restrictions. `normOpenRealization_natural`
  states the coefficient-map square. `normOpenPullback` is the canonical
  adjoint of precomposition with the base-change projection, and
  `normOpenRealization_restriction` states its compatibility with the recorded
  `upperStarFromPointComp`. These formulas transport the normalized quotient
  cones and multiplication cocones across the open restriction. Their universal
  properties determine the induced comparison maps, including the derived
  comparison, with no unspecified isomorphism substituted for restriction.

Dependency declarations read and used:

- `def-sfb-continuous-map-condensed-ring`:
  `Sheaf.Topology.ContinuousMapCondensedRing`,
  `Profinite.continuousMapRingObjOfUniverse` and its ring-sheaf construction.
- `sk-def-sfb-pulled-back-coefficients`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`,
  `AlgebraicGeometry.ProEtale.coefficientRing`, `coefficientRing_X`,
  `upperStarFromPoint`, its adjunction and `upperStarFromPointComp`.
  The underlying abelian object is exactly p_X^*C_R.
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`,
  `AlgebraicGeometry.Scheme.ProEt` and `Scheme.ProEt.topology`.
- `sk-def-pe-weak-contractible`:
  `WeilConjectures.CategoryTheory.Sites.WeaklyContractible`,
  `CategoryTheory.GrothendieckTopology.IsWeaklyContractible`.
- `def-weil-pbc-constant-sheaf`: `Mathlib.CategoryTheory.Sites.ConstantSheaf`,
  `CategoryTheory.constantSheaf` and `sheafificationAdjunction`.
- `def-pur-sheaf-inverse-limit`, `def-weil-pbc-category-colimit`:
  `Mathlib.CategoryTheory.Limits.HasLimits`, `limit`, `limit.lift`,
  `Cone`, `IsLimit`, `Cocone`, `IsColimit` (the existing universal properties).
- `def-weil-derived-limit`:
  `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`,
  `CategoryTheory.IsDerivedLimit` and `IsDerivedLimitTriangle`.
  The comparison itself is `AlgebraicGeometry.ProEtale.milnorLimitComparison`
  from `Sheaf.AlgebraicGeometry.ProEtaleMilnorEpimorphic`.
- `def-weil-abstract-derived-category`:
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory` and Q.
  The statement uses the equivalent `QuasiIso` test on the concrete maps.
- `def-pur-ringed-site-zeroth-hypercohomology`:
  `Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses`,
  `CategoryTheory.ringedSiteZerothHypercohomologyOfUniverses`. The source specifies
  underlying abelian sheaves here, so evaluation on the existing functorial
  K-injective resolution gives the identical derived-sections convention.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec`; affine schemes are encoded by `[IsAffine V]` and
  the principal open by `V.basicOpen f`.
- `def-weil-l-adic-numbers` is a Mathlib leaf (no Lean record required):
  `Mathlib.NumberTheory.Padics.PadicNumbers`, `Padic` / `ℚ_[ℓ]`.
- Existing continuous-function sheaf model:
  `Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse`,
  `AlgebraicGeometry.ProEtale.continuousCoefficientRingSheaf`.
  Its normalized relative test projection is the existing `profiniteTestProjection`
  from `Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization`.

All stated proof dependencies are imported with plain `import`, including
`ProEtaleBoundedContinuitySections`, `ProEtaleContinuousCohomologyLimit`,
`TotallyDisconnectedCoefficientRealization`, `ExactFunctorDerivedFunctor` and
Mathlib's abelian/set locally-surjective epimorphism criteria. The metric-group
quotient lemma has no Lean record yet and is not used in the signature; its
future proof import is left to the maintainer. The main docstring retains the
seven-step accepted proof: realization, metric quotient reconstruction,
epimorphic derived limit, torsion restriction, rationalization, filtered
continuity, and exact evaluation at V.

Edge cases checked before finalizing:

- Empty V and T are allowed: no `Nonempty` scheme, point or section is required.
  Their abelian section groups are zero. The `Nonempty IsLimit/IsColimit` binders
  mean existence of universal-property witnesses and impose no geometric
  nonemptiness condition.
- An invertible f gives T=V and the actual identity restriction. f=0 gives
  the empty principal open and is still covered whenever htorsion holds.
- The zero torsion group and all infinite ell^n-torsion groups occur in the
  hypothesis. No finite-dimensionality, local compactness, finite residue
  field or finite quotient hypothesis appears anywhere.
- B=Q_ell recovers the usual tower. Complete extensions with infinite residue
  field or nondiscrete value group are allowed: `IsUltrametricDist` does not
  impose discreteness and the ideals are actual principal powers.
- n=0 in the Lean tower is the paper's n=1; the transition from paper level
  2 to level 1 is present. m=0 is the inclusion O→B. q=0 is intentionally not
  claimed to vanish, while every q>0 is included.
- Site objects have universe u+1 and arrows universe u. Coefficients and
  abelian sections are lifted to u+1; no equality between site object and
  morphism universes is imposed. Both auto-implicit modes are disabled.

Searches made (actual results retained in sandbox `searches.jsonl`):

- `msearch.py ... leanfinder` with the complete-field/unit-ball/torsion-open
  statement returned eight perfectoid/adic-completion hits (`BDeRhamPlus`,
  `BDeRham`, Fontaine theta and related declarations), not this theorem.
- `msearch.py ... loogle '"Padic", "IsAdicComplete"'` returned
  `PadicInt.instIsAdicCompleteMaximalIdeal`, which concerns only the adic
  completeness of Z_ell, not arbitrary complete normed B or open restriction.
  The earlier Loogle query using `CategoryTheory.IsDerivedLimit` reported
  an unknown identifier; this is not counted as a successful absence search.
- `msearch.py ... grep` with
  `(complete|Complete).*(norm|Norm).*(open|Open)|(torsionAcyclic|completeNorm)`
  returned five separation-theory hits for completely normal spaces only.
- The retained LeanSearch run for continuous coefficient sheaves, inverse
  limits, and unit-ball quotients returned completion and profinite-limit
  declarations, none with the node's hypotheses or restriction conclusion.
- `rg` on `lean/WeilConjectures` for the item id found no existing statement;
  searches for complete-norm/torsion-acyclic names found only different
  cohomological torsion results. The project search found
  `torsionAcyclic_normCoefficient_test`, the parent criterion for finite
  extensions and their algebraic closures, which does not state this
  arbitrary complete-field lemma. The existing continuous realization,
  constant sheaf and Roos comparison APIs were reused rather than copied.

No statement correction, disputed assertion, new DAG node or dependency module.

## Second reading by Q148

This worker did a separate clause-by-clause rereading after the retained module
compiled. It found and repaired the unresolved auxiliary sheafification universe,
one long line, missing proof-plan imports, and the missing explicit coefficient
and open-restriction compatibility formulas. The maps now have normalized real
data, and all postponed structural lemmas have proof docstrings. This is a
self-check, not a claimed independent review: the dispatch brief assigns the
independent reading to the maintainer, and explicitly forbids starting another
agent. The maintainer should independently check the ambient-site computation
of derived restriction and the normalized compatibility formulas in particular.

Validation: the complete module compiled cleanly through scompile.py in both
sandbox and final module-name modes. The first dry run caught a metadata
extraction error: splitting the signature at the first `:=` had stopped at
`(K := B)`. The record now retains the entire signature through the theorem
proof delimiter; no Lean or mathematical statement changed in this repair.

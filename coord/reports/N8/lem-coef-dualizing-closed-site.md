## Worker report

The delivery states `AlgebraicGeometry.ProEtale.dualizingClosedSite` in
`lean/Sheaf/Paper/DualizingClosedSite.lean`. Its sole postponed proof is `sorry`.
Three transparent Prop-valued definitions expand this node's notation and clauses:
`dualizingClosedSiteProperty`, `dualizingClosedSiteTransport`, and
`dualizingClosedSiteDirectImage`. They contain real expressions and no postponed data.
The two identity-open comparisons now have the definition owner
`def-sf-closed-identity-open-comparison`; no new mathematical assumption is introduced. The mathematical node
statement, proof, and proof dependencies are unchanged.

Hypotheses and objects, clause by clause:

- `D : WeilConjectures.FiniteFieldDatum.{u}` supplies the specified finite field,
  its algebraic closure `D.k`, characteristic prime, and base `Spec (.of D.k)`.
  `l : ℕ`, `[Fact l.Prime]`, and `_hl : l ≠ D.p` are exactly the prime and
  characteristic restriction.
- `E : Type u`, `[Field E]`, `[Algebra (Padic l) E]`, and
  `[FiniteDimensional (Padic l) E]` specify the finite extension. The valuation ring
  and chosen uniformizer are the existing Padic coefficient conventions from
  `FiniteFieldFiber`, not new input structures.
- `m n : ℕ`, `hm : 1 ≤ m`, and `hmn : m ≤ n` give exactly `1 ≤ m ≤ n`.
  `A` and `B` in the property are the canonical `ULift.{u+1,u}` of
  `Padic.coefficientExtensionRing l E n` and `... m`. This is the established
  module-value universe convention, retaining the same quotient ring. Their finite
  instances are supplied by `Padic.finite_coefficientExtensionRing`.
  `φ` is the actual `Ideal.Quotient.factor` for the power-ideal inclusion, followed
  by `RingHom.ulift`, never an arbitrary ring homomorphism.
- `r : ℕ`, `P := AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k))`,
  `Y : Scheme.{u}`, `[IsAffine Y]`, and `i : Y ⟶ P`, `[IsClosedImmersion i]`
  give the specified affine closed embedding. `ULift (Fin r)` has exactly r
  coordinates and permits every scheme universe, including zero coordinates.
  The k-structure of Y is `i ≫ aP`, where `aP := P ↘ Spec (.of D.k)`.
  A closed immersion into this separated finite-type affine space is itself
  separated and finite type over k. Thus no scheme or geometric hypothesis is
  omitted by using the embedding to encode that structural morphism.
- `Etale.dualizingComplex (ModuleCat A) aP` is M: the ordinary structural
  exceptional right adjoint applied to the coefficient unit. Its underlying
  compact-support adjunction is the recorded unbounded ordinary-etale one.
  `MB := (pbcFixedScalarExtension P.smallEtaleTopology φ).obj M` is exactly `T_P M` with actual
  B-module structure. `N := IA.obj M` and `IB.obj MB` are the two closed
  exceptional objects.
- `IA` and `IB` are the ordinary right adjoints at
  `c := Compactification.ofIsProper i`. This retains the identity-open
  compactification literally. Its ordinary left adjoint is identified with
  `Ri_et,*` by `closedIdentityOpenEtaleComparison`; adjunction uniqueness identifies
  the right adjoints with `I_R`, compatibly with their counits. These are the
  canonical coordinate identifications already used by
  `lem-coef-closed-identity-open-hom-normalization`, not additional choices or
  an assumption that a pro-etale unbounded adjoint exists.
- `S R W` is `(comparisonUpperStar (ModuleCat R) W).mapDerivedCategory`;
  `U` is `(comparisonLowerStar (ModuleCat R) P).rightDerivedFunctor`.
  `JA := U_A ⋙ IA ⋙ S A Y` is precisely the stated transported J at A;
  the one-ring transport property uses the identical composite at either ring.
- The first conjunct, for `W ∈ {Y,P}`, is
  `IsIso (pbcComparisonReductionMap W φ)`. The named natural transformation
  goes from `S_A ⋙ T_pro` to `T_et ⋙ S_B`; its inverse is exactly
  `t_W := (pbcComparisonReduction W φ).symm`. Its component is the requested
  `S_B(T_et K) ≅ T_pro(S_A K)` for EVERY K, including unbounded K.
  This states invertibility of the actual canonical B-linear map, rather than
  existence of an arbitrary equivalence. Both endpoints are derived categories
  of actual B-module-valued sheaves. The published map is the restriction-scalar
  mate and is computed by the constant-scalar tensor comparison on K-flat models.
- The next four conjuncts use the intersection of `Etale.DerivedCategory.isBoundedConstructible` and
  `∃ a b, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn ... a b` on M, N, MB,
  and `IB.obj MB`, with their respective rings and schemes. This is recorded
  finite-value bounded constructibility intersected with finite Tor amplitude.
  The latter is the derived tensor test against EVERY module sheaf in degree
  zero. The interval endpoints are explicitly ordered, including for the zero object.
  It does not test only constructible sheaves.
- The next four conjuncts apply the intersection of the `.map (S R W)` of the same
  bounded-constructible property and
  `∃ a b, Scheme.HasFixedCoefficientProEtaleTorAmplitude W R K a b` to their
  four S-images, and the fifth applies it to `JA.obj ((S A P).obj M)`.
  The existing finite-coefficient convention is bounded constructible etale
  origin plus actual pro-etale finite Tor amplitude against ALL module sheaves.
  The Tor condition is imposed on the pro-etale object itself, not just its
  antecedent. Thus all named comparison pullbacks, including J_A S_A M, occur.
- `dualizingClosedSiteDirectImage A i` and its B version quantify over every
  ordinary bounded-below L. They state
  `q.inv ≫ compactSupportSiteComparison.hom ≫ S(e.hom) = delta.inv`,
  where e and q are the two canonical identity-open identifications and
  delta is `fixedDirectImageComparisonIso`. This is exactly the assertion
  that the specified direct-image comparison is inverse compact-support
  comparison in closed direct-image coordinates.
- `dualizingClosedSiteTransport A i M` and its B/MB version retain proofs
  `hH`, `hIH` of the two ordinary bounded-below domains and require invertibility
  of the actual `(derivedComparisonAdjunction C P).unit.app H`.
  They require invertibility of the literal
  `α := S_Y.map (I.map (η.app H))`. They retain a bounded-below
  `FixedEtaleOriginWitness` W of J S H with `W.complex = ⟨I H,hIH⟩`
  and `HEq W.iso.hom α`; no origin or isomorphism can be freely substituted.
- The final equation is the literal composite
  `compactSupportSiteComparison.inv ≫ F_pro.map α ≫ E = S_P.map e`,
  with ordinary counit `e := (Adjunction.ofIsLeftAdjoint F).counit.app H` and
  `E := (specifiedExceptionalHomEquiv ... W ...).symm (𝟙 _)`.
  The identity-open identifications of the previous clause make this exactly
  `E ∘ Ri_pro,*(α) ∘ delta = S_P(e)` in the question's closed direct-image
  coordinates. The Hom equivalence is the specified normalized chain and both
  arguments are explicitly D+; an unrelated counit or Hom bijection cannot
  satisfy the definition by being chosen as extra data.

The introductory compact-support coefficient map c is the existing
`Etale.compactSupportCoefficientComparisonPlus` imported from the recorded
owner. This node asserts no separate equality involving that map; the existing
actual quotient tensor functors are used throughout. Likewise omega_Y and its
structural counit provide the proof route, not additional conclusion clauses.

Dependency declarations used (source signatures and docstrings read):

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`;
  `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `Etale.rightDerivedLowerShriekOfCompactification`;
  `...LowerShriekLeftAdjoint`:
  `Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification`;
  `...Dualizing`: `Etale.dualizingComplex`.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`: `Etale.derivedTensor`;
  `...Coefficients`: `Etale.DerivedCategoryModule`,
  `Etale.DerivedCategory.hasTorAmplitudeIn`;
  `Sheaf.AlgebraicGeometry.EtaleTorAmplitude`: the recorded lower-bounded
  companion `Etale.DerivedCategory.hasTorAmplitudeGE` (the bounded predicate
  is the existing upstream declaration).
- `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `Etale.DerivedCategory.isBoundedConstructible`;
  `WeilConjectures.AlgebraicGeometry.DerivedCategories`: ordinary category,
  homology, D+ interfaces reexported by the dependency.
- Mathlib `AlgebraicGeometry.Morphisms.FiniteType` and `...Proper`:
  `LocallyOfFiniteType`, `QuasiCompact`, `IsProper`, `IsSeparated`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparisonModules`, the actual `comparisonUpperStar`,
  `comparisonLowerStar`; `...EtaleClosedAmbientAdjoint`:
  `Etale.isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion`.
- `Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt` owns
  `sfFiniteExceptionalAt`; its formula is the U-I-S composite used here.
- `Sheaf.Paper.EtaleCompactSupportCoefficientChange`:
  `Etale.compactSupportCoefficientComparisonPlus`;
  `Sheaf.Paper.WitnessCompatibility`: `pbcFixedScalarExtension`.
- `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`:
  `compactSupportSiteComparison`; `...FixedComparisonDirectImageMate`:
  `fixedComparisonDirectImageMatePlus`, its canonical fixed direct-image
  isomorphism interface; `...SpecifiedExceptionalClassHom`:
  `specifiedExceptionalHomEquiv`.
- Definition owners added to the original live `stmt_deps`:
  `def-weil-pbc-witness-compatibility` owns `Sheaf.Paper.WitnessCompatibility`
  and `pbcFixedScalarExtension`, `pbcComparisonReductionMap`,
  `pbcComparisonReduction`;
  `def-weil-proetale-tor-amplitude` owns
  `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations` and
  `Scheme.HasFixedCoefficientProEtaleTorAmplitude` (the ordered interval and
  universal degree-zero pro-etale module test);
  `def-sf-closed-identity-open-comparison` owns
  `Sheaf.AlgebraicGeometry.ClosedIdentityOpenComparison` and the two explicit
  identity-open comparisons. The module imports only the upstream ordinary and
  finite-coefficient derived lower-shriek definitions, ordinary etale inverse-image
  coherence, and Mathlib adjunction uniqueness. No dependency record is altered.
- `Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed` supplies the bounded-below
  `siteComparisonDerivedPullbackPlus` used to type the target of the specified Hom
  equivalence; its source is the same recorded site comparison.

The theorem-owned `det-sp-et-proet-adjunction-transfer` is not a statement dependency
and its quarantined module is not imported. The theorem node
`lem-coef-closed-identity-open-hom-normalization` stays only a proof dependency,
as on the live base: its theorem is cited by step 6 of the proof docstring, while the
statement uses the new definition owner. It is not imported because its two plain
definitions were the returned ownership defect. The legacy module is not modified.

Proof imports: recorded proof-dependency modules are imported privately unless
they also supply a statement object, with the normalization theorem module omitted
for the explicit ownership reason above. The properness theorem's
upstream audit module is included. `lem-coef-dualizing-construction` and
`lem-coef-dualizing-affine-space` had no recorded Lean module in the read snapshot;
there is consequently no import for those two proof-only dependencies. Their
mathematical steps are retained in full in the theorem docstring. No statement
prerequisite waits on them.

Edge cases checked: empty Y has no excluded Nonempty hypothesis and all its derived
module objects are zero; identity closed immersion remains allowed; r = 0 is the
empty coordinate type, giving Spec k; m = n uses the literal identity quotient
reduction; m = n = 1 is permitted; all finite positive levels are covered. No
flatness or finite projective dimension of B over A is assumed. K in the tensor/site
comparison has no boundedness restriction. The site object universe remains u+1
and its morphism universe u; only coordinate types and coefficient values are lifted.
All variables and the universe u are explicitly bound; autoImplicit is false.

Searches made before writing:

- `msearch.py ... leanfinder` query: "Etale proetale comparison commutes with
  derived coefficient extension and preserves bounded constructible finite Tor
  dualizing objects with closed exceptional counit". Result: OK, 8 hits, all
  unrelated (Condensed scalar counits and elementary algebraic-geometric
  etaleness); no statement of the node.
- `msearch.py ... loogle` query:
  `AlgebraicGeometry.ProEtale.pbcComparisonReduction, AlgebraicGeometry.ProEtale.siteClosedCounitTransport`.
  Result: OK, 0 hits; index reports unknown first project identifier. The project
  source was searched directly instead.
- `msearch.py ... grep` query `dualizing|pbcComparisonReduction`, subdirectory
  `AlgebraicGeometry`: OK, 0 Mathlib hits.
- `rg` of WeilConjectures and Sheaf for dualizing objects, the node id, and
  `pbcComparisonReduction`: upstream has ordinary/pro-etale dualizing definitions
  and purity statements, and Sheaf has the canonical scalar comparison and
  closed identity-open/counit lemmas. None packages this node's four finiteness
  assertions, their five pro-etale counterparts, both tensor comparisons and
  specified counit assertions. All usable pieces are imported and reused.
- Exact-name/node-id search in `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: no existing `dualizingClosedSite` declaration
  or attachment of this node. No private replacement of an existing notion.

Validation: the initial saved packet dry run passed at temporary commit
`81a52aae8f9`, but that did not resolve the independent review. The packet was then
repaired substantively as below. The new definition module compiles without warnings.
Final validation compiles both files together in dependency order with `scompile.py`
and then uses `deliver2.py --no-push`; results are recorded below before delivery.
No live source was edited and no direct git command was used.
No statement dispute or source-based correction is needed.

## Second reading by N8

I reread the node, all three expanded predicates, the canonical comparison definitions,
and the theorem together. This is a self-check, not a claim of an independent agent
review; the dispatcher explicitly forbids starting another agent, and the maintainer
provides the independent review. The clause matching above is the result of that read.
The checks caught the finite-coordinate universe mismatch (fixed with ULift) and an
ambiguous elaboration of a functor isomorphism: the tensor conclusion now asserts
invertibility of the literal published natural map, whose inverse is precisely the
requested isomorphism. The final check specifically follows all four endpoints of
the counit composite and verifies that the Hom equivalence is evaluated at the
identity of the same U-I-S object, with the retained origin constrained to alpha.
No extra geometric, Tor, or nonemptiness hypothesis was introduced.


## Returned review repaired

Point (1), H2/H13: removed the public import of
`Sheaf.Paper.EtaleProEtaleAdjunctionTransfer` and both `AdjunctionTransfer` abbreviations.
The four ordinary clauses now directly intersect recorded bounded constructibility
with the existential ordered `hasTorAmplitudeIn` test. The five pro-etale clauses
intersect bounded constructible etale origin with the already landed, definition-owned
`HasFixedCoefficientProEtaleTorAmplitude`. Searching the current DAG found that
`def-weil-proetale-tor-amplitude` already owns this exact fixed-module presentation,
so no redundant pro-etale definition node was added. The saved-only theorem dependency
is dropped by rebuilding the node from current live state, then adding only the three
needed definition owners. The live base never contained that theorem in stmt_deps;
this is not a change to the reviewed mathematical split.

Point (2), H2/H13: removed the normalization theorem module from the statement imports
and its saved-only statement dependency. Added the definition node and module below,
containing the exact adjunction-uniqueness constructions. Distinct declaration names
avoid colliding with the legacy theorem module if downstream code imports both.
No natural isomorphism is postulated or chosen arbitrarily. The theorem's mathematical
normalization claim stays in proof step 6 and in the unchanged proof_deps.

Advisory: MB now uses `pbcFixedScalarExtension P.smallEtaleTopology φ`, from the
already cited witness-compatibility definition owner. Removed the direct public
`EtaleDerivedScalarTensor` import. The scalar functor is the left adjoint determined
by actual restriction of scalars on the same small etale coefficient sheaf categories.

## New nodes

`def-sf-closed-identity-open-comparison` defines the ordinary etale and pro-etale
identity-open compactification identifications. Its source is the current blueprint
`thm-sf-ambient-adjoint-class.proof.md` four-factor Hom chain specialized to (id_Z,i),
and the closed-embedding computation of `lem-coef-finite-dualizing.proof.md` paragraph 3.
For each finite commutative A and closed immersion i, its two Lean definitions have
source `rightDerivedLowerShriekOfCompactification ... (Compactification.ofIsProper i)`
and target the corresponding `lowerStar ... i |>.rightDerivedFunctor`. Their real
bodies are `isoWhiskerRight (mapDerivedCategoryNatIso (leftAdjointIdIso ... upperStarId)
≪≫ mapDerivedCategoryIdIso _) _ ≪≫ leftUnitor _`. Thus the normalization is fixed by
identity inverse image and its specified extension-by-zero adjunction, on all objects.
No theorem is added to this module, and there is no sorry in either construction.

Searches are recorded verbatim in the new node: LeanSearch for the identity-open
compact-support/direct-image comparison returned 8 unrelated topological/ordinary
scheme restriction results; LeanFinder for removing identity extension by zero returned
8 unrelated support-extension results; Mathlib grep for `leftAdjointIdIso` and
`mapDerivedCategoryIdIso` found the general adjunction constructions (5 hits), which
are reused. Direct rg in WeilConjectures and Sheaf found only the two plain definitions
in the theorem-owned `ClosedIdentityOpenHomNormalization` module. DAG rg found only
that theorem node. `blueprint_refs.py search identity-open identifications` returned
0 blueprint nodes. This is the definition-owner extraction required by the return,
not an additional mathematical construction. The new names were searched in both
source trees before definition, with no hits.

Second reading of the repair by N8: reread both definition bodies against the legacy
constructions and their node; they differ only in declaration names, owning blueprint
id and imports. Checked every ordinary clause uses the original scheme and ring,
every pro-etale Tor test is on the actual pro-etale object, and the retained origin
uses the same bounded constructibility predicate. Checked MB's quotient map remains
literal, and the counit equation and W.complex/HEq constraints are unchanged. Empty Y,
r=0, m=n and i=id remain allowed. Ordered intervals do not exclude zero complexes:
choose a=b=0, and every test tensor is zero. No equality of site universes is imposed.


Validation of the repair: `scompile.py N8 lem-coef-dualizing-closed-site` on both
modules passed without errors or non-sorry warnings (main module sandbox 22.0 s,
library form 11.5 s). The first repaired dry run found grouped DAG citations that
its exact citation checker did not recognize; each citation was given its own
brackets, without changing dependencies or mathematical text. The second dry run
validates the resulting packet before the prescribed push.

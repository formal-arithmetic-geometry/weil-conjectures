## Worker report

The delivery states `WeilConjectures.finiteMappingAdjunction` in
`Sheaf.SixFunctors.FiniteMappingAdjunction`. It is a natural isomorphism of functors
on the entire fixed-scalar presentation of `Dᵇ_ctf(X,Aₙ)`, with a prescribed
comparison equation for every finite-Tor constructible etale representative and an
explicit counit-pairing equation for every M in its entire intrinsic domain.
The only postponed proof is the main theorem. Every helper has explicit data;
there is no chosen arbitrary map, exceptional functor, point isomorphism or tensor
comparison. The node's statement and dependencies are unchanged.

Source read: current blueprint main-20261015,
`blueprint/sec-smooth-purity/sk-lem-sp-tower/prop-coef-integral-dualizing.proof.md`,
second paragraph. It explicitly constructs the finite mapping-complex adjunction
from the ordinary etale internal adjunction by the finite site comparisons and
specifies its transition maps by their counits. This is the node's six-step route.

### Hypotheses and objects

- The global datum is `D : FiniteFieldDatum.{u}`. Its fields give the finite base
  field, prime characteristic and the specified algebraic closure `D.k`.
  `Spec (.of D.k)` is the point s. The imported point-coefficient module supplies
  `pointFibreBaseIsAlgClosed`, derived from the datum, without an added premise.
- The prime is `l : ℕ` with `[Fact l.Prime]`; `hl : l ≠ D.p` retains the exclusion
  of the characteristic. `E : Type u`, `[Field E]`, `[Algebra (Padic l) E]` and
  `[FiniteDimensional (Padic l) E]` give exactly the finite coefficient extension.
- The ring, valuation ring and chosen uniformizer are the published
  `Padic.coefficientExtensionRing`, `Padic.coefficientExtensionIntegers` and
  `Padic.coefficientExtensionUniformizer`. Level `n + 1` with `n : ℕ` covers
  every positive integer, including level 1 at n=0. There is no level-zero ring.
  The canonical `ULift.{u+1,u}` puts the same ring into the module universe
  required by the small-site APIs; it changes neither scalars nor modules.
- `X : Scheme.{u}` and `[X.Over (Spec (.of D.k))]` supply a. The three instances
  `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact` on its structure
  morphism mean separated and finite type. No smoothness, purity, properness,
  dimension bound or extra ambient exceptional adjunction is assumed.
- `c : Compactification (X ↘ Spec (.of D.k))` is the single fixed factorization
  used throughout. `finiteMappingCompactSections` uses exactly
  `ProEtale.rightDerivedLowerShriekOfCompactification ... c`, followed by
  ordinary derived global sections on s. It is Cₙ, since point sections is exact
  on the recorded constructible coefficient class. The finite part of the
  recorded compact-support realization is this proper/open composite.
- M ranges over `(finiteTorConstructibleProEtaleModule ... X).FullSubcategory`
  via its inclusion in `finiteMappingGlobalHom` and `finiteMappingCompactSections`.
  This is the intrinsic bounded constructible condition with one finite Tor
  interval, transported by `finiteCoefficientIntrinsicRealization`; it is not
  replaced by an assumption that M has an etale origin.
- `ProEtale.finiteDualityProEtaleObject ... c` is omega: the recorded finite
  exceptional inverse image `Rν_* ⋙ a^× ⋙ ν^*` applied to the coefficient unit.
  It is fixed before the isomorphism is quantified. The etale omega and its
  canonical map are `finiteDualityEtaleObject` and `finiteDualityObjectMap`.
- The completed R_W mentioned in the node is ambient notation, not an argument
  to this finite-level theorem. Its recorded module is imported; no replacement
  completion or coefficient sheaf is constructed in this delivery.

### Conclusion and normalization, clause by clause

1. `finiteMappingGlobalHom` is inclusion (opposite), then the published
   `ProEtale.derivedHom` into omega, then `ProEtale.rightDerivedGlobalSections`.
   Thus its object is precisely global derived mapping complex on X, retaining
   its Aₙ-module action rather than only an abelian-group Hom set.
2. The other functor is `(finiteMappingCompactSections ...).op ⋙
   coefficientDerivedDual (ULift ... Aₙ)`. The imported coefficient dual is
   internal Hom into the module tensor unit Aₙ[0], hence the displayed derived
   coefficient Hom of Cₙ(M) into Aₙ.
3. `∃ γ : ... ≅ ...` asserts a natural isomorphism, so invertibility and
   contravariant naturality in every M and every derived morphism are part of
   its type. An unnormalized `Nonempty` objectwise isomorphism is insufficient
   and is not used here.
4. The additional condition quantifies over EVERY etale J satisfying the
   recorded `finiteTorConstructibleEtale` predicate. It supplies only the
   bounded-below proof `hplus` and the proof `hpro` that its comparison pullback
   lies in the domain. These are conclusions, not extra hypotheses or choices
   of representatives. The equation therefore fixes gamma independently of an
   origin, because constructible origin and bounded-below comparison provide
   an essentially surjective presentation of the entire domain.
5. The equation is `FiniteMappingSameComposite` of two fully specified arrow
   lists. `FiniteMappingComposite` recursively says that each arrow has exactly
   the indicated endpoints and that the result is their ordinary composite;
   it ends at an identity arrow. It is equality of composites in D(Aₙ), not a
   weaker comparison up to an unspecified automorphism. All the witnesses in
   this predicate are equal to the named arrows; they are proof witnesses.
6. The left route first takes `finiteMappingHomComparisonArrows`: the derived
   comparison-unit global map, global sections of evaluation-defined site Hom,
   and global sections of Hom applied to `finiteDualityObjectMap`. Next comes
   the actual `γ.hom.app` at the comparison pullback of J. Finally,
   `finiteMappingDualTransportArrows` takes the coefficient dual of global
   sections of the inverse support comparison, then the dual of the derived-unit
   global comparison at the base. Contravariance fixes both directions.
7. The right route, `finiteMappingEtaleGammaArrows`, is inverse Leray, global
   sections of `derivedHomRightDerivedLowerShriekIsoOfFinite` at (J,Aₙ),
   global sections of internal Hom precomposed by
   `rightDerivedLowerShriekIso ... c`, and the point Hom evaluation comparison.
   The support isomorphism is essential: the adjunction uses the compactification
   chosen by its instance, whereas Cₙ uses exactly c. The explicit third arrow
   makes these identical without a hidden identification.
8. `finiteMappingEtalePointDual` constructs the point comparison from the actual
   constant-sheaf equivalence: its canonical sections/inverse isomorphism,
   `DerivedCategory.mapDerivedCategoryInvIhomUnitIso`, and internal Hom of the
   sections/inverse isomorphism. The middle map is the evaluation transpose of
   the monoidal equivalence, so this fixes the evaluation normalization. Under
   finite site comparison it is the recorded `finitePointInternalHomKappa`
   normalization of `finitePointInternalHomEvaluation`, including the
   comparison counit at the coefficient unit.
9. The second conjunct states the counit normalization explicitly. It supplies
   `homega`, the bounded-below proof for `finiteMappingCounitInput ... c`, as a
   conclusion. This input is the ordinary etale exceptional inverse image of
   Rnu_* of the pro-etale coefficient unit; its comparison pullback is exactly
   `finiteDualityProEtaleObject ... c` used by the first functor.
10. `finiteMappingCounit` is the four-arrow list from F_n omega to the pro-etale
    coefficient unit: fixed-c support comparison, comparison pullback of
    `rightDerivedLowerShriekIso ... c`.hom, comparison pullback of the ordinary
    exceptional adjunction counit, then the comparison adjunction counit.
    The `.hom` orientation converts compact support for c to the support functor
    used by the ordinary exceptional adjunction. Thus c need not be the global
    instance's compactification. Every factor is a published canonical map.
11. The existential `scalar` is an isomorphism from A_n[0] to RΓ(s,A_n,s).
    Its hom is prescribed by `FiniteMappingComposite
    (finiteMappingScalarUnitArrows ...) (Arrow.mk scalar.hom)`. This list is the
    actual derived constant/sections adjunction unit, the exact-derived-functor
    comparison, the degree-zero constant-sheaf comparison, the normalized
    monoidal unit map and the derived degree-zero unit identification. This
    fixes scalar uniquely; neither its invertibility nor its normalization is
    an added hypothesis.
12. `finiteMappingPairing` is the required pairing in Hom-first order. A Koszul
    braiding followed by inverse Leray puts its factors in support-first order.
    `finiteMappingSectionsTensorArrows` applies canonical global tensor, using
    Leray for comparison direct image, ordinary etale constant projection and
    its counit, and the lax comparison image tensor map (unit, pullback tensor,
    tensor of its two counits). Then follow global sections of compact-support
    projection for c, F_n of tensor with the ordinary pullback counit, F_n of
    sheaf Hom evaluation, all four factors of `finiteMappingCounit`, and
    `scalar.inv`. Its source is RΓ(X,RHom(M,omega)) tensor C_n(M) and its target
    is A_n[0]. No arbitrary projection or pairing map is quantified.
13. The final clause quantifies over EVERY
    `M : (finiteTorConstructibleProEtaleModule ... X).FullSubcategory` and states
    `FiniteMappingSameComposite (finiteMappingTransposeArrows ...
    (γ.hom.app (op M))) (finiteMappingPairing ... c homega scalar M.obj)`.
    The transpose list consists of the same canonical Koszul braiding followed
    by `MonoidalClosed.uncurry` of the actual gamma component. Hence this is
    equality of its tensor-Hom transpose with projection/evaluation/counit,
    explicitly on all intrinsic M, independently of the etale equation.

### Dependencies read and used

- `def-weil-finite-field-fiber`: `Sheaf.Paper.FiniteFieldFiber` — `WeilConjectures.FiniteFieldDatum`.
- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` — `Padic.finite_coefficientExtensionRing`.
- `def-weil-scheme-morphism-properties`: `None` — `None`.
- `lem-weil-pbc-comparison-global-cohomology`: `Sheaf.AlgebraicGeometry.ComparisonGlobalCohomologyFiniteNormalized` — `AlgebraicGeometry.ProEtale.isIso_finiteComparisonGlobalSections`.
- `thm-weil-pbc-site-comparison`: `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit` — `AlgebraicGeometry.ProEtale.isIso_compactSupportComparisonUnit`.
- `lem-coef-finite-point-internal-hom-evaluation`: `Sheaf.Paper.FinitePointInternalHomEvaluation` — `WeilConjectures.finitePointInternalHomEvaluation`.
- `lem-sf-comparison-tor-amplitude`: `Sheaf.Paper.ComparisonTorAmplitude` — `AlgebraicGeometry.finiteCoefficient_comparison_preserves_torAmplitude`.
- `lem-weil-finite-duality-site-comparison`: `Sheaf.SixFunctors.FiniteDualitySiteComparison` — `WeilConjectures.finite_duality_site_comparison`.
- `thm-fix-general-biduality`: `Sheaf.Paper.FiniteStageVerdierBiduality` — `WeilConjectures.finite_stage_verdier_biduality`.
- `det-thm-sf-ctf-stability-direct-images`: `Sheaf.SixFunctors.CtfStabilityDirectImages` — `AlgebraicGeometry.ProEtale.CondensedRing.constructibleFiniteTor_stability_direct_images`.
- `lem-sf-etale-proetale-exceptional-transport`: `Sheaf.AlgebraicGeometry.EtaleProEtaleExceptionalTransport` — `AlgebraicGeometry.ProEtale.etale_proEtale_exceptional_transport`.
- `def-pur-derived-internal-hom`: `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses` — `CategoryTheory.derivedInternalHomOfUniverses`.
- `def-weil-completed-integral-coefficients`: `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` — `WeilConjectures.integralConstantToCompletionOfUniverses`.
- `def-weil-exceptional-inverse-image`: `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` — `WeilConjectures.ConstructibleExceptionalCoefficients.System`.
- `def-weil-finite-coefficient-point`: `Sheaf.Paper.FiniteCoefficientPoint` — `WeilConjectures.pointQbarFibre`.
- `def-weil-finite-tor-amplitude`: `Sheaf.Paper.FiniteTorAmplitudeSites` — `WeilConjectures.finiteTorConstructibleEtale`.
- `def-weil-finite-torsion-constructibility`: `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility` — `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible`.
- `def-weil-integral-rational-qbar-compact-support`: `Sheaf.Paper.QcqsCompactSupportRealization` — `WeilConjectures.sfQcqsCompactSupportRealization`.
- `lem-asd-internal-adjunction-evaluation`: `Sheaf.SmoothPurity.InternalAdjunctionEvaluation` — `AlgebraicGeometry.Etale.internalAdjunctionEvaluation`.
- `lem-pur-bounded-site-adjunction-transpose`: `Sheaf.Paper.BoundedSiteAdjunctionTranspose` — `AlgebraicGeometry.ProEtale.boundedSiteAdjunctionTranspose`.
- `lem-pur-projection-comparison-etale-origin`: `Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOrigin` — `AlgebraicGeometry.ProEtale.projectionComparison_etaleOrigin`.
- `lem-sf-class-compact-support-comparison`: `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison` — `AlgebraicGeometry.ProEtale.compactSupportSiteComparison`.
- `lem-sf-proetale-constructible-origin`: `Sheaf.Paper.ProEtaleConstructibleOrigin` — `AlgebraicGeometry.ProEtale.constructible_proEtale_origin`.
- `prop-asd-internal-adjunction`: `WeilConjectures.SixFunctors.Etale.Derived.TensorHom` — `AlgebraicGeometry.Etale.derivedHomRightDerivedLowerShriekIsoOfFinite`.

The scheme-properties node is explicitly a convention collecting other nodes,
not a declaration. Its separated and finite-type clauses use Mathlib classes.
The recorded generic derived-Hom node publicly exports the ordinary-etale
specialization; the finite-duality interface publicly exports the corresponding
pro-etale `derivedHom`. The recorded exceptional and compact-support nodes also
reexport their actual finite-level constructions. No dependency was restated.
Proof-only dependencies are imported without `public`; the modules owning the
objects and canonical maps in the signature are public imports.

### Edge cases

- X empty, M=0 and J=0: all mapping and support objects are zero; the actual
  functors and the named unit/counit/evaluation maps retain their usual zero
  components. Neither a nonempty scheme nor a nonzero complex is assumed.
- X=s with the identity compactification: the equation reduces to derived
  module evaluation and the comparison adjunction triangles. The point map
  has its evaluation normalization, so a scalar multiple is excluded.
- n=0 is precisely the residue-field coefficient level A₁. All finite instances
  come from `finite_coefficientExtensionRing ... (Nat.succ_pos n)`.
- Nontrivial c: the explicit `rightDerivedLowerShriekIso` arrow retains the
  fixed compactification, including when it differs from the instance's choice.
- Singular and nonproper finite-type X are included. No smoothness or dimension
  hypothesis was smuggled into the signature.
- No common Tor interval across different M is asserted; each M has the
  recorded finite Tor interval. No finite-Tor condition on arbitrary J is
  inferred from bounded constructibility alone.
- Universe u is arbitrary; both site presentations use the published small
  sites and ModuleCat at u+1. No site object/morphism universe is equated.

### Searches and validation

The retained `searches.jsonl` contains the earlier msearch searches, and these
were repeated during this continuation:

- msearch leanfinder: “finite coefficient derived global mapping complex
  exceptional adjunction compact supports”: eight HomologicalComplex support
  results, no finite mapping adjunction.
- msearch loogle: `CategoryTheory.Adjunction`: twelve ordinary adjunction
  declarations; none is the stated finite-coefficient mapping theorem.
- msearch grep: `derivedHomRightDerived|mappingAdjunction|GlobalHom`,
  Mathlib/CategoryTheory: zero matches.
- msearch leansearch: “derived mapping complex exceptional adjunction compact
  support finite coefficient sheaves”: ordinary derived adjunctions, sheaf
  pullback adjunctions and constantSheafΓAdj, no exact theorem.
- rg in upstream WeilConjectures and side lean/Sheaf for the node id,
  `finiteMapping`, and all new helper names: no existing statement or helper
  definition (one downstream docstring mentions the item). The upstream
  TensorHom and Point modules were opened, not inferred from search names.
- rg Mathlib/CategoryTheory for list-of-Arrow composition predicates and the
  helper names: no match. The helper predicates only package this equation,
  using existing Mathlib Arrow, List, equality and category composition.

The retained attempt timed out when it forced expensive definitional conversion
between equivalent derived closed-structure presentations, and lacked a public
TensorHom import. Naming each actual arrow and expressing the composite equation
with endpoints solves the conversion problem without an added premise, a new
axiom, a weakened normalization or a higher timeout. The canonical support
independence arrow was also made explicit. All scratch checks are retained in
`scratchpad/`, outside the deliverable module tree.

The repaired module was compiled through `scompile.py` in sandbox and actual
module-name modes: 10.6 s and 11.0 s on the final recorded run, no errors or
warnings. The unchanged 60-second limit is respected. The only sorry is the
main theorem; the helpers are actual definitions. All new declarations are
listed in the item's lean.declarations, every variable and universe is bound,
and autoImplicit is false.

Additional repair searches: msearch leanfinder for “canonical derived global
sections tensor comparison from constant sheaf adjunction and exceptional counit
finite compact support” returned eight condensed-category declarations, no match;
msearch grep for `rightDerivedGlobalSections.*[Tt]ensor|finiteMappingCounit|finiteMappingPairing`
in Mathlib CategoryTheory returned no matches. Project/source rg found no
published helper of these names. The existing constant projection, site tensor,
compactification projection, adjunctions and coefficient dual are reused.

## Repair of H3 at returned head 43ffcb71243a

The returned theorem had only etale agreement; claiming its counit clause followed
from proof step 5 did not state that clause. The old claim has been removed from
this report. The retained theorem and its etale equation now have the additional
explicit counit-pairing equation described in clauses 9–13 above. The main
proof docstring states how to supply both normalization witnesses and prove
that equation. This is a completion of the unchanged node statement, not a node
statement correction. Only the lean field of the item's node changes.

`lem-coef-finite-adjunction-transition` uses the finite traces and their counit
normalization. `lem-coef-tower-natural-currying` uses the identification of the
curried tower evaluation/trace pairing with each gamma component. The added
all-M equation supplies exactly these two consumers' missing characterization.
Neither citer was edited. No additional DAG nodes or dependency modules were
needed: all new helpers package the canonical maps of this same node.

## Second reading by Q55

This is a self-reading by the dispatched worker, as required by the instruction
not to start other agents. It does not claim independent review; the maintainer
performs that review.

I reopened the unchanged DAG statement, its source second paragraph, the revised
module and the two consumers named in the return. The field, prime exclusion,
coefficient extension, positive level n+1, separated finite-type X and fixed c
remain the same inputs. The domain remains the entire intrinsic bounded
constructible finite-Tor category. The source/target functors still give the two
global derived mapping complexes; gamma is still a natural isomorphism. The
retained etale equation still fixes its agreement on every etale representative.
The new explicit final conjunct now states its transpose characterization for
EVERY M, using the exceptional counit for exactly c and the normalized point
scalar isomorphism. homega and scalar are conclusions, not hypotheses.

The unit, projection, evaluation and counit factors were read in their owning
source modules. The four-arrow counit agrees with the earlier prescribed
finiteMappingCounit formula, including the `.hom` compactification-independence
orientation. I checked every adjacent endpoint of the 18-arrow pairing by
scratch `rfl` declarations (all 17 junctions passed elaboration). Those scratch
checks used debug.skipKernelTC only for their repeated, expensive endpoint
rechecks; this option is absent from every delivered file. The delivered module
itself passed normal kernel compilation in both modes. The pairing and transpose
both start at the same Hom-first tensor product and end at A_n[0]. Their initial
braidings use the same canonical DerivedMonoidal.braiding, so tensor order and
Koszul signs match.

I rechecked X empty, M=0, n=0 (meaning level 1), singular/nonproper X, arbitrary
universe u, and c different from an instance's chosen compactification. The
normalization uses the same genuine functors in all these cases and excludes
none. There is no new nonemptiness, smoothness, finite-dimension, common Tor
interval or ambient pro-etale exceptional-adjunction hypothesis. The output
contains no STATEMENT-DISPUTED flag or statement_change.

### Continuation self-check after saved-packet dry run

The saved repaired packet passed deliver2.py --no-push at dry-run commit
`b8cb5a4aae`, including preflight and per-file compilation. I retained its Lean
module unchanged and reread all 475 lines, the current node statement, both
consumers named in H3, and the current blueprint proof paragraph. The final
conjunct explicitly quantifies over every intrinsic M and equates the transpose
of the actual gamma component with finiteMappingPairing. The pairing contains
the fixed-c projection, evaluation, all four finiteMappingCounit factors, and
the inverse of the scalar isomorphism whose hom is fixed by the derived unit.
The natural-isomorphism and etale-agreement clauses are retained. Comparing the
packet node with the current shared node finds only the permitted lean field
different; the positive-level, empty/zero and arbitrary-c cases remain covered.
The sole postponed proof is finiteMappingAdjunction. This continuation is also
a worker self-reading, not an independent review.

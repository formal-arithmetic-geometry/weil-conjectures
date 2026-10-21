## Worker report

The delivered theorem is `WeilConjectures.roosIntrinsicCompletenessEquivalence` in
`Sheaf.Paper.RoosIntrinsicCompletenessEquivalence`. It states the five conditions
as `List.TFAE`, in the order of the node. The node statement and proof are unchanged.
All postponed proofs are named theorems with source, owning blueprint node and
natural-language proof. Definitions contain actual data; the scalar chain map is
chosen only from an existence-and-UNIQUENESS theorem specifying every section value.

Source read: Stacks `algebraization.tex`, tags 099B and 0A0E, including the local
localization vanishing criterion and the Koszul completion unit; the node's reviewed
six-step proof and all recorded statement-dependency declarations and docstrings.
The main theorem docstring carries that full proof plan, including the normalized
coefficient presentation transport and the restriction on what TR3 proves.

Hypotheses and objects, individually:

- Primes p and l: `(p l : ℕ) [Fact p.Prime] [Fact l.Prime]` and `_hpl : p ≠ l`.
- Finite E/Q_l: `(E : Type u) [Field E] [Algebra ℚ_[l] E]`
  `[FiniteDimensional ℚ_[l] E]`; its ring A and chosen t are the published
  `Padic.coefficientExtensionIntegers l E` and `coefficientExtensionUniformizer l E`.
- Noetherian A, additive-torsion A/I and finite/perfect positive quotients are the
  fields of the published `Scheme.AdicCoefficientDatum A`, bound as `d`.
  `_hd : d.ideal = Ideal.span {coefficientExtensionUniformizer l E}` identifies
  that ideal with the node's specified ideal; this is not an arbitrary replacement datum.
- T is arbitrary `(T : Scheme.{t})`. There is no characteristic, finiteness,
  separation, dimension or cohomological boundedness hypothesis on T or K.
- The site is the actual `T.ProEt` with `Scheme.ProEt.topology T`.
  Site objects have universe t+1, morphisms t, independently of E's universe u.
- R is `completedIntegralCoefficientSheafUnrestricted l E T`, the actual limit
  of the finite constant quotient sheaves, used by `IntegralOnSlice.ring ... none`.
  It is never replaced by the discrete constant ring A.
- K is `(K : IntegralOnSlice.D l E T none)` in the published derived category
  of module sheaves over precisely this R.
- The single chosen flat-term K-flat representative is
  `(P : (IntegralOnSlice.Good l E T none).FullSubcategory)` and its realization
  `(e : DerivedCategory.Q.obj P.obj ≅ K)`. `Good` is K-flatness together with
  flatness in every degree. This binds the representative specified in the node,
  rather than assuming a special property of K. No different representatives are
  silently chosen for the three units.

Clauses, individually:

1. `IntegralOnSlice.IsComplete l E T none K` is exactly the published global
   existential Roos distinguished-triangle convention. Its first map is the tuple
   of actual quotient-reduction maps. This is not redefined as a canonical-unit test.
2. The second entry quantifies every `U : T.ProEt` and every compatible section
   `s` of R restricted to the slice over U. A covering sieve S and local equalities
   `s.val (op (Over.mk f)) = integralCompletionScalarValue ... (op V) * c`
   assert exactly that s belongs to the SHEAF ideal tR. Local divisibility is used
   rather than the potentially smaller sectionwise image. Quantifying sections on
   every slice tests all local sections, including nonconstant multiples and zero.
   `integralCompletionLocalTest` is the existing derived internal Hom applied to
   the existing sheafified sectionwise localization R_U[1/s] in degree zero and
   the existing exact derived restriction of K. `IsZero` is categorical vanishing.
3. `IsIso (integralKoszulLimitUnit ... K P.obj e)` tests the degree-zero Koszul
   unit into the total derived inverse limit. At exponent n+1 the complex is
   `mappingCone (t^(n+1) : P → P)`, the standard total-cone coordinates of
   P tensor the negative one-generator Koszul complex `[R → R]`. The scalar acts
   by its compatible residues through the actual constant-to-limit map. The
   transition is multiplication by t on the source copy and identity on the
   target copy. The unit is the target inclusion, on every level.
   The inverse limit uses the exact-products Roos fiber of the specified 1-s.
4. `IsIso (integralKoszulIntrinsicUnit ... K P.obj e)` tests the specified
   intrinsic augmentation. Its complex is `mappingCocone (-(1-s))`, whose
   differential in the existing Mathlib cocone coordinates is
   `(dx, (1-s)x - dy)`. Its chain map is explicitly `mappingCocone.lift ... u 0`.
   This retains the signed fiber and zero second cochain of the node, including
   its normalization, rather than testing an unspecified isomorphism K ≅ completion.
5. `IsIso ((IntegralOnSlice.completionUnit ... none).app K)` tests the published
   canonical quotient derived-limit comparison. That unit is characterized on
   every good representative by its actual strict quotient augmentation `(c,0)`.

`List.TFAE` asserts equivalence of all five entries. The main proof plan
uses TR3 only to transfer local completeness along an isomorphism, never to claim
that an arbitrary TR3 filler is the canonical comparison.

Dependency declarations used (recorded module and declaration):

- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses`, through `IntegralOnSlice.hom`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `Q` and
  `singleFunctor`; `HasDerivedCategory.standard` supplies the standard localization.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `WeilConjectures.integralConstantToCompletionOfUniverses` and the actual
  `completedIntegralCoefficientSheafUnrestricted` exposed by that interface.
- `Sheaf.Paper.DerivedCompleteOnSlices`: `WeilConjectures.IntegralOnSlice.IsComplete`.
- `Sheaf.Paper.IntegralReductionTowerCanonical`:
  `WeilConjectures.canonicalIntegralReductionTower`, retained by import; the actual
  strict reduction tower and comparison are the published operations below.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and its coefficient ring/integers/uniformizer.
- `Sheaf.Paper.AdicCoefficientDatum`: `Scheme.AdicCoefficientDatum` and the
  original recorded `Scheme.completedReductionTower` construction.
- `Sheaf.Paper.IntrinsicCompletionCompleted`, directly publicly imported:
  `Scheme.IsCompletedIntrinsicallyDerivedComplete` and
  the original general completed Koszul constructions; independent-universe
  actual-R chain models are defined in the item module.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and its topology.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Sheaf.Paper.KoszulReconstruction`: `Scheme.koszulReconstruction`, publicly
  retained; its general theorem remains unchanged; the item defines its actual-R chain model.
- Newly cited already-landed `def-pur-integral-derived-operations`, module
  `Sheaf.Paper.IntegralDerivedOperationsOnSlices`:
  `IntegralOnSlice.ring`, `rings`, `D`, `Good`, `hom`, `tower`, `augmentation`,
  `completion`, `completionComparison`, `roosUnit`, and `completionUnit`.
- Newly cited already-landed `def-weil-pbc-ringed-section-localization`, module
  `Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses`:
  `CategoryTheory.ringedSectionLocalizationOfUniverses`, the module sheafification
  of the sectionwise away-localization, not an arbitrary object.
- Newly cited already-landed `def-weil-pbc-ringed-site-derived-restriction`, module
  `Sheaf.CategoryTheory.RingedSiteDerivedRestrictionUniverses`:
  `CategoryTheory.ringedSiteDerivedRestrictionOfUniverses`, the canonical derived
  functor of exact restriction to the slice.
- Proof dependencies are explicitly imported: completed coefficient presentation
  transport, completed Koszul quotient comparison, completed tensor reflector,
  independent-coefficient strict-tower homotopy limit, strict Roos derivation,
  pro-etale exact countable products, and the pretriangulated triangle API.
  The original general dependency records and modules are not changed.

Edge cases checked before stating the result:

- K=0: all units have zero source and target and all five conditions hold.
- Empty T: its module category is trivial; all five conditions hold.
- Torsion A/t^a at a point (a positive): completion recovers the object and all
  five conditions hold. No boundedness assumption is introduced to force this.
- A[1/t] at a nonempty point: all reductions and Koszul levels are acyclic, so
  completion is zero and the three units fail to be invertible; local RHom detects
  the nonzero object, and the Roos triangle also cannot hold.
- Positive powers are indexed by n+1 for n : ℕ; the spurious quotient A/t^0 is
  absent. The first transition is t on degree -1 and identity on degree zero.
- The section s=0 is included; localization at zero is the zero ring, hence its
  derived Hom vanishes, as required. All local sections of the sheaf ideal,
  not merely the constant generator, are quantified.
- No scheme/field universe equality is imposed. Slice sheafification is supplied
  by essential smallness inside the helper definition, not by a new theorem hypothesis.

Searches for reuse:

- `msearch.py` LeanFinder: "Roos derived completeness equivalent to local derived
  completeness and invertibility of canonical Koszul and quotient completion units";
  eight hits (`IsPrecomplete`, `IsAdicComplete`, ordinary adic-completion lemmas),
  none stating the derived ringed-site equivalence.
- Loogle: "IsDerivedComplete, reconstructionKoszulDerivedUnit, intrinsicCompletionUnit";
  zero hits, unknown `IsDerivedComplete` identifier. This was not treated as
  evidence that the already-published project notions were absent.
- Mathlib grep: `[Rr]oos|[Kk]oszul.*[Cc]omplet|[Cc]omplet.*[Kk]oszul`, CategoryTheory;
  zero hits.
- LeanSearch: "Roos completeness equivalent canonical Koszul completion map is
  isomorphism ringed site"; eight hits concerning ordinary adic completion,
  uniform completion and `isIso_toSpecΓ`, none matching this statement.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the item id, Roos/intrinsic
  completeness and the proposed declaration names: no existing five-condition
  statement or collision. Mathlib and the project were also inspected for the
  actual localization, restriction, scalar action, cones and completion interfaces.
  Existing declarations were reused wherever their objects and universes fit.
  Wrapper search provenance is in sandbox `searches.jsonl`.

No statement dispute or source correction is needed. No new definition nodes or
dependency repairs are delivered. All integral chain-model helpers belong to this
item and are recorded in its `lean.declarations`. The item
gains only `lean` and the three existing landed statement-dependency ids named above.

Validation of the repaired single-module packet uses the prescribed `scompile.py`,
followed by `deliver2.py --no-push` and `deliver2.py`. Results are recorded below.

## Second reading by NL

The dispatcher explicitly requires a single worker and prohibits starting other
agents. This is a fresh self-review, not a claim that a second independent worker
reviewed it; the maintainer supplies the independent delivery review.

Re-read the node against the unchanged final signature and the helpers now in its
module. The five conditions, their order, every hypothesis and all canonical maps agree as
mapped above. The review specifically checked full local sheaf-ideal membership,
actual completed rather than discrete coefficients, independent coefficient/site
universes, positive indexing, and the distinction between the signed intrinsic
fiber and the ordinary Roos cone. During elaboration, powers in the transition
square needed parentheses, and slice sheafification/derived-category structures
were supplied canonically inside the local test helper. The Roos limit was written
directly with the specified transitions to avoid unnecessary definitional unfolding
of `Functor.ofOpSequence`. These changes preserve every mathematical object and
augmentation. All definitions have actual data and every postponed proof is named.

## Repair of return H13 (2026-10-21)

The retained packet's required initial dry run passed (`0338417c2fe`), but the
independent review correctly found that its two dependency records rebound the
published general interfaces to narrower integral cases. The repair therefore
changes the packet rather than re-pushing that mechanically accepted packet.

- Dropped `def-weil-pbc-intrinsic-completion.json` from the delivery. The published
  `IntrinsicCompletionCompleted` record and all 27 declarations stay intact.
- Dropped `prop-weil-pbc-koszul-reconstruction.json` from the delivery. The published
  `KoszulReconstruction` record and its already-proved general theorem stay intact.
- Moved the scalar value and ExistsUnique-characterized scalar map, Koszul level,
  (t,1) step and tower, product unit, one-minus-shift, signed intrinsic fiber and
  explicit (u,0) unit into `RoosIntrinsicCompletenessEquivalence.lean`.
- Moved the ordinary `mappingCocone(1-s)` Koszul limit and its normalized unit into
  that same item module. Retagged every helper docstring to the item's blueprint
  id and listed every helper in its `lean.declarations`.
- Removed `integralKoszulReconstruction` entirely. Its additional sorry is absent;
  the main theorem's proof plan uses the published general reconstruction theorem
  through the documented normalized coefficient-presentation transport.
- Removed both obsolete standalone integral helper modules from the packet.
  The only Lean module delivered now imports the two published general modules.

The main theorem signature is byte-for-byte unchanged. In particular the full
sheaf-ideal local test includes s=0, transitions are (t,1), the signed fiber has
(dx,(1-s)x-dy) and unit (u,0), the quotient unit and IsComplete are the published
ones, and the field and scheme universes remain independent. No dependency record
is replaced, no old module is orphaned, and no statement correction is needed.

The only postponed theorems now are `integralKoszulScalar_existsUnique`,
`integralKoszulStep_square`, `integralKoszulUnit_compatible`,
`integralKoszulIntrinsicUnit_condition`, `integralKoszulLimitUnit_condition`, and
`roosIntrinsicCompletenessEquivalence`. The first five are the proof obligations
of the item's explicitly specified chain data; their docstrings give their full
naturality, power, product-component or zero-cochain arguments.

Repaired-module compile: `scompile.py NL
lem-pur-roos-intrinsic-completeness-equivalence <item module>` passed both the
sandbox compile (44.5 s) and library-name compile (32.3 s), with no errors or
warnings. Static packet check confirms exactly one module and the item's one node
file, 20 declarations recorded, all source/blueprint docstrings present, no line
over 100 columns, and only `lean` plus the three documented landed dependencies
changed on the item. The preserved node statement and proof are unchanged.

The repaired packet's prescribed `deliver2.py --no-push` passed preflight and
server compilation: `OK (dry run): commit 9116596e588 passes the preflight and
compiles; nothing pushed`. Its staged set contains only the report, the item node
and `RoosIntrinsicCompletenessEquivalence.lean`; both returned dependency records
and both obsolete standalone integral modules are absent. The final push uses
the prescribed delivery wrapper.

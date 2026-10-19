## Worker report

The module `Sheaf.Paper.ClosedSupportedCupVanishing` states
`WeilConjectures.PurityFiniteSetting.closed_supported_cup_vanishing`, with `sorry` as
its entire proof. Three concrete helpers specialize existing constructions; none chooses
an arbitrary operation, isomorphism, coefficient object, or proof datum.

Hypothesis and clause correspondence:

- The finite datum A=A_{E,n}, n≥1, is `P : PurityFiniteSetting.{u}`. Its fields contain
  the finite-field datum, the distinct coefficient prime, finite coefficient extension,
  and positive coefficient index. `P.Coefficient` is the standard size lift of the
  specified quotient, as required by the existing small-site coefficient convention.
- A k-scheme X is `[X.Over (Spec (.of P.field.k))]`. Separated and finite type are
  `[IsSeparated (X ↘ Spec (.of P.field.k))]`,
  `[LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]`, and
  `[QuasiCompact (X ↘ Spec (.of P.field.k))]`. These last two are precisely finite type.
- The closed immersion is `(i : Z ⟶ X) [IsClosedImmersion i]`.
- Nonnegative integers a,b are `(a b : ℕ)`, cast to ℤ when used as shifts.
  Arbitrary signed twists are `(t s : ℤ)`.
- The class alpha is `P.FunctorialCupOrdinaryH true X (a : ℤ) t`, and beta is
  `P.FunctorialCupH true i (b : ℤ) s`. Here `true` selects the small pro-etale site.
  These are the published ordinary and supported derived-Hom models of cohomology
  with the actual finite twist sheaves. Degree-zero sheaves are bounded below, so the
  supported-Hom identification applies without an extra boundedness assumption.
- The hypothesis i^*alpha=0 is `hα`, using exactly
  `P.functorialCupOrdinaryPullback true i (X ↘ Spec (.of P.field.k)) a t α = 0`.
  This includes the canonical ordinary inverse-image, constant-unit, twist, and shift maps.
- The first conclusion is `P.closedSupportedCup i a b t s α β = 0`, in
  `P.FunctorialCupH true i ((a : ℤ) + b) (t+s)`.
  `closedCupFullSupport` precomposes alpha with the degree-zero image of the actual
  `ProEtale.lowerStarId` isomorphism. `closedSupportedCup` then calls the recorded
  `functorialCup` for supports (identity,i) and applies `functorialCupChangeSupport`
  along `pullback.snd (𝟙 X) i`. Its over-X equation is `pullback.condition.symm`.
  This identifies the scheme-theoretic intersection X times_X Z with Z; it is a
  specialization and transport of the existing operation, not a second cup definition.
- The second conclusion is the conjunction's second equality, in ordinary cohomology
  of degree a+b and twist t+s. Its second input is exactly the recorded
  `P.functorialCupForget true i b s β`. `closedOrdinaryCup` is the same cup with
  both supports full, followed by `functorialCupForget` for full support.
- There is no smoothness, regularity, Cartier, purity, constructibility, finite-Tor,
  ramification-divisibility, or exceptional-base-change hypothesis.

Dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `PurityFiniteSetting.Coefficient`, its finite datum and coefficient structures.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, the closed embedding with surjective stalks.
- `Sheaf.AlgebraicGeometry.SupportCohomology`:
  `AlgebraicGeometry.ProEtale.supportSections`, `supportCohomology`, and
  `supportHypercohomology`; these define the kernel-of-restriction groups represented
  by the dependency's supported-Hom interface.
- `Sheaf.Paper.SupportedCup`: `AlgebraicGeometry.ProEtale.supportedCup`,
  `cupComposite`, `cupIntersection`, and the normalized coefficient and shift maps.
- `Sheaf.Paper.SupportedCupFunctoriality`:
  `WeilConjectures.PurityFiniteSetting.FunctorialCupOrdinaryH`, `FunctorialCupH`,
  `functorialCupTwist`, `functorialCupSingle`, `functorialCup`,
  `functorialCupChangeSupport`, `functorialCupForget`, and
  `functorialCupOrdinaryPullback`. The pro-etale cup is explicitly the published
  tensor-morphism composite followed by the canonical twist multiplication.
  `supportedCupFunctoriality` is the recorded theorem providing the ordinary
  pullback and twist compatibility used in the node's proof plan.
- `AlgebraicGeometry.ProEtale.lowerStarId`, from the upstream pro-etale direct-image
  framework already imported by the recorded modules, supplies the identity comparison.

All recorded statement-dependency modules are imported. Proof-only dependencies are
non-public. One proof-only import is necessarily omitted under the human duplicate-import
repair instruction: `Sheaf.Paper.SupportedHomAdjunctionTranspose` imports
`Sheaf.AlgebraicGeometry.ProEtaleSupportedExteriorProduct`, which imports the general
`WeilConjectures.SixFunctors.ProEtale.Derived.Tensor`. The actual supported cup imports
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`; importing both
is rejected because both declare `AlgebraicGeometry.ProEtale.laxMonoidal_Q`. The finite
coefficient construction needed by this statement is retained. The transpose lemma
remains in the unchanged DAG proof plan and in the proof docstring; its module adds no
object needed to state the theorem. All other recorded proof modules are imported. The main theorem's docstring includes
all ten proof steps and their DAG identifiers: finite-type Noetherian geometry; normalized
Hom representatives and forgetting; ordinary twist pullback; flat supported coefficient
and shifted sheaf target; the exact derived unit; pullback of the tensor factor; unit
naturality; bifunctorial factorization; and the forgetting-support square. No new node,
dependency repair, or statement correction is needed.

Source checked: `literature/stacks-project/cohomology.tex`, labels
`remark-support-cup-product`, `remark-support-cup-product-global`, and
`lemma-support-cup-product` (Tags 0G75--0G77). The middle remark factors the action through
restriction to the support, and the lemma specifies the square forgetting support.
As the DAG explicitly requires, the proof here is the finite-coefficient pro-etale
analogue in the recorded tensor-Hom framework; no ringed-space theorem is silently
applied to the pro-etale site.

Edge cases checked: X or Z empty; full support i=identity; nonreduced closed supports;
a=0 or b=0; alpha=0 or beta=0; twists 0 and negative twists; n=1 and coefficient levels
not divisible by the ramification index. Full support uses only the direct-image
identity and the identity-pullback projection. Empty support has the zero constant
direct-image source, hence its supported group vanishes. Empty X is permitted by every
geometric hypothesis. No reducedness, smoothness, dimension, ramification-divisibility,
or extra coefficient-unit witness is imposed. The fixed u is the common scheme and
base-field universe of the recorded setting; sheaves and coefficients use its standard
u+1 lift, with no extra universe equality.

Searches performed before writing:

- `msearch.py ... leanfinder`: "A cohomology class whose restriction to a closed
  subscheme is zero has zero cup product with a class supported on that subscheme".
  Eight results, headed by `AlgebraicGeometry.exists_of_res_zero_of_qcqs` and
  `exists_of_res_zero_of_qcqs_of_top`; their displayed signatures concern sections of
  structure sheaves, powers, and restrictions, not cohomology or supported cup products.
- `msearch.py ... loogle`: `"cup", "support"`: zero hits.
- `msearch.py ... grep`: `cup.*support|support.*cup|cup.*vanish`: zero Mathlib hits.
- `rg` of `WeilConjectures` for the item id: no hit. The concept search
  `closed.*[Cc]up|[Cc]up.*vanish|cup.*eq_zero` found the fundamental-class product
  in `EtaleCohomology/Purity/Smooth/RegularImmersion.lean`; it is a different assertion.
- The same concept search in `lean/Sheaf` found unrelated alteration and trace
  docstrings. Searches for all four proposed declaration names across Mathlib,
  `WeilConjectures`, and `lean/Sheaf` found no duplicates.

No statement dispute or source correction was found.

## Second reading by Q59

Author's separate second pass, not an independent maintainer review: re-opened the node
and module and matched the finite datum, scheme hypotheses, closed immersion,
nonnegative degrees, signed twists, both input groups, ordinary pullback-zero hypothesis,
and both vanishing conclusions as above. Checked that support transport has the correct
contravariance: `functorialCupChangeSupport i intersection` takes the projection from
the intersection to Z, not its inverse; corrected the draft accordingly. Both operations
remain concrete specializations of the recorded cup, and the ordinary second conclusion
uses the recorded forget-support map on beta. All declaration names, explicit universe
binders, docstrings, and the 100-character line bound were checked. The maintainer's
independent delivery review remains separate, as specified by the dispatcher brief.

Validation: `scompile.py Q59 lem-pur-closed-supported-cup-vanishing
<...>/lean/Sheaf/Paper/ClosedSupportedCupVanishing.lean` succeeded for both the
sandbox check and actual library module, with no errors or warnings. An initial
recorded-dependency timeout was diagnosed with a temporary profiler copy; the
unchanged dependency subsequently compiled. The duplicate-tensor proof-only import
failure was repaired as documented above. No compiler limit, launcher script, live
source, dependency declaration, or mathematical hypothesis was changed.

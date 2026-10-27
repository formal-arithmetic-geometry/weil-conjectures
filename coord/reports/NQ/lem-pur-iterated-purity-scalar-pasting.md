## Worker report

Stage 2, NQ, `lem-pur-iterated-purity-scalar-pasting`. The item is stated in
`WeilConjectures.IteratedPurityScalarPasting.iteratedPurityScalarPasting`. The
statement and proof of the DAG item are unchanged. Every new theorem has a
`sorry` proof; every definition has specified data.

Sources read: the item's complete DAG statement and eight proof steps; all its
statement dependencies and their recorded Lean declarations; current blueprint
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-purity-transport/sk-thm-purity-transport.proof.md`,
especially Steps 2--4 and the final composition paragraph; the existing finite
composition construction in `PurityCompositionCoherence.lean`; the complete
normalized rational comparison data and result. The current blueprint still
requires the normalized coefficient and composition comparisons. I also read the
current `sk-prop-sp-composition/thm-pur-composition-coherence.md`, its proof
(Step 2 fixes the pullback/twist reassociation), and
`sk-prop-sp-composition/sk-prop-sp-composition-comparisons.md` (the horizontal
coefficient comparison and composite counit). No statement
fault or disputed mathematical assertion was found.

Hypotheses and objects, clause by clause:

- `D : FiniteFieldDatum.{u}` supplies p, a, q, the finite field and its algebraic
  closure k. `C : D.CoefficientDatum` supplies the distinct prime l and the fixed
  algebraic closure of Q_l. Neither a prime nor a characteristic is specialized.
- `X Y Z : Scheme.{u}` with `Over (Spec (.of D.k))` and
  `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` on their structural maps
  are precisely separated finite-type k-schemes. Both arrows have `IsOver`,
  `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`; these last two properties
  are consequences of the geometric setting, retained as the existing API's
  inferred instances, rather than any properness or flatness restriction.
- `d e : ℕ`, `SmoothOfRelativeDimension d f` and
  `SmoothOfRelativeDimension e g` express smoothness and pure relative
  dimensions including zero. Mathlib's `smoothOfRelativeDimension_comp` supplies
  the instance for `(f ≫ g)` of dimension `(d + e)`; it is not an extra hypothesis.
- `Field D C` is the existing finite coefficient subfield poset. The equations
  quantify over `E L` and `h : E ≤ L`, including equality. `RCat` is the actual
  raw rational constructible category `sfRationalConstructibleCategory`, with
  its existing integral objects and scalar-localized morphisms, not its Karoubi
  envelope or an arbitrary equivalent category.
- `H` is the recorded `rationalSource`: shifted Tate line first, then tensor
  with the actual completed derived pullback. This is the existing canonical
  coordinate presentation of Lh*(-)(d_h)[2d_h]. `G` and `O` are the specified
  exceptional right adjoint and its compact-support adjunction. `T` is the
  specified rational scalar extension, not the different PBC pullback.
- `Sf Sg Sc` and `If Ig Ic` are presentations of the simultaneous integral
  purity data for f, g and gf. They carry all the canonical finite reduction and
  coefficient equations of the supplied adic dependency; they are not arbitrary
  functors or purity maps. The dependency's existence theorem supplies them.
- `Family` bundles the already specified rational comparison-identification
  data. Its source localization is pinned by `SourceLocalizationNormalization`
  on every good representative. `gamma_localization` explicitly identifies
  gamma with `Q(I.gamma)` through the prescribed source and exceptional
  localization maps. `a_normalization` fixes a to `sourceScalar` at every
  rational object. `family_existsUnique` makes the subsequent selection unique;
  no mere existence of endpoint isomorphisms is used to manufacture data.
- The `b` used throughout is the existing field-passage exceptional comparison
  of `S.fields.rationalComparison`. `SingleCoherent` includes equality of its
  components with `coefficientTranspose`, the inverse compact-support
  comparison followed by the scalar-extended counit and the adjunction Hom
  bijection. Thus b is the mate specified in the node.
- `RationalTwistedPullback.compositor` is the canonical u, supplied by the new
  definition node below. The helper `u` merely unfolds H to give that same
  isomorphism in the existing H coordinates. It uses no gamma and no exceptional
  comparison.
- `q` is `isoWhiskerRight gamma_g Hf` followed by
  `isoWhiskerLeft Gg gamma_f`. Its K-component is Hf(gamma_g,K), then
  gamma_f,Gg(K), exactly the node's order.
- `A` is `isoWhiskerLeft Hg,E a_f` followed by
  `isoWhiskerRight a_g Hf,L`. Its K-component is a_f,Hg,E(K), then Hf,L(a_g,K).
  `beta` is the identical construction with G and b.
- The first component equation of `Result` is `T_X.map u_E ≫ A = a_gf ≫ u_L`.
  It has exactly source T_X H_gf,E(K) and target Hf,L Hg,L T_Z(K).
  The second is `T_X.map q_E ≫ beta = A ≫ q_L`, with source
  T_X Hf,E Hg,E(K) and target Gf,L Gg,L T_Z(K). These are the node's displayed
  equations, in Lean's left-to-right composition convention.
- Naturality in K is retained as natural isomorphisms, including the constructed
  compositor's named `component_naturality` theorem. The equations quantify over
  every rational K and therefore are natural-transformation equalities, not
  equalities only on integral arrows or a special family of test objects.
- `Coherent` spells out `UnitEquation`, `CompositionEquation` and
  `ShiftCompatibility` with the existing `unit`, `alpha`, `tShift` and
  `composeShift`. `SingleCoherent` retains these for a and b at each of f,g,gf,
  as well as the gamma shift and the mate normalization. `Result` also retains
  them for the actual horizontal families A and beta. Its last two conjuncts
  are the shift equations for the canonical u and q. Consequently the equality,
  successive-extension and shifted-input cases are present explicitly.

Dependency declarations used:

- `Sheaf.Paper.PurityFiniteSetting`: `FiniteFieldDatum`, `CoefficientDatum`.
- Mathlib `AlgebraicGeometry.Morphisms.Smooth`: `SmoothOfRelativeDimension`,
  `smoothOfRelativeDimension_comp`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `rationalDerivedPullback`,
  `rationalDerivedTensor`, their unique normalized object clauses,
  `constructibleIntegralPullback`, `constructibleIntegralTensor`.
- `Sheaf.Paper.SfRationalizationKaroubi`: the raw
  `sfRationalConstructibleCategory`, localization functor and its shift.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`: the existing integral
  and rational Tate coefficients and twists.
- `Sheaf.Paper.PuritySourceTransports`: `rationalSource`, `sourceScalar`.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`: `System`,
  `rationalization`, the specified adjunctions and field-passage comparisons.
- `Sheaf.Paper.PbcScalarExtension`: `sfRationalScalarExtension`,
  `sfRationalScalarComp`, `sfRationalScalarUnit`.
- `Sheaf.Paper.OrientationIntegralCoefficientTwists`:
  `sfOrientationIntegralComplex`, `sfOrientationIntegralDerivedProduct`,
  `sfOrientationIntegralDerivedPull`; these are fixed by pure root tensors and
  the actual operation augmentation, including exponent zero.
- `Sheaf.Paper.DerivedPullbackTensorIso`:
  `pullbackTensorRationalComposition`, `pullbackTensorRationalAssociator`,
  `canonicalRationalPullbackTensor`.
- `Sheaf.Paper.AdicPurityScalarNaturality` publicly exports the landed
  `WeilConjectures.AdicPurityScalarNaturality.Data` and existence theorem.
- `Sheaf.Paper.RationalScalarComparisonData` supplies the landed
  `WeilConjectures.RationalScalarComparisonIdentification` definitions:
  `SourceLocalizationNormalization`, `Q,H,G,T,b`, scalar associators/unitors,
  localization shifts and `coefficientTranspose`. The item cites its definition
  node `def-pur-rational-scalar-comparison-data`, not the theorem node whose
  conclusion is only relevant to the postponed proof.

Edge cases checked before drafting and again against the final signatures:
E=L is included by non-strict `≤` and has the actual tensor-unit equations;
a tower E≤L≤M has its actual scalar associators, with no strict-inclusion
assumption; d=0, e=0 and both zero use the root-line unit product; identity arrows
are allowed; empty schemes and zero K are not excluded; no nonzero-object,
connectedness, chosen root generator, unramified-coefficient or stable-lattice
hypothesis occurs. Arbitrary integral shifts of K occur in `ShiftCompatibility`.
The product uses one-term degrees -2d and -2e, hence retains the canonical even
Koszul sign, including swapping from the finite construction's right-line order
to this existing left-line source presentation. All universes and variables are
explicit; no additional universe equality is imposed.

Searches actually run with the prescribed msearch wrapper:

- LeanFinder: `Scalar extension compatibility of smooth purity and composition
  of twisted pullbacks`; only generic scheme/module pullback results, no exact item.
- Loogle: `NatTrans.naturality, isoWhiskerLeft, isoWhiskerRight`; 0 hits
  (unknown `NatTrans.naturality` in that service), not an exact match.
- LeanSearch: `Canonical compositor for rational Tate twisted derived pullbacks`;
  8 generic ordinary pullback-compositor hits, no rational Tate compositor.
- Mathlib grep, CategoryTheory: `purity.*scalar|scalar.*purity|twisted.*pullback`;
  0 hits. A second grep `twisted.*composit|composit.*twisted` also returned 0.
- `rg` in the named upstream WeilConjectures and Sheaf trees, by item id,
  purity/scalar, twist/pullback/composition and tensor shifts; it found the
  recorded scalar data and finite composition construction, but no exact item
  or rational canonical twisted compositor. The finite source compositor has
  finite coefficient-ring categories and cannot supply the rational map.
- DAG exact-id search for the new definition: no hit;
  `blueprint_refs.py search 'twisted pullback'`: 0 blueprint nodes;
  `blueprint_refs.py ancestor` identified
  `prop-pur-rational-purity-trace-coherence` as the prescribed ancestor.

## New nodes

`def-pur-rational-twisted-pullback-compositor` supplies the missing rational u.
Its module `Sheaf.Paper.RationalTwistedPullbackCompositor` identifies the existing
shifted rational Tate line with the localization of the existing one-term
integral line model, using the canonical localization shift and single-functor
shift isomorphisms. `product` and `pull` localize the recorded root-normalized
integral multiplication and pullback. The component of u splits B_(d+e) into
Bd tensor Be, applies pullback composition, then tensor associativity, inverse
line pullback in the e-block and inverse tensor pullback. The only postponed
proof is the named naturality theorem. All map data is constructed independently
of purity. The source is the current composition-compatibility paragraph and
its referenced ordered Tate splitting; the three search kinds and local
DAG/project searches are recorded verbatim in the new node. Existing ordinary,
finite-coefficient and untwisted maps do not supply this rational twisted map.

## Repair of returned delivery

The returned immutable head was bda5388bf0fb. The repair follows both points:

- H13/H4: deleted `AdicPurityScalarInterface.lean` and
  `RationalScalarComparisonInterface.lean`, including the copied `source_closed`
  theorem. Removed the sandbox overrides for
  `lem-pur-adic-purity-scalar-naturality` and
  `lem-pur-rational-scalar-comparison-identification`; both landed dependency
  records remain unchanged. The item imports the landed
  `RationalScalarComparisonData` and `AdicPurityScalarNaturality` modules and
  uses their original namespaces. No duplicate interfaces remain.
- H2: replaced the added statement dependency on
  `lem-pur-rational-scalar-comparison-identification` with the landed definition
  node `def-pur-rational-scalar-comparison-data`. Only its definitions occur in
  the item statement; the identification conclusion is not a hypothesis.

The reviewed compositor and all pasting Result clauses are unchanged. The
item's natural-language statement and proof are unchanged. There is no
statement correction and no replacement dependency module in this repair.
The prior import-failure workaround is withdrawn; it is not a justification
for retaining copies of the landed definitions.

## Second reading by NQ

This is a second pass by the dispatcher-assigned worker, not a claim that a
second agent reviewed it. The human brief forbids starting agents and assigns
the independent delivery review to the maintainer.

With the node and modules open, I checked each hypothesis and each clause using
the correspondence above. In particular I checked the two different endpoints,
the order of gamma_f/gamma_g in q, the order of a_f/a_g and b_f/b_g, and the
exceptional comparison's inverse-compact-support-then-counit direction. The
source-shift choice is normalized through the same source localization as gamma,
so choosing a different shift or an unrelated purity isomorphism cannot satisfy
the package. The new u uses the actual shifted integral root-line maps; it is
not defined via either side of the desired scalar equation. The second pass
found that the last clause should explicitly retain the single-map a,b laws as
well as the horizontal laws; `SingleCoherent` and its three Result conjuncts
were added. No hypothesis or clause of the DAG item was changed.

The repair pass additionally checked that every formerly copied reference now
resolves to the landed namespace, that only the two owning modules remain in
the sandbox, and that neither landed dependency node is overridden.

## Validation

The repaired two-module scompile.py check succeeds with no errors or unexpected
warnings. Every delivered file was checked separately in dependency order.
Library timings: RationalTwistedPullbackCompositor 14.2 seconds;
IteratedPurityScalarPasting 31.2 seconds. Sandbox checks take 18.2 and 28.5
seconds respectively. All delivered files meet the 60-second limit.

Earlier attempts stopped in a read-only overlay dependency before checking the
item; that tool/library mismatch no longer prevents compilation. The successful
check uses the landed AdicPurityScalarNaturality and RationalScalarComparisonData
namespaces. Neither duplicate interface nor dependency-record override was
restored to obtain this result.

The retained sandbox has exactly the two owning modules and two node files.
Against the current read-only item, only lean and stmt_deps differ. The requested
H13/H4 and H2 repairs are complete. The canonical compositor and all reviewed
pasting clauses retain their definitions and order.

Prescribed deliver2.py --no-push: OK. Dry-run commit 8176b27a8df passes
the server preflight and all per-file compile checks; nothing was pushed by
the dry run.

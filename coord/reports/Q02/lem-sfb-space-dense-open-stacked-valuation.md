## Worker report

The delivery states `AlgebraicGeometry.AlgebraicSpace.exists_denseOpen_stackedValuation`
in `Sheaf.AlgebraicGeometry.AlgebraicSpaceDenseOpenStackedValuation`. Its only theorem
proof is `sorry`. Its complete source-based proof plan is in the theorem docstring.
The helper `stackedValuationSpec` has real data: it is `Scheme.Spec` composed with
`(Over.equivalenceOfIsTerminal specULiftZIsTerminal).inverse`. It only packages the
canonical map from each scheme spectrum to Spec Z, including its functorial maps.
It neither chooses an algebraic space nor postpones any construction.

The input is the independently reviewed stage-1 split currently recorded in the shared
repository. The inherited BLOCKED ending concerned an unchanged stage-1 delivery;
there was no earlier Lean module or report in the sandbox. The stage-2 handoff in
`coord/brief-stage2.md` section 0 explicitly permits this assignment. The queue lists
this item in stage 2. No repair note exists for the item. Nothing in the accepted split
or its source statement is corrected.

### Hypotheses and objects

- Absolute base and sizes: `H X V : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))` uses
  the recorded fppf-sheaf algebraic-space category over Spec Z in the test-scheme
  universe `u`. The rings, fields, and existential valuation ring all lie in `Type u`.
  `ULift` places the integer ring in this same universe without restricting
  characteristic or the test rings. All variables and the universe are explicitly
  bound; `set_option autoImplicit false` checks this.
- Arbitrary morphism `p : H ⟶ X`: no property is assumed of it.
- Open immersion `h : V ⟶ H`: `hh` is the existing `IsRepresentableWith` predicate
  applied to Mathlib `IsOpenImmersion f.left`. Thus every scheme test is an actual
  representing pullback square whose projection is an open immersion of schemes.
- Quasi-compactness: `hqc : MapIsQuasiCompact h.hom.hom` is exactly compactness of
  the point space of each pullback to an affine scheme. This reuses the landed
  definition in `ProperCurveModuli.lean`, not a stronger representable-all-tests
  predicate. Its owning node `def-sfb-proper-curve-moduli` is the only added
  statement dependency, as permitted for already landed definitions. No field of
  that dependency node changes, and no new definition node is introduced.
- Dense image: `hd : Dense (pointImage h.hom.hom)` uses precisely the recorded
  field-valued point classes, their image, and the atlas topology.
- Valuation ring A: `[CommRing A] [IsDomain A] [ValuationRing A]` is the dependency's
  Mathlib valuation-ring class, including the domain condition.
- Fraction field K: `[Field K] [Algebra A K] [IsFractionRing A K]` allows any chosen
  fraction-field model, not only Mathlib's particular quotient construction.
- The maps `a` and `η` have domains the Yoneda presheaves of Spec A and Spec K over
  Spec Z, and codomains `X.obj.obj` and `H.obj.obj`. A map from a represented scheme
  to an algebraic-space sheaf is exactly this natural transformation.
- The original valuative square is `hη`: `η ≫ p.hom.hom` equals the restriction of
  `a` along `Spec (algebraMap A K)`. The helper functor and `yoneda.map` retain the
  actual scheme morphism and the natural transformation, not just its point image.

### Every conclusion clause

Write D = `Localization.AtPrime q`, E = `C ⧸ q`, L = `FractionRing C`, and
F = `FractionRing (C ⧸ q)` in this explanation; these are explicit expressions
in the Lean signature, with no statement-local `let` binders.

- `∃ (C : Type u) (_ : CommRing C) (_ : IsDomain C) (_ : ValuationRing C)` supplies
  a valuation ring C, and `(q : Ideal C) (_ : q.IsPrime)` supplies its prime.
- E is literally the quotient C/q. `(_ : ValuationRing (C ⧸ q))` states that it is
  a valuation ring; its domain structure follows from primality of q.
- `(ι : A →+* C ⧸ q) (hι : Function.Injective ι) (_ : IsLocalHom ι)` is exactly an
  injective local extension of valuation rings. For local rings, Mathlib's
  unit-reflection definition of `IsLocalHom` is equivalent to contraction of the
  maximal ideal to the maximal ideal. Both rings are local by `ValuationRing`.
- D is literally localization at the prime complement. Its valuation-ring property
  is the existential `ValuationRing (Localization.AtPrime q)`.
- L is the canonical fraction field of C; the conclusion also states
  `IsFractionRing (Localization.AtPrime q) (FractionRing C)`, so it is the same
  fraction field for D, with Mathlib's canonical localization-to-fraction-field
  algebra structure. No independently chosen generic-point map is substituted.
- F is the canonical fraction field of E. The isomorphism
  `ρ : IsLocalRing.ResidueField D ≃+* F` identifies it with D's residue field.
  The equation preceding the morphisms requires the composite C → D → residue(D)
  → F to equal C → C/q → F. This normalizes ρ over C and makes it exactly the
  canonical residue identification, rather than an arbitrary field isomorphism.
- The induced embedding K → F is the explicit `IsFractionRing.lift (A := A)
  (K := K) (g := (algebraMap E F).comp ι)` applied to the composite of `hι` with
  `IsFractionRing.injective E F`. Its restriction on A is therefore A → E → F;
  it is an injective field homomorphism. No arbitrary map is existentially chosen.
- Existential `b`, `α`, and `v` are the maps from Spec C to X, Spec D to H, and
  Spec L to V, respectively; `v` renders the node's map named u.
- `p α = b j_D` is the first equality following these maps, with j_D constructed
  from `algebraMap C D`.
- `α|Spec L = h u` is the second equality, with the generic restriction constructed
  from `algebraMap D L`.
- `α s_F = η Spec(K → F)` is the third equality. The source of s_F is Spec F and
  its ring map is `ρ.toRingHom.comp (IsLocalRing.residue D)`. The right side uses
  the canonical fraction-field lift described above.
- `b i_E = a Spec(A → E)` is the fourth equality, using `Ideal.Quotient.mk q`
  and the very same injective local map `ι`.
- No separatedness, finite-type, quasi-compactness of p, or valuation-lifting
  assumption is introduced. All four equalities are equalities of maps of
  presheaves, hence of the displayed morphisms of algebraic spaces.

### Dependencies and source reading

Read the entire target node, its statement dependencies and their records, then the
full relevant signatures and docstrings in their recorded source modules:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map`. Schemes and affine spectra use these actual constructions.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `IsRepresentable`, `IsEtale`,
  `IsSurjective`, and `IsAlgebraicSpace`. The last predicate supplies the fppf
  sheaf, representable diagonal, and etale surjective scheme atlas.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, and
  `etale_fibreProduct_isScheme`; these are the recorded fibre-product interfaces.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointImage` and
  `pointTopologicalSpace`, on the `Point` and `PointRepresentative` definitions of
  `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses`.
- `Mathlib.RingTheory.Valuation.ValuationRing`: `ValuationRing`,
  `ValuationRing.TFAE`, and the local-ring instance. This dependency is a Mathlib
  leaf without a Lean record and needs no repair.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
  `IsRepresentableWith` applies this scheme property to algebraic-space tests;
  it is not a duplicate private definition.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `MapIsQuasiCompact`, read with its
  affine-test definition and source docstring as the added landed dependency.
- `Mathlib.AlgebraicGeometry.Limits`: `specULiftZIsTerminal` and the existing
  terminal-slice equivalence; `Mathlib.RingTheory.Localization.AtPrime.Basic`:
  the actual prime localization and its local/domain structures;
  `Mathlib.RingTheory.Localization.LocalizationLocalization`: the canonical
  fraction-field structure of the prime localization;
  `Mathlib.RingTheory.Localization.FractionRing`: `IsFractionRing.lift` and its
  injectivity/uniqueness properties; `Mathlib.RingTheory.LocalRing.ResidueField.Basic`:
  the actual residue field and residue quotient map.

The metatheoretic size-convention node has no corresponding Lean object; it is
rendered by the explicit universe. No dependency interface repair is necessary.

Opened `literature/stacks-project/spaces-morphisms.tex`, from
`lemma-refined-valuative-criterion-universally-closed` through the construction of C
and the subsequent localization identification. The node extracts the construction
before assumption (4); quasi-compactness of p is used later in the full criterion,
not in this configuration. Restricting h to an open immersion is already part of
this node's statement. The docstring follows every one of its eight proof steps.

All recorded proof-dependency modules are imported privately when already stated:
`AlgebraicSpacePointClasses` is also available publicly through the topology module;
`AlgebraicSpace` and `AlgebraicSpaceFibreProductsEtaleCovers` are public statement
imports; `FlatValuationLifting` and Mathlib's etale module are private proof imports;
the probe, extension, and composite valuation constructions are privately imported
from `WeilConjectures.Compactification.ValuativeCriterion`,
`WeilConjectures.Mathlib.RingTheory.Valuation.LocalSubring`, and
`WeilConjectures.Mathlib.RingTheory.Valuation.ValuationSubring`. The recorded
polynomial-flatness Mathlib match is available through the valuative-criterion
module's public polynomial/flat imports. The four currently unstated proof nodes
`lem-sfb-space-reduced-closed-support`,
`lem-sfb-space-reduced-map-closed-factorization`,
`lem-sfb-stack-chartwise-smooth-etale-calculus`, and
`lem-sfb-stack-schematic-image-qc` have neither Lean records nor upstream audits;
there is no module to import yet. They are not needed to type the statement.

### Edge cases

- Empty H admits no η from a field spectrum. Likewise, if V is empty, density
  forces H to be empty. These cases give no impossible existential obligation.
- For h the identity, take C = A and q = 0. Then D and L identify with K, E with
  A, and F with K; b = a and alpha is η. All four equalities reduce to the
  original square or identities. The chosen Mathlib models are transported along
  their canonical isomorphisms.
- When A is a field, its valuation-ring structure is still permitted; locality
  and the field extension do not force positive dimension.
- Both q = 0 and q maximal are permitted; no nonzero/properness condition beyond
  primality is imposed. Arbitrary-rank valuation rings are permitted.
- Nonreduced, nonseparated, non-quasi-compact, and non-finite-type p are retained.
  The source's reduction argument concerns the proof, not extra hypotheses.
- No independent smaller test-field universe makes density or any scheme-test
  condition vacuous. The open's quasi-compactness is tested on precisely the
  same test universe as the algebraic spaces.

### Searches

Performed the prescribed three searches via
`/home/ubuntu/weil-launcher-all/batch2/msearch.py Q02
lem-sfb-space-dense-open-stacked-valuation`:

- `leanfinder`: “A dense quasi compact open of an algebraic space gives stacked
  valuation rings extending any valuation diagram”. Eight hits, including
  `AlgebraicGeometry.ValuativeCriterion.existence`, `.eq`, `.Existence.eq`,
  `.Existence`, `ValuativeCommSq.valuationRing`, and `ValuativeCommSq.K`.
  These are scheme-only valuative criteria or components of a square, not this
  algebraic-space construction. Read the scheme declarations and the existing
  dense-source probe in `WeilConjectures.Compactification.ValuativeCriterion`.
- `loogle`: `AlgebraicGeometry.ValuativeCommSq, IsLocalHom, IsLocalization.AtPrime`.
  The combined query returned no hits. The local source declarations were read
  directly to select the actual local-ring and localization interfaces.
- `grep`: `stack.*valuation|valuation.*stack|AlgebraicSpace`, subdirectory
  `AlgebraicGeometry`. No Mathlib matches for this construction.

Direct `rg` searches in both `lean/WeilConjectures` and `lean/Sheaf` for
`stacked_valuation|stackedValuation|dense_open.*valuation` and the exact node id
found no existing statement. Searches for `Dense (pointImage ...)`,
`IsRepresentableWith`, `MapIsQuasiCompact`, `Localization.AtPrime`, and
`specULiftZIsTerminal` found the interfaces reused above. Checked the chosen new
fully qualified names in Mathlib and both project source trees: no clashes.
No new mathematical notion is introduced, so no new definition-node searches or
node fields are required. The spectrum helper only composes two existing functors.

### Validation

`scompile.py` compiled the module twice (sandbox declaration check and its actual
library module name) against the live published library with no errors or warnings.
An initial elaboration error inferred the source ring of `IsFractionRing.lift`
from its injectivity argument as E; explicitly specifying `A := A` and the composite
`g` fixed this without changing any mathematical objects or hypotheses.
`deliver2.py Q02 lem-sfb-space-dense-open-stacked-valuation --no-push`
then returned `OK (dry run)`: commit `7f30ec98086` passed server preflight and
compiled without warnings. The delivery uses the prescribed direct-worker push;
the maintainer supplies the independent review, as required by the current brief.

No STATEMENT-DISPUTED flag, node fault, dependency repair, or statement correction.

## Second reading by Q02

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

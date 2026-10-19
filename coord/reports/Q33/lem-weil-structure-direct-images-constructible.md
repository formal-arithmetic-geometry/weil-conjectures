## Worker report

This repairs the returned immutable head 8b900f1a3488. The saved packet's initial
`deliver2.py --no-push` passed mechanically (b013e68410), but the required semantic
self-check confirmed the returned H3/H4 and H6 defects were still present. They are
repaired here, rather than repushing that packet unchanged. The current shared node
was compared with the saved node: there are no differences outside `lean`.

The module `lean/Sheaf/Paper/DirectImagesConstructible.lean` states
`WeilConjectures.directImages_constructible`. All theorem proofs are `sorry`.
The helper `finiteFieldDatumPrimeUnit` is now a theorem with a source, blueprint tag,
and complete proof docstring; its former tactic proof and linter suppressions are gone.

Hypothesis correspondence:

- The global tuple p,a,q,k₀,k is `D : FiniteFieldDatum.{u}`. Its fields carry
  primality, a ≥ 1, q = p^a, the finite base field and its fixed algebraic closure.
- The coefficient prime and exclusion are `(l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)`.
- The chosen algebraic closure of Q_l is `(Ω : Type v) [Field Ω]
  [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]`.
- The finite subextension is `E₀ : Padic.FiniteCoefficientFields l Ω`.
  Its canonical small model is `Coefficient.{u} l Ω E₀`; the recorded coefficient
  definitions supply its valuation ring, uniformizer, and quotient
  `Padic.coefficientExtensionRing l (Coefficient.{u} l Ω E₀) n`.
- Positive exponent is `(n : ℕ) (hn : 1 ≤ n)`.
- The k-scheme is `(Y : Scheme.{u}) [Y.Over (Spec (CommRingCat.of D.k))]`.
  Its actual structure morphism is `Y ↘ Spec (CommRingCat.of D.k)` throughout.
- Finite type is the pair of `LocallyOfFiniteType` and `QuasiCompact` instances
  on that morphism. Separatedness is `IsSeparated` on the same morphism.
- `c : Compactification (Y ↘ Spec (CommRingCat.of D.k))` presents the
  compactification-independent compact-support construction at one arbitrary choice.
- The finite input is `Kₙ : proEtaleDerivedCategory Y (...)` with
  `hKₙ : intrinsicFiniteTorsionConstructible ... n hn Y Kₙ`.
- The integral input is `K : sfIntegralConstructibleCategory l (...) Y`.
  Its membership is stored in `K.property`, and `K.obj` is the ambient object.
- `L : SfIntegralDirectImage l (...) (Y ↘ Spec (CommRingCat.of D.k)) K.obj`
  ranges over all specified Roos derived limits of the ordinary finite-image tower.
  Its explicit `HasProduct` argument installs the published countable-product theorem locally
  in the instance argument and then uses `infer_instance`; the theorem is
  `integralOperationsDerivedCountableProducts`, imported from
  `Sheaf.Paper.IntegralOperationsWellDefined`; no additional product hypothesis is imposed.
  The tower terms are `sfDirectImageTerm`, namely finite-level direct image of
  derived reduction followed by scalar restriction; the transition and Roos data
  are precisely those of the recorded direct-image definition.

Conclusion correspondence, in the order of the eight conjuncts:

1. Finite ordinary image: `intrinsicFiniteTorsionConstructible ... (Spec ...)
   ((proEtaleConstantDerivedDirectImage a_Y A).obj Kₙ)`.
2. Finite compact-support image: the same intrinsic predicate on
   `(@AlgebraicGeometry.Scheme.sfIntrinsicCompactSupport ... c A _
   (Padic.finite_coefficientExtensionRing ... n hn)).obj Kₙ`.
3. Integral ordinary image: `sfIntegralConstructible ... (Spec ...) L.obj`.
   This is now the required derived limit, replacing the rejected use of the
   ordinary completed-coefficient derived pushforward.
4. Integral compact-support image: `sfIntegralConstructible ... (Spec ...)
   (sfIntegralCompactSupportValue ... D.k (finiteFieldDatumPrimeUnit D l hl) c K).obj`.
   This clause is retained; the helper supplies only the already implied invertibility.
5. Rational ordinary image: `∃ M : sfRationalConstructibleCategory ... (Spec ...),
   M.obj.obj = L.obj`. The equality identifies the localized object's integral
   representative with exactly the ordinary derived-limit output.
6. Rational compact-support image: an object in the same rational category with
   `M.obj.obj` equal to the integral compact-support output of clause 4.
7. Algebraically closed ordinary image: `∃ M :
   generalAlgebraicallyClosedConstructibleCategory l Ω (Spec ...),
   M.stage = E₀ ∧ HEq M.obj.obj L.obj`. This retains the representative stage
   and identifies its rational object's underlying integral object with the limit.
8. Algebraically closed compact-support image: the same stage equality, with
   `HEq M.obj.obj` to the integral compact-support output of clause 4.

The rational categories have unchanged objects, so arbitrary rational inputs are
covered by their integral representatives. Arbitrary common-stage inputs are covered
because E₀ is arbitrary. The final 'in particular' follows from these category
memberships: the four coefficient-point functors' domains are precisely these
categories. The statement does not assert a new equivalence of fibre functors.

Dependency declarations actually used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible`.
- `Sheaf.Paper.SfIntegralConstructible`: `WeilConjectures.sfIntegralConstructible`
  and `WeilConjectures.sfIntegralConstructibleCategory`.
- `Sheaf.Paper.SfRationalizationKaroubi`:
  `WeilConjectures.sfRationalConstructibleCategory` (the raw scalar localization).
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `WeilConjectures.generalAlgebraicallyClosedConstructibleCategory` and its pair
  fields `stage` and `obj`; the imported coefficient model is
  `AlgebraicallyClosedCoefficients.Coefficient`.
- `Sheaf.Paper.SfDerivedDirectImage`: `WeilConjectures.SfIntegralDirectImage`,
  its `obj` field and the recorded finite-image tower; finite ordinary image uses
  `AlgebraicGeometry.Scheme.proEtaleConstantDerivedDirectImage` through this import.
- `Sheaf.Paper.IntegralOperationsWellDefined`:
  `WeilConjectures.integralOperationsDerivedCountableProducts`, used by instance
  synthesis to supply the tower's derived-category product.
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`:
  `AlgebraicGeometry.Scheme.sfIntrinsicCompactSupport`.
- `Sheaf.Paper.IntegralRationalQbarCompactSupport`:
  `WeilConjectures.sfIntegralCompactSupportValue`.
- Scheme properties use Mathlib's `Scheme.Over`, `LocallyOfFiniteType`,
  `QuasiCompact`, and `IsSeparated`, as the convention dependency specifies.

H4/H9 cleanup: removed direct imports of `ProEtaleConstructibleOrigin` and
`FiniteCoefficientPoint`, which contribute no term to the signature. Removed the
arithmetic import used only by the former prime-unit proof. No use of
`sfRationalCompactSupportValue`, `sfQbarCompactSupportValue`, or
`constructible_proEtale_origin` is claimed: the rational/common-stage membership
clauses are stated using the actual integral output and the recorded category
constructions. Origin and coefficient-point results are cited only in the
natural-language proof, not claimed as declarations used in the statement.

Edge cases: n = 1 is admitted; n = 0 is excluded by the source's hn. Empty Y and
zero objects are admitted; there is no nonemptiness or dimension hypothesis.
The characteristic case l = p is excluded exactly by hl. All chosen finite
subextensions E₀ and algebraic closures Ω are quantified. The site and coefficient
universe u and the independent closure universe v are explicit. No universe
equality or arbitrary replacement map is assumed. Every choice of the Roos-limit
presentation L is covered, with its product supplied by the published theorem.

Searches retained from the saved packet (`searches.jsonl`):

- `msearch.py ... leanfinder "direct images to the point of bounded constructible
  complexes remain bounded constructible"`: eight generic constructible-image
  hits, none stating this theorem.
- `msearch.py ... loogle "proEtaleConstantDerivedDirectImage,
  sfCompletedDerivedDirectImage, sfIntegralCompactSupportValue"`: no hits
  (Loogle does not know the first project-specific identifier).
- `msearch.py ... grep "constructible.*direct image" AlgebraicGeometry`: no hits.
- The saved `rg` searches in the source project and shared `lean/Sheaf` found
  no pre-existing declaration of this node. Repair-time `rg` located and the
  source reading verified `SfIntegralDirectImage`,
  `integralOperationsDerivedCountableProducts`, and
  `sfIntegralDirectImage_constructible`; the latter explicitly concerns the
  tower-defined image used in this repair.

No node statement correction is needed: this repairs its Lean rendering. No new
nodes or dependency modules are introduced. `lean.statement` is extracted verbatim
from the final theorem signature; only the node's `lean` record changes.

## Second reading by Q33

I reopened the node and the module and matched each hypothesis individually:
D supplies the full finite-field datum; l/Fact/hl the distinct prime; Ω and its
three instances the algebraic closure; E₀ the finite subextension; n/hn the positive
quotient exponent; Y/Over its structure morphism; LocallyOfFiniteType/QuasiCompact
its finite type; IsSeparated its separatedness; c the arbitrary compactification;
Kₙ/hKₙ finite bounded constructibility; and K the integral full-subcategory input.
I checked the new L binder against the actual `SfIntegralDirectImage` signature:
its obj, projection, boundary and roos fields encode the derived limit specified by
the node, and the imported product instance supplies its sole class parameter.
This replaces the old completed-pushforward rendering without changing the node.

I then read every output against the node: (1) ordinary finite image uses the
actual finite derived direct-image functor and intrinsic bounded constructibility;
(2) compact finite image uses the chosen compactification functor and the explicit
finite quotient-ring instance; (3) ordinary integral constructibility is now on
L.obj; (4) compact integral constructibility stays on sfIntegralCompactSupportValue;
(5) rational ordinary output now has ambient object L.obj; (6) rational compact
output retains the clause-4 object; (7) common-stage ordinary output now has stage
E₀ and ambient object L.obj; (8) common-stage compact output retains stage E₀ and
the clause-4 object. Thus all four coefficient levels and both operations occur.
The coefficient-point domain consequence is exactly the obtained membership and
requires no further output clause or new fibre equivalence.

The rereading found and fixed all returned points: H3/H4 in clauses 3/5/7,
H6 in the prime-unit helper, H11 by this detailed hypothesis/output comparison,
and H4/H9 by removing the unused imports and inaccurate usage claims. Both named
theorems now have `sorry` and source/proof docstrings. No mathematical statement
or source hypothesis was altered.

Compilation repair: product-instance inference before elaborating the Roos-limit
argument caused a typeclass timeout. The final signature uses
`@SfIntegralDirectImage` and `@SfIntegralDirectImage.obj`, with coefficient instances
resolved by explicit `inferInstance` arguments and the product proof supplied
explicitly each time. That proof installs
`integralOperationsDerivedCountableProducts l (Coefficient.{u} l Ω E₀) (Spec ...)`
as the precise `HasCountableProducts` instance, then obtains the tower product by
`infer_instance`. This follows the published `coefCompactSupportHasProduct`
construction, uses no additional mathematical assumption or new declaration, and
introduces no universe restriction. The explicit projection is exactly L.obj;
the correspondence above uses that shorter notation for readability. All inline
proofs here supply existing typeclass instances; both mathematical theorems have
only `sorry` proofs. The scratch signature-check module is removed from the packet.

Validation: `scompile.py` type-checked the repaired theorem at both its sandbox and
library paths. Its sole diagnostic was a 105-character line in the common-stage
ordinary clause; that line is now wrapped and the verbatim node signature refreshed.
The final delivery dry run recompiles this final packet and checks its records.


### Maintainer second-reader import repair (2026-10-18)

The report's earlier H4/H9 cleanup incorrectly removed proof-only imports.
The standing brief §3 requires the modules of stated proof dependencies even when
the postponed proof uses no Lean terms. Restore ordinary (non-public) imports of
`Sheaf.Paper.ProEtaleConstructibleOrigin` and `Sheaf.Paper.FiniteCoefficientPoint`.
Also import the available `Sheaf.Paper.SfIntegralDirectImageConstructible` used by
proof step 4. No declaration, theorem signature, node record, mathematical
statement, or universe changes. The original module and this complete replacement
are separately checked through the prescribed scompile.py wrapper.

Maintainer validation: original snapshot: sandbox 9.3 s, library 7.5 s; fixed
module: sandbox 6.6 s, library 7.3 s. Both scompile.py invocations returned
exit 0 with no diagnostics. No build, delivery, merge or clone edit was run.

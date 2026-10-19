## Worker report

This repairs return L on immutable head f3a2d5aff73a: the preliminary compilation
of PurityAffineChartBounds imported both the legacy and reorganized pro-etale
UpperLowerStar.Defs, which declare the same notation and functors. This is a source
repair, not an unchanged re-push. Both delivered modules now use the published
legacy derived interface and fixed-scalar module sheaves throughout. They have no
import of FiniteCoefficient.UpperLowerStar.Defs, intrinsic module operations or the
intrinsic constructibility/Tor modules. No node statement, dependency list or proof
plan is changed. Two theorem proofs remain wholly `by sorry`; every definition has
real data.

I read the current dependency records, the published FiniteTypeExceptionalInverseImage
source through scompile.py --source, the full upstream Derived.Constructible,
Derived.TorAmplitude and Derived.UpperShriek definitions and their docstrings, and the
blueprint theorem, corollary and unit. The DAG already incorporates the reviewed
bounded-class and empty-case corrections; these govern the statement, rather than
the older blueprint wording that identifies all etale-origin objects with finite Tor
objects. No further statement correction or STATEMENT-DISPUTED issue is needed.

Hypothesis and object correspondence for thm-sf-preservation-class:

- `F : WeilConjectures.FiniteFieldDatum.{u}` supplies p, a0, q, k0 and the chosen
  algebraic closure k=`F.k`. The coefficient prime is `l`, `[Fact l.Prime]` and
  `_hl : l ≠ F.p`. The finite extension is `E`, `[Field E]`, `[Algebra (Padic l) E]`
  and `[FiniteDimensional (Padic l) E]`. The positive exponent is `n` with
  `hn : 1 ≤ n`; the actual quotient is `Padic.coefficientExtensionRing l E n`.
- Coefficients are `ModuleCat.{u+1} (ULift.{u+1,u} A_{E,n})`. The ULift changes only
  size. These are sheaves of modules over the constant coefficient ring, in the
  published fixed-scalar presentation. The small site is still `ProEt.topology T`
  on `T.ProEt`, with object universe u+1 and morphism universe u. No site universe
  equality, regularity of A, or restriction to prime coefficients is imposed.
- `X Y : Scheme.{u}` and their `Over (Spec (.of F.k))` structures are the k-schemes.
  `LocallyOfFiniteType` plus `QuasiCompact` on both structural maps states finite
  type; `IsSeparated` on Y's structural map is exactly the separated target clause.
- `f : X ⟶ Y`, `[f.IsOver (Spec (.of F.k))]`, `[LocallyOfFiniteType f]`,
  `[QuasiCompact f]` and `[IsSeparated f]` state the separated finite-type k-morphism.
- `c : Compactification f` is the chosen compactification. The finite-stage
  specialization `ProEtale.sfFiniteExceptionalInverseImage F.k l E n hn c` now calls
  the already published `finiteTypeExceptionalInverseImage`. It installs only the
  published finiteness proof and the compactifiability witness `⟨⟨c⟩⟩`. Its underlying
  functor is exactly `Rν_Y,* ⋙ f^× ⋙ D(ν_X^*)`. The ordinary etale adjoint is determined
  by its adjunction, and changing the chosen compactification gives its canonical
  isomorphism. No arbitrary coefficient equivalence, new exceptional construction,
  ambient pro-etale adjoint or extra bounded-below hypothesis is supplied.
- `C : SfAffineChartPresentation f` gives `Fin count` target opens, their affineness
  and cover, and `Fin (size i)` source opens with affineness, containment in the
  corresponding inverse image and cover of that inverse image. Its dimension,
  presentation, presentation_closed and presentation_over fields are precisely
  closed embeddings into affine d_U-space over the target open. The coordinate
  type `ULift.{u} (Fin (C.dimension i j))` has d_U elements.
- `C.maxDimension` is the finite supremum of all original chart dimensions, with
  empty supremum 0. It retains dimensions of empty charts. `sfDimension Y` reads
  `topologicalKrullDim Y` via `unbotD 0` and ENat.toNat. On finite-type k-schemes
  dimension is finite; for empty Y the result is 0.

Conclusion correspondence, clause by clause:

1. The first conjunct quantifies over every L in the actual derived category of
   module sheaves. `ProEtale.DerivedCategory.constructibleIn ... Y a b L` is exactly
   bounded constructibility and homology concentrated in [a,b]. Its output is the
   identical predicate on X at [a-2*C.maxDimension,b+2*sfDimension Y+1], evaluated
   on the specified exceptional image. In particular there is no Tor premise in
   this clause. At finite coefficients the published bounded-etale-origin predicate
   agrees with intrinsic bounded constructibility by lem-sf-proetale-constructible-origin;
   this equality is the reason the presentation change preserves the node's meaning.
2. The second conjunct takes `ProEtale.DerivedCategory.constructibleFiniteTor` and
   `ProEtale.DerivedCategory.torAmplitudeIn ... Y a b K`, and concludes the same Tor
   test on X in the displayed shifted interval. `torAmplitudeIn` tests the derived
   tensor with EVERY degree-zero module sheaf; it is not a test only on free modules
   or on one chosen resolution. The third conjunct gives constructibleFiniteTor
   membership of every such exceptional image independently of an amplitude witness.
   These are exactly the Tor bound and its separate “in particular” clause.
3. `c` and `C` precede `∀ n hn`; both endpoints depend only on the fixed charts and
   Y. Thus every positive finite coefficient stage has the same shifts. The theorem
   does not add a coefficient-change isomorphism.
4. The displayed shifts are c_f^-=-2D and c_f^+=2e+1. The first conjunct and finite-Tor
   membership are the constructible analogues of admissibility clauses (2) and (3).
   There is no ambient-adjoint/FullCD premise or conclusion. Only positive finite
   stages and bounded constructible inputs occur; no integral or field-coefficient
   assertion is made. Scope exclusions are documented rather than encoded as an
   unrelated negative proposition.

For the corollary dependency the same coefficient and geometric binders occur,
without an extra separatedness assumption on Y. `C.nonemptyCharts` really restricts
source indices to `{j // Nonempty (C.source i j)}` and reindexes with Fintype.equivFin.
All chart data are inherited. A point in any original covering member proves it
survives, so both cover obligations are filled by real data. The theorem accepts
arbitrary C, with no `_hC` premise. For nonempty X its assemblyDimension is the
maximum D0 of surviving charts and assemblyConstant is 2D0+2dim Y+1, exactly the
common value of c_U+1+2(D0-d_U) for c_U=2(d_U+dim Y). Both are 0 for empty X.
Its two conclusions are constructibleIn at [a-2D0,b-2D0+c] and constructibleFiniteTor
membership together with the same Tor interval. The main theorem uses D0≤D to widen
only the lower endpoint. Both docstrings retain complete stepwise DAG proof plans,
including empty-source vanishing and the open-complement assembly argument.

Dependency declarations used:

- Sheaf.Paper.FiniteFieldFiber: WeilConjectures.FiniteFieldDatum.
- Sheaf.NumberTheory.Padics.CoefficientExtensionFinite: Padic.finite_coefficientExtensionRing
  and its imported coefficientExtensionRing/integers/uniformizer constructions.
- Sheaf.Paper.FiniteTypeExceptionalInverseImage:
  AlgebraicGeometry.ProEtale.finiteTypeExceptionalInverseImage and its named
  finiteTypeHasBoundedBelowUpperShriek theorem. This module was checked against the
  current server source, rather than copied from an obsolete local record.
- WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriek:
  ProEtale.rightDerivedUpperShriek, whose three defining factors are the comparison
  direct image, ordinary etale exceptional functor and comparison inverse image.
- WeilConjectures.SixFunctors.ProEtale.Derived.Constructible:
  ProEtale.DerivedCategory.constructibleIn and DerivedCategoryConstructibleIn.
- WeilConjectures.SixFunctors.ProEtale.Derived.TorAmplitude:
  ProEtale.DerivedCategory.constructibleFiniteTor and torAmplitudeIn. This agrees with
  the finite-stage mathematical notion of def-weil-finite-tor-amplitude under the
  canonical coefficient-presentation comparison. The snapshot record itself names
  the intrinsic finiteTorConstructible, not this fixed-scalar declaration; see the
  independent maintainer clarification below.
- WeilConjectures.Compactification.Refinement: Compactification and its existing
  refinement category. Mathlib's LocallyOfFiniteType, QuasiCompact, IsSeparated,
  IsClosedImmersion, IsAffineOpen, AffineSpace and topologicalKrullDim supply the
  geometric notions; Fintype.equivFin and Finset.univ.sup supply the finite indexing.

Imports deliberately omitted to avoid the returned duplication: the intrinsic
ConstructibleIntervals/FiniteTorAmplitude modules; ProEtaleIntrinsicExtensionByZero;
AmbientExceptionalRightAdjoint (its datum is expressly excluded); and the old intrinsic
ProEtaleConstructibleOrigin module. The last is still cited mathematically for the
finite-coefficient equivalence, as is the proof-only OpenComplementCondition interface.
Their proof-import closures would reintroduce the incompatible reorganized modules.
The published finite-stage interfaces supply the notions actually used by the signature.
PurityFiniteSetting is replaced by the smaller FiniteFieldFiber import, which is the
only datum used from it here. The proof plan still records its purity conventions.

Edge cases: empty X; empty Y, forcing X empty; count=0; size i=0 over an empty inverse
image; empty target opens; arbitrarily large dimensions assigned to empty source
charts; duplicate charts; dimension-zero charts; zero complexes and zero module
sheaves; n=1 and every n>1; negative endpoints and a=b. For nonempty X at least one
surviving chart exists, and D0≤D. For empty X all module sheaves are zero by the empty
cover, so all displayed cohomology and tensor bounds hold, including D=c=0 in the
corollary. No nonemptiness premise is added. All universes and variables are bound;
autoImplicit is false. No local notation, private definition or local instance is used.

Reuse searches (the previous packet's searches were also read):

- msearch LeanFinder, “Exceptional inverse image preserves constructible cohomological
  intervals and finite Tor amplitude with bounds from affine chart embedding dimensions”:
  eight generic affine-cover/limit and derived-t-structure hits, no exact numerical theorem.
- msearch Loogle on the full upstream constructibleIn and constructibleFiniteTor names:
  no indexed match (unknown upstream identifier); the actual source definitions above
  were opened and reused instead.
- Direct rg for sf_preservation_class, sf_purity_affine_chart_bounds,
  SfAffineChartPresentation and sfFiniteExceptionalInverseImage in Mathlib,
  upstream WeilConjectures and project lean/Sheaf: no duplicate declarations.
  The upstream node-id search found only a documentation reference in Etale/Derived/
  Stability/Matrix. The source search for constructibleIn, constructibleFiniteTor,
  torAmplitudeIn and finiteTypeExceptionalInverseImage found the reused interfaces.
- Earlier LeanSearch attempts were unavailable (Internal Server Error), not no-match
  evidence. Earlier Loogle upperShriek searches found no exact match. The ordinary
  etale numerical theorem existentially chooses a bound on finite-Tor inputs and
  does not state this prescribed-chart, separate cohomological assertion.

## Dependency modules

`cor-pur-general-admissibility-datum`: this previously unstated dependency is supplied
with its actual chart data and both numerical conclusions. It now uses the same
published fixed-scalar coefficient presentation as the exceptional functor and Tor
predicates. The empty-chart restriction, finite reindexing, cover proof and numerical
constants are retained from the earlier repaired packet. Its two clause signatures
are changed only in coefficient presentation and the reused interval/Tor notation.
Its owning module also includes sfFiniteExceptionalInverseImage, the positive-stage
specialization of the existing published exceptional functor. It only installs the
finite coefficient and compactifiability witnesses from hn and c; there is no new
exceptional construction or postponed helper theorem. This helper is listed in the
corollary lean.declarations with that owning node's source/blueprint docstring. The
already published def-weil-exceptional-inverse-image record is reused UNCHANGED,
rather than replaced by a second record of the same construction.

`def-weil-constructible-intervals`: section 1(B) lean-only repair to the exact existing
upstream constructibleIn and DerivedCategoryConstructibleIn. The intrinsic ringed-module
record imports the conflicting reorganized modules, so cannot be combined with the
published exceptional interface. The reused predicate is bounded constructibility
intersect homologyConcentratedIn, with no added Tor condition. Its full subcategory
inherits all morphisms. The finite-stage origin equivalence identifies it with the
node's intrinsic reading; no claim is made about integral or field coefficients.
This dependency has existing:true and no new module. Its other fields are unchanged.

All delivered node copies differ from the base only in lean. No new nodes are added.
The worker compile and mandatory no-push dry run are run after this repair; their
outputs are kept in scratchpad/return-generic-final-compile.log and
scratchpad/return-generic-dry-run.log. A fresh second reader must review the revised
coefficient presentation and interval dependency before delivering.

The final delivery has two modules and reuses the published exceptional dependency
record unchanged. The coefficient specialization is a helper of the chart assembly
module, not a second exceptional construction or a dependency override. Each Lean
process retains the 60-second limit; displayed wrapper wall times can include waiting
for a compiler slot.

Final two-module compilation passed without errors or warnings, including preliminary
Sheaf/Paper/PurityAffineChartBounds.lean, the exact compilation step named in return L.
The mandatory no-push packaging check is rerun on these final files and the existing
interval-declaration probe.

## Second reading by ND

I did not write these statements. I read the item and both delivered dependency
records, the two delivered Lean modules, all statement-dependency records, the
archived blueprint theorem and corollary at orders 2085 and 2079, and the actual
signatures and bodies of the constructions used below. The source archive is
`/home/ubuntu/weil-launcher-nt/literature/blueprint/master/blueprint/`; the relative
literature paths are not populated in the shared checkout. The original blueprint's
ambient-adjoint and empty-maximum wording has already been corrected in the base
DAG; this packet makes no further statement correction. I assessed the current
node, including its bounded-class and empty-case conventions, rather than reverting
it to the archived scope errors. No target or unit statement is changed.

My object/hypothesis/conclusion list and its Lean correspondence:

1. Global datum p,a0,q,k0,k with k an algebraic closure of the finite field:
   `F : WeilConjectures.FiniteFieldDatum.{u}`. I opened FiniteFieldFiber: its fields
   include primality, positive exponent, q=p^a, the finite field's cardinality,
   and the algebraic-closure algebra and instance. Verdict: same datum. In particular
   p is the characteristic forced by the finite-field cardinality; `_hl` is the
   requested different-characteristic condition, not an unrelated characteristic.
2. Prime l different from p, finite extension E/Q_l, actual positive quotient:
   `(l : ℕ) [Fact l.Prime] (_hl : l ≠ F.p)`, `(E : Type u) [Field E]
   [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`, and `n, hn : 1 ≤ n`.
   I opened CoefficientExtension and CoefficientExtensionFinite: the quotient is
   the recorded integer subring modulo `(Ideal.span {uniformizer})^n`; its positive
   level finiteness is the named dependency theorem. Verdict: no regularity,
   field-coefficient or prime-coefficient assumption has been introduced.
3. X finite type over k; Y separated finite type over k: the `Over (Spec (.of F.k))`
   structures and `LocallyOfFiniteType` plus `QuasiCompact` on both structural maps,
   with `IsSeparated` only on Y's structural map. I opened the Mathlib classes:
   quasi-compactness concerns compact open inverse images; local finite type is
   affine-local finite generation; separatedness is the closed diagonal.
   Verdict: exact assumptions; separatedness of X over k is a consequence and is
   not an extra binder. The dependency corollary correctly omits separatedness of Y.
4. Separated finite-type k-morphism: `f`, `f.IsOver`, `LocallyOfFiniteType f`,
   `QuasiCompact f`, `IsSeparated f`. Verdict: every morphism hypothesis present;
   no smoothness, properness or nonemptiness premise.
5. Chosen compactification and the specified exceptional functor: `c : Compactification f`
   and `ProEtale.sfFiniteExceptionalInverseImage F.k l E n hn c`. I read the
   Compactification fields and the published finiteTypeExceptionalInverseImage body,
   then fetched current Derived.UpperShriek with `scompile.py --source`. The helper
   installs only the positive quotient's finite instance and `HasCompactification`
   from c, and calls the existing functor. The latter is definitionally
   `R(ν_*) ⋙ Etale.rightDerivedUpperShriek ⋙ D(ν^*)`. Its ordinary etale right adjoint
   is determined by its adjunction. Verdict: actual canonical comparison composite,
   not an arbitrary functor, ambient adjoint, or additional assumed adjoint interface.
   The chosen compact-support functor is the recorded lower-shriek construction;
   no unused independent compact-support functor must be quantified in this bound.
6. Finite affine chart family: `C : SfAffineChartPresentation f`. Its `count`, target,
   affine and cover fields encode the target cover; `size`, source, affine,
   containment and source_cover encode the covers of each inverse image. Its natural
   dimensions and closed presentations into `AffineSpace (ULift (Fin d)) V`, with
   `presentation_over`, encode exactly the presentations over V. I opened Mathlib
   AffineSpace: it is relative affine space with this coordinate index type.
   Verdict: the ULift has exactly d coordinates, including d=0; the commuting
   equation really fixes the projection to V, since V's inclusion is mono.
7. D=max d_U, empty maximum zero: `C.maxDimension` is `Finset.univ.sup` over the
   finite dependent pair of original chart indices. Verdict: includes all original
   charts, even empty charts with artificially large dimensions, as this node says.
8. e=dim Y, with e=0 for empty Y: `sfDimension Y` reads the actual Mathlib
   `topologicalKrullDim` via `unbotD 0` and `toNat`. I opened that dimension definition
   (chains of irreducible closed sets). Under the finite-type-over-field hypotheses
   the dimension is finite, so toNat does not truncate an allowed infinite case.
   Verdict: exact nonnegative dimension, including bottom for the empty scheme.
9. Clause 1, all integers a≤b and every bounded constructible L with cohomology in
   [a,b]: `∀ n hn a b _hab`, followed by the first conjunct's `∀ L` and
   `ProEtale.DerivedCategory.constructibleIn ... Y a b L`. The output has the same
   predicate on X with endpoints `a - 2 * (C.maxDimension : ℤ)` and
   `b + 2 * (sfDimension Y : ℤ) + 1`, on the specified exceptional image.
   Verdict: all clauses present; in particular there is no finite-Tor input condition.
10. Clause 2, K bounded constructible of finite Tor amplitude, with specified
    amplitude [a,b]: second conjunct's `constructibleFiniteTor` and `torAmplitudeIn`.
    Its output is torAmplitudeIn at exactly the same shifted endpoints as clause 1.
    The third conjunct separately asserts constructibleFiniteTor membership for
    every such K, without a chosen amplitude witness. Verdict: includes the full
    “in particular” assertion. Its repetition under `∀ a b _hab` causes no restriction:
    instantiate a=b=0 to obtain this independent membership assertion.
11. Clause 3, one chart family and one pair of shifts for every n≥1: c and C are
    bound before `∀ n hn`, and neither C.maxDimension nor sfDimension depends on n.
    Verdict: uniformity is asserted, with no coefficient-change isomorphism added.
12. Clause 4 and scope: the three conjuncts give precisely the two constructible
    preservation formulas with signed shifts -2D and 2e+1. There is no ambient datum
    binder and no claim of an unrestricted adjunction or FullCD. The positive finite
    quotient and bounded-constructibility predicates delimit the finite-stage scope.
    Verdict: the explanatory correspondence to admissibility and the exclusions are
    correctly documented, with no unrelated negative or tautological conjunct added.

I independently opened upstream Derived.Constructible at boundedConstructible,
constructibleIn and DerivedCategoryConstructibleIn, and Derived.TorAmplitude at
constructibleFiniteTor, finiteTorAmplitude and torAmplitudeIn. constructibleIn is
boundedConstructible intersect homologyConcentratedIn, without a Tor conjunct;
its category is the full subcategory with inherited arrows. constructibleFiniteTor
is boundedConstructible intersect finiteTorAmplitude. The underlying derived
Tor test quantifies over EVERY sheaf F in the coefficient category and tensors
with `(singleFunctor ... 0).obj F`; it is not merely a test on free coefficients.
The existential interval in finiteTorAmplitude need not explicitly require a≤b:
a reversed interval can only describe zero tensor tests, and can be widened to
[0,0], so it gives the same finite-Tor property as the node.

For the interval lean-only repair, I checked the dependency's complete finite-level
statement and the exact existing declarations, not just their names. I also opened
ProEtaleConstructibleOrigin, its canonical scalar/derived comparison and the
ConstructibleOriginComparison conclusion. At the actual finite quotients its
comparison identifies intrinsic bounded constructibility with the etale-origin
reading. Stacks proetale.tex, definition-constructible and lemma-compare-constructible
(Tag 09AK), assumes a Noetherian coefficient ring; the finite quotient is such a
ring. I also read more-algebra.tex, definition-tor-amplitude (under Tag 0651): its
all-module, degree-zero tensor test is the one reused here. No integral or field
identification is claimed by the finite-stage repair. No new definition node is
present, so H12 has no new-node field obligation. The repaired interval node changes
only lean, and its lean.note records both the incompatible import closure and the
precise equivalent finite-level interface.

I read the added corollary dependency against its node and source, including every
proof step. `nonemptyCharts` uses the exact subtype `{j // Nonempty (C.source i j)}`
and Fintype.equivFin, inherits all chart data, and constructs the source-cover witness
from the given point; no mathematical theorem is postulated to choose the charts.
`assemblyDimension` is the maximum of surviving dimensions for nonempty X, zero
otherwise. `assemblyConstant` is 2D0+2dimY+1 for nonempty X, zero otherwise, equal
to each summand of the node's maximum. The two corollary conclusions have exactly
[a-2D0,b-2D0+c], and the second contains both finite-Tor membership and its Tor bound.
This is a real dependency module for the genuine previously unstated corollary;
its lean.note explains the interface. The main theorem correctly widens D0≤D rather
than silently discarding empty charts from its own D.

Edge cases checked: empty X (including nonempty Y), empty Y (then X empty), count=0,
size i=0, empty target opens, empty source opens with arbitrary assigned dimensions,
duplicate opens, d_U=0, zero complexes and module sheaves, negative endpoints and
a=b, n=1 and n>1. n=0 and l=p are excluded by the node itself. Empty source sites
have the empty covering on every object, forcing module sheaves and their derived
objects to be zero, so both sets of empty-case constants are valid. The theorem
adds no Nonempty hypothesis. All universes are explicitly bound: Scheme.{u}, site
objects in u+1 and arrows in u, ModuleCat.{u+1}, and the standard ULift of the actual
quotient. No site object/morphism universe equality is imposed; finite field
extensions have representatives at the base universe and no isomorphism class is
excluded by this coefficient convention.

Independent reuse searches used different wording from the worker:

- msearch LeanFinder: “Extraordinary pullback sends bounded constructible torsion
  complexes to bounded constructible complexes with uniform cohomological bounds
  and finite Tor dimension”. Eight general derived t-structure hits, no exact theorem.
- msearch Loogle: `"torAmplitudeIn"`, zero indexed hits; I nevertheless read the actual
  upstream declarations as described above, rather than treating indexing as absence.
- rg on Mathlib, upstream WeilConjectures and project lean/Sheaf for extraordinary,
  exceptional bounds, upperShriek amplitude, the theorem names and chart structure.
  No duplicate prescribed-chart pro-etale numerical theorem or chart structure.
  The etale Stability/UpperShriek results existentially choose a shift, concern the
  etale site and combine constructibility with Tor amplitude; they do not replace
  the separate no-Tor cohomological assertion and prescribed bounds here.

No mathematical or signature mismatch was found in this repaired worker packet.
I changed only this report by appending the independent second reading; the correct
Lean statements and definitions were retained. Both theorem docstrings carry the
full stepwise current DAG proof, including empty-case vanishing and interval widening.
Definitions have real data; the only postponed proofs in this packet are the two
named matching DAG theorems. There are no private definitions, file-local notation
or instances, unbound variables, overlong lines, or extra assumptions hidden in a
binder. The proof-only intrinsic/ambient import omissions are explained in the
worker report: their closures bring in conflicting reorganized declarations; the
published canonical finite-stage operations are already imported.

Fresh `scompile.py ND thm-sf-preservation-class` on BOTH delivered modules passed
without errors or warnings, including preliminary, sandbox and library compilations.
I checked programmatically that both node lean.statement strings are verbatim equal
to their file signatures, and that all three delivered node copies change only lean.
The mandatory packaging dry run and final delivery follow this reading.


## Independent maintainer clarification

The immutable snapshot record of def-weil-finite-tor-amplitude names
WeilConjectures.finiteTorConstructible in Sheaf.Paper.FiniteTorAmplitude.
The delivered statements instead reuse the existing fixed-scalar
ProEtale.DerivedCategory.constructibleFiniteTor and torAmplitudeIn. The earlier
phrase “agrees with the current record” meant mathematical equivalence, not
identity of declarations or ambient categories.

For the actual positive finite quotients, sheaves of fixed-scalar modules are
canonically equivalent to modules over the constant ring sheaf. This is an exact
tensor equivalence: scalar actions extend from constant sections locally and glue
uniquely; conversely constant scalars act by restriction. It preserves degree-zero
sheaves, cohomology, and the derived tensor product, hence every module-sheaf Tor
test. The finite-stage constructible-origin comparison identifies the two bounded
constructibility predicates. Thus the alternative existing Tor interface expresses
exactly the finite-stage condition used here, without a free equivalence or new
definition. This clarification is also recorded in the item's lean.note. The
intrinsic dependency record, including its integral and field interfaces, is retained.

An independent reproduction on the two immutable Lean files through scompile.py
passed locally in the private side overlay: preliminary chart module 4.3 s; chart
sandbox 9.3 s; chart library 7.3 s; main sandbox 11.8 s; main library 37.7 s.
Exit status was zero, with no errors or warnings. No Lean source or theorem
signature was changed by this clarification.

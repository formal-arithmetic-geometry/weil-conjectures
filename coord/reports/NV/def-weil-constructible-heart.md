## Worker report

The module `Sheaf.Paper.ConstructibleHeart` defines the two constructible hearts as full subcategories of the specified rational and common-stage categories. It states the bounded standard-t-structure assertion, defines its truncations at every integer, and states both vanishing characterizations and abelianity. Definitions have actual data. The four postponed theorems have source references and complete proof plans. The choice of each standard t-structure is from an existence-and-uniqueness theorem specifying all its aisle functions; it does not choose an arbitrary structure from mere existence.

Hypothesis and clause correspondence:

- The finite-field datum is `D : FiniteFieldDatum`; its fields contain the paper's `p,a,q,k₀,k` and their relations. The prime is `l : ℕ` with `[Fact l.Prime]`, and `hl : l ≠ D.p` is retained in every coefficient category.
- `Padic l` is the recorded ℚ_l. The fixed closure is `Ω : Type v` with `[Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]`. Its universe is independent of the scheme universe.
- The paper's finite coefficient subfield is `E : AlgebraicallyClosedCoefficients.Index l Ω`, the actual finite intermediate-field index from the coefficient-category dependency. `AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E` is that dependency's specified small algebra-equivalent model. The generic rational declarations accept any finite extension with `[FiniteDimensional (Padic l) E]`; the public paper-specialized `constructibleHeart` uses precisely the finite subfield of the fixed closure.
- The geometric scheme is `Y : AlgebraicGeometry.Scheme` with `[Y.Over (AlgebraicGeometry.Spec (CommRingCat.of D.k))]`. The two instances `LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))` and `QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))` are exactly finite type, with no separatedness or smoothness assumption. They occur in the selected t-structure and therefore in both paper-specialized heart definitions.
- For finite coefficients, `rationalConstructibleCategory D l hl E Y` is the raw integral rationalization from `def-weil-rationalization-karoubi`, without a Karoubi enlargement. Its integral representatives are the dependency's `integralConstructibleCategory`, whose defining reduction condition is `intrinsicFiniteTorsionConstructible`; no substitute category or extra boundedness assumption is introduced.
- For the closure, `algebraicallyClosedConstructibleCategory D l hl Ω Y` is the actual common-stage pair category. It uses the specified finite-stage transitions, common-stage Hom equivalence, shifts and distinguished triangles; it is not a product or a category merely postulated equivalent to that construction.
- The standard pair is exactly `rationalConstructibleLEZero` / `rationalConstructibleGEZero`, or `algebraicallyClosedConstructibleLEZero` / `algebraicallyClosedConstructibleGEZero`, from `Sheaf.Paper.ConstructibleStandardTStructure`. The integral conditions are ordinary completed-module cohomology vanishing; the rational and closure conditions are their required isomorphism closures.
- `rationalConstructibleStandardTStructure_existsUnique` and `algebraicallyClosedConstructibleStandardTStructure_existsUnique` prescribe `t.le n` and `t.ge n` for every `n : ℤ` and assert `∀ K, t.bounded K`. These are the bounded-t-structure assertions used by this node. They do not purport to encode the additional scalar-extension and automorphism assertions of `prop-constructible-truncations`, which this definition does not use.
- `rationalConstructibleTruncLE`, `rationalConstructibleTruncGE`, and their algebraically closed counterparts use Mathlib's `t.truncLE m` and `t.truncGE m` for every `m : ℤ`.
- Each `...Heart_properties` states `LEZero K ↔ IsZero ((...TruncGE ... 1).obj K)` and `GEZero K ↔ IsZero ((...TruncLE ... (-1)).obj K)`, precisely the two displayed equalities of object classes. Vanishing is categorical `IsZero`.
- `...HeartProperty` is the intersection `LEZero ⊓ GEZero`; `...Heart` is its `FullSubcategory`, retaining all ambient morphisms. The property theorem identifies it with Mathlib's `t.heart`. The paper-facing `constructibleHeart` and `constructibleHeartAlgebraicallyClosed` directly use `t.heart.FullSubcategory` on the two prescribed coefficient categories. The same property theorems state `Nonempty (Abelian (...Heart ...))`, expressing that these full hearts are abelian.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- Mathlib Padic and algebraic-closure definitions: `Padic`, `IsAlgClosure`; finite-extension support from `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, especially `Padic.finite_coefficientExtensionRing`.
- Mathlib scheme morphism definitions: `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`: `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible` (through the integral category).
- `Sheaf.Paper.RationalizationKaroubi`: `WeilConjectures.rationalConstructibleCategory`, its localization and inherited triangulated structure.
- `Sheaf.Paper.AlgebraicallyClosedCoefficients`: `WeilConjectures.algebraicallyClosedConstructibleCategory`, `AlgebraicallyClosedCoefficients.Index`, `Coefficient`, `Stage`, `stageSystem` and `inclusion`.
- `Sheaf.Paper.ConstructibleStandardTStructure`: the integral, rational and algebraically closed standard object properties in degrees zero and every integer.
- `Mathlib.CategoryTheory.Triangulated.TStructure.Basic`, `Heart`, `TruncLEGT`: `CategoryTheory.Triangulated.TStructure`, `TStructure.heart`, `TStructure.truncLE`, `TStructure.truncGE`, and the two general truncation-vanishing lemmas. The heart is Mathlib's existing construction.
- `Sheaf.CategoryTheory.Triangulated.TStructure.HeartAbelianKernelSplitting`: `CategoryTheory.Triangulated.TStructure.heart_abelian_and_idempotent_kernel_decomposition`, used in the future abelianity proof.
- The transitive coefficient dependencies and their exact interfaces are documented below. Each delivered source is assigned to its existing DAG node.

Edge cases checked: the empty finite-type scheme and zero complex require no nonemptiness condition; the base coefficient field ℚ_l is an allowed finite stage; equality of two coefficient stages uses the normalized unit comparison; torsion integral objects become zero under rationalization, so rational classes must use isomorphism closure, not a predicate on a chosen representative. Both positive and negative integer cutoffs and the adjacent cutoffs 1 and -1 have the required cohomological shift convention. The algebraic closure may have a larger universe: its finite subfields use the coefficient dependency's actual small model. There is no invertibility assumption on l in the integral coefficient ring, and no completion/idempotent enlargement is silently added to either heart.

Searches (2026-10-16; launcher search responses are in `searches.jsonl`):

- LeanSearch, “The heart is the full subcategory of a t-structure on objects in degrees at most zero and at least zero”: generic t-structure/derived-category results, no l-adic constructible heart.
- LeanFinder, “The constructible heart of the standard t-structure on rational l-adic constructible derived categories”: generic derived t-structure results only.
- Loogle, `CategoryTheory.Triangulated.TStructure.heart`: generic heart declarations, used directly here.
- Mathlib grep, `constructibleHeart|ConstructibleHeart|constructibleStandard|ConstructibleStandard`: no result. Direct `rg` over upstream `WeilConjectures` and side-library `lean/Sheaf` found no existing declaration of this heart. Upstream adic constructibility references concern a different category, not this raw rational/common-stage construction. The source-id search likewise supplied no exact declaration.
- For unstated dependencies, `scompile.py --source` and a read-only check of server delivery branches were made before adding them. The canonical coefficient packet was found in Q18's sandbox, with a successful final dry-run log; the standard-pair draft was found in NO's sandbox. Their needed sources were copied only into this sandbox and are being compiled anew as part of this delivery. No live source or shared checkout is edited.

No statement correction or disputed mathematical assertion is needed. The node's original statement is retained. The
item's `stmt_deps` remains the original twelve direct notions; the supplied modules below repair declarations in its
statement-prerequisite closure without adding unrelated direct edges. No new mathematical notion/node is invented.

## Dependency modules

`def-weil-constructible-standard-tstructure`: the shared node still has no usable Lean
record on the current base. `Sheaf.Paper.ConstructibleStandardTStructure` supplies the
integral cohomology-vanishing classes, rational isomorphism closures, and common-stage
isomorphism closures in every shifted degree. It supplies the standard pair used by the
heart module, rather than an arbitrary assumed t-structure. Its imports use the landed
coefficient, rationalization, and common-stage declarations already present in the base.

The other prerequisite modules formerly present in this sandbox are now landed on the
current `newtargets-dag` base and are consumed from there; they are not copied or changed
by this repair. No new definition node is introduced.

## Earlier second reading (a previous round; superseded)

I read the node and `ConstructibleHeart.lean` independently. I also read the original
blueprint node and its enclosing unit on the server: the source introduces precisely a
finite-type geometric k-scheme, not a separated or smooth scheme. The corrected stage-1
node expands the source's reference to the standard t-structure and removes its informal
closing gloss; this delivery does not change that natural-language statement. There is no
`statement_change` and no new definition node in this packet.

The objects, hypotheses and conclusions, in their order in the node, match as follows.

1. The tuple p,a,q,k₀,k is `D : FiniteFieldDatum`. I opened its structure: primality,
   positive a, q = p^a, cardinality of k₀, and the algebraic-closure structure on k are
   fields, not arbitrary unverified assumptions. Verdict: same finite-field datum.
2. The prime distinct from p is `(l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)`.
   The rational coefficient field is the existing `Padic l`. Verdict: exact.
3. The fixed algebraic closure is `(Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
   [IsAlgClosure (Padic l) Ω]`. The finite subfield is
   `E : AlgebraicallyClosedCoefficients.Index l Ω`, namely
   `Padic.FiniteCoefficientFields l Ω`. The coefficient construction transports that
   actual finite intermediate field by `Shrink.algEquiv` to `Coefficient.{u} l Ω E`.
   This is an algebra-equivalent small model, with the inclusion conjugated by those
   equivalences; it does not replace finite extensions by finite-type field algebras.
   The generic rational helpers allow any finite-dimensional E, and the paper-facing
   abbreviation specializes them to precisely the finite subfields. Verdict: exact.
4. Y is `Scheme.{u}` over `Spec (CommRingCat.of D.k)`. Its structure morphism has
   `LocallyOfFiniteType` and `QuasiCompact`, precisely finite type. I checked the
   `include base finiteTypeLocal finiteTypeCompact`: these otherwise-unused hypotheses
   are retained in both existence/uniqueness theorems and hence their chosen structures.
   There is no extra Noetherian, separation, smoothness or coefficient-invertibility
   binder. Verdict: exact, including nonseparated finite-type schemes.
5. The E category is `rationalConstructibleCategory D l hl E Y`: its definition is
   `ScalarLocalization` of the actual bounded constructible derived-complete integral
   full subcategory at the specified uniformizer. Its objects are the integral objects;
   the Hom-coordinate theorem gives Hom tensor E. Its representatives use the finite
   reduction constructibility condition through that integral dependency. No Karoubi
   envelope is used. Verdict: correct category, not the similarly named upstream
   Karoubi rational category.
6. The Ω category is `algebraicallyClosedConstructibleCategory D l hl Ω Y`, the actual
   upstream `StageSystem.PairCategory` specialized to the prescribed rational stages.
   `StageHom`, `transport`, `ColimitHom`, `homCoordinates`, `representatives`,
   `shiftRepresentative` and `Distinguished` specify respectively the common-stage
   Hom system, its quotient coordinates, shift and triangle criterion. Verdict: the
   required common finite-stage category, with no extra idempotents.
7. The standard nonpositive/nonnegative classes are exactly the dependency's
   `rationalConstructibleLEZero`/`rationalConstructibleGEZero` and
   `algebraicallyClosedConstructibleLEZero`/`algebraicallyClosedConstructibleGEZero`.
   I read their definitions: integral cohomology vanishes for r > 0 / r < 0;
   rational classes are isomorphism closures of integral ones; Ω classes are
   isomorphism closures of the images of finite stages. Verdict: exact standard pair.
8. Both `...StandardTStructure_existsUnique` theorems prescribe every `t.le n` and
   `t.ge n` and assert `∀ K, t.bounded K`. In Mathlib `TStructure` the only data are
   those two functions; its other fields are propositions. Thus these choices determine
   the structure and are not hollow choices of an arbitrary object. The proof plans
   explain restriction of integral truncation triangles, rationalization, common-stage
   descent, orthogonality and boundedness. Verdict: precisely the node's bounded
   standard-t-structure assertion.
9. For every `m : ℤ`, `...TruncLE m` and `...TruncGE m` are Mathlib's actual truncation
   functors of those structures. Verdict: all integer cutoffs, with the standard signs.
10. The `...Heart_properties` theorems state, object by object, both displayed class
    equalities: `LEZero K ↔ IsZero ((...TruncGE ... 1).obj K)` and
    `GEZero K ↔ IsZero ((...TruncLE ... (-1)).obj K)`. They also identify the
    zero-class intersection with `t.heart`. Verdict: both directions of both displays.
11. Each `...HeartProperty` is `LEZero ⊓ GEZero` and its heart abbreviation is the
    `FullSubcategory`, retaining all ambient morphisms. The public `constructibleHeart`
    and `constructibleHeartAlgebraicallyClosed` use `t.heart.FullSubcategory` directly.
    The property theorems supply `Nonempty (Abelian (...Heart ...))`; their equality
    with `t.heart` transports this structure to the public abbreviation. I read the
    cited `heart_abelian_and_idempotent_kernel_decomposition` signature: its first
    conjunct gives exactly the needed abelian structure. Verdict: full, abelian heart.

Edge cases: there is no nonempty-scheme or nonzero-object assumption. Zero and the empty
finite-type scheme are included. The coefficient index is nonempty because it contains
ℚ_l, including identity extensions, and directed by the actual compositum. Thus no
empty common-stage index is silently assumed. All integer m, especially 0, 1 and -1,
are included. Positive reduction levels and the zero-level convention belong to the
unchanged integral dependencies; this heart adds no restriction on n. The characteristic
condition is exactly l ≠ p. Closure universe v is independent of scheme universe u;
finite-dimensionality gives `Small.{u}` using finite basis coordinates. The geometric
base field is in the scheme universe as required to form its structure morphism. No
identification of the small pro-etale site's object and morphism universes was added.

Independent searches: I ran msearch LeanFinder with `constructible heart`, Loogle with
`CategoryTheory.Triangulated.TStructure.heart`, and grep with
`adic.*[Hh]eart|[Hh]eart.*adic|constructible.*[Tt][Ss]tructure`. LeanFinder returned only
ordinary derived-category t-structures; Loogle returned Mathlib's generic heart (used
here); grep returned no match. I additionally searched upstream `SixFunctors/Etale`,
all upstream WeilConjectures, Mathlib, and the project's `lean/Sheaf` by heart/t-structure
and adic terminology. The upstream perverse-heart candidate is a different notion.
`IntegralTStructure.pbcIntegralTStructure` uses the distinct PBC integral encoding and
extra geometric instances, not this raw rational/common-stage heart. I read its
signature and did not confuse it with the current standard pair. Current-server source
queries confirm the heart and standard-pair modules were not already published; the
coefficient and stage-system modules are now landed prerequisites on the current base. No exact existing heart replaces this module.

I read the remaining dependency module and the landed prerequisite declarations it
imports. The item's direct dependency edges are unchanged; only the still-missing
standard-pair declaration is supplied in this repair.
There is no invented new definition node to audit under H12.


The landed coefficient and stage-system modules were read from the current base and are
used unchanged by the remaining standard-pair module.

No mathematical signature mismatch was found in this second reading. I retained the
Lean files and node statements. All recorded `lean.statement` strings occur verbatim
in their owning files; every file has lines at most 100 characters, explicit universes,
and source/blueprint declaration docstrings. Postponed proofs are named theorems with
proof plans, and no theorem is proved in stage 2. The only initial compile failure was
compiling the heart alone without its unlanded standard-pair sibling; validation therefore
passes the dependency module and heart together through scompile.py as required. Final compile and
delivery-preflight results are recorded after the checks below.

Second-reader validation: scompile.py compiled the delivered dependency module and heart successfully
with no warnings or errors using the local side overlay. The compiler retained its
normal per-file limits and isolated builds. All named declarations are included in
their owning node's `lean.declarations` list. No Lean or mathematical-node repair was
needed; this second reading adds the independent audit and fresh validation evidence.

The second-reader dry run returned `OK`: all delivered modules and the landed pair-category declarations compile, and the current-server preflight passes. During that
run a shared local overlay-cache artifact disappeared; the wrapper's automatic
server confirmation completed successfully without a Lean error or warning.


## Second reading by NV

Fresh independent reading, 2026-10-16. I opened both sandbox node records and Lean
modules, the twelve direct dependency records, and the dependency declarations.
I fetched the heart blueprint and its enclosing section from the server because
that literature is absent from this read-only local mirror. The source fixes an
arbitrary finite-type k-scheme Y; the enclosing section's separated morphism f is
not an additional hypothesis on this independent definition. The node's earlier
stage-1 expansion of the standard pair agrees with that source. This delivery
makes no statement correction and introduces no new definition node.

The node's objects, hypotheses and conclusions, with their Lean counterparts:

1. Global p,a,q,k₀,k: `D : FiniteFieldDatum`. Its structure explicitly records the
   prime, positive exponent, q = p^a, finite base field cardinality and fixed
   algebraic closure. Verdict: exact datum.
2. Prime l distinct from p: `(l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)`.
   `Padic l` is Mathlib's completion Q_l. Verdict: exact characteristic condition.
3. Fixed closure: `(Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
   [IsAlgClosure (Padic l) Ω]`. Finite subfield:
   `(E : AlgebraicallyClosedCoefficients.Index l Ω)` in `constructibleHeart`.
   I read `Index = Padic.FiniteCoefficientFields l Ω` and the finite-dimensional
   intermediate-field subtype, plus `Coefficient = Shrink E.val` and its actual
   `Shrink.algEquiv`. Verdict: precisely a finite subextension of the fixed closure;
   the small model changes only its presentation. Generic rational helper binders
   use `[FiniteDimensional (Padic l) E]`, the same finite-extension notion.
4. Finite-type geometric scheme: `Y : Scheme.{u}`, its `Y.Over (Spec (.of D.k))`,
   `LocallyOfFiniteType` and `QuasiCompact` instances. The `include` command retains
   these three instances in the existence theorems and chosen standard structures.
   Verdict: finite type, with no extra separatedness, smoothness or Noetherian binder.
5. E coefficient category: `rationalConstructibleCategory D l hl E Y`. I read its
   current server definition: `ScalarLocalization` of the recorded bounded complete
   integral category at the chosen uniformizer, with unchanged integral objects.
   I read that integral predicate: derived completeness, every positive reduction's
   `intrinsicFiniteTorsionConstructible`, and one common finite support interval.
   Verdict: the stipulated raw rationalization; no Karoubi envelope is substituted.
6. Closure coefficient category: `algebraicallyClosedConstructibleCategory D l hl Ω Y`.
   Its current server source specializes `StageSystem.PairCategory` to exactly the
   rational stages, prescribed inclusions and normalized associators; it supplies
   common-stage Hom coordinates, shifts and distinguished triangles. Verdict: the
   actual common-stage category, without additional retract objects.
7. Standard pair: the sibling's `rationalConstructibleLEZero`/`GEZero` and
   `algebraicallyClosedConstructibleLEZero`/`GEZero`. The integral definitions use
   ambient completed-module homology vanishing for every r > 0 / r < 0; rational
   definitions take isomorphism closure of integral images; closure definitions take
   isomorphism closure of finite-stage inclusions. Verdict: each of the dependency
   node's three clauses is rendered, including the necessary isomorphism closures.
8. Bounded standard t-structure: both `...StandardTStructure_existsUnique` theorems
   require `∀ n : ℤ, t.le n = ...LE ... n ∧ t.ge n = ...GE ... n` and `∀ K, t.bounded K`.
   I read Mathlib's `TStructure` fields: le/ge are all its data and the other fields
   are propositions. Verdict: boundedness is objectwise for every object; uniqueness
   follows from prescribed classes and makes the subsequent choice non-hollow.
9. Integer truncations: both coefficient cases define `...TruncLE (m : ℤ)` and
   `...TruncGE (m : ℤ)` as the chosen t-structure's Mathlib truncation functors.
   Verdict: every integer cutoff, with the canonical t-structure construction.
10. Both displayed vanishing tests: each `...Heart_properties` quantifies over every
    K and states `LEZero K ↔ IsZero ((...TruncGE ... 1).obj K)` and
    `GEZero K ↔ IsZero ((...TruncLE ... (-1)).obj K)`. I read the general Mathlib
    lemmas `isLE_iff_isZero_truncGT_obj` and `isGE_iff_isZero_truncLE_obj`.
    Verdict: both directions, with the correct adjacent cutoffs and categorical zero.
11. Full heart and abelianity: `...HeartProperty` is `LEZero ⊓ GEZero`, its heart is
    `.FullSubcategory`, and the property theorem identifies this with `t.heart` and
    states `Nonempty (Abelian (...Heart ...))`. The two paper-facing abbreviations
    use `t.heart.FullSubcategory` directly. The property equality transports the
    asserted abelian structure to them. I read the recorded heart-abelian theorem's
    first conjunct and ambient hypotheses. Verdict: full subcategory with all ambient
    morphisms and the exact abelianity conclusion in both coefficient cases.

Dependency-module audit (H13): `def-weil-constructible-standard-tstructure` is an
existing DAG node with no published declaration (confirmed by `scompile.py --source`).
I read its full statement against `ConstructibleStandardTStructure.lean`, and read the
source displays in `prop-weil-pbc-integral-tstructure` and
`prop-weil-localized-tstructure` from the server. Its three levels, all integer shifts
and arbitrary-scheme domain agree; in particular this module asserts no t-structure
axioms or finite-type condition. The theorem source's additional hypotheses matter
for proving truncation stability, not for defining these predicates. The shifted
classes use K[n] exactly as the dependency node says, consistent with Mathlib's
`a + n' = n` shift convention. Its lean.note correctly explains the missing interface.
The already landed coefficient modules are consumed without redelivery or modification.
The upstream Adic.Constructible module defines stratified lisse sheaves in a different
sheaf category, and IntegralTStructure defines the separate PBC integral encoding;
neither is an existing declaration of this rational/common-stage heart.

Edge cases: empty schemes and zero objects are admitted, without nonempty or nonzero
binders. The finite coefficient index contains the bottom field Q_l and is directed
by finite composita, including repeated and identity stages. All m in Z are included,
particularly 0, 1 and -1. Positive finite reductions are indexed by n+1 in the integral
dependency, so this item discards no reduction level and adds no n restriction.
Torsion representatives becoming zero rationally are covered by isomorphism closure.
The prime hypothesis includes l = 2, excluding exactly l = p. The closure universe v
is independent of u; coefficientSmall is constructed from finite-basis coordinates,
so no universe equality or extra Small assumption is imposed. Base field and scheme
share u to form the specified structure morphism; no small-site universes are equated.

Fresh searches, logged by msearch.py in this sandbox: LeanFinder queried
`standard l-adic constructible sheaves heart of bounded t-structure` and returned
ordinary derived-category support predicates and their canonical t-structure;
Loogle queried `CategoryTheory.Triangulated.TStructure.heart` and returned the generic
heart construction used here. Mathlib grep queried
`constructible.*heart|heart.*constructible|adic.*heart|heart.*adic` and returned no hits.
LeanSearch queried `The constructible heart of the standard t-structure on rational
l-adic constructible complexes` and returned only generic t-structure declarations.
Independent rg over Mathlib, upstream WeilConjectures and project lean/Sheaf found
no matching rational/common-stage heart; I opened the upstream Adic.Constructible
candidate instead of treating its blueprint comment as an exact match. Current-server
source queries also show neither delivered module is already published.

Mismatches and repairs: no mathematical or Lean-signature mismatch was found. I retained
both Lean modules and both node records. The previous audit was explicitly headed as
superseded, so I appended this required current `## Second reading by NV` section and
fresh search evidence. Both lean.statement strings were checked verbatim in their
owning files; all delivered declarations are listed, all Lean lines fit 100 characters,
and autoImplicit is false with universes declared. The only four postponed proofs
are the two bounded-standard-structure theorems and two heart-properties theorems,
all named, belonging to the heart node, and carrying source and step-by-step proof
docstrings. No theorem is proved and no definition contains sorry data. Fresh wrapper
compilation and preflight evidence follow below.

Fresh validation: the required scompile.py invocation covered both sibling modules.
The current deliver2.py --no-push run compiled both files individually with the
normal 60-second limits, produced no warning or error, and returned
`OK (dry run): commit 1ecc769be0 passes the preflight and compiles; nothing pushed`.
The staged packet contains only the two Lean modules, their two node records and
this report. No source or natural-language statement was changed by this reading.

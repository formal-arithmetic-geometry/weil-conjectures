## Worker report

The module `lean/Sheaf/TraceFormula/ValuativeDominationEtaNormal.lean` states the
valuative domination criterion for an eta-normal flat reduced scheme, with theorem
`AlgebraicGeometry.valuative_domination_eta_normal`. Its hypotheses render the node
clause by clause as follows:

- `S : Scheme.{u}` with `[IsIntegral S]`, and a structure morphism
  `s : S ⟶ Spec (CommRingCat.of (ULift.{u} ℤ))` carrying
  `[LocallyOfFiniteType s] [QuasiCompact s]`.
- Schemes `C X Y : Scheme.{u}` and maps `c : C ⟶ S`, `a : X ⟶ C`,
  `b : Y ⟶ C`, with reducedness instances for all three and flatness,
  locally-finite-type, and quasi-compactness instances for `c`, `a ≫ c`, and
  `b ≫ c`.
- `ha` and `hb` are `EtaModification` hypotheses over
  `S.fromSpecStalk (genericPoint S)` for `a` and `b`.
- `hnormal` says every finite eta-modification `f : Z ⟶ Y` is an isomorphism.
- `hvaluative` quantifies over every valuation subring `V` of `S.functionField`,
  assumes `Finite (PrimeSpectrum V)`, and every map
  `v : Spec (CommRingCat.of V) ⟶ S` whose generic restriction is the specified
  generic-point map; it supplies a morphism between the two base-changed objects
  over `C_V`, with the required commutative triangle.
- The conclusion is an `Over` morphism `h` from `b ≫ c` to `a ≫ c`, satisfying
  `h.left ≫ a = b` and identifying its generic pullback with the generic pullback of `b` followed by the inverse of the
  generic pullback of `a`.

The dependency declarations used are:

- `def-pc-integral-scheme`: `AlgebraicGeometry.IsIntegral` in
  `Mathlib.AlgebraicGeometry.Properties`.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact` in Mathlib finite-type/quasi-compact modules.
- `def-weil-flat-morphism`: `AlgebraicGeometry.Flat` in
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`.
- `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsFinite` and
  `AlgebraicGeometry.IsIntegralHom` in the Mathlib finite/integral morphism modules.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback` and its projections in
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsProper`, `IsSeparated`, and
  `UniversallyClosed` in `Mathlib.AlgebraicGeometry.Morphisms.Proper`.
- `def-trf-modification`: `AlgebraicGeometry.EtaModification` in
  `Sheaf.TraceFormula.Modification`.
- `def-sc-function-field`: `AlgebraicGeometry.Scheme.functionField`/the project
  function-field interface in `Sheaf.AlgebraicGeometry.FunctionField`.
- `def-pc-reduced-scheme`: `AlgebraicGeometry.IsReduced` in
  `Mathlib.AlgebraicGeometry.Properties`.

Edge cases checked: valuation rings of finite height are included through
`Finite (PrimeSpectrum V)`; the empty or zero-dimensional fibres are not excluded;
all three schemes may have arbitrary universe `u`; no surjectivity, smoothness, or
extra normality assumptions are added; and the generic-fibre equality is stated
using the canonical inverse supplied by `ha.2`.

Searches made: `msearch.py Q91 lem-trf-valuative-domination-eta-normal leanfinder`
for a valuative domination criterion (no exact match; only pointwise valuative
criteria); `msearch.py ... loogle "ValuativeCriterion"` (no exact match);
`msearch.py ... grep "factor.*[Vv]alu|[Vv]alu.*factor|eta.normal"` in Mathlib
(no exact match); `rg` over the project and source checkouts for the node id and
`valuative_domination_eta_normal` (the existing project module was found and its
signature was checked). The existing declaration is not a Mathlib match: it is the
statement module being delivered here, so no duplicate definition is introduced.

## Second reading by Q91

Independent maintainer reading of immutable delivery
`0c401aed13ac6bad4b59bb86268dd4239908b775`, performed 2026-10-18.
This section replaces the delivered generic assurance (delivery-errors H11).
The worker report above is retained, with its prose description of composition
order corrected. No Lean declaration, mathematical statement, or node record changed.

I read the packet, immutable item node and module, all nine statement-dependency
nodes and their records, and the actual dependency declarations. The extracted
snapshot has no separate report file; the delivered report is the text embedded
under `## Delivered report` in packet.md. This complete file replaces that report.

Source checked: Temkin, arXiv:0707.3953v3, *Stable modification of relative curves*,
[Proposition 5.2 and its proof](https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf),
printed pp. 34–35 (PDF pages 34–35), §3 conventions on printed p. 14,
§1.2 on modifications, and the finite-height reduction immediately following
Proposition 5.2 in the proof of Theorem 1.2. The node deliberately specializes
the integral Noetherian base to a base of finite type over Z; its finite-height
valuation tests suffice by the Abhyankar bound. This is already the node's
statement, not a new source-based correction in this delivery.

Clause-by-clause reading:

1. The base is `S : Scheme.{u}` with `[IsIntegral S]`. Mathlib's `IsIntegral`
   includes nonemptiness and domains of sections on nonempty opens, equivalent
   to the affine formulation in def-pc-integral-scheme. The map `s` to
   `Spec (CommRingCat.of (ULift.{u} ℤ))` with `[LocallyOfFiniteType s]`
   and `[QuasiCompact s]` states finite type over Z. The lift only places the
   integer ring in the scheme universe. It adds no geometric assumption.
2. `S.functionField` is exactly the stalk at `genericPoint S`; Mathlib supplies
   its field instance under `IsIntegral S`. This uses the arbitrary integral
   scheme clause of def-sc-function-field, not its reducible-curve product.
   `S.fromSpecStalk (genericPoint S)` is the specified generic map.
3. `C X Y : Scheme.{u}`, `c : C ⟶ S`, `a : X ⟶ C`, and `b : Y ⟶ C`
   give all the objects and structure maps. `[IsReduced C/X/Y]` (written as
   three separate instances) matches reduced local rings: I checked
   `IsReduced` and the two stalk/sections comparison declarations.
4. Flatness is assumed for exactly `c`, `a ≫ c`, and `b ≫ c`, not for `a`
   or `b`. I checked `Flat.iff_flat_stalkMap` against def-weil-flat-morphism.
   Each of these same three structure maps has both locally-finite-type and
   quasi-compact instances, exactly the finite-type requirement.
5. `ha` and `hb` use the recorded `EtaModification` from
   `Sheaf.TraceFormula.Modification`. I opened that definition and
   `SchemeModification`: they require properness, a common isomorphism open
   with schematic density on BOTH sides, and invertibility of the actual
   generic base-change map. `SchematicallyDenseOpen` is injectivity of
   restriction on every ambient open. There is no arbitrary fibre isomorphism.
6. `hnormal` quantifies over every `Z : Scheme.{u}` and every `f : Z ⟶ Y`;
   `IsFinite f → EtaModification ... f (b ≫ c) → IsIso f` is precisely the
   inline eta-normality hypothesis. It adds neither reducedness nor flatness
   of Z. `IsFinite` is the recorded finite affine morphism notion.
7. `hvaluative` quantifies over every `ValuationSubring S.functionField`.
   Its defining membership-or-inverse condition is the node's valuation-ring
   condition; Mathlib supplies `IsFractionRing V S.functionField`. Thus no
   fraction-field hypothesis is missing. Prime ideals of a valuation ring are
   totally ordered, so `Finite (PrimeSpectrum V)` is exactly a finite chain
   of prime ideals, including the height-zero field valuation.
8. For each V the next quantifier is every `v : Spec V ⟶ S`, followed by
   the equality of its generic restriction with the specified generic map.
   `Spec.map` is contravariant, so the inclusion V into K has exactly the
   direction required. All centres, including multiple possible centres on
   a nonseparated base, remain quantified.
9. The comparison `hV` is a morphism in `Over (Spec V)` between the full base
   changes of Y and X. Its displayed equality is equality of morphisms to
   the full base change of C. I read `Over.pullback.obj` and `.map`; these
   are the pullback objects and induced pullback maps, not chosen substitutes.
   Hence the condition is exactly being a C_V-morphism, and no compatibility
   among different V is silently imposed.
10. The conclusion gives `h : Over.mk (b ≫ c) ⟶ Over.mk (a ≫ c)`, hence an
    S-morphism Y to X. `h.left ≫ a = b` is the required factorization.
    Its second conjunct equates the canonical generic pullback of h with
    b_eta followed by inverse(a_eta). The explicit `ha.2` supplies the
    IsIso proof for that very map. Composition order and domains agree.

Edge cases: S is nonempty by integrality; C, X and Y may be empty, and no
nonemptiness or positive-dimensional-fibre assumption was added. The trivial
valuation V=K is included. Both positive and zero characteristic are allowed.
Valuation subrings live in the universe of K. The universe `u` is arbitrary;
no accidental equality of unrelated universes is imposed. Quantifying finite
modifications in Scheme.{u} is appropriate: finite schemes over Y admit models
in this universe. There is no restriction on smoothness, normality of S, or
separatedness of the three structure maps.

The module and theorem docstrings name the source and blueprint id. The nine
numbered proof steps reproduce the node's nine steps: Noetherian/finite-height
reduction; flat generic density and uniqueness; valuation approximation;
common base modification and gluing; generic graph closure; proper surjection;
closed-point graph fibres; proper zero-dimensional finiteness and eta-normality;
and extraction of h. In particular, Step 7 cites the recorded corrected
`lem-trf-base-modification-comparison-fibre-image`; it does not reuse the
invalid printed inference from quasi-finiteness over the modified base to
quasi-finiteness of its image. No local proof was supplied: the only delivered
theorem ends `:= by sorry`, and there are no new definitions or helper axioms.

One-definition-per-notion checks: I searched the read-only project's
`lean/Sheaf` and upstream `WeilConjectures` for eta-normality, valuative
domination, and finite eta-modifications, and inspected Mathlib
`ValuativeCriterion.Existence`, `.Uniqueness` and `.ValuativeCriterion`.
Those criteria concern lifts of individual valuative squares, not comparisons
of whole base-changed families. The project copy at this module path agrees
except for the author attribution (Q122 versus Q91); it is the earlier binding
of this same node/module, not a second differently named theorem to import.
Existing eta-normality interfaces elsewhere do not replace the recorded
EtaModification interface used here. The worker's three search kinds are
recorded above; these independent source searches found no separate exact match.

Record and compilation checks: the node's `lean.statement` equals the entire
Lean theorem signature after whitespace normalization; the module/declaration,
file path, branch and existing:false fields agree. No statement_change was
made, so no citer audit is required. No new node or dependency module is delivered.
The direct statement/proof dependency ids have empty intersection with
`origin/newtargets-dag:coord/route-pivot-dropped.txt`; no route-pivot repair note
exists at the named path. This is ordinary scheme geometry, with no dropped
higher-category machinery or pro-etale substitute.

Reproduction command:

```text
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q91 lem-trf-valuative-domination-eta-normal /home/ubuntu/weil-launcher-nt/reviews-stage2/Q91__lem-trf-valuative-domination-eta-normal__0c401aed13ac/snapshot/lean/Sheaf/TraceFormula/ValuativeDominationEtaNormal.lean
```

Exit code 0. The wrapper compiled `Sheaf/Stage2/Sandbox0.lean` in its private
side overlay (24.0 seconds) and confirmed
`Sheaf/TraceFormula/ValuativeDominationEtaNormal.lean` at the library module path
(5.3 seconds), both without Lean diagnostics. Initial SSH multiplexing messages
were transport messages; compilation completed successfully. No global build,
live Lean write, repository edit, direct SSH command, or delivery action was run.

Finding and disposition: H11 is repaired by this complete replacement report.
The worker's composition-order prose is corrected to match its already-correct
Lean equation. Mathematical signature, source match and compilation pass;
no Lean or node-record fix is needed. FIX, report only.

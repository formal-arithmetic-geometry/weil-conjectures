## Worker report

The module `Sheaf.AlgebraicGeometry.FrobeniusTrivializationPullback` states
`AlgebraicGeometry.Scheme.absoluteFrobenius_proEtale_trivialization_pullback`.
It has one theorem with proof `by sorry`, and no new definition. The node is
unchanged outside its `lean` field. No new nodes or dependency repairs are needed.

The statement uses the existing ordinary intrinsic module category, constant-ring
operations, and exact derived descent. Its canonical data are exposed by the same
normalized existential format as the recorded
`absoluteFrobenius_proEtale_trivialization`. This is not an assertion about an
arbitrary choice of trivializations: the two projections fix `r`, the conjugate
adjunction's section equation fixes `comp`, and the adjunction unit's section
equation fixes `tau`. Thus these are precisely the canonical maps specified by the
node, including its reference to the b=1 trivialization in the dependency.

Clause-by-clause correspondence:

- Prime p: `(p : ℕ) (hp : Nat.Prime p)`. Characteristic-p schemes:
  `(X Y : Scheme.{u})`, `(hX : X.IsCharacteristic p)` and
  `(hY : Y.IsCharacteristic p)`. No reducedness, finite type, smoothness, properness,
  or scheme flatness is required. The morphism `(u : X ⟶ Y)` is arbitrary.
- A finite commutative ring: `(A : Type u) [CommRing A] [Finite A]`.
  There is no nonzero-ring assumption or invertibility condition on p in A.
- The small pro-etale sites are the actual `X.ProEt` and `Y.ProEt` with their
  published topology. `proEtaleRingModules X (proEtaleConstantRing X A)` and
  `proEtaleDerivedCategory X A` are the recorded constant-ring module sheaves and
  their ordinary unbounded derived category. Their coefficient ULift and site
  object universe u+1/morphism universe u are retained.
- The canonical coefficient map is the existing
  `proEtaleConstantRingComparison`, used inside all
  `proEtaleConstantRingPullback`, `Pushforward`, `Adjunction`, and
  `DerivedPullback` terms. It is `asIso` of the existing
  `proEtaleCoefficientInverseImageMap`, the constant-preserving comparison.
  `ProEtaleConstantRingMap` supplies the finite-coefficient normalization and its
  uniqueness. No coefficient comparison is supplied as a free parameter.
- Absolute iterated Frobenius is exactly
  `X.iterateFrobenius hp (hX.2 ⊤) b` (and the corresponding Y expression).
  All exponents are `ℕ`, including zero.
- The canonical relative-Frobenius isomorphisms are the existential family
  `r X hX n : 𝟭 X.ProEt ≅ proEtaleBaseChange (...)`. The first conjunct fixes
  their first projection to `V.left.iterateFrobenius hp hV n`. Their second
  projection is already fixed by being arrows over X, and equals `V.hom`.
  Thus these are `(F_V^n,v)`, not unspecified site automorphisms.
- The canonical ordinary composition comparisons are the family `comp f g`.
  Its conjugate under the actual normalized module adjunctions is evaluated on
  every module, site object, and section, and equals restriction along
  `(MorphismProperty.Over.pullbackComp f g).hom`. This is fibre-product pasting,
  hence the unique canonical module-pullback comparison, with compatible constant
  coefficients. `proEtaleFrobeniusDerivedComp A f g (comp f g)` is its exact
  derived descent. This is the constant-coefficient instance of the canonical
  composition of `ProEtaleCanonicalPullbackComposition`, whose K-flat
  normalization determines the same descent; see proof step 6 in the docstring.
- The family `tau X hX n` is the ordinary module-pullback trivialization.
  The sectionwise unit equation says that its adjunct is exactly restriction
  along `(r X hX n).inv.app V`. Equivalently it is the left-adjoint identification
  induced by direct-image restriction along r. Its derived version is the existing
  `proEtaleFrobeniusDerivedIso A (tau X hX n)`, which applies this map termwise
  and uses the canonical derived identity comparison.
- The final conjunct fixes `r X hX 0` to
  `(MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).symm`, transported across
  `F_X^0 = 𝟙 X`. Together with the unit equation this fixes tau at zero to the
  identity under the canonical identity-pullback identification. Thus the identity
  case is explicit even though pullback along an identity is not definitionally
  the identity functor.
- For arbitrary X, Y, u, b, the existential equality `w` states
  `F_X^b ≫ u = u ≫ F_Y^b`. The first three arrows of the natural-transformation
  equation are inverse composition for `(u,F_Y^b)`, transport across `w.symm`, and
  composition for `(F_X^b,u)`. They are exactly `c_{u,b}`.
- The remaining left side is `Functor.whiskerLeft (Lu*) tau_X.hom` and the
  right unitor; with Lean's left-to-right functor composition this means applying
  tau_X after Lu*. The right side is `Functor.whiskerRight tau_Y.hom (Lu*)`
  and the left unitor, meaning applying Lu* to tau_Y. Both are natural
  transformations from `L(F_Y^b)* ⋙ Lu*` to `Lu*`. This is precisely
  `(tau_X Lu*) ∘ c_{u,b} = Lu* tau_Y`.
- The penultimate conjunct quantifies over every scheme X and `a b : ℕ`.
  Its `w` states `F_X^a ≫ F_X^b = F_X^(a+b)`. The equation for tau_(a+b)
  is transport to the composite, the canonical derived comparison, tau_a
  whiskered on the left by `L(F_X^b)*`, the right unitor, then tau_b. In functional
  notation this is exactly the node's order `L(F^a)* L(F^b)*`, tau_a at
  `L(F^b)*(-)`, then tau_b. Universality in X gives both T=X and T=Y.
  The stated b-fold-iterate consequence follows by induction with a=1 and the
  explicitly normalized zero case; it introduces no separate notion.

Dependency declarations used (the files and full signatures/docstrings were read):

- `Sheaf.AlgebraicGeometry.SchemeCharacteristic`:
  `AlgebraicGeometry.Scheme.IsCharacteristic`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`:
  `AlgebraicGeometry.Scheme.proEtaleConstantRingComparison`,
  `proEtaleConstantRingPullback`, `proEtaleConstantRingPushforward`,
  `proEtaleConstantRingAdjunction`, `proEtaleConstantRingDerivedPullback`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`:
  `AlgebraicGeometry.ProEtale.finiteCoefficientInverseImageMap_isIso`,
  `finiteCoefficientInverseImageMap_constant`, and
  `finiteCoefficientConstantComparison_isIso`, used for the coefficient
  interpretation and imported as the statement dependency prescribes.
- `WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius`:
  `AlgebraicGeometry.Scheme.iterateFrobenius` and its section formula.
- `Sheaf.AlgebraicGeometry.AbsoluteFrobeniusSite`:
  `AlgebraicGeometry.Scheme.absoluteFrobenius_proEtale_trivialization`,
  `proEtaleFrobeniusDerivedIso`, `proEtaleFrobeniusDerivedComp`.
- `Sheaf.AlgebraicGeometry.ProEtaleCanonicalPullbackComposition`:
  `AlgebraicGeometry.Scheme.proEtaleCanonicalPullbackComposition` and
  `proEtaleCanonicalPullbackComposition_existsUnique`, whose normalized
  comparison is the one expressed by the section-normalized comp and exact
  descent in this statement.

The recorded proof dependencies are imported too: `SfIntrinsicRealizationTransport`,
`KFlatResolutionIndependentCoefficients`, Mathlib's pullback module, adjunction
`Mates` and `Basic`, and localization `Predicate`. The latter three correspond to
Mathlib matches rather than missing Lean records. No proof import was omitted for
an import cycle. The docstring carries all six proof steps of the DAG, including
the K-flat resolution argument identifying exact descent with the canonical
comparison on every unbounded derived object.

Edge cases checked: b=0, either summand of a+b zero, u the identity, X or Y empty,
A the zero ring, and nonreduced characteristic-p schemes. The last `r` clause
and the unit normalization retain zero iterates; no site section is assumed
nonzero or to distinguish constants on an empty object. The arbitrary-map
naturality equation uses only a commuting square, not a Cartesian Frobenius
square. In particular no reducedness or perfectness assumption slipped in.

Searches made with `msearch.py Q61 lem-pur-frobenius-trivialization-pullback`:

- LeanSearch: "The canonical trivialization of absolute Frobenius pullback on pro
  etale sheaves is compatible with arbitrary scheme morphisms". Eight hits: fibre
  bundle trivializations and `Scheme.Modules.pullbackCongr`; no match on the small
  pro-etale derived category.
- LeanFinder: "Canonical absolute Frobenius trivialization on pro etale derived
  module sheaves is natural under arbitrary scheme pullback and additive in
  exponents". Eight hits: Witt vector isocrystals, relative differentials,
  formally-etale Kaehler base change, untilts, etale composition; no matching theorem.
- Loogle: `"frobenius", "pullback"`. One hit,
  `CategoryTheory.Regular.frobeniusMorphism_isPullback`, unrelated regular-category
  Frobenius reciprocity.
- Mathlib grep: `Frobenius|frobenius|relativeFrobenius` in
  `AlgebraicGeometry/Sites`: zero hits.
- Source-project rg: Frobenius/trivialization and Frobenius/pullback combinations
  in `WeilConjectures`, including the side pro-etale framework. Existing geometric
  Galois Frobenius and Weil-complex transport statements do not identify absolute
  Frobenius pullback with the identity using relative Frobenius for every scheme.
  Grep for the exact node id has no upstream hit.
- Side-library rg: the existing `AbsoluteFrobeniusSite` is the relevant normalized
  construction. It gives open-restriction compatibility and the iterate law;
  it does not give arbitrary u naturality. No duplicate of this item was found.
  The exact declaration name is absent in Mathlib, upstream names and source,
  and the existing `lean/Sheaf` library.

Source check: Stacks `more-morphisms.tex`,
`lemma-relative-frobenius-weakly-etale` (0F6W), states precisely that relative
Frobenius is an isomorphism for a weakly etale map over any characteristic-p
scheme. The current blueprint `lem-trf-absolute-frobenius-site.proof.md` explains
restriction, adjunction, exact descent, and iteration; the item's six-step DAG
proof supplies arbitrary pullback naturality. The ancestor's final comparison
formula needs that arbitrary-morphism case. No statement fault or dispute found.

Validation: the module was compiled with the prescribed `scompile.py` wrapper.
All universes and variables are bound explicitly, with `autoImplicit false`.

## Second reading by Q61

I independently read the sandbox theorem and node, all seven statement-dependency
nodes and their recorded declarations, Stacks `more-morphisms.tex` at
`lemma-relative-frobenius-weakly-etale` (Tag 0F6W), and the cited
main-20261015 `lem-trf-absolute-frobenius-site.proof.md`. The Stacks lemma assumes
only a weakly etale morphism over a characteristic-p scheme; it imposes no
Noetherian, reduced, finite-type, perfectness, or scheme-flatness hypothesis.
The arbitrary-u compatibility is the node's stated deduction from that lemma,
not a claim that Tag 0F6W itself states a derived naturality theorem.
There is no repair note for this item and no `statement_change`.

Object/hypothesis/conclusion checklist, written from the node and then matched:

1. A prime p. Rendered by `(p : ℕ) (hp : Nat.Prime p)`. Verdict: exact.
2. Schemes X and Y in characteristic p. Rendered by the universally quantified
   `(X Y : Scheme.{u})`, `hX : X.IsCharacteristic p`, and
   `hY : Y.IsCharacteristic p`. I opened `SchemeCharacteristic`: the predicate
   says p is prime and p vanishes on every open. Using `hX.2 ⊤` as the argument
   to `iterateFrobenius` adds no hypothesis. Verdict: exact, including empty schemes.
3. An arbitrary morphism u from X to Y. Rendered by `(u : X ⟶ Y)` inside the
   naturality conjunct, with no property instance. Verdict: exact.
4. A finite commutative coefficient ring A. Rendered by
   `(A : Type u) [CommRing A] [Finite A]`. There is no field, nonzero-ring,
   characteristic, or prime-invertibility assumption on A. Verdict: exact.
5. The small pro-etale sites, their constant sheaves, module categories, and
   ordinary unbounded derived categories. Rendered by `X.ProEt`,
   `proEtaleConstantRing X A`, `proEtaleRingModules`, and
   `proEtaleDerivedCategory`, via the recorded dependency modules. I opened the
   actual category definitions: module values and lifted coefficients live in
   u+1, site objects in u+1 and site morphisms in u. This retains the small-site
   size convention rather than identifying the two site universes. Verdict: exact.
6. The canonical identification of inverse-image coefficients. The
   `proEtaleConstantRing*` operations use `proEtaleConstantRingComparison`, which
   is `asIso (proEtaleCoefficientInverseImageMap f A)`. I read the operations
   construction, its uniquely tensor-unit-normalized adjunction, and
   `finiteCoefficientInverseImageMap_constant`: the finite coefficient map is
   carried to precisely the constant-section-preserving map under the specified
   coefficient identifications. No freely chosen coefficient map occurs here.
   Verdict: the same coefficient identification as the node.
7. Absolute p-power Frobenius and all its iterates. Rendered by
   `X.iterateFrobenius hp (hX.2 ⊤) n`. I opened its upstream definition: it fixes
   the underlying space and raises sections to p^n. The nonnegative exponents
   of the node are represented by ℕ, including zero. Verdict: exact.
8. Canonical relative-Frobenius isomorphisms `(F_V^n,v)` for every weakly etale
   site object. Rendered by the existential family `r`, whose first conjunct
   specifies the first projection of every component to be the same iterated
   Frobenius on V. The second projection is fixed by the component being a
   morphism over X, namely V.hom. The pullback universal property therefore
   determines each component uniquely; natural isomorphism data is not arbitrary.
   `proEtaleBaseChange` is the existing `MorphismProperty.Over.pullback`.
   Verdict: exact, with the product order in that existing construction.
9. The trivialization induced by restriction along those r, taking its adjoint
   and then exact termwise derived descent. Rendered by the family `tau`, its
   sectionwise equation for the actual `proEtaleConstantRingAdjunction.unit`,
   and `proEtaleFrobeniusDerivedIso A (tau X hX n)`. The equation fixes the
   adjunct to restriction along `r.inv`, the inverse of the direct-image
   trivialization. The adjunction bijection fixes tau uniquely. I checked
   `proEtaleFrobeniusDerivedIso`: it is `mapDerivedCategoryNatIso` followed by
   `mapDerivedCategoryIdIso`, with no independent derived comparison choice.
   Verdict: exactly the prescribed construction and direction.
10. Agreement at b=1 with `lem-trf-absolute-frobenius-site`. Its recorded theorem
    uses exactly the same projection and unit normalizations and the same
    `proEtaleFrobeniusDerivedIso`. Their uniqueness identifies the witnesses.
    Its open-only naturality does not already provide this item's arbitrary-u
    assertion. Verdict: same canonical trivialization, no duplicate theorem.
11. Identity at exponent zero. The final conjunct fixes `r X hX 0` to the inverse
    of `MorphismProperty.Over.pullbackId`, transported through `F^0 = 𝟙 X`.
    The unit equation then fixes tau to the canonical identity-pullback
    identification, and its derived descent retains the derived identity
    comparison. Verdict: the identity clause is present, including u=id.
12. Canonical composition comparisons. The existential `comp` is fixed by its
    conjugate under the normalized module adjunctions: on every module, object,
    and section it is restriction along `Over.pullbackComp.hom`. I checked the
    direction against Mathlib's `conjugateIsoEquiv`: its first adjunction here
    is the composite, and it maps `comp : direct pullback ≅ composite pullback`
    to `composite direct image ≅ direct direct image`, as required. I also read
    `proEtaleCanonicalPullbackComposition_existsUnique` and its selected
    comparison: it uses the same section equation and normalized adjunctions.
    `proEtaleFrobeniusDerivedComp` is their exact termwise derived descent.
    The docstring's step 6 identifies this descent with the recorded canonical
    K-flat-normalized comparison by resolution and naturality. Verdict: the
    canonical c of the node, not an arbitrary isomorphism of those functors.
13. The commuting Frobenius square and its c_{u,b}. The first equality witness
    `w` is `F_X^b ≫ u = u ≫ F_Y^b`. The three initial arrows of the naturality
    equation are inverse comparison for `(u,F_Y^b)`, equality transport along
    `w.symm`, then comparison for `(F_X^b,u)`. Verdict: precisely the node's c,
    without assuming that the Frobenius square itself is Cartesian.
14. Equality `(tau_X Lu*) c = Lu* tau_Y` as natural transformations. The remaining
    left side is `whiskerLeft (Lu*) tau_X.hom` then the right unitor. The right
    side is `whiskerRight tau_Y.hom (Lu*)` then the left unitor. With Lean's
    composition order, both go from `L(F_Y^b)* ⋙ Lu*` to `Lu*`.
    Verdict: exact natural-transformation equality, not objectwise existence.
15. Addition of exponents at both X and Y. The second-to-last conjunct quantifies
    over every X and `a b : ℕ`. It transports `F^(a+b)` to `F^a ≫ F^b`, applies
    the canonical comparison, then `whiskerLeft (L(F^b)*) tau_a.hom`, the right
    unitor, and tau_b. This applies tau_a at `L(F^b)*(-)`, then tau_b, in exactly
    the stated order. Universality over X supplies both schemes of the node.
    Verdict: exact. The b-fold-iterate clause is its induction consequence with
    a=1, starting from the normalized zero case; it needs no further data.

The existential families precede the universal naturality and addition clauses.
Because the projections and section equations determine them uniquely, this is
an expression of the canonical construction; it does not permit choosing new
trivializations separately for each u. No hypothesis has been added or removed.
All seven recorded statement-dependency modules are publicly imported. Proof
imports cover the stated proof dependencies, including the Mathlib pullback,
adjunction and localization leaves and independent-coefficient K-flat resolution.
There is one named theorem with `sorry`, no new definition, no local notation,
no file-local instance, and no unbound universe or implicit object.
The docstring follows all six DAG proof steps, including the resolution argument
that identifies the two derived comparisons.

Edge cases: b=0 and either a or b zero are retained by the last conjunct and the
addition clause. Empty schemes have no nonempty-object premise, and no argument
assumes that distinct coefficients remain distinct on the empty object. The zero
coefficient ring and zero module are allowed. No hypothesis requires a nonzero
section or excludes a nonreduced scheme. All prime characteristics are allowed,
with no relation required between p and A. There is no index set in this theorem;
the empty-index issue does not arise. `u` is an arbitrary scheme universe, with
the existing u/u+1 site distinction preserved; a finite ring needs no independent
larger universe to express its elements. No universe equality was introduced.

Independent searches, using different wording from the first reader:

- LeanFinder via `msearch.py`: "Relative Frobenius on the small proetale site
  induces a natural identity isomorphism of derived inverse image compatible
  with arbitrary morphisms". Eight hits, including `Scheme.Modules.restrictFunctorId`,
  perfect-ring Frobenius equivalences, and free-module pullback comparisons;
  none is the assertion on the small pro-etale derived category.
- Loogle via `msearch.py`: `"Frobenius", "Iso"`. Five hits concern categorical
  Frobenius reciprocity and Witt-vector isocrystals, not this assertion.
- LeanSearch via `msearch.py`: "The natural identification of absolute Frobenius
  inverse image with the identity on derived proetale sheaves commutes with
  pullback along any scheme map". Eight hits concern ordinary module pullback,
  identity pullback and direct-image congruence; no match.
- `rg -i` for `frobenius.*(trivial|pullback|inverse.image)`,
  `trivial.*frobenius` and `relativefrobenius` in the upstream WeilConjectures,
  this project's `lean/Sheaf`, the shared pro-etale framework, and Mathlib's
  algebraic geometry directory. I inspected the plausible results: the existing
  `AbsoluteFrobeniusSite` gives open restriction, while upstream
  `GeometricFrobenius` compares geometric Galois Frobenius on geometric fibres,
  and `TraceFormula/Frobenius` uses geometric/model Frobenius and Weil complexes.
  Those are different objects or do not state arbitrary-u compatibility for
  this canonical absolute-Frobenius trivialization. Mathlib Sites has no
  Frobenius hit. The exact new declaration name has no upstream/Mathlib/names-map
  match. Consequently the module is retained, not replaced by `existing: true`.

Findings and changes: no mathematical mismatch, missing notion, unusable
statement dependency, or node correction was found. I repaired only the broken
line wrap inside the step-5 LaTeX expression, which had split `F_T` between `F`
and `_T`, and appended this independent reading. The theorem signature and node
record are unchanged and were checked textually equal after whitespace
normalization. No new nodes or dependency modules are delivered.

Validation: the prescribed `scompile.py` compiled the final source cleanly in
both sandbox and library contexts (2.7 s and 2.9 s). No errors or warnings were
reported. Server preflight and delivery use the prescribed `deliver2.py` wrapper.

# Stage-1 report: lem-trf-point-sections-finite-reduction

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-point-sections-finite-reduction.json` — statement node, split; no new nodes and no Mathlib leaf.
- `citations.json` — one verbatim statement quote for every cited node at every proof step.

Attachments: none. No finished declaration carrying the blueprint tag or the exact statement was found under `WeilConjectures/` in `/home/ubuntu/weil-src-slopmaster2`.

WANTED: none.

The reviewer-created item had an empty proof and was unsplit. I kept its statement and hypotheses exactly. The route in `prop-trf-adic-coefficient-morphism-systems.proof.md`, Proof (1), uses the reduction comparison for compact-support sections and geometric-point stalks. I checked the existing exact point-sections node and its source, the stronger all-small-colimits evaluation node, the K-flat resolution and derived change-of-rings nodes, the fixed-second-factor derived-tensor node, and the mixed-tensor K-flat invariance node. The proof now transports a simultaneous K-flat total-tensor computation through exact, colimit-preserving evaluation, then records resolution independence, naturality, unit, and successive-reduction coherence. The finite cohomological interval is retained as a hypothesis of the item; the comparison itself does not need finite generation of the individual cohomology modules. Edge cases `N=0`, `j=n`, and `j=1` are explicitly covered. No duplicate node or clause-restatement node was created.

## Review by NO

I read the item, `dag/units/sk-prop-trace-adic.json`, `dag/chapters/sec-trace-formula.json`, and the current blueprint proof file `literature/blueprint/main-20261015/blueprint/sec-trace-formula/sk-prop-trace-adic/prop-trf-adic-coefficient-morphism-systems.proof.md`. I also read the complete statements of every node cited in the five proof steps. Step 1 uses the exactness statement for sections over an algebraically closed point and the separate theorem that evaluation at a weakly contractible affine object preserves all small colimits; the algebraic-closure, affine-spectrum, pro-etale-site, and constant-sheaf definitions supply the point and coefficient identifications. Step 2 uses the K-flat resolution statement, the sheaf derived-change-of-rings interface, the one-point fixed-second-factor derived tensor interface, the total-complex and sheaf-tensor definitions, and all-small-colimits evaluation to identify the sheaf and module total tensors. Step 3 uses the mixed-tensor K-flat quasi-isomorphism statement, the canonical resolution-independence clauses of both derived-tensor interfaces, exactness of sections, and the derived-category localization for naturality through roofs. Step 4 uses the functorial and associative clauses of the two derived-tensor interfaces and the derived-category framework to check the identity case and compatibility for `A_n -> A_j -> A_i`. Step 5 checks the zero object, endpoint reductions, and the fact that no extra finite-generation hypothesis is used.

I checked every `uses` entry against its node statement and copied a literal statement prefix into `citations.json` for each citation. `proof_deps` is the union of all step uses. The item blueprint ancestor and proof location are unchanged and the split report records the generic off-unit tool uses. Mathlib searches were run for the item with LeanFinder, Loogle, grep, and LeanSearch; the unavailable/empty and irrelevant results are retained in the sandbox search log. No Lean source, compiler, Lake, or build tool was run.

## Worker report

The module defines the canonical finite coefficient ring sheaf, quotient map, ordinary derived tensor, sheaf derived reduction, and exact derived point-sections functor. The theorem states the comparison in `D(A_j)` for every bounded-above object `N`; the bounded-above hypothesis is rendered by `∃ b, ∀ q, b < q → IsZero (H^q N)`. The source hypotheses are `k` algebraically closed, `l` prime and invertible in `k`, and `E/ℚ_l` finite-dimensional. The target is the natural point-sections/reduction isomorphism at the object level. All definitions have real constructions and all postponed proofs are `sorry` only in the theorem.

Dependencies used are the recorded point-sections exactness, constant sheaf, derived category, derived change-of-rings, derived tensor, and coefficient-extension declarations. Edge cases `n=j`, `j=1`, zero `N`, and empty cohomology are covered by the quantifiers; `n=0` is excluded by the node's `i≥1` convention. Searches in the inherited `searches.jsonl` found no Mathlib or upstream declaration of this comparison.

## Second reading by NO

I opened the node, the blueprint Proof (1), and the source declarations for every dependency. The Lean binders render the algebraically closed field, the invertible prime, the finite extension and its valuation-ring quotients, the small pro-etale site, the final-object sections functor, the inequalities `n≥j≥1`, and the bounded-above derived input. The ring sheaf is Mathlib's `constantSheaf`; the quotient is the canonical ideal factor map; the left derived tensor is the recorded K-flat derived-tensor functor; and the right side is the recorded derived change-of-rings followed by exact point sections. The theorem's `Nonempty` is an object-level isomorphism in `D(A_j)`, so it retains the quotient coefficient action.

The original stage-1 statement was corrected from bounded to bounded-above, as required for successive reductions: over `A_2`, reduction of the residue object has nonzero negative Tor in every degree. I preserved that corrected hypothesis. No extra Noetherian, constructibility, finite-Tor, or finite-generation hypothesis was added. The edge cases `j=n`, `j=1`, zero objects, and all positive indices remain admitted. The searches found no duplicate notion in Mathlib, slopmaster2, or `lean/Sheaf`; the integral analogue is specialized to completed integral coefficients and is not this node.

The only implementation mismatch found was universe inference for the independent-coefficient derived category and exact scalar restriction. I repaired it by supplying the canonical `u+1` coefficient/site universes, the standard small-site sheafification and W-equals-locally-bijective instances, and the exact finite-limit/colimit instances from `point_proEtale_sections_exact`. No mathematical clause was changed.

### Resumed second reading (2026-10-17)

The earlier second-reading text is retained above. Its assertion that the only mismatch
was universe inference is superseded by this reading: the retained theorem was only
`Nonempty` of an objectwise isomorphism and omitted the naturality, unit, and successive
reduction clauses of the current node. The initial required dry run also diagnosed that
`lean.statement` retained the trailing `:=`, whereas preflight compares the signature
without it. I repaired the Lean and its record, without changing the node's mathematical
statement, dependencies, proof, source, or any unit statement.

I read the current node's eight-step proof and all eight statement dependencies, including
their source signatures, rather than relying on the older five-step stage-1 report. The
source is `main-20261015/.../prop-trf-adic-coefficient-morphism-systems.proof.md`, Proof (1).
Its compact-support and geometric-stalk reductions require the comparison to retain the
quotient coefficient action. I also read Stacks `sites-modules.tex`, constant-sheaf section
(093J and the finitely-presented tensor and flat-sections lemmas),
`sites-cohomology.tex`, derived-base-change lemma (06YY), `more-algebra.tex`, derived
change-of-rings section and lemma (06Y6), and the point criterion in `proetale.tex` (0982).
No extra Noetherian, finite-generation, finite-Tor, or constructibility hypothesis occurs
in those source statements for the comparison proved here.

The complete object/hypothesis/conclusion list and matching verdicts are:

1. **Algebraically closed field kappa.** The section variables `(k : Type u) [Field k]`
   and `[IsAlgClosed k]` are captured by `point_sections_finite_reduction`. This is an
   arbitrary algebraically closed field, not only the algebraic closure of a finite
   field. Verdict: exact.
2. **t = Spec kappa and its small pro-etale site.** `Spec (.of k)` and
   `Scheme.ProEt.topology (Spec (.of k))` are the site in the recorded
   `Scheme.proEtaleDerivedCategory` declaration. `pointFiniteReductionSheaves` is an
   abbreviation for its actual `SheafOfModules` category. Verdict: same site and category.
3. **Final-object sections on derived categories.** The retained `pointFiniteSections`
   evaluates at `op (ProEt.mk (𝟙 (Spec (.of k))))`, then restricts scalars along the
   actual `pointConstantSectionMap`. `pointFiniteReductionSections` is its
   `mapDerivedCategory`; the two exactness instances are projections of
   `point_proEtale_sections_exact`. Verdict: the specified functor and coefficient action.
4. **Prime l invertible in kappa.** `(l : ℕ) [Fact l.Prime]` and
   `(_hl : IsUnit (l : k))` occur in the theorem's context/signature. There is no fixed
   characteristic or additional characteristic-zero assumption on kappa. Verdict: exact.
5. **Finite extension E/Q_l, valuation ring, chosen uniformizer, and A_i.**
   `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]` supplies the
   recorded `Padic.coefficientExtensionRing l E i`; its real construction is the
   quotient by the power of the chosen uniformizer ideal. The current dependency record
   points to `CoefficientExtensionFinite`, which imports these constructions unchanged.
   The module now imports that recorded interface. Verdict: exact coefficient data.
6. **Constant ring sheaves and the quotient maps.** `pointFiniteReductionRingSheaf`
   specializes Mathlib `constantSheaf`; `pointFiniteReductionRingMap` is
   `RingHom.ulift (Ideal.Quotient.factor (Ideal.pow_le_pow_right h))` and
   `pointFiniteReductionSheafMap` is its constant-sheaf image. The canonical constant
   section map supplies the identification Gamma(t,(A_i)_t)=A_i through restriction of
   scalars; no arbitrary ring identification is chosen. Verdict: exact constructions.
7. **Derived categories and the two reductions.** The source is
   `DerivedCategory (pointFiniteReductionSheaves k l E n)`; the output is
   `DerivedCategory (pointFiniteReductionModules l E j)`. Ordinary reduction uses the
   recorded `exists_derivedTensor_second_factor_functor` at the quotient ring in degree
   zero. Sheaf reduction uses the recorded
   `derivedChangeOfRingsIndependentCoefficients`. Their actual universal computation
   counits are exposed and retained with those same choices. Verdict: reduction over
   A_n with target action by A_j, without forgetting that action.
8. **n >= j >= 1 and bounded-above N.** The family quantifies `(n j : ℕ)`,
   `(hn : 1 ≤ n)`, `(hj : 1 ≤ j)`, and `(hjn : j ≤ n)`. Its domain is Mathlib's
   canonical t-structure `minus` full subcategory, specialized by
   `pointFiniteReductionBoundedAbove`; `DerivedCategory.isLE_iff` identifies this with
   the node's eventual positive-degree cohomology vanishing. Bounds vary with N.
   The theorem also states bounded-above preservation for both reductions. Verdict:
   exactly the corrected, already-landed stage-1 domain, including unbounded negative Tor.
9. **Isomorphism natural in N.** The conclusion now supplies one family `e` of natural
   isomorphisms between the two functors on the entire bounded-above full subcategory.
   Naturality includes every derived morphism, not only maps of chosen representatives.
   Flatness and termwise bounds appear only in the subsequent representative
   specification, not as additional assumptions on N. Verdict: repaired H3.
10. **Unit and successive-reduction compatibility.** These clauses are rendered by the
    canonical representative specification, rather than by unspecified associator
    witnesses. For every bounded-above flat P, the chain isomorphism q sends the actual
    mixed-tensor generator `b tensor (c tensor x)` to `(b*c)` times the image of x under
    the actual quotient/sheafification unit. The final equation identifies this q with
    the component of e using both universal derived-tensor counits and the exact-section
    localization comparisons. This fixes the descended comparison on every flat model.
    For j=n the ring factor is the identity and that generator equation is the usual
    tensor unit map. For n>=j>=i, use P and its flat reduced model P_j: the two routes,
    under the tensor associator `((x tensor b) tensor c) -> x tensor bc`, have the same
    value on every generator, hence the same chain map and the same derived morphism.
    Naturality and the counit normalization transport those equalities to every N.
    This is the canonical, equivalent representative formulation of both coherence
    clauses in proof steps 7-8. Verdict: repaired H3; no arbitrary map or mere
    Nonempty isomorphism replaces the canonical comparison.

I checked the edge cases. Zero objects and shifts lie in the full bounded-above domain;
no lower bound is imposed. `j=n`, `j=1`, and `n=j=i=1` remain included, as do the identity
stages of successive reductions. `n=0` is excluded exactly by the node's positive-index
convention; the coefficient helpers still make sense at zero. An empty scheme is not an
input of the node, since Spec of a field is nonempty; empty objects of its small site
remain present, and Mathlib's actual sheafification enforces their zero sections. There
is no nonempty index assumption on the total-complex coproducts. The source's common
ambient universe is u; the site retains object universe u+1 and morphism universe u,
and coefficients/modules use the standard u+1 lift. All smallness and sheafification
instances are constructed, not assumed. I did not force the two site universes equal.

Independent searches used different wording from the author's searches:

- LeanFinder: `Derived scalar extension global sections quotient ring natural
  isomorphism` returned eight cotangent-complex/differential results, no comparison.
- Loogle: `"extendScalarsComp"` found the actual ordinary-module associator and its
  tensor-generator formula; it does not state the point-sections comparison.
- LeanSearch: `Sections at an algebraically closed point commute with derived scalar
  extension along a finite quotient ring` returned eight scalar-tower and affine-stalk
  declarations, none with this statement.
- `rg` in Mathlib, slopmaster2 `WeilConjectures`, and the project's `lean/Sheaf` searched
  `globalSections.*(tensor|quotient)`, the reverse word order, and
  `sections.*(changeOfRings|extensionOfScalars)`, as well as point/reduction names.
  I opened `PointSectionsDerivedReduction`, `PointInverseEvaluationKFlat`,
  `CompactSupportCoefficientChange`, and the current dependency modules. The first
  comparison is integral-to-finite on the finite-field datum and constructible domain;
  the second is Zariski evaluation on a one-point ringed space; the third is compact
  support with constructibility and finite-Tor conditions. None is this comparison on
  the small pro-etale site of an arbitrary algebraically closed point for every
  bounded-above object. Existing tensor, constant-sheaf, t-structure-minus, and exact
  derived-functor notions are reused, not copied.

Other repairs: added the missing source/blueprint docstrings for the exactness instances;
expanded the theorem docstring to all eight current proof steps and imported the stated
proof interfaces; fixed coefficient/sheafification universe inference using the canonical
small-site instances; and shared the typed computation helpers to avoid expensive repeated
unfolding. The full file then compiled in about 24 seconds, within the unchanged 60-second
wall limit. The only remaining diagnostic was the comment requirement for a scoped
heartbeat setting; that explanatory comment has now been added. The single postponed
proof is `WeilConjectures.point_sections_finite_reduction`. Every helper has real data,
including the literal tensor generator and the actual sheafification-unit section.
There are no new DAG nodes and no dependency modules in this delivery.

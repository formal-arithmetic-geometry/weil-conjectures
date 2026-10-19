## Worker report

The delivery states `SheafOfModules.systemLevelLeftExtensionTheory` in
`Sheaf.CategoryTheory.SystemLevelLeftExtension`. Its conclusion is a simultaneous
family of the constructions for arbitrary inverse sequences of commutative ring
sheaves on the fixed site. This family formulation permits comparison of a sequence,
a selected subsequence, and a twice selected subsequence in the same conclusion.
It does not assume their functors or adjunctions. Every theorem has proof `sorry`;
all construction data are explicit. All 48 named declarations are recorded.

Source read: Zheng, *Six Operations and Lefschetz--Verdier*, Construction 4.1,
printed p. 21, including the paragraph defining the evaluation geometric morphism,
its ordinary module left adjoint, its evaluated tensor/zero formula, and the
unbounded-derived adjoint pairs. Also read the current blueprint's
`sec-six-functors-basics/sk-prop-a1-kummer/def-weil-exceptional-inverse-image.md`,
particularly the integral-stage paragraph before inverse limits. The node supplies
the general coefficient and subsequence construction extending that source. Its
thirteen current ordinary-derived proof steps are transcribed completely into the
main theorem's docstring, with their dependency citations. The resolved repair note
was read: no flat-model, section-model, infinity-categorical, or dg Quillen
machinery is used in this statement or its proof plan.

Hypothesis and clause correspondence:

1. The small site is `C : Type u`, `[Category.{v} C]`,
   `J : GrothendieckTopology C`, `[EssentiallySmall.{w} C]`. The usual sheafification,
   locally-bijective, and ring-forgetful sheaf-composition instances are explicit.
   These are the existing infrastructure for module sheaves on a site small
   relative to the coefficient universe, rather than additional geometric
   hypotheses. Object universe `u`, morphism universe `v`, and coefficient universe
   `w` remain independent. No equality of these universes is imposed.
2. The inverse sequence is arbitrary
   `B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}`. The Lean index `n` is positive level `n+1`.
   Its actual iterated ring map is `B.map (homOfLE h).op` for `h : m ≤ n`.
3. The category `S(B)` is the constructed `StrictRingSystem B`.
   `systemLevel B n` is the recorded `ringedSiteModules` over the actual `B_n`.
   Its `transition h` is a `B_n`-linear map to `systemRestriction B h` of level m.
   `identity` and `compose` fix the iterated maps on every section. Specifying
   these is equivalent to specifying just successive transitions: composition
   determines every finite iterate uniquely, and conversely the iterates give
   these laws. `StrictRingSystem.Hom.app` and `.comm` give precisely the commuting
   componentwise linear morphisms, and category operations are componentwise.
4. The abelian structure is the uniquely normalized componentwise structure in
   `strictRingSystem_abelian_exists`; its normalization requires additive actual
   evaluations. Choosing this structure uses unique data, not a mere existence
   assertion about an unspecified abelian structure. All other proof-dependent
   constructions refer to separately named theorem declarations. The final
   `grothendieck` field is `IsGrothendieckAbelian.{w} (StrictRingSystem B)`.
5. Ordinary coproducts are `coproducts` and `evaluationCoproducts`; their index is
   **any** `I : Type w`, including the empty type. Derived coproducts are
   `derivedCoproducts`, `levelDerivedCoproducts`, and
   `derivedEvaluationCoproducts`, with exactly the same arbitrary indexing size.
   `cohomology` is a natural isomorphism
   `H^q ⋙ systemEvaluation B n ≅ derivedSystemEvaluation B n ⋙ H^q`.
   Inserting a complex by `DerivedCategory.Q` gives the componentwise cohomology
   assertion for complexes too.
6. `systemEvaluation_exact` supplies additivity, finite-limit and finite-colimit
   preservation of actual evaluation. `derivedSystemEvaluation` is precisely its
   `mapDerivedCategory`, with Mathlib's canonical factorization on complexes,
   shift structure and triangulatedness. `detectsIso` is the biconditional for
   every morphism, and `detectsBounds` gives both `IsGE q` and `IsLE q` iff the
   same bound q holds at **every** level. Bounds are not allowed to vary with n.
7. `single B n` is a `SystemDerivedLeftExtension` of actual evaluation.
   Its `ordinaryAdj` is the ordinary left-extension universal property;
   `derived`, `comparison`, `universal`, and `pointwise` assert the total,
   everywhere-defined left derived functor. `computes` identifies its comparison
   on flat-term K-flat complexes. `shift` and `triangulated` assert exactness.
   `adjunction` is the actual derived adjunction with evaluation and therefore
   contains natural units/counits and both triangle identities.
8. `singleBelow` and `singleAbove` give the ordinary tensor and zero formulas.
   `singleDerivedBelow` is the natural functor isomorphism to the recorded
   derived tensor for m ≤ n; `singleDerivedAbove` asserts the zero object at
   m > n. `singleTranspose` and `singleDerivedTranspose` fix those identifications
   by the tensor Hom correspondence and the actual system transition, rather
   than permitting unrelated chosen isomorphisms at each object.
9. The strictly increasing unbounded sequence is `r : ℕ ↪o ℕ`. This is exactly
   a strictly increasing map of naturals; it is automatically unbounded because
   `r.strictMono.id_le m` gives m ≤ r m. Shifting all indices by one gives the
   node's positive-integer convention, without losing any sequence.
   `selectedSystemRings B r` composes the actual ring diagram with r.
   `systemSubsequence B r` explicitly selects its levels, transitions and maps;
   `systemSubsequence_exact` states its exactness. `derivedSystemSubsequence`
   is its actual exact derived functor.
10. `systemNextSelected r m` is `Nat.find` applied to the proved nonempty set of
    indices i with m ≤ r i. `systemNextSelected_spec` states both the bound and
    minimality; `systemNextSelected_mono` gives a ≤ b. No arbitrary selection is
    substituted for this minimum.
11. `selected B r` is a total left derived strict-system extension, with its
    ordinary and derived adjunctions to these actual restrictions.
    `selectedBelow` and `selectedDerivedBelow` state the natural formula at m as
    evaluation at `systemNextSelected r m` followed by the appropriate ordinary
    or derived tensor. `selectedEvaluation_rep` fixes the restriction/evaluation
    comparison on actual complexes; `selectedTranspose` and
    `selectedDerivedTranspose` fix the evaluation identifications by the actual
    adjunctions and actual transition from r(t(m)) to m.
12. `transition` is a natural transformation of the actual derived evaluation
    functors. `transition_rep` pins it to `strictSystemTransition` on every
    strict complex, under the exact-localization comparisons.
    `selectedTransition` is precisely the displayed adjoint transition formula:
    transpose the transition m+1 → m; tensor the identification at m+1; use the
    associator through r(b); invert the associator through r(a); tensor the
    adjoint of N's actual selected transition b → a; and invert the evaluation
    identification at m. The source is the tensor over B_(m+1), and its target
    is evaluation at m, exactly as in the node. `transition_identity` identifies
    the adjunct of the identity transition with the canonical tensor unit, so
    the case a=b uses the identity under that unit; the case a<b uses the
    specified iterated transition. The variable N is an object of the ordinary
    derived category of strict systems throughout.
13. `scalar` uses the dependency's `DerivedChangeOfRingsCochainModel` for every
    actual coefficient map, fixing the ordinary E on both objects and maps,
    its universal derived pair, K-flat comparison and exactness.
    `SystemScalarModel.unit_normalized` fixes ordinary adjunctions on local
    `1 ⊗ x`; `.transpose` fixes their derived adjunctions by the same universal
    comparisons. `tensor.ordinaryAssoc` is fixed on nested local pure tensors
    by `(c ⊗ (d ⊗ x)) ↦ (c * image(d)) ⊗ x`; `derivedAssoc_rep` fixes the derived
    associator by these chain-level associators on flat-term K-flat models.
    The corresponding ordinary and derived tensor units are also normalized.
14. `restrictionComposition` has its canonical representative normalization in
    `restrictionComposition_rep`. `extensionComposition` compares the composite
    left extension to the extension for `s.trans r`, i.e. r ∘ s.
    `composition_mate` equates the direct Hom bijection with the composite Hom
    bijection followed by the actual restriction comparison. Thus it is the
    uniquely determined adjunction-preserving comparison, including its unit
    and counit identifications on all derived morphisms. Combined with the
    normalized evaluation transposes and tensor associators above, it expresses
    their compatibility with subsequence composition. For three selections both
    paths transpose to the same composite unit, so no arbitrary coherence is
    hidden in the comparison. Identity selections are covered by the same
    normalized constructions.
15. The structures are conclusions of `systemLevelLeftExtensionTheory`, with
    no normalization, ring-map flatness, Tor-amplitude or cohomological-bound
    hypothesis on any system or sequence. Left-extension universal properties
    are ordinary `Adjunction`s and ordinary localization universal properties.
    There is no replacement by a diagram of independently derived objects.

Dependency declarations read and used:

- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q`, and the standard localization from
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`. The selected standard
  localizations are at sufficiently large sizes; no small Hom universe is
  imposed on an unbounded category.
- `def-sp-grothendieck-abelian`: `CategoryTheory.IsGrothendieckAbelian` from
  `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`.
- `lem-pur-derived-change-of-rings`: the recorded
  `SheafOfModules.DerivedChangeOfRingsCochainModel` from
  `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`. Its full source and
  docstring were read, including its independent localization sizes and cochain
  counit. Its `E`, object/map equations, `T`, universal counit and K-flat
  computation are reused, rather than copying any tensor or derived functor.
- `def-weil-pbc-sites-and-cohomology`: import
  `Sheaf.CategoryTheory.SiteCoveringAxioms`; the site is used in its
  `GrothendieckTopology`/`Sheaf` encoding, as retained by that interface.
- `def-weil-sheaf-of-modules-category`:
  `CategoryTheory.ringedSiteModules` from
  `Sheaf.CategoryTheory.RingedSiteModules`, transparently Mathlib's module sheaves.
- `def-pc-sheaf-restrict-scalars`: `SheafOfModules.restrictScalars` from
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`, read together with
  the presheaf construction. Restriction preserves the underlying sections and
  restricts only their scalar action.

Every recorded statement-dependency module and each available proof-dependency
module is imported; proof-only imports are non-public. The theorem docstring
retains all thirteen proof steps and their actual node citations.

Edge cases checked against the definitions and formulas: the first positive
level (Lean 0); m=n and m>n; zero modules and zero complexes; the zero coefficient
ring; empty sites; arbitrary empty coproducts; unbounded complexes; the identity
selection; selections with gaps and the initial interval before r(0); successive
m with the same t(m); and three successive selections. A composite selection is
`s.trans r`, so its object map is r(s(i)), in the required order. The identity
transition clause deals with a=b; it is not excluded by an inequality hypothesis.
Both lower and upper bounds have a single common q. The only choices used in
definitions concern uniquely determined normalized abelian structure; the
existence package is a theorem and is not used to manufacture unspecified data.

Searches actually run (logged by the prescribed launcher search wrapper):

- LeanFinder: `Derived category of strict semilinear inverse systems of sheaves
  of modules evaluation left adjoint extension by zero and subsequence left Kan
  extension`. Eight hits, including condensed-solid and Kan-extension results;
  none is this construction.
- Loogle: `SheafOfModules.restrictScalars, Functor.LeftDerived, Adjunction`.
  Zero hits; the service reported unknown identifier `Functor.LeftDerived`.
  This is recorded as an unsuccessful query, not evidence that the valid
  scalar-restriction API is absent; that API was read directly in Mathlib.
- Mathlib grep via msearch: `SemilinearSystem|StrictSystem|systemLevelLeft|CoefficientTower`.
  Zero hits.
- LeanSearch: `strict semilinear inverse systems module sheaves left adjoint
  evaluation derived category`. Eight hits, including module-sheaf scalar
  adjunctions and section evaluation; none states the node.
- Direct rg in the upstream source and `lean/Sheaf` for strict systems,
  semilinear systems, coefficient towers, and the proposed declaration names;
  plus the exact-node-id grep in upstream and the upstream-name index.
  No exact arbitrary-ring-sequence declaration. The existing
  `CoefficientEvaluationDerivedLeftAdjoint` was opened: its `CoefficientSystem`
  and associated package require constant sheaves of O/(ell^(n+1)), so cannot
  receive an arbitrary B. `CoefficientRingedSequenceSite` supplies the particular
  pro-etale coefficient tower, not arbitrary B. Neither was copied or imported.
- DAG grep found the existing specialized coefficient-system and sequence-site
  nodes. `tools/blueprint_refs.py search 'strict semilinear'` returned zero
  blueprint matches. No separate independent missing notion is introduced:
  this module constructs the strict-system notion and left-extension interfaces
  that the item's own statement explicitly defines. No new node or dependency
  repair is needed.

No statement correction, disputed statement, or source fault was found. The original
packet changed only `lean`; this returned repair additionally removes the four
obsolete `tool_uses` entries explicitly named by the maintainer.

## Second reading by NH

This is the author's second pass; as the direct-delivery brief specifies, the
maintainer supplies the independent review. I re-read the node alongside the
final package, with particular attention to every boundary case and formula.
The comparison above matches all its hypotheses and clauses. The two technical
mismatches found during construction were repaired before delivery: the system
Hom's sequence parameter had to be implicit for componentwise composition, and
all quantified coefficient diagrams in the final package needed explicit site
annotations to prevent a second inferred site. Compilation now checks both the
sandbox and the named library module using the required wrapper. Other compiler
repairs fixed a wrong import path, a shadowed identity function, and term syntax;
they changed none of the mathematical statements. All universes and variables
are declared, and every auxiliary construction's source is documented.

## Returned route-metadata repair

The returned review identified four obsolete maintainer-side route entries. I removed
`lem-coef-sheaf-flat-model`, `lem-coef-quillen-section-rectification`,
`lem-coef-dg-derived-quillen-calculus`, and `lem-coef-pointed-model-stability` from
the item's `tool_uses`. They are absent from the proof steps, `proof_deps`, and
`split_report.tool_uses`; the ordinary-derived route retained above uses only the
remaining generic foundations. The Lean module and statement are unchanged.

## Delivery-wrapper failure

On 2026-10-18, the repaired packet compiled in both sandbox and library paths and
passed the prescribed dry run at `bca4c655c8`. However, the wrapper printed:

> note: lem-pur-system-level-left-extension: these fields differed in your copy and were NOT delivered (not yours to change): ['tool_uses']

The required metadata removal is therefore absent from the generated delivery.
Reading `deliver2.py` confirms that it copies only the stage-2 owned fields from
the sandbox and retains the base's top-level `tool_uses`. A subsequent delivery
was interrupted during server preflight before pushing, to avoid resubmitting
the rejected metadata. The prescribed wrapper needs an authorized repair path
for this specific maintainer-requested metadata change; no tool or shared source
was edited. The corrected sandbox node and unchanged Lean module are retained.

## Repair retry, 2026-10-18

Retained the saved packet and ran the prescribed `deliver2.py NH
lem-pur-system-level-left-extension --no-push` against the current fetched base.
The completed dry run exited 0 at commit `05fd02fa93`, compiled both sandbox and
library forms, and printed:

> note: lem-pur-system-level-left-extension: these fields differed in your copy and were NOT delivered (not yours to change): ['tool_uses']
> OK (dry run): commit 05fd02fa93 passes the preflight and compiles; nothing pushed

The sandbox node has no occurrence of the four returned machinery ids in its
`tool_uses`; that field equals the nine accepted `split_report.tool_uses` node
ids. Its only deltas from the read-only shared node are `lean` and `tool_uses`.
The recorded primary signature matches the Lean file, auto-implicit variables
are disabled, and its maximum line width is 100. No Lean statement or proof
plan was changed during this retry.

The fresh dry run confirms a delivery-tool failure: `deliver2.py` permits
`lean` and `stmt_deps` for an unchanged stage-2 statement, but neither copies the
explicitly requested `tool_uses` repair nor provides an option to do so. Thus
the generated packet retains exactly the rejected metadata. The saved Lean
packet passes compilation and preflight, but pushing it would repeat the
maintainer's return. No tool or shared file was edited, no bypass was attempted,
and the invalid packet was not pushed. The wrapper needs a scoped way to carry
this maintainer-requested metadata repair before delivery can complete.

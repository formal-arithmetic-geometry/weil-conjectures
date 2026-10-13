## What changed

Repair of reviewer X-a9a3d, head a9a3da850, E2 review point 4.
In `Sheaf.AlgebraicGeometry.CohomologySectionLocalizationGluingAux`, corrected
`AlgebraicGeometry.Scheme.Modules.localized_middle_comparison_bijective`:
inserted the canonical fraction formula `hc` immediately after `c`, and
replaced the vacuous `h_locUV` predicate `True` with the intersection fraction
formula requested in the return. The docstring now supplies the source and
complete natural-language proof: uniqueness on fractions, identification
with the diagram and local equivalences, degree-zero left exactness, and the
positive-degree five lemma. The historical counterexample remains recorded.

Adapted the sole caller in
`Sheaf.AlgebraicGeometry.CohomologySectionLocalizationGluing`: pass `hc` and
the full `h_locUV` instead of discarding the formulas. Its existing statement,
universes and visibility are unchanged. No imports or definitions changed.
Updated the auxiliary node's `lean.statement` and proof plan and the change
record's Reason, New and Users. The abstract node statement already describes
the canonical diagram comparison; its text and statement dependencies stay.

## Proved and sorry left

Zero of the item's one original holes is closed; zero holes are added.
The sole remaining named `sorry` is
`AlgebraicGeometry.Scheme.Modules.localized_middle_comparison_bijective`
(node `lem-sc-invert-s-cohomology-gluing-aux`). It now has the corrected
interface and complete proof in words, but is not claimed as a Lean proof.
The caller `AlgebraicGeometry.Scheme.Modules.cohomologyFractionPresentation_gluing`
has a complete adapted proof from that intermediate theorem; it was already
proved and does not count as an additional hole closed. This is an interface
repair, not a proof or decomposition. Both delivered modules compile cleanly.

The earlier proposed helper holes
`localized_middle_comparison_injective` and
`localized_middle_comparison_surjective` remain withdrawn, together with their
modules and nodes. They never landed; their removal closes no baseline holes.

## No longer needed

No baseline import, node or module is pruned by this repair.
The discarded intersection-formula-to-True proof fragment is removed.
The previously withdrawn helper modules
`Sheaf.AlgebraicGeometry.localized_middle_comparison_injective` and
`Sheaf.AlgebraicGeometry.localized_middle_comparison_surjective` and nodes
`lem-sc-invert-s-cohomology-gluing-aux-injective` and
`lem-sc-invert-s-cohomology-gluing-aux-surjective` remain absent.
The existing plain `Sheaf.Paper.LocalizedCohomologyMayerVietoris` import stays
for the documented intended proof. The unit realization route is unchanged.

## Where the brief, the DAG or earlier work was wrong

Historical STATEMENT-DISPUTED counterexample: for a nonzero field k, take
X = Spec k, U = V = S = top, L = F = O and s = 1. The former compactness,
affine, nonvanishing and local equivalence premises held for c W p = 0.
In degree zero both groups are k; the asserted bijection was the zero map
k to k, which is neither injective nor surjective. The false injective and
surjective decomposition inherited this counterexample and was withdrawn.
The previous binder-name repair did not fix the false proposition.

The corrected `hc` prevents this example: at degree zero and numerator degree
zero the formula forces the comparison of each fraction to be its restricted
numerator. Multiplication by the section is invertible on S, so more generally
the formula uniquely determines the comparison. Restoring the intersection
formula also identifies its local equivalence with the same comparison.
The caller already possessed both formulas; its old proof discarded them.
No false helper theorem or arbitrary-map claim is retained.

## Forced adaptations

Adapted module:
`Sheaf.AlgebraicGeometry.CohomologySectionLocalizationGluing` (unclaimed).
Only original lines 108–112 changed, to the two-line exact application
passing `c hc h_locU h_locV h_locUV`. Every existing signature and visibility
is identical, confirmed by the delivery declaration parser.

Counterfactual compilation of the original caller against the corrected
auxiliary failed, exit 1, with this primary compiler error:

```text
CohomologySectionLocalizationGluing.lean:109:6: error: Application type mismatch:
The argument h_locU has type ∀ p, ∃ e, ...
but is expected to have type ∀ (W : X.Opens) (p n : ℕ) (ξ : ...), ...
in the application
localized_middle_comparison_bijective X L s F S hS₀ U V hU hV c h_locU
```

The old trailing fragment also yields a type mismatch at line 112 and an
unsolved h_locUV goal. The adapted caller compiles, exit 0. The insertion of
hc forces the application change, and the restored intersection formula
forces forwarding h_locUV instead of replacing its proof by trivial.
The change record is
`coord/changes/localized_middle_comparison_bijective.md`.

## New nodes

None. Updated the existing auxiliary node's recorded Lean signature and
four-step proof plan; its proof dependencies and source route remain.

## Earlier second reading (a previous round; superseded)

The earlier second reading is superseded by reviewer X-a9a3d's E2 point 4:
it approved retaining the disputed arbitrary-c interface, which was still
false. This repair corrects the interface and adapts the sole caller as the
return explicitly requests. It preserves the historical counterexample,
withdrawn-helper history and honest zero-hole accounting.

Repair evidence recorded by the current worker for the independent second
reader: the complete corrected auxiliary and adapted caller compile; the
original caller fails against the corrected signature at line 109; its
signature and visibility are unchanged; the node matches the corrected
signature; the docstring and node describe canonical-map uniqueness, local
identification and both degree cases. The corrected theorem remains the sole
named hole. This section updates the old reading's status and does not claim
that an independent second reading of this repair has already occurred.


## Second reading by P4

1. Compared both delivered modules with the repository using diff and the declaration
   parser. The only changed signature is localized_middle_comparison_bijective:
   hc is added and h_locUV's True is replaced by the canonical fraction formula,
   exactly as declared in the change record. No definition, target statement,
   caller signature, universe or visibility changes. Independently compiled the
   repository's original caller against the delivered overlay: it fails at line
   109 because h_locU is supplied where hc is now required, and at line 112.
   The two-line replacement passes precisely the already available formulas.
   Verdict: authorized interface repair and necessary, minimal forced adaptation.

2. Independently compiled both delivered modules in import order (exit 0).
   Scratch copies with #print axioms for both declarations report only propext,
   Classical.choice, Quot.sound and sorryAx. The auxiliary still has its one
   whole-proof named sorry; the caller has none. There are no new declarations,
   definitions or prohibited trust mechanisms. Verdict: compilable repair,
   explicitly not a completed proof; zero holes closed and zero holes added.

3. No statements were split off and no new nodes or helper modules remain.
   Read the corrected auxiliary, the explicit direct-sum quotient presentation,
   the comparison/section-division interfaces and the Mayer--Vietoris diagram.
   Multiplication on W intersect S is invertible; applying its injectivity to
   hc and to the local fraction formulas identifies the comparisons on each
   generator. Quotient and direct-sum induction extend equality to all elements.
   Tested the former Spec k, s=1, degree-zero case: hc forces restriction on
   generators and excludes the zero comparison. For s=0, S is empty; positive
   transition powers kill the fraction generators and both groups are zero.
   Empty opens, U=V and degree zero likewise introduce no missing hypothesis.
   Read Stacks Tag 09MR's Mayer--Vietoris paragraph directly at
   https://stacks.math.columbia.edu/tag/09MR. Its canonical-map gluing argument
   agrees with the corrected claim. Verdict: the repaired statement is true;
   its mathematical argument is supplied, but its Lean proof remains open.

4. Searched again using grep, Loogle and LeanFinder with different queries,
   and searched the project sources for comparison uniqueness and fraction
   extensionality. Mathlib.Algebra.FiveLemma already supplies
   AddMonoidHom.bijective_of_bijective_of_injective_of_left_exact and
   AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective.
   These perform the final degree-zero and positive-degree diagram chases;
   they do not supply the canonical-comparison identifications or an immediate
   proof of this scheme statement. The existing private fraction_addHom_ext in
   CohomologyFractionMayerVietorisSquares confirms the generator argument.
   No new helper is necessary for this repair. Both public auxiliary imports
   serve the signature; the Mayer--Vietoris import is plain and retained for
   the stated intended proof. No baseline dependency or import was removed,
   so No longer needed is complete. Read sk-thm-curveestimate.json: its
   realized statement is thm-sc-proper-cohomology and it has no realized steps;
   this delivery alters neither the unit record nor its route. Verdict: no
   unsupported pruning or bypass, and no claim to have closed the open proof.

5. Checked the auxiliary node's lean.statement against the raw Lean signature:
   byte-for-byte equality. Its four proof steps give canonical-map uniqueness,
   local/product bijectivity, the degree-zero left-exact chase, and the
   positive-degree five lemma. proof_deps and proof_origin retain the diagram
   and five-lemma source route. No new-node obligations arise. Verdict: node
   and corrected interface agree; the proof plan is explicitly still intended.

Second-reading changes: appended this independent review and its search and
compile evidence. No further Lean, node or change-record edits were needed.

## Forced adaptations

### Sheaf.AlgebraicGeometry.CohomologySectionLocalizationGluing
Original against changed dependencies failed:
```
 F).inv ≫ F ◁ tensorPowSection (L.homOfGlobalSection s) n)))
        ((c W p) (L.cohomologyFraction F s p W n ξ)) =
      (ConcreteCategory.hom ((X.toRingedSpace.openModuleCohomologyRestriction p (homOfLE ⋯)).app (F ⊗ L.tensorPow n))) ξ
hca :
  ∀ (p : ℕ) (x : L.CohomologyFractionPresentation F s p (U ⊔ V)),
    (c U p) ((a p) x).1 =
        (ConcreteCategory.hom ((X.toRingedSpace.openModuleCohomologyRestriction p (homOfLE ⋯)).app F))
          ((c (U ⊔ V) p) x) ∧
      (c V p) ((a p) x).2 =
        (ConcreteCategory.hom ((X.toRingedSpace.openModuleCohomologyRestriction p (homOfLE ⋯)).app F)) ((c (U ⊔ V) p) x)
hcb :
  ∀ (p : ℕ) (x : L.CohomologyFractionPresentation F s p U × L.CohomologyFractionPresentation F s p V),
    (c (U ⊓ V) p) ((b p) x) =
      (ConcreteCategory.hom ((X.toRingedSpace.openModuleCohomologyRestriction p (homOfLE ⋯)).app F)) ((c U p) x.1) -
        (ConcreteCategory.hom ((X.toRingedSpace.openModuleCohomologyRestriction p (homOfLE ⋯)).app F)) ((c V p) x.2)
hcd :
  ∀ (p : ℕ) (x : L.CohomologyFractionPresentation F s p (U ⊓ V)),
    (c (U ⊔ V) (p + 1)) ((d p) x) =
      (ConcreteCategory.hom ((X.toRingedSpace.openModuleCohomologyRestriction (p + 1) (homOfLE ⋯)).app F))
        ((ConcreteCategory.hom ((δ (U ⊓ S) (V ⊓ S) p).app F))
          ((ConcreteCategory.hom ((X.toRingedSpace.openModuleCohomologyRestriction p (homOfLE ⋯)).app F))
            ((c (U ⊓ V) p) x)))
⊢ ∀ (p : ℕ),
    ∃ e,
      ∀ (n : ℕ) (ξ : ↑((X.toRingedSpace.openModuleCohomology p (U ⊓ V)).obj (F ⊗ L.tensorPow n))),
        (ConcreteCategory.hom
              ((X.toRingedSpace.openModuleCohomology p (U ⊓ V ⊓ S)).map
                ((ρ_ F).inv ≫ F ◁ tensorPowSection (L.homOfGlobalSection s) n)))
            (e (L.cohomologyFraction F s p (U ⊓ V) n ξ)) =
          (ConcreteCategory.hom
              ((X.toRingedSpace.openModuleCohomologyRestriction p (homOfLE ⋯)).app (F ⊗ L.tensorPow n)))
            ξ

(with the modules compiled into /tmp/forced-adaptation-h0hk3bjs/.lbuild) [7.8 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

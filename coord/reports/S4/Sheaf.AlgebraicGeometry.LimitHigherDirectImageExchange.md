## What changed

`Sheaf.AlgebraicGeometry.LimitHigherDirectImageExchange` replaces the proof of
`AlgebraicGeometry.Etale.isIso_limit_homology_derivedBaseChangeMapPlus` without
changing its signature, docstring, visibility, or public imports. Two private
helpers use exact inverse-image/homology comparison and cancellation of
isomorphisms. The target proof constructs pulled-back stage exchange
isomorphisms, factors the limit exchange through canonical legs, proves stage
transitions invertible by exchange pasting, and proves fiberwise bijectivity.

Three new modules contain the concrete cartesian constructions and pasting
proof, and the two unresolved geometric continuity components:
`CartesianHigherImageTransitions`, `CartesianHigherImageGermDescent`, and
`CartesianHigherImageGermVanishing`. All new objects are explicit constructions;
none chooses data from an unproved existence statement. Proof dependencies are
plain imports; public imports supply signatures and definition bodies.

## Proved and sorry left

One existing hole is closed syntactically:
`AlgebraicGeometry.Etale.isIso_limit_homology_derivedBaseChangeMapPlus`
(node `lem-sc-limit-higher-direct-image-exchange`). Its term still depends on
unproved geometric continuity, so this is a decomposition, not an axiom-free
completion of the item. The new pasting theorem
`AlgebraicGeometry.Etale.cartesianDerivedImageMap_exchange` and projection laws
`AlgebraicGeometry.Etale.cartesianImageProjection_fst` and
`AlgebraicGeometry.Etale.cartesianImageProjection_snd` are proved with only
`propext`, `Classical.choice`, and `Quot.sound`.

Two holes are added, each exactly `:= by sorry`, with source, complete informal
proof, and matching node:

- `AlgebraicGeometry.Etale.exists_cartesianHigherImage_germ_rep`, in
  `CartesianHigherImageGermDescent`, node
  `lem-sc-cartesian-higher-image-germ-descent`.
- `AlgebraicGeometry.Etale.exists_cartesianHigherImage_germ_eq_zero`, in
  `CartesianHigherImageGermVanishing`, node
  `lem-sc-cartesian-higher-image-germ-vanishing`.

Thus the local closed-minus-added count is 1 minus 2 = -1. Target-import-closure
progress and actual pruning are for the pinned sorry ledger to determine; this
report does not claim that a landing or syntactic closure is net progress.
The complete target term has only the three permitted axioms and `sorryAx`.
There are no other holes in the four delivered modules.

## No longer needed

Every old direct proof-dependency node removed from the target's `proof_deps`:

- `lem-weil-pbc-cofiltered-limit-directed-reindex` (Mathlib leaf): the formal
  assembly uses cofiltered nonemptiness directly, without reindexing.
- `lem-weil-pbc-limit-fibre-products`, module
  `Sheaf.AlgebraicGeometry.LimitFibreProducts`.
- `lem-weil-pbc-affine-etale-site-colimit`, module
  `Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit`.
- `sbc-lem-higher-direct-image-presheaf`, module
  `Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf`.
- `lem-weil-pbc-etale-cohomology-limit-of-schemes`, module
  `Sheaf.AlgebraicGeometry.EtaleCohomologyLimitOfSchemes`.

The last four direct imports are replaced by the two geometric germ components.
Their underlying mathematics remains in the informal proofs of those components;
there is no claim to have formalized it anew or eliminated its future need.
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` is also removed as a
redundant direct import: definitions remain available through retained imports.
`def-weil-pbc-inverse-image` remains a proof dependency. The fixed-base
`HigherDirectImageLimitSystem` and upstream `higherDirectImage_limit` do not
compare inverse images of relative higher images along a varying base.

No globally unreachable module has been established by this local review;
**pruned modules: none claimed**. These are direct-import removals only.

## Where the brief, the DAG or earlier work was wrong

The original plan calls for a varying-base continuity bridge between affine
étale cohomology and canonical derived exchange, beyond the declarations of
its imported ingredients. The delivered reduction isolates its independent
surjectivity and kernel components. In particular,
`AffineEtaleSiteColimit.lean` currently contains only a withdrawal notice, not
a usable site-colimit theorem; it cannot close either component by application.
Both components are genuine parts of [Stacks 0EYM](https://stacks.math.columbia.edu/tag/0EYM),
whose second proof uses sheafification, affine étale descent, and cohomology
continuity. The detailed ingredients are [03Q8](https://stacks.math.columbia.edu/tag/03Q8),
[0EYL](https://stacks.math.columbia.edu/tag/0EYL), and
[09YQ](https://stacks.math.columbia.edu/tag/09YQ).

The first report called the target a complete proof without distinguishing
its continuity holes. Its pruning list omitted the reindex node and the
redundant `UpperLowerStar.Defs` import. New construction docstrings all referred
to nonexistent `def-sc-cartesian-higher-image-transitions`; new node statement
dependencies were empty, and the pasting node omitted its actual upstream
coherence dependency. These metadata faults are repaired below.

## New nodes

`def-sc-cartesian-derived-image` records the derived direct image of the
concrete cartesian pullback with coefficients pulled back from X.
`def-sc-cartesian-image-projection` records its canonical projection, with
projection laws `lem-sc-cartesian-image-projection-fst` and
`lem-sc-cartesian-image-projection-snd` proved by the pullback lift laws.
`def-sc-cartesian-derived-image-map` records the canonical exchange followed
by inverse-image composition, and
`lem-sc-cartesian-derived-image-map-exchange` proves its exchange pasting
identity using the existing upstream horizontal derived-pasting theorem.

`def-sc-cartesian-higher-image-stage` and
`def-sc-cartesian-higher-image-limit` record degree-q homology of these
objects. `def-sc-cartesian-higher-image-leg` and
`def-sc-cartesian-higher-image-transition` give explicit canonical maps with
inverse-image composition transports.

`lem-sc-cartesian-higher-image-germ-descent` states only the representative
part of continuity, with no stage-isomorphism assumption.
`lem-sc-cartesian-higher-image-germ-vanishing` states only eventual vanishing
of a stage fiber element with zero limit image, also without that assumption.
They are strictly distinct components needed by the surjectivity and
injectivity branches, rather than renamed versions of the item.
No existing statement or definition was changed, and there is no change record.

## Second reading by S4

1. **Signatures: pass.** Compared all four delivered modules with the read-only
   repository. Only the target existed there; its theorem signature is byte for
   byte identical, and its public imports and docstring are unchanged. The three
   support modules and twelve support nodes are new. There are no forced
   adaptations or undeclared interface changes.
2. **Proof and construction: pass, conditional on the listed holes.** Compiled
   all four files through `lcompile.py`. Read every proof and definition. The
   pasting calculation uses upstream horizontal pasting, projection identities,
   and equality transport; the target's cancellation and fiberwise injectivity
   and surjectivity arguments are valid. All data is concrete. A scratch audit
   directly imports every delivered module and prints axioms of every public
   declaration; construction and pasting declarations use only allowed axioms,
   while the two named holes and target include `sorryAx`. No forbidden command
   or hidden definition hole was found. The delivery probe also checks private
   declarations.
3. **Split statements: pass.** Read the second proof of Stacks 0EYM and the
   supporting tags linked above. Each statement expresses one strictly smaller
   continuity component independently of `hstage`. Checked terminal/constant
   diagrams (identity comparison), q=0, zero coefficients, empty X, and empty
   limit base (no geometric point to quantify over). Cofilteredness ensures the
   index is nonempty. No torsion, smoothness, or injectivity assumption is needed.
   Repeated Lean Finder searches with “filtered colimit of inverse images of
   relative higher direct image sheaves under affine transition limits”, Loogle
   `"sheafFiber"`, and grep/rg for continuity and stalk-colimit variants. These
   expose generic fiber-colimit APIs and fixed-base continuity, not either
   varying-base statement. Read the existing fixed-base theorem signatures and
   the original presheaf and cohomology ingredients. Closing either geometric
   bridge requires further formal work, not a short application already present.
4. **Route and pruning: pass after report repair.** The formal assembly uses
   the shortest available exact inverse-image and canonical pasting API. The
   new geometry is the representative/kernel split of the original affine
   étale continuity step. Neither the item nor these nodes realizes a unit
   statement or step: `sk-thm-vanishing.json` has empty realized lists. Its unit
   and chapter route is preserved. Every old removed dependency and all five
   removed direct imports are now listed; global pruning is not asserted.
5. **Nodes: pass after metadata repair.** Matched each new declaration to its
   node, replaced abbreviated node signatures by verbatim multiline Lean
   signatures, added statement dependencies, and named upstream derived-exchange
   coherence and both projection laws in the pasting node's proof dependencies.
   Corrected the target plan: stage hypotheses prove e_i and transitions
   invertible, not limit legs before continuity. Sources and origins agree with
   the mathematical and formal steps, and source-linked proof docstrings remain
   attached to both named holes.

Second reading changed only construction/projection docstrings, node metadata,
and this report. No proof term or existing signature was changed. The scratch
axiom check was repaired to import the private-to-target support modules directly.

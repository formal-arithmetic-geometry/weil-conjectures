## What changed

Proved the sole theorem of
`Sheaf.AlgebraicGeometry.EtaleAbelianH0FiniteConnectedCriterion` without changing its
statement. Its proof imports the existing Gabber set-valued criterion and inverse-image
algebraic-structures comparison, plus the new Zariski comparison module.

The proof obtains the Zariski hypotheses on X and every finite cover from connected
point-closure intersections. Mathlib supplies finite-cover qcqs permanence, stability of
closed immersions, irreducibility of point closures, and the pullback-image equality.
Gabber gives the set-valued unit bijection. Evaluating the existing coefficient-comparison
unit equation and cancelling its isomorphism factors gives the abelian unit isomorphism.
The forgetful functor reflects isomorphisms. Naturality along the isomorphism between the
identity étale object and the chosen terminal object then gives the global-sections map.

Added `Sheaf.AlgebraicGeometry.ZariskiClosedImmersionConnectedRestriction`, a comparison
for a single closed immersion and Zariski sheaves, with connected point closures as its
hypothesis. This isolates the universe and closed-image transport missing from the current
spectral interface. Updated the assigned node's proof and dependencies to match the Lean.
No existing statement, definition, public import, or target signature changes.

## Proved and sorry left

Proved:
`AlgebraicGeometry.Etale.isIso_abelian_globalSectionsUpperStarMap_of_finite_connected_closed_intersections`
(node `lem-weil-pbc-etale-abelian-h0-finite-connected-criterion`).
The assigned module has no direct sorry left. This is a reduction to named dependencies,
not an assertion that its transitive dependencies are already sorry-free.

One new sorry:
`AlgebraicGeometry.zariski_closed_immersion_connected_restriction`
(node `lem-weil-pbc-zariski-closed-immersion-connected-restriction`).
Its complete proof plan transports the existing spectral comparison through a topological
universe lift and the homeomorphism from a closed immersion onto its image, preserving the
adjunction unit by uniqueness of left adjoints. Its statement is strictly the Zariski
part of the argument: it contains neither finite covers nor étale or abelian coefficients.

The imported `AlgebraicGeometry.gabber_h0_etale_criterion` and
`AlgebraicGeometry.etaleInverseImageAlgebraicStructures` remain existing obligations and
are not edited here.

Checked the new statement on empty X (then Z is empty and both sets of sections are
singletons), identity immersions, and empty Z with nonempty X (the nonempty intersection
hypothesis fails). The ambient-space connectedness condition transfers correctly to the
closed image and its homeomorphic source. Connectedness includes nonemptiness.

## No longer needed

Removed the original proof-only imports
`Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits` and
`Sheaf.Topology.SpectralClosedRestriction` from the assigned module. The former remains
imported by the existing Gabber criterion; the latter is now imported by the new Zariski
bridge, whose proof plan requires it. A trial explicit import of
`Mathlib.AlgebraicGeometry.PullbackCarrier` was removed because GlobalSections already
exposes it transitively.

The original direct proof dependencies
`lem-weil-pbc-qcqs-scheme-spectral`,
`lem-weil-pbc-h0-spectral-closed-restriction`,
`lem-weil-pbc-presheaf-pullback-sets-left-exact`, and
`lem-weil-pbc-sets-etale-inverse-image-composition-units`
are no longer direct steps of this module: the first two belong to the new Zariski bridge;
the last two are used inside the existing Gabber/algebraic-structures results.
They remain needed transitively; no global pruning of these nodes or modules is claimed.
The coefficient transfer uses the existing algebraic-structures theorem directly rather
than reconstructing filtered-colimit/sheafification compatibility in this file.

## Where the brief, the DAG or earlier work was wrong

The original spectral restriction declaration accepts `TopCat.{u}` with values in
`Type u`, but the Gabber criterion and underlying abelian sheaves require `Type (u + 1)`.
It is also stated for a literal closed subset, whereas Gabber's hypotheses use the given
closed immersion and its specific left-Kan-extension/sheafification unit. This is an
interface gap, not a false mathematical statement. The new Zariski bridge records both
transports explicitly and its remaining proof is documented.

The planned composition-units and left-exact presheaf results alone do not state
compatibility of forgetting abelian groups with the inverse-image unit. The existing
`lem-weil-pbc-etale-inverse-image-algebraic-structures` states the exact equation needed;
that equation is evaluated and used in the delivered Lean proof.

`blueprint_refs.py ancestor` cannot follow this item's `created.item`, which is a module
name rather than a node id. The new node's ancestry follows the recorded blueprint.from
links through `prop-weil-pbc-gabber-pair-comparison` to
`lemma-weil-pbc-injective-restriction-acyclicity`. The unit's realized route is unchanged.

## New nodes

`lem-weil-pbc-zariski-closed-immersion-connected-restriction`, in
`dag/nodes/sec-proper-base-change/`, realized by
`Sheaf.AlgebraicGeometry.ZariskiClosedImmersionConnectedRestriction`.
Source: Stacks Project, Tag 09ZG, `etale-cohomology.tex`, `lemma-h0-topological`;
read in the local source copy. This is a single-immersion Zariski bridge for the higher
coefficient universe, with a proof by universe lift and closed-image transport from the
existing spectral restriction node. LeanSearch was unavailable (HTTP 500); LeanFinder
and Mathlib/source searches found no existing matching interface. No change record is
needed because existing interfaces are unchanged.


## Second reading by T2

1. PASS. Compared the assigned module with the repository version using diff and
   verified the existing theorem signature byte for byte through `:=`. Its docstring,
   hypotheses, conclusion, definitions and public imports are unchanged. The other
   delivered module is new; there is no change record because no existing interface
   changes.
2. PASS. Both modules compiled with lcompile in import order. Scratch copies with
   `#print axioms` showed only propext, Classical.choice, Quot.sound and sorryAx.
   The only direct sorry in this delivery is the named Zariski bridge listed above;
   there are no definitions or forbidden declarations. Read the actual unit equation,
   the isomorphism cancellation, reflection by the forgetful functor, terminal-object
   naturality and the definition of globalSectionsUpperStarMap. These prove the
   unchanged theorem conditional on the recorded open dependencies.
3. PASS. Read Tag 09ZG, lemma-h0-topological, in the local Stacks source copy at
   /home/ubuntu/weil-sandbox/B2/Sheaf.ConstructibleSheaf.LocallyConstantRetraction/
   scratchpad/etale-cohomology.tex, lines 15098–15164. The new statement is its
   closed-image and universe transport, with a complete four-step docstring and node.
   Checked empty X, empty Z, identity immersions, and a closed point in the spectrum
   of a local ring. Connectedness includes nonemptiness; empty Z is excluded when
   X has a point. The bridge concerns Zariski sets and a single immersion, so it is
   strictly part of the finite-cover abelian etale argument, not a restatement.
   Independent LeanFinder, Loogle and Mathlib grep searches used sections unchanged,
   point closures, stalkPullbackIso and unit_leftAdjointUniq as alternative terms.
   Also searched lean/Sheaf and lean/WeilConjectures. The upstream
   TopCat.Sheaf.bijective_unit_app_top is for abelian coefficients in the space's own
   universe and a literal closed subset; it does not close this set-valued bridge.
   No exact existing interface or short proof was found.
4. PASS after repair. All proof-only imports in the assigned module serve its actual
   proof; public imports serve its unchanged signature. Corrected the report to name
   the two removed original proof imports. Added a plain import of
   Sheaf.Topology.SpectralClosedRestriction to the new bridge, retaining its stated
   pending proof dependency in the library import graph. The old dependencies no
   longer used directly are all listed above, and remain needed transitively.
   Read dag/units/sk-thm-p1.json, including realized: this reduction is below its
   unit steps and keeps the Gabber comparison route; no realized field changes.
5. PASS. Existing node proof/proof_deps/proof_origin describe the actual Zariski,
   finite-base-change, Gabber and coefficient-unit argument. Both proof_deps lists
   equal the union of their step uses. The new node has the required source, searches,
   ancestry, creation data, chapter/unit, Lean signature and realization. The sole
   named open bridge agrees with its node and docstring.

Second reading changed the pruning report and added the bridge's missing proof-only
spectral import. No mathematical statement or proof body was rewritten. Final local
and server compilation and the delivery preflight are checked by deliver3.py below.

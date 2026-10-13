## What changed

The original module now proves
`AlgebraicGeometry.Scheme.exists_affine_restriction_quasiIso_of_perfect_stalk_quasiIso`
with its existing signature and visibility unchanged. A proved private helper,
`perfect_stalk_isKProjective`, takes the finite-free retractions to projective stalk
modules and transports the support bound. Mathlib's
`CochainComplex.IsKProjective.quasiIso_iff` then gives a homotopy inverse for the
specified stalk map. The proof lifts that inverse, explicitly transports both inverse
homotopies by naturality of the restriction/stalk comparison, spreads them, and assembles
an actual `HomotopyEquiv` whose forward map is the exact restriction of the input map.
`HomotopyEquiv.quasiIso_hom` finishes the proof.

Added proof-only imports of `OpenModuleStalkFreeProjective`,
`Mathlib.Algebra.Homology.DerivedCategory.KProjective`, and the two new modules
`PerfectOpenStalkChainMapLift` and `PerfectOpenStalkInverseHomotopiesSpread`.
The public imports and the original statement are unchanged. The original DAG node's
proof, proof_deps and proof_origin now describe this route. No definition, target,
existing public signature, or other held module was changed.

Local compilation uses lcompile.py only. All three modules compile without warnings.
The proof of the original theorem relies on the two new named obligations below;
its axiom closure still includes their unfinished proofs.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.exists_affine_restriction_quasiIso_of_perfect_stalk_quasiIso`
(node `lem-sc-perfect-stalk-quasi-iso-detection`). The original module has no remaining
sorry. The private helper `perfect_stalk_isKProjective` is fully proved.

Added exactly two holes, each a named public theorem with its entire proof `:= by sorry`:

- `AlgebraicGeometry.Scheme.exists_affine_perfect_open_stalk_chainMap_lift`, node
  `lem-sc-perfect-open-stalk-chain-map-lift`, in
  `Sheaf.AlgebraicGeometry.PerfectOpenStalkChainMapLift`.
- `AlgebraicGeometry.Scheme.exists_affine_perfect_open_stalk_inverse_homotopies_spread`,
  node `lem-sc-perfect-open-stalk-inverse-homotopies-spread`, in
  `Sheaf.AlgebraicGeometry.PerfectOpenStalkInverseHomotopiesSpread`.

This is a decomposition: one upper hole closed, two lower holes added (net -1).
The first lower theorem treats an arbitrary stalk chain map and assumes no
quasi-isomorphism or inverse. The second takes an already lifted candidate inverse
and two specified stalk homotopies; it performs only descent of the inverse equations.
Neither restates quasi-isomorphism detection. The K-projectivity proof, extraction of
an inverse, transport of its homotopies, and the final quasi-isomorphism inference are
real compiled Lean in the original module. No data definition contains a hole and no
arbitrary witness is chosen to define an object.

## No longer needed

Second reading also removed the redundant public import
`Mathlib.Algebra.Homology.Homotopy` from both new modules: their existing
`PerfectComplex` import already exposes it. Both signatures still compile.

Removed the following proof-only imports and their direct proof dependencies from
this module's route:

- `Sheaf.Algebra.Homology.ModuleStalkExact`,
  `lem-weil-pbc-module-stalk-exact`.
- `Sheaf.AlgebraicGeometry.AffinePerfectHomColimit`,
  `lem-pc-affine-perfect-hom-colimit`.
- `Sheaf.RingTheory.LocalizationColimitPrincipalLocalizations`,
  `lem-weil-pbc-localization-colimit-principal-localizations`.
- `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`,
  `lem-pc-affine-qcoh-derived-equivalence`.

The argument no longer needs the section-complex cone, its derived zero-object
criterion, a derived Hom colimit diagram, or the affine derived equivalence. Both new
obligations admit direct finite-component germ calculations. The ordinary
finite-presentation internal-Hom stalk comparison is recorded as a tool in their
proof plans; it is not the affine derived equivalence. These are claims about this
proof's dependencies, not claims that those modules are globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The original statement is true and was not changed. Its cone/derived-colimit plan
is mathematically sound but unnecessarily elaborate at the assembly level:
bounded projective stalk complexes admit a homotopy inverse by an existing Mathlib
criterion. The existing finite-free chain-map and homotopy spreading declarations
use `Scheme.Modules` and pullback to `Spec` of a stalk, with globally free terms
(and, for the homotopy pair, a single free target complex). They do not directly
state the general bounded finite-projective retract case on the slice site used here.
The existing derived stalk lifting result also requires ambient global complexes
and derived model comparisons, so it cannot be directly applied to arbitrary P,Q
on the supplied open U. No false statement was found.

Read the official source proofs at https://stacks.math.columbia.edu/tag/09RE
(affine case (1)) and https://stacks.math.columbia.edu/tag/0BC7 (2); the local
literature/stacks-project/perfect.tex file is absent on this machine. The new
finite-retraction expansions are written by M3 and explicitly recorded as such.
The finite-presentation internal-Hom comparison
`lem-weil-pbc-stalk-internal-hom-finite-presentation` is a generic tool from another
unit used in the new proof plans; it supplies lifting and detection of local error
maps, and does not replace the unit's cube-theorem route.
`lem-sc-open-module-stalk-free-projective` is a proved generic tool for the private
helper. The original unit sk-prop-av-cube has empty realized.statement and empty
realized.steps[0]; no designated unit statement or step was bypassed or edited.

Searches: leanfinder and loogle found the homotopy/quasi-isomorphism and K-projective
components; additional leanfinder searches returned ordinary stalk results, not the
required neighbourhood chain-map descent. Loogle `Homotopy, "stalk"` and the logged
Mathlib grep found no combined result. LeanSearch returned HTTP 500 and is recorded
as unavailable, not as no match. Local rg of Sheaf, WeilConjectures, and Mathlib
located and checked the alternative finite-free and internal-Hom declarations above.
Blueprint searches for homotopy, chain map and 09RE found no equivalent blueprint node.
The ancestor helper printed None for this Lean-module-created item; the new nodes
therefore inherit the explicit thm-sc-theorem-of-cube ancestor and via chain already
recorded in the item's blueprint.from, with the local comparison step specified.

## New nodes

`lem-sc-perfect-open-stalk-chain-map-lift` corresponds to
Sheaf.AlgebraicGeometry.PerfectOpenStalkChainMapLift. It descends one arbitrary chain
map of stalk complexes, together with a natural restriction/stalk comparison, and
asserts no invertibility. The proof in words lifts the finitely many components using
finite presentation, then makes the finitely many chain errors vanish by shrinking.
Rank zero, zero complexes, empty support intersections, unequal support bounds and
boundary equations were checked; zero sources give unique zero maps. The comparison
is defined by restriction cofinality and open-immersion stalk-ring isomorphisms.

`lem-sc-perfect-open-stalk-inverse-homotopies-spread` corresponds to
Sheaf.AlgebraicGeometry.PerfectOpenStalkInverseHomotopiesSpread. It starts with the
candidate inverse on V and its two stalk homotopies; only reverse-degree homotopy
components and their finitely many error equations are descended. The forward map
is fixed throughout. Boundary degrees adjacent to the support intervals are included;
outside them zero terms give automatic equations. No coherence, Noetherian hypothesis,
or cohomology-support closedness is used. After intersecting finitely many opens an
affine neighbourhood can always be chosen inside V, hence inside U. Both nodes inherit
the original chapter/unit, carry the source and search records, and each has exactly
one public theorem. No change record or forced adaptation was required.

## Second reading by M3

1. Compared the original module against the repository with diff and separately
   compared the existing theorem signature byte for byte through `:=`: identical.
   Its visibility and two public imports are unchanged. Only this item and its
   two new modules/nodes are delivered; no existing definition was modified.
2. Independently compiled all three files with lcompile.py, including after import
   cleanup: no errors or warnings. There are exactly two `sorry` tokens, each the
   entire proof of the named new theorem reported above. Scratch-copy `#print axioms`
   gives only propext, Classical.choice and Quot.sound for the private K-projectivity
   helper, and additionally sorryAx for the original theorem and the two obligations.
   No forbidden declarations or hollow definitions occur. Naturality transports
   both inverse homotopies for the exact input map; the concluding HomotopyEquiv
   therefore proves the original conclusion without changing the map.
3. Read Stacks 09RE, affine case (1), 0BC7 (2), and 00CR. The two new obligations
   expand the finite-component calculations in those proofs; they are not quoted
   as verbatim source statements. Sandwiching a map from a retract P to a retract Q
   means free(P) -> P -> Q -> free(Q), then recovering it by P -> free(P)
   and free(Q) -> Q. The retraction identities recover the original germ exactly.
   Chain equations involve finitely many degrees, including the adjacent boundary;
   homotopies involve finitely many reverse-degree components and errors. Each error
   is a finite matrix with zero germs, so one finite intersection kills them all.
   Rank zero, empty or reversed bounds, disjoint supports, and arbitrary rings cause
   only zero maps. Affine neighbourhoods exist inside the resulting open; no
   separatedness or Noetherian assumption is used. Neither obligation restates
   quasi-isomorphism detection. Read the existing FiniteFreeStalkChainMapLift,
   FiniteFreeStalkHomotopyPairShrink, PerfectStalkDerivedHomLift and
   StalkInternalHomFinitePresentation interfaces: the first two use a different
   module/stalk interface and free terms; the derived lift needs ambient models.
   Independent leanfinder search for descent of morphisms or chain homotopies of
   bounded finite projective sheaves, loogle `"Homotopy", "restrict"`, and logged
   grep plus local rg found no direct replacement. Neither lower hole admits a
   few-minute closure with the existing slice-site interfaces.
4. The K-projective criterion is already the short assembly route. All four old
   proof-only imports and their old proof dependencies are reported above. Removed
   only the redundant Homotopy public import in each newly created module; the
   statements compile through PerfectComplex's existing public imports. Read
   sk-prop-av-cube's realized fields and its cube-theorem step: this is a local
   comparison below that step, and the unit's route is preserved unchanged.
5. Read all three node records. The original proof/proof_deps/proof_origin follow
   the actual K-projective, chain-map-lift, inverse-homotopy-spread assembly. New
   nodes have source, complete proof plans, searches, provenance, chapter/unit and
   matching Lean signatures, checked verbatim. The internal-Hom comparison is a
   generic component-descent tool, not a replacement for the cube route.

Second reading changed only the two redundant imports and this report. The delivery
remains a decomposition: one original hole closed, two lower holes added, net -1;
the original theorem is not claimed axiom-free.

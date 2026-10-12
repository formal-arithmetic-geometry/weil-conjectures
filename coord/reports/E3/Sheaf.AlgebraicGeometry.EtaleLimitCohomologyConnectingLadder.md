## What changed

Replaced the single sorry of `AlgebraicGeometry.Etale.etale_limit_cohomology_connecting_ladder`
with a complete Lean proof from two strictly smaller intermediate statements. The first supplies
an acyclic replacement, a short exact limit sequence, extension-class boundary formula, and
untransported naturality square. The second constructs a canonical comparison diagram in an
arbitrary degree for an arbitrary coefficient system and cocone. The original theorem's signature
and docstring are unchanged. Added their proof imports and a proof import of Mathlib Ext exactness.

The main proof uses `Ext.covariant_sequence_exact₁` to deduce boundary surjectivity from vanishing
of the middle term. It then conjugates boundaries by the given isomorphisms, proves surjectivity
using the categorical epimorphism criterion, and proves the final square by cancellation and the
two comparison-leg equations. No cohomology descent or continuity in positive degree is assumed.
The DAG now records these actual steps.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.etale_limit_cohomology_connecting_ladder` (one of one original
holes). This is a decomposition into two holes, not a net reduction of holes.

Added and left exactly `:= by sorry`:

- `AlgebraicGeometry.Etale.etale_limit_acyclic_replacement`
  (`lem-weil-pbc-etale-limit-acyclic-replacement`).
- `AlgebraicGeometry.Etale.etale_limit_canonical_cohomology_diagram`
  (`lem-weil-pbc-etale-limit-canonical-cohomology-diagram`).

No sorry remains inside the main proof; no definitions or private holed declarations were added.
All three modules compile together. The two intermediate statements were checked on n=0,
zero coefficient systems, empty schemes, and a one-object index. The replacement's acyclic middle
term implies surjectivity by the existing Ext exactness theorem, rather than asserting it.
The canonical diagram requires neither a scheme limit nor a sheaf colimit nor acyclicity.

## No longer needed

The original public import is unchanged and needed for the statement. The main module removes
these direct proof imports, retaining their planned use inside the split modules:

- `Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit`
- `Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`
- `Sheaf.AlgebraicGeometry.EtaleQcqsCofinalFiniteCoverings`
- `Sheaf.AlgebraicGeometry.FullAffineEtaleTopos`
- `Sheaf.AlgebraicGeometry.LimitAffineTransition`
- `Sheaf.CategoryTheory.ColimitSiteSections`
- `Sheaf.CategoryTheory.SiteCechVanishingCriterion`
- `Sheaf.CategoryTheory.SiteInjectiveCechAcyclic`
- `Sheaf.CategoryTheory.SitePullbackAbelianExact`
- `Sheaf.Paper.ColimitSitesInjectiveSystem`

It also removes `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` as a redundant direct
import (already public through TopologicalInvariance), and
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`, unused on the Ext route.
`Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence` is replaced by Ext exactness. Apart from the derived-long-exact node listed below, the old proof dependencies remain
transitively needed by the split statements: the site embedding,
inverse-image coherence/exactness, filtered sheaf colimit exactness, affine-site presentation and
topos comparison, limit affine transition, finite qcqs covers, injective Cech acyclicity, filtered
group exactness, Cech criterion, section comparison, finite-limit commutation and sheaf condition
remain under the acyclic replacement. Pullback functoriality remains under the canonical diagram.

The second reader also searched for compatible monomorphisms into injective systems with
acyclic pullback colimit: LeanFinder returned only generic injective complexes and dimension
lemmas. No scheme replacement was found.

The general right-derived full-long-exact-sequence module
`Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence` and its node
`lem-weil-pbc-derived-functor-long-exact` are no longer needed on this route. The existing Ext
cohomology long exactness node `lem-weil-pbc-sheaf-ext-cohomology-long-exact` supplies exactly the
required boundary and exactness. The two cohomology definition nodes remain statement
dependencies. The generic site connecting ladder and site cohomology diagram modules were
inspected but not imported; their signatures need a substantial site-to-scheme translation.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found in the stated theorem. The original DAG planned a right-derived
long exact sequence, while the library already encodes `Sheaf.H` as Ext; its proved exactness
lemma makes the surjectivity step direct. The original module already had proof-dependency imports; these are now assigned to the
corresponding split modules, rather than dropped from the import closure.
The generic site connecting ladder is proved, but its precoverage, site colimit, `Under i`,
objectwise cohomology, and universe inputs do not specialize directly to this scheme statement.

The unit's route is unchanged. The replacement retains precisely the injective-system and
Cech-vanishing argument of 09YP/0EXZ/0739, with scheme passage of 09YQ. Source pages 09YP, 0EXZ,
0739 and 09YQ were read. Search tooling returned no matching scheme replacement or canonical
comparison-diagram theorem; LeanSearch was unavailable with Internal Server Error. A direct
canonical-diagram proof was attempted in scratchpad, but excessive inverse-image unfolding
prevented completing its functor and cocone laws within the single-file limit. The delivered
statement gives that exact step, with a full mathematical proof, rather than a restatement of
the connecting-ladder theorem.

## New nodes

`lem-weil-pbc-etale-limit-acyclic-replacement`, in
`lean/Sheaf/AlgebraicGeometry/EtaleLimitAcyclicReplacement.lean`, isolates original steps 1–3
and the untransported naturality square from step 4. It asserts no surjective map and no
lower-degree comparison diagram. Its DAG proof retains the corresponding existing nodes.

`lem-weil-pbc-etale-limit-canonical-cohomology-diagram`, in
`lean/Sheaf/AlgebraicGeometry/EtaleLimitCanonicalCohomologyDiagram.lean`, isolates only the
canonical diagram and cocone construction, valid in every degree without limit, qcqs, affine,
exactness or acyclicity assumptions. Its proof uses the existing pullback functoriality node.
No change record is needed: no existing signature, definition or public import was changed.

## Second reading by E3

1. Compared the delivered main module with the repository using a file diff and verified
   the theorem signature byte for byte. No existing declaration, hypothesis, conclusion,
   definition, docstring, or public import changed. The two added modules only state
   intermediate theorems; there is no arbitrary-witness definition. Verdict: pass.
2. Compiled all three modules in dependency order through lcompile.py. Inspected the main
   proof: Ext exactness supplies a preimage, vanishing kills the next map, isomorphisms
   transport surjectivity, and cancellation plus hB/hBR/hbeta gives the square. Printed
   axioms for all three declarations: only propext, Classical.choice, Quot.sound and
   sorryAx from the documented open statements. Scanned for forbidden declarations and
   holes in data definitions; none occur. Verdict: pass, conditional on the listed holes.
3. Read both split signatures, proofs in words, and matching nodes. The acyclic replacement
   omits the diagram and surjectivity conclusions; the canonical diagram needs neither
   a limit nor acyclicity. They are strictly separate parts of the argument, not renamed
   copies of the item. Checked n=0 (the boundary is H^0(R) to H^1(F)), zero systems
   (zero replacement suffices), empty schemes (zero cohomology), singleton indices
   (ordinary injective dimension shifting), and nontrivial prescribed eG isomorphisms
   (transport by their inverses in the legs). Read Stacks 0EXZ, 09YP, 0739, 09YQ directly.
   Independent LeanFinder search for varying-coefficient comparison cocones found only
   structure-sheaf and scheme cocones; Loogle does not index cohomologyMap. Local searches
   found the generic site diagram/replacement and the spectrum/fixed-base diagrams;
   their hypotheses do not instantiate to this arbitrary varying coefficient system.
   Verdict: true and needed; no matching shorter scheme theorem found.
4. Read the old proof dependencies, the new route, and sk-thm-p1.json's realized fields.
   No unit statement or realized step is bypassed. The main proof takes direct Ext
   exactness instead of the general derived long exact sequence. Corrected the pruning
   report to list every removed direct import and to distinguish moved dependencies from
   the discarded derived-long-exact node. Restored the planned proof imports in the two
   split modules, preventing accidental pruning merely by moving their holes. Verdict: pass.
5. Checked each node's verbatim Lean signature and its proof/proof_deps/proof_origin.
   Only these permitted proof fields changed on the existing node. New nodes have source,
   full proof steps, searches, creation, blueprint, chapter/unit and Lean records. The
   supplied witnesses are only destructured inside a proof; no data definition chooses
   a witness from an unproved existence statement. Verdict: pass.

Changed: corrected the report's false claim that the original module had no proof imports,
listed the removed imports precisely, retained planned dependencies in the split modules,
and narrowed the acyclic replacement's public Ext import to ExtClass (needed by its signature).

A second-reader scratch attempt normalized the identity and composition functor laws, but
the comparison cocone law still failed to rewrite through the dependent inverse-image types.
No scratch theorem or partial proof is delivered; the canonical-diagram hole remains listed.

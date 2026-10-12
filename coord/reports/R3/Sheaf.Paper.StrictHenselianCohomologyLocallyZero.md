## What changed

Completed the proof of `strictHenselian_cohomology_locally_zero` without changing its
signature, assumptions, conclusion or implicit Ext universe. The proof uses an injective
resolution comparison, preservation of homology, and Mathlib's concrete filtered-colimit
equality criterion. Its final equality is for the actual restriction map in the statement.

Added `Sheaf.Paper.EtaleObjectCohomologyStalkComplex`, containing the real composite functor
`etaleObjectStalkSections`, its proved additive instance, and the unresolved comparison
`etaleObjectCohomology_stalk_complex`. Added `Sheaf.Paper.StrictHenselianStalkSectionsEpi`,
containing the unresolved degree-zero lifting result
`strictHenselian_stalkSections_preservesEpimorphisms`. Preservation of finite limits is
already supplied by Mathlib, and the main proof derives preservation of homology from it
and preservation of epimorphisms. Replaced the earlier sandbox's stronger exactness hole
with this smaller obligation and removed its obsolete module.

Updated the existing DAG node and added a complete node for each new obligation. The
unit `sk-thm-p1` and every node in its `realized` fields retain their statements and route.
The Stacks sources were read from the local source mirror; Tags 03F3, 03Q6, 03QO and 09AX
were also checked on the Stacks website. LeanSearch was unavailable; LeanFinder and source
searches supplied the other checks. No data-valued definition chooses an unproved witness:
the functor is constructed explicitly, and the existential comparison is eliminated only
inside the proof of the original theorem.

## Proved and sorry left

Closed one original hole: `strictHenselian_cohomology_locally_zero`
(`lem-weil-pbc-strict-henselian-cohomology-locally-zero`). There is no `sorry` in the item's
module. The private filtered-colimit preservation helper and the additive instance are proved.

Added two holes, both named public theorems with exactly `:= by sorry`:

- `etaleObjectCohomology_stalk_complex` in `Sheaf.Paper.EtaleObjectCohomologyStalkComplex`,
  node `lem-weil-pbc-etale-object-cohomology-stalk-complex`.
- `strictHenselian_stalkSections_preservesEpimorphisms` in
  `Sheaf.Paper.StrictHenselianStalkSectionsEpi`, node
  `lem-weil-pbc-strict-henselian-stalk-sections-epi`.

This is a decomposition: one hole closed and two added, net minus one before pruning.
The target theorem still depends on these unproved sublemmas. The comparison concerns
arbitrary schemes and functors and contains no henselianity or local vanishing conclusion.
The lifting theorem concerns only epimorphisms on degree-zero sections, with henselianity
at a single point. Neither repeats the theorem being reduced.

All three modules compile together in import order through `lcompile.py`. The main module
also compiles alone against the new modules. The final dry run checks compilation, the
axiom probe and preflight; the second reader supplies the independent review.

## No longer needed

Removed these direct proof imports and their direct use by the item's proof:

- `Sheaf.AlgebraicGeometry.EtaleCohomologyLocalRingColimit`, node
  `lem-weil-pbc-etale-cohomology-local-ring-colimit`.
- `Sheaf.Paper.StrictlyHenselianEtaleAcyclic`, node
  `lem-weil-pbc-strictly-henselian-etale-acyclic`.
- `Sheaf.CategoryTheory.KInjectiveComputes`, node `lem-sp-kinjective-computes`.

The section-level lifting node still references the continuity and strict-henselianity
arguments of the first two nodes in its proof plan. The current Lean import closure does
not import their higher-cohomology modules. Global pruning is determined by the maintainer
across all other users. The K-injective computation module is unnecessary for both the main
proof and the new section-complex route.

Removed the earlier sandbox-only module `StrictHenselianStalkSectionsExact`; it had never
been delivered and is replaced by the epimorphism statement. Removed unnecessary imports
of `Mathlib.Topology.Sheaves.Abelian` and `Mathlib.CategoryTheory.Abelian.RightDerived`
from the earlier comparison module, using the abelian-group exact-colimit and injective
resolution modules instead. Homology-preservation and concrete-colimit imports are private
proof imports of the original module.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox report said the target remained `sorry`, although a substantial proof
had been written and failed only at the final colimit step. That report and the incomplete
node records are replaced here. The earlier use of `Types.FilteredColimit.isColimit` named
no existing declaration. Universe inference also needed a general private preservation
lemma accepting the actual diagram; naming the Ext universe in the public signature was
unnecessary, so its original implicit form is retained.

The existing local-ring continuity theorem uses a scheme in universe u and coefficients
in u+1. This item has scheme universe u+1 and coefficients u+1; those signatures cannot
be directly specialized to each other. The new comparison retains coefficient sheaves
in their original universe and lifts only the cohomology groups. Its proof plan uses a
dense small affine etale subsite to establish enough injectives, rather than assuming
that the category of all etale objects is essentially small in the coefficient universe.

Edge cases were checked in the argument: empty schemes supply no point; q=0 is included
only in the comparison and excluded from the original positive-degree assertion; zero
sheaves cause no difficulty; cofinal affine neighbourhoods avoid any global qcqs
assumption. The structural arrow of `i(top)` can be a nonidentity etale endomorphism.
The degree-zero lifting argument therefore restricts first to that etale object and uses
its underlying scheme X, with all its canonical open inclusions.

## New nodes

`lem-weil-pbc-etale-object-cohomology-stalk-complex` records the actual stalkwise section
functor and its injective-resolution comparison. Its proof combines a dense small subsite,
representability of evaluation, the Ext-resolution comparison and exact filtered colimits.
Its statement, source, complete proof steps, searches and Lean signature are in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-object-cohomology-stalk-complex.json`.

`lem-weil-pbc-strict-henselian-stalk-sections-epi` records the degree-zero local lifting
step, separately from the comparison and all positive-degree cohomology. Its proof uses
degree-zero continuity and the section of an etale cover meeting the closed point of a
strictly henselian local scheme. Its complete record is in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-strict-henselian-stalk-sections-epi.json`.
No existing declaration's statement or definition changes. The conservative interface check
flags the added universe names and open command; their command-only change record is
`coord/changes/strictHenselian_cohomology_locally_zero_commands.md`.


## Second reading by R3

1. Compared the delivered item module with the repository version. The theorem signature is unchanged; only imports, proof commands, and the proof body changed. Verdict: pass.
2. Compiled all three delivered modules with lcompile.py; there are no errors, forbidden declarations, or unlisted sorries. The two remaining sorries are named split-off theorems with docstrings and DAG nodes. Verdict: pass.
3. Reviewed the split-off statements and their edge cases. Both are strict sublemmas: the arbitrary object-cohomology/stalk-complex comparison and degree-zero epimorphism preservation. Neither restates the target, and neither changes a definition by an unproved witness. Verdict: pass.
4. Checked the proof route against the DAG and unit. The target proof uses the two split-off nodes, finite-limit and homology preservation, and concrete filtered-colimit equality; removed imports are documented above. Verdict: pass.
5. Confirmed the DAG proof, proof_deps, and proof_origin match the Lean route, and the unit realized route is retained. Verdict: pass.

Changed during second reading: removed a parser-sensitive `set_option` wrapper around the target theorem so the delivery checker recognizes the closed target; no mathematical statement or proof step changed.

## What changed

Replaced the hole in `AlgebraicGeometry.Scheme.affine_koszul_section_roof` with a complete
proof from a transported Hom-colimit comparison. The proved private helper
`kflat_augmentation_realization` uses Mathlib `DerivedCategory.right_fac` and the existing
`CochainComplex.exists_isKFlatResolution` to produce the actual chain augmentation.
The main proof extracts a finite stage using `Types.jointly_surjective`, transports local
perfect models along the resulting derived isomorphism, and proves the restriction equation
by functoriality and cancellation. Every existing declaration signature and public import stays
unchanged. The local heartbeat allowance addresses elaboration of the chosen restriction functors;
the file compiles well within the 60-second wall limit.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.affine_koszul_section_roof`
(`lem-sc-affine-koszul-section-roof`), 1 of 1 original holes.
Added: `AlgebraicGeometry.Scheme.affine_koszul_section_colimit`
(`lem-sc-affine-koszul-section-colimit`), exactly one public theorem with `:= by sorry`.
There are no holes in the item's module or private helpers.
This is a decomposition, not a net hole reduction: one closed minus one added equals zero.
The remaining result is the whole transported Hom-colimit, with no chosen section,
chain augmentation, complex representative, or K-flatness conclusion. The substantial
chain realization and final assembly are proved in the item.

The new statement was checked on empty U (singleton restricted Hom sets and zero tail),
zero E (singleton Hom sets), the zero ring (empty spectrum), U=X (unit augmentation),
and unbounded E (the existing cohomology comparison has no bounds). No new hypothesis
or arbitrary data definition is introduced. The witnesses from the colimit theorem are
eliminated only inside a propositional theorem proof; no definition chooses data from it.

## No longer needed

Removed direct proof imports:
- `Sheaf.AlgebraicGeometry.AffinePerfectOpenRepresentCohomology` is now used by the new
  colimit item, so it is relocated, not pruned from the overall closure.
- `Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat` and its node
  `lem-pc-bounded-above-flat-kflat` are not needed for this route: general K-flat resolution
  replaces the bounded finite-free term calculation.

`def-sc-koszul-open-system` / `Sheaf.AlgebraicGeometry.KoszulOpenSystem` remains needed
below the new colimit theorem, but the upper chain realization no longer uses its chain
construction directly. No claim is made that any of these modules leaves the whole target
closure: other branches or the K-flat-resolution dependencies may retain them.
All original public imports are retained to preserve the existing interface.
The new colimit module imports `Mathlib.CategoryTheory.Limits.Types.Colimits` privately: its
statement only needs the basic cocone and colimit API already available through its public imports.
Every old roof proof dependency is accounted for: `lem-sc-affine-perfect-open-represent-cohomology`
and `def-sc-koszul-open-system` move below the colimit lemma;
`lem-pc-bounded-above-flat-kflat` is removed from this roof route.

## Where the brief, the DAG or earlier work was wrong

The original plan treated affine transport and compatibility with independently chosen
localizations as elementary, but its recorded lemmas expose only the spectrum Hom-colimit.
The reduction isolates precisely that transport interface rather than duplicating a section-roof
assertion. Conversely, the plan's direct finite-free K-flatness calculation is unnecessary:
Mathlib's right fraction factorization and the existing K-flat resolution theorem realize any
derived augmentation by a chain map after changing its representative. This avoids building a
Koszul chain model on an arbitrary affine scheme.

The local `literature/stacks-project/perfect.tex` packet is absent. Source Tags 08DC, 08DD
and 08EH were read from the Stacks Project website; the node records this reconstruction as
agent-written. The unit record's realized lists are empty and no unit route is bypassed.
LeanSearch returned Internal Server Error; its search is recorded as unavailable.

## New nodes

`lem-sc-affine-koszul-section-colimit`, in
`dag/nodes/sec-picard-framework/lem-sc-affine-koszul-section-colimit.json`, states the
transported perfect-object Hom-colimit and the formula for all its legs. Its new module is
`Sheaf.AlgebraicGeometry.AffineKoszulSectionColimit`. Its proof follows 08DC/08DD through
the existing isomorphism-localization, equivalence, restriction-square, quasi-coherence and
perfect-transport lemmas. The new theorem is strictly the colimit step of the argument;
it has no section-specific conclusion and no chain/K-flat assertion. Searches of the blueprint
for Koszul section, 08DC and colimit Hom found no exact existing blueprint statement.
The original node's proof and proof dependencies now match the compiled reduction.
No definition or statement changes and no forced adaptations were made; no change record needed.


## Second reading by U2

1. **Interface: pass.** Compared both delivered modules with the repository. The colimit
   module is new. The existing roof theorem signature is byte-for-byte identical, including
   universes, localization instances, every hypothesis and the chain-level conclusion.
   There are no changed definitions or forced adaptations. The private helper is new and proved.
2. **Proof and trust: pass as a decomposition.** Compiled both modules in import order with
   lcompile.py, without errors or warnings (about 7 and 21 seconds). Scratch copies with
   `#print axioms` give only propext, Classical.choice and Quot.sound for
   kflat_augmentation_realization. Both public theorems additionally use sorryAx, as expected
   from the one named colimit hole. The main module contains no sorry, and the only new sorry
   is affine_koszul_section_colimit. No forbidden declaration or hollow definition occurs.
   Read the fraction factorization, quasi-isomorphism inversion, transport of local perfect
   models, casts, cocone-leg extraction and final cancellation; each has the required direction.
3. **New statement: pass.** Read Stacks Tags [08DC](https://stacks.math.columbia.edu/tag/08DC),
   [08DD](https://stacks.math.columbia.edu/tag/08DD) and
   [08EH](https://stacks.math.columbia.edu/tag/08EH), the spectrum comparison and the scheme
   isomorphism transport declarations. The new theorem isolates the derived Hom-colimit step;
   it has neither a section-specific roof nor a chain representative nor K-flatness. The main
   proof genuinely supplies those remaining steps. For empty U one may use P_n=0, giving
   singleton restricted Hom sets and singleton colimit. For zero E all Hom sets are singleton;
   for the zero ring the spectrum is empty; for U=X the constant system P_n=Q(T) works.
   The source allows unbounded E. The docstring gives the finite principal-open presentation,
   localization transport, unit comparison, Hom-set equivalences and cocone transport.
   No object is defined by choosing an arbitrary witness from an unproved existence theorem.
   Independent LeanFinder and Mathlib grep searches used different wording (recorded in
   searches.jsonl and the new node); searches of lean/ and the upstream affine geometry code
   found the spectrum theorem and general transport tools, but no exact existing affine
   colimit assertion. Closing that remaining transport proof is not a few-minute repair.
4. **Route and pruning: pass after import repair.** The proof uses the spectrum colimit
   comparison through its new affine transport step and the proved general K-flat-resolution
   theorem, rather than calculating bounded finite-free terms again. The original public
   dependencies provide symbols needed by the roof signature. Changed the new colimit
   module's public Types.Colimits import to a plain import; recompiled successfully.
   All three old proof dependencies are accounted for under No longer needed. No global
   closure pruning is claimed. Read dag/units/sk-thm-picard-duality.json: its realized
   statement and step lists are empty, and this delivery changes no unit or chapter route.
5. **Records: pass.** Checked both nodes against the Lean statements, and checked that each
   proof_deps list equals the union of the proof steps' uses. The roof node records the
   colimit extraction, right-fraction/K-flat realization and perfectness/cancellation steps.
   The new node has its source, proof in words, statement dependencies, proof dependencies,
   agent origin, searches, split status, creation, blueprint provenance, unit, chapter and
   verbatim Lean record. One hole is closed and one is added: net zero, explicitly reported
   as a decomposition rather than a completed proof of the import closure.

Second reading changed the new colimit module's Types.Colimits import from public to plain,
completed the old-dependency accounting, added independent search records and this review.
The Lean proof bodies and declaration signatures were retained.

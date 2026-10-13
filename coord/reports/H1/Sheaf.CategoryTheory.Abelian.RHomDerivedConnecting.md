## What changed

Replaced the sole deferred proof in
`Sheaf.CategoryTheory.Abelian.RHomDerivedConnecting` with a compiling reduction of
`CategoryTheory.Functor.exists_rhom_hom_derived_connecting`. Its signature, universes,
visibility, hypotheses, and all three conclusions are unchanged.

The proof obtains a single natural, roof-normalized family from the new
`Sheaf.CategoryTheory.Abelian.RHomDerivedRoof` theorem. For the boundary clause it
applies the new `Sheaf.CategoryTheory.Abelian.RHomDerivedRoofShift` theorem to the
class obtained by applying the derived functor to the triangle's third morphism.
It then uses naturality for that morphism and explicitly expands both canonical
boundary maps. Functoriality and associativity identify the resulting composites.
The calculation works for every triangle; the distinguished-triangle hypothesis
is retained in the original signature.

Added the proof-only imports `Sheaf.CategoryTheory.Abelian.RHomDerivedRoofShift`
and `Mathlib.CategoryTheory.Triangulated.Yoneda`. The roof theorem is exposed by
RoofShift's public import, so its additional direct import was removed after
compilation. Added the two new modules, one public deferred theorem per module,
and their DAG nodes. Updated only `proof`, `proof_deps`, and `proof_origin` of the
original node to agree with this calculation. No definition, existing statement,
public import, or other module's interface changes; no adaptations or change
records are needed.

Validation: repeated single-file and dependency-ordered sandbox compilation
succeeded, without errors or warnings. All Lean lines are at most 100 characters.
The original theorem's signature was checked against the repository declaration.
The final delivery dry run checks the complete set and its axiom inventory.

The new statements allow arbitrary integer degrees, arbitrary lower bounds, the
zero object and complex, and independent derived-category Hom universes. Their
normalization quantifies over every degreewise injective bounded below resolution.
For n=0 and negative n the unit-shift calculation still uses the canonical
shift-addition isomorphism; it introduces no sign. For M=0, f=0, or a zero boundary,
all maps preserve zero. No projectivity of M, Grothendieck condition, upper bound,
nonzero condition, or finiteness assumption was added. Data is not extracted into
any definition from an unproved mere-existence statement; the witness is used only
inside a theorem proof.

## Proved and sorry left

Closed the original hole
`CategoryTheory.Functor.exists_rhom_hom_derived_connecting`
(node `lem-sc-p1-rhom-hom-derived-connecting`) by a complete Lean proof from two
strict parts of its argument. No `sorry` remains in the item's module.

Added exactly two deferred public theorems, each with its entire proof `by sorry`:

- `CategoryTheory.Functor.exists_rhom_hom_derived_roof`, node
  `lem-sc-p1-rhom-hom-derived-roof`: Steps 1 and 2, the natural additive comparison
  and cocycle roof formula, with no shift or connecting-map clause.
- `CategoryTheory.Functor.rhom_hom_derived_roof_shift`, node
  `lem-sc-p1-rhom-hom-derived-roof-shift`: the unit-shift computation of Step 3 for
  an already supplied natural roof-normalized family; no family existence and no
  triangle or boundary morphism occurs in its conclusion.

This is a decomposition, not a sorry-free proof of RHom comparison: one upper hole
closed, two lower holes added, net holes closed minus added = -1. The final theorem
still depends on these two deferred results. Their combination is the explicit
naturality/shift/boundary calculation in the original module, rather than an
application of a renamed copy of the complete original statement.

## No longer needed

Removed the original proof-only direct import
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`:
its instances are already exposed by the retained public PlusSingle import.
Removed the trial direct proof import
`Sheaf.CategoryTheory.Abelian.RHomDerivedRoof`, since RoofShift publicly imports it.

Second reading also removed the redundant public import
`Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift` from the new Roof module:
HomComplexSingle publicly imports HomComplexCohomology, which publicly imports it.
The existing module's public imports are unchanged.

No library module or unit is claimed pruned from the targets' import closure.
The original node no longer directly lists
`def-sp-kinjective-bridge`, `lem-weil-pbc-bounded-below-injectives-kinjective`,
`def-weil-abstract-derived-category`, `lem-weil-pbc-kinjective-hom-derived`, or
`lem-weil-pbc-derived-direct-image-triangulated` as proof edges: their uses are
accounted for by the two child nodes. All remain needed transitively; this is
relocation of the proof obligations, not pruning them. The long-exact homology
and representable connecting-map nodes remain direct proof dependencies for
expanding their canonical maps. The chapter and unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The unit record
`sk-thm-picard-duality` has empty `realized` lists; this worker changes neither the
unit nor the chapter. The parent route is retained: cocycle/localization,
naturality/independence, and compatibility via shifting the third morphism.

The original proof-dependency declarations provide K-injective localization,
triangulated right-derived functors, and the two boundary definitions. They do
not themselves supply the all-D+ natural, roof-normalized comparison or its
unit-shift coherence. Those two missing parts are now explicit independent items.
Mathlib's object-resolution Ext comparison is not an all-complexes comparison,
and the cohomology-class localization API is for a fixed Hom complex; neither
is treated as an exact match for the new statements.

LeanSearch was unavailable (Internal Server Error) for both concepts. The failed
requests were recorded as unavailable, without an absence verdict; LeanFinder,
Loogle, source searches, and blueprint searches were also performed. The original
Stacks pages for [06XR](https://stacks.math.columbia.edu/tag/06XR),
[070I](https://stacks.math.columbia.edu/tag/070I), and
[05TE](https://stacks.math.columbia.edu/tag/05TE) were read. The local copy of
`literature/stacks-project/derived.tex` is absent on this machine; the source
records retain the project's standard document path and exact tags. In particular,
05TE supplies the derived-functor/connecting-map context, while the comparison
and its shift calculation use 06XR, 070I and the explicit computation recorded
in the parent's proof, rather than claiming 05TE alone states the full comparison.

## New nodes

`lem-sc-p1-rhom-hom-derived-roof` is the natural additive equivalence with its
normalization on every bounded below injective resolution, corresponding to
parent Steps 1 and 2. Its module is
`Sheaf.CategoryTheory.Abelian.RHomDerivedRoof`. Its docstring and node explain the
cocycle quotient, K-injective localization, inverse-resolution roof, and
naturality/independence. It does not state the boundary compatibility.

`lem-sc-p1-rhom-hom-derived-roof-shift` is the unit-shift coherence for any supplied
family satisfying the first child's two conditions, corresponding to the shift
computation in parent Step 3. Its module is
`Sheaf.CategoryTheory.Abelian.RHomDerivedRoofShift`. Its docstring and node explain
calculation on cocycle representatives and transport by naturality, retaining
all canonical shift comparisons. It does not mention triangles or prove
existence of the comparison family. Both nodes belong to the parent's chapter
and unit and point to the same blueprint ancestor through the parent and its
Ext-resolution caller. No change record is required.


## Second reading by H1

1. **Interface preservation: pass.** Read the complete repository and sandbox modules
   and their diff. The existing declaration, from `theorem` through its final conclusion,
   is byte-for-byte identical before `:= by`. Universes, all category assumptions, the
   every-resolution formula, and the distinguished-triangle restriction are preserved.
   There is no changed definition or existing public import. Only the author line,
   private proof imports, and proof body differ. No forced adaptation or change record.

2. **Proof and axioms: pass as a decomposition.** Independently compiled all three
   modules in import order, including again after the import repair, with no errors or
   warnings. Read each proof: the only two sorries are the public named child theorems
   listed above; neither file introduces a definition or forbidden declaration.
   A separate scratch import with `#print axioms` for all three declarations printed
   exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The parent's
   `sorryAx` is expected from the two unresolved children; this is not a completed
   axiom-free RHom comparison. The existential witness is eliminated inside a theorem,
   never used to choose data for a definition.

3. **Split statements: pass.** Read both child signatures, docstring proofs and nodes.
   The roof theorem is exactly the first two parent clauses, omitting the boundary
   clause. The shift theorem assumes these clauses and proves a one-object shift
   equality, without asserting family existence or mentioning any triangle. Neither
   restates the whole parent. Read Stacks [06XR](https://stacks.math.columbia.edu/tag/06XR)
   (injective-resolution Ext computation), [070I](https://stacks.math.columbia.edu/tag/070I)
   (K-injective localization), and [05TE](https://stacks.math.columbia.edu/tag/05TE)
   (derived delta-functor context). The full normalized comparison and shift formula
   require the explicit arguments in the docstrings, not a claim that 05TE states them.
   EnoughInjectives suffices for bounded below injective representatives; no projective
   M or Grothendieck hypothesis is used. Checked zero M/classes/maps, degree zero and
   negative degrees, and shifted lower bounds: the formulas preserve zero, and the
   right-target shift is unsigned for every integer. Read Mathlib HomComplexShift's
   unsigned right shift (in contrast to left shift), KInjective localization, and the
   upstream `commShift_rightDerivedFunctorPlusUnit` instance: the derived unit really
   commutes with the canonical shift used in the child's formula. Its invertibility
   on degreewise injectives supplies all cocycle representatives. These observations
   rule out arbitrary degree-dependent signs in a normalized family.

   Independently searched LeanFinder with a localization/translation query, Loogle
   with `"CohomologyClass", "shift"`, and Mathlib grep for
   `extEquiv|toHom_mk|toSmallShiftedHom|commShift.*Unit|Unit.*commShift` (recorded in
   searches.jsonl), and searched both source roots with alternate Hom/cohomology
   words. Read the resulting fixed-complex localization declarations, PlusSingle's
   injective-object computation, and Sheaf.ExtRightDerivedHom's object-level theorem.
   They are ingredients rather than either complete child statement. Neither child
   can be closed by a brief application of an existing result found in this reading.

4. **Top-down route and imports: pass after repair.** Read the actual reduction:
   obtain one normalized family; apply the shift child to H^n(RV(T.mor3))(a);
   rewrite by that same family's naturality; expand the representable boundary and
   derived homology boundary. The resulting composites agree by map composition and
   associativity. This works for arbitrary triangles, hence the required distinguished
   ones. The calculation is genuine and does not merely rename the deferred theorem.
   Removed one redundant direct import in the new Roof module; recompiled the set.
   Existing public imports were retained. `No longer needed` lists all five original
   proof edges relocated to children and the removed imports, without claiming those
   transitively required nodes are pruned. Read the unit sk-thm-picard-duality: its
   realized statement and step lists are empty; no realized route is bypassed or
   edited. The parent's cocycle, naturality, then shift/boundary route is retained.

5. **DAG consistency: pass.** Compared the parent JSON with the repository: only
   proof, proof_deps and proof_origin differ. Every proof_deps list equals the union
   of its steps' uses. Checked the new nodes' source, chapter/unit, ancestor/via,
   creation record, search records, status and full Lean signatures. Each new module
   carries precisely its named theorem and matching node. Their arguments match
   the docstrings and the parent invokes both declarations exactly as its new plan
   records. No statement or definition is silently revised.

**Second-reading changes:** removed the redundant direct HomComplexShift public import
from the new Roof module and recorded that removal here and under No longer needed.
Proofs and statements needed no repair. One original hole closed, two lower holes
added: this remains a decomposition, net -1, with no library module pruned.

## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.CoherentSupportUnionExactSequence`
with a complete Lean reduction following Stacks Tag 01YD. The statement and all four
public imports are unchanged. The construction uses the actual Mathlib vanishing ideal
of Z, restricts to the Noetherian open X minus Z', applies the existing ideal-power
annihilation theorem, and takes the canonical image inclusion of K^t F.

Private, fully proved helpers establish quasi-coherence of multiplication images,
the proper-stalk locus of an ideal, the restriction-stalk singleton comparison,
and vanishing of quotient stalks where the ideal is the unit ideal. Coherence follows
from the existing coherent-submodule theorem. Short exactness follows directly from
the abelian cokernel sequence. Both support inclusions are proved in Lean.

Added one general restriction lemma in a new module; its mathematical proof and source
are in its docstring and node. Updated the original node's proof, proof_deps and
proof_origin to match the reduction. No existing definitions, signatures or visibility
were changed, and no forced adaptations are needed.

Validation: both sandbox modules compile together using lcompile.py without warnings.
The zero exponent is handled explicitly in both quasi-coherence and the quotient-stalk
calculation; it is not silently excluded. The original source was read at
https://stacks.math.columbia.edu/tag/01YD because literature/stacks-project/coherent.tex
is not present on this machine. The new restriction lemma was checked at exponent zero,
for the empty open, the zero module, and the zero and unit ideals: in each case its two
sides are the same zero-object condition under the canonical restriction comparison.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.exists_coherent_submodule_of_support_union`
(node `lem-weil-pbc-coherent-support-union-exact-sequence`). No sorry remains in that
module. The four private helpers are fully proved.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.idealPowerProduct_restrict_isZero_iff`, in module
`Sheaf.AlgebraicGeometry.IdealPowerProductRestrictionZero`, node
`lem-weil-pbc-ideal-power-product-restriction-zero`.

This is a decomposition: one upper hole closed, one strictly smaller structural hole
added, net zero holes before pruning. Existing imported declarations may still rest on
sorry; this delivery claims the compiled reduction, not axiom-free closure of the target.
No data definition takes a witness from the new theorem.

## No longer needed

Removed these direct proof imports and their original direct proof dependencies:

- `Sheaf.Algebra.Homology.ModuleStalkExact` /
  `lem-weil-pbc-module-stalk-exact`: use the categorical cokernel sequence and the already
  stated ideal-product quotient stalk formula.
- `Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase` /
  `def-weil-pbc-closed-subset-proper-over-base`: support is the inline nonzero-stalk locus.
- `Sheaf.AlgebraicGeometry.CoherentFormalModule` /
  `def-weil-pbc-coherent-formal-module`: use the actual product, powers and cokernel
  directly, without the unrelated category of formal modules.
- `Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme` /
  `lem-weil-pbc-reduced-induced-closed-subscheme`: Mathlib's vanishingIdeal and its support
  equality supply the ideal; the reduced-subscheme existence theorem is unnecessary.
- `Sheaf.Topology.PresheafModuleStalkFunctor`: Mathlib's restriction-stalk isomorphism
  and the ringed-space module stalk functor suffice; the extra general presheaf functor
  is unnecessary. The stalk definition node is still mentioned in the updated proof
  because the argument does use stalks.

- `pqf-def-coherent`: no longer a separate proof dependency; its definition remains
  a statement dependency and `Sheaf.AlgebraicGeometry.Coherent` remains publicly imported.

These are removals from this module's direct dependency list, not claims that no other
branch of the targets imports those modules. Some remain transitively reachable through
other dependencies. None of the removed imports realizes a mandatory statement or proof
step of unit sk-thm-p1; that unit's route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The original plan's restriction step needs a comparison for every ideal power. The
existing ideal_times_quasiCoherent_affine_sections declaration supplies restriction of
one product whose ideal is encoded by IdealSheafData. Its quasi-coherent power clause
supplies module sheaves with inclusions, not new IdealSheafData objects, so the asserted
inductive application does not directly typecheck. The new lemma isolates exactly this
comparison, rather than restating the support-splitting result. Its proof in words
explains the required identification of restricted inclusions and the induction on
powers, including exponent zero.

The plan also invokes the formal-module category and stalkwise exactness unnecessarily:
the shared power construction is already in IdealModuleProductStalk, and a monomorphism
followed by its canonical cokernel is short exact in the abelian category.

Searches: Lean Finder found only ring-module support results for the main theorem;
Loogle confirmed the categorical cokernel API; rg found no other support-union theorem
in Sheaf or WeilConjectures. For the new restriction lemma, LeanSearch was unavailable
(HTTP Internal Server Error), Lean Finder returned only section localization results,
and rg found only the single-product restriction statement. The whole blueprint search
for "ideal power restriction" found no matching node. These outcomes are recorded in
the new node, without treating an unavailable search as a negative mathematical result.

## New nodes

`lem-weil-pbc-ideal-power-product-restriction-zero` states that restriction of K^n F to
an open is zero iff the product of the restricted ideal power and restricted F is zero.
This is precisely the general structural content of step 6 of the old plan, sourced to
the proof of Stacks Tag 01YD and the tensor/product restriction facts. It has no support
union hypotheses, no existential choice of submodule, no coherence or exact-sequence
conclusion, and is strictly a part of the argument. Its new module is
`lean/Sheaf/AlgebraicGeometry/IdealPowerProductRestrictionZero.lean`.
No change record is needed: every existing signature and definition is unchanged.


## Second reading by S2

1. **Interfaces: pass.** Compared the delivered main module with the repository by
   `diff -u`, and compared its theorem signature as an exact string through `:= by`.
   `exists_coherent_submodule_of_support_union` is byte-for-byte unchanged: locally
   Noetherian and compact X, coherent F, closed Z and Z', support equality, and all
   five conclusions. All four original public imports remain unchanged. Only private
   proof helpers were added. The existing node changes exactly `proof`, `proof_deps`,
   and `proof_origin`; no definition or existing signature changed.

2. **Lean proof: pass as a decomposition.** Independently compiled both delivered
   modules in import order with lcompile.py, without errors or warnings. Inspected
   all definitions used to construct K, G', and i: vanishingIdeal, image, and powers
   are real constructions; no data is selected from an unproved mere existence theorem.
   The only delivered sorry is the named restriction lemma. Scratch copies with
   `#print axioms` checked that lemma, the main theorem, and all four private helpers.
   Only propext, Classical.choice, Quot.sound, and sorryAx occur. The proper-locus
   and restriction-stalk helpers use only the three allowed axioms; the other results
   still depend on open imported theorems. There are no forbidden declarations.

3. **Split-off statement: pass.** Read the new Lean declaration and its node against
   the definitions of idealModuleProduct and idealSheafPower. It asserts just the
   zero-object comparison under restriction for a quasi-coherent ideal and module;
   it assumes no support decomposition and constructs no submodule or exact sequence.
   It is true and strictly smaller than the item. At n = 0 both products are F up to
   the unit isomorphism; for the zero ideal and n > 0 both are zero; for the unit
   ideal both are F; the empty open and F = 0 give zero on both sides. Read Stacks
   [01YD](https://stacks.math.columbia.edu/tag/01YD),
   [01I8](https://stacks.math.columbia.edu/tag/01I8),
   [01CE](https://stacks.math.columbia.edu/tag/01CE), and
   [01CD](https://stacks.math.columbia.edu/tag/01CD). The last is the actual pullback
   tensor comparison; 01CE concerns preservation of quasi-coherence by tensoring.
   Corrected the new lemma's citation to 01CD and expanded its complete prose proof:
   restriction preserves sectionwise kernels and adjunction preserves cokernels;
   the tensor and unit comparisons respect multiplication on pure tensors; induction
   identifies power inclusions and then their products with F.
   Independently searched with Lean Finder for "image of multiplication by ideal
   sheaf commutes with pullback along open immersion": results included
   ideal_comap_of_isOpenImmersion, but no product-power restriction theorem. Searches
   with rg in Sheaf, WeilConjectures, the upstream checkout, and Mathlib found no
   duplicate. The existing single-product theorem compares subobjects for an
   IdealSheafData input; it does not supply the iterated power-inclusion comparison.
   Formalizing that comparison requires more than a short replacement proof, so the
   named structural hole remains and the delivery claims net zero holes closed.

4. **Route and pruning: pass after report repair.** Read the actual six proof steps.
   The vanishing ideal has support Z; its proper-stalk locus is identified by the
   zero-set theorem. The open complement is Noetherian, restriction preserves
   coherence, and the stalk comparison transports the support containment, so the
   power-annihilation theorem applies with every hypothesis available. The new
   comparison gives vanishing on that open. Quasi-coherence of powers, tensors, and
   images and the coherent-submodule theorem give both coherence conclusions.
   Monicity plus the categorical cokernel sequence gives short exactness. Finally
   the restriction-stalk isomorphism gives the first support bound; the quotient
   stalk formula with unit ideal gives the second, separately handling n = 0.
   No hypothesis was silently strengthened. Reviewed sk-thm-p1.json `realized`:
   none of the removed dependencies realizes a mandatory unit statement or step.
   The report now additionally lists pqf-def-coherent among removed direct proof
   dependencies, while retaining its statement dependency and public definition
   import. Replaced the new module's unused public Tilde import with the specific
   Quasicoherent import that supplies its hypothesis. All remaining imports supply
   statement vocabulary or declarations used in the reduction.

5. **Nodes: pass.** Matched the existing node's six steps to the Lean argument above
   and checked that proof_deps is their union. The new node's chapter, unit, source,
   blueprint ancestry, created record, Lean module/declaration/signature, and searches
   are present. Its four prose steps prove the stated restriction comparison rather
   than reasserting support splitting. Clarified its exactness/multiplication step,
   corrected its source to 01CD, and explicitly marked the failed LeanSearch service
   as unavailable. The new node and theorem agree, and no change record is needed.

Changes from this reading: narrowed the new module import; corrected its tensor
restriction source; expanded its prose proof and matching node step; completed the
removed-dependency report; recorded the unavailable search verdict. No Lean proof
body or theorem signature changed during this reading.

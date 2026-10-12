## What changed

Replaced the sorry in `AlgebraicGeometry.idealPowersReesGradedData` with a compiling
proof from two strictly smaller intermediate statements. Its signature, existing
public imports, and all definitions are unchanged. Four proved private helpers
establish quasi-coherence of products and powers, sectionwise injectivity, and
heterogeneous equality by monomorphism cancellation. The proof derives additivity,
composition, and the degree-zero scalar identity from the section formula.

Added `Sheaf.AlgebraicGeometry.IdealPowersReesMultiplication` for the existence of
multiplication maps, without the finite-type, properness, or Noetherian assumptions.
Added `Sheaf.AlgebraicGeometry.IdealPowersReesZeroGenerators` for local generation
in degree zero, assuming only quasi-coherence, finite type, and the section formula
for a given action. These are independent parts of the argument, rather than
restatements of the original conjunction. The main proof combines them with the
proved laws and quasi-coherence. Updated the original DAG proof to match.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.idealPowersReesGradedData`
(node `lem-weil-pbc-ideal-powers-rees-graded-data`). There is no sorry left in the item.

Added two holes, each the whole proof of its named public theorem:

- `AlgebraicGeometry.idealPowersReesMultiplication`
  (node `lem-weil-pbc-ideal-powers-rees-multiplication`).
- `AlgebraicGeometry.idealPowersReesZeroGenerators`
  (node `lem-weil-pbc-ideal-powers-rees-zero-generators`).

This is a decomposition: one hole closed, two added, net minus one hole. It is not
an unconditional proof of the original theorem. The existing statements imported
by the new nodes remain their future proof dependencies. All three delivered
modules compile; no axioms or data definitions were added. Edge cases checked in
the mathematical arguments: empty scheme, zero module, zero and unit ideals,
zeroth power, and degree-zero multiplication.

## No longer needed

Removed the item's direct proof imports of
`Sheaf.AlgebraicGeometry.ModulePullbackIdealQuotient` and
`Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`.
Their nodes are no longer direct proof dependencies of the original theorem;
they remain proof dependencies of the two new, smaller statements and are imported
there. Consequently no global module or node pruning is claimed.

The main quasi-coherence proof uses tensor quasi-coherence and the existing proved
kernel/cokernel closure results. It does not use the affine section formulas or
quotient comparison directly. The old direct proof dependency `pqf-def-coherent` is also no longer used directly
by the main proof; it remains a statement dependency and is used by the new
generation theorem. Removed the redundant private import
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module` from the main module:
its declarations are already publicly available through the original imports.
All original public imports are retained for the unchanged interface.

## Where the brief, the DAG or earlier work was wrong

No statement error or departure from the unit route was found. The existing
interfaces do not provide the two sheaf-level constructions that the original
proof sketch describes: multiplication lifts for all degrees, and the local
Rees span condition. They are now explicit parallel items with complete proofs
in words. The original sketch's algebraic-law step has been proved directly.

The source was read at the existing literature mirror's `coherent.tex`, lines
5330--5400, including the preceding multiplication-map paragraph and Tag 02O8.
The source uses a surjection from the pulled-back Rees algebra; this delivery
does not assume that pullback is injective or that the morphism is flat.

## New nodes

`lem-weil-pbc-ideal-powers-rees-multiplication` records the coefficient-multiplication
maps and their gluing. Its module contains one public theorem with a complete
source-based proof in its docstring. The maps are uniquely determined by their
inclusions into F; no arbitrary data is defined from an existence theorem.

`lem-weil-pbc-ideal-powers-rees-zero-generators` records the degree-zero generating
family and its local span property for any action satisfying the section formula.
Its module contains one public theorem with a complete source-based proof in its
docstring. This isolates finite generation from construction of the action.

There are no change records: no existing interface, definition, or statement changed.

## Second reading by X3

1. Compared the main module with the repository by diff and extracted its theorem
   signature: byte-for-byte identical. All original public imports and definitions
   are unchanged. The other two modules are new; there are no forced adaptations
   or undeclared interface changes. Verdict: pass.
2. Independently compiled all three delivered modules with lcompile.py. The main
   theorem has no sorry; the only two delivered sorries are the complete named
   theorem proofs listed above. No forbidden declarations or hollow definitions
   occur. Scratch-copy #print axioms checks show only propext, Classical.choice,
   Quot.sound and sorryAx for the three public theorems; this is a conditional
   decomposition, not a closed proof. No object is defined by choosing an arbitrary
   existence witness. The coefficient formula uniquely determines every mu under
   its monomorphic inclusion. Verdict: pass.
3. Read both new statements, their docstring arguments, and Stacks coherent.tex
   lines 5330--5405 from the local literature mirror. Multiplication containment
   and local degree-zero generation are separate, strictly smaller assertions.
   Checked m=0, k=0, the zero/unit ideals, the zero module and the empty scheme.
   The powers of the extended ideal are generated locally by images of I^m;
   this requires neither flatness nor injectivity of pullback. Independent Lean
   Finder, Loogle and repository rg searches found no duplicate theorem. The
   existing finite-type local-generators result supplies only the generators of F,
   not the asserted Rees span. Neither remaining hole admits a short direct proof
   from an existing declaration. Verdict: pass.
4. Read the main proof from its conclusion down: obtain the action, establish
   quasi-coherence by tensor/image closure, cancel monic inclusions to prove the
   three algebraic laws, and specialize the generation degrees to zero. The
   existing CoherentFormalModule quasi-coherence helpers are private. No shorter
   public theorem supplies the entire reduction. Checked sk-thm-p1.json realized
   and its unit source: this auxiliary split changes none of the unit steps or
   their realizing nodes. The pruning report now lists all three old direct proof
   dependencies removed; no global pruning is claimed. Verdict: pass.
5. Compared all node changes: only proof, proof_deps and proof_origin change in
   the existing node. Each proof_deps list is exactly the union of its step uses,
   and each referenced node exists. New nodes have sources, complete proof plans,
   search records, creation/blueprint/unit/chapter metadata and Lean declarations.
   Corrected their omitted def-pc-scheme statement dependency, which their prose
   already cites, and stored their signatures verbatim. Verdict: pass.

Second-reading changes: removed one redundant private import from the main
module; completed the direct-dependency pruning report; corrected the two new
nodes' statement-dependency lists and verbatim signatures; recorded independent
searches and this review. No mathematical statement or proof was changed.

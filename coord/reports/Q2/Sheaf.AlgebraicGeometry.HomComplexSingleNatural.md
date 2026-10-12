## What changed

Proved `AlgebraicGeometry.homComplex_single_natural_iso` in
`Sheaf.AlgebraicGeometry.HomComplexSingleNatural`, with its statement and
visibility unchanged. The proof uses the degree-zero product projections from
`homComplex_exists`. All other factors are zero, so the product universal
property makes each projection an isomorphism. The differential and map formulas
prove compatibility with differentials and naturality. A proved private
`natIsoOfDegreewise` helper assembles these into the natural isomorphism.

The previous sandbox attempt timed out. Small proved helpers handle zero-source
internal Hom, the zero precomposition map, and the sole nonzero product factor.
The proof chooses projection data from the already proved `homComplex_exists`;
it adds no data chosen from an unproved existence theorem. Proof-only import
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree` supplies
contravariant additivity. The original public import stays unchanged.

The second reader repaired reproducible 60-second compile timeouts by adding a
proved private `homComplex_spec` wrapper around `homComplex_exists.choose_spec`.
It exposes the existing projection formulas with `homComplexFunctor` in their
types, avoiding repeated unfolding of the chosen bifunctor during elaboration.
The differential simplification now uses `with_reducible`. Both changes affect
only proofs and private helpers; they add no public statement or hole.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.homComplex_single_natural_iso`
(node `lem-sc-hom-complex-single-natural`). No holes remain in the item, and no
new holes or modules were added. This is a proof, not a decomposition.
All private helpers are proved. The full module compiled through `lcompile.py`.

## No longer needed

Removed the redundant direct proof-only import
`Sheaf.Algebra.Homology.HomComplex`: the unchanged public import
`Sheaf.AlgebraicGeometry.HomComplexSingle` already publicly imports it.
The Hom-complex module and node `def-pur-hom-complex` remain needed for the
product, differential, and map formulas. Node `lem-sc-hom-complex-single`
remains needed for the additive instance used by the termwise Hom functor.
No mathematical dependency, DAG node, or transitive module is claimed as pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error was found. The DAG's route is unchanged,
and `dag/units/sk-thm-picard-duality.json` has no realized unit step bypassed
by this proof. The objectwise theorem alone does not specify natural
projections. Its private product helper is unavailable to importers, so this
proof reconstructs the elementary product argument privately.

The earlier report claimed a proof without a successful compile. The revised
proof compiles: generic proved helpers keep Lean from repeatedly unfolding
large scheme-specific types while constructing componentwise isomorphisms.
The transparency setting is local to the theorem. No compiler tool, library
source, definition, or public interface was changed.

Searches were rerun through `msearch.py`: Lean Finder returned group-valued
single-source Hom-complex equivalences, Loogle found `NatIso.ofComponents`
(used by the generic assembly helper), and the prescribed grep search found
zero matches. Local source searches found the proved objectwise comparison
and the Hom-complex specification, but no shorter internal sheaf-valued natural
comparison. Source checked: Stacks Project tag 0A8X, Hom complexes,
https://stacks.math.columbia.edu/tag/0A8X (the local literature TeX copy is absent
on this machine). Its product and differential formulas specialize exactly to
the projection argument. No boundedness, nonzero-object, or nonempty-scheme
hypothesis enters the construction; zero factors are handled by `IsZero`.

## Second reading by Q2

1. Compared the delivered module with the repository using `diff` and checked
   the existing theorem signature as literal text: byte-for-byte identical.
   Its visibility, docstring, public import, and all public definitions remain
   unchanged. Only the claimed module is delivered. No change record is needed.
   Verdict: pass.
2. Read every private helper and the complete target proof. The repaired module
   compiles without warnings. A scratch copy with `#print axioms
   AlgebraicGeometry.homComplex_single_natural_iso` compiled in 26.1 seconds
   and reported exactly `propext`, `Classical.choice`, and `Quot.sound`.
   There is no `sorry`, forbidden declaration, or hollow definition. Projection
   data come from the proved Hom-complex specification, and the sole-factor
   inverse is a real product lift. Verdict: pass.
3. No split-off statements, new holes, or new public statements are delivered.
   Checked the product argument when every factor, including the distinguished
   one, is zero; zero source and target sheaves; empty schemes; and arbitrary
   integer degrees and unbounded target complexes. None requires an extra
   hypothesis. Independent searches used Loogle `"IsZero", "IsLimit"`, Lean
   Finder for a unique nonzero product factor, and grep for single-functor/sheaf
   Hom combinations. The results give generic zero limits and binary zero
   products, not this natural sheaf-valued chain comparison. Local searches
   confirmed the objectwise comparison and its private inaccessible product
   helper. Verdict: pass.
4. Read the proof from the target downward, including the product, differential,
   and map clauses of `homComplex_exists`, and checked them against Stacks tag
   0A8X, https://stacks.math.columbia.edu/tag/0A8X. Objectwise existence alone
   does not provide naturality; the specified projections do. The sole remaining
   public import is needed for signature types and its additive instance; the
   plain InternalHomFree import supplies contravariant additivity. The report's
   pruning list is complete: the redundant direct HomComplex import is removed,
   but neither of the old mathematical proof dependencies is pruned. Read the
   unit's `realized` record: no realized step is bypassed. Verdict: pass.
5. Read node `lem-sc-hom-complex-single-natural` and both old `proof_deps`.
   Its product-projection and differential/naturality steps describe the actual
   proof; `lem-sc-hom-complex-single` supplies the additive instance and
   `def-pur-hom-complex` supplies the specification. The source and proof origin
   still agree. No node changes are necessary. Verdict: pass.

Changed the private proof plumbing to repair repeated local 60-second timeouts:
added the proved `homComplex_spec` wrapper, used its projections instead of
elaborating `homComplex_exists.choose_spec` directly in the scheme-specific
proof, and restricted differential simplification with `with_reducible`.
The repaired proof and its axiom check finish in about 26 seconds. No public
interface, definition, mathematical route, or hole count changed in this repair.

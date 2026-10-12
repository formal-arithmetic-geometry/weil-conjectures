## What changed

Replaced the sorry in `RingHom.popescu_smoothing` by a complete Lean proof of the existing
six-step DAG plan, without changing its signature, public imports, or docstring.

Three fully proved private helpers implement the glue:

- `RingHom.smooth_factorization_of_resolutions`: choose a maximal radical of an extended
  singular ideal among finitely presented factorizations. A resolution at a minimal prime
  strictly enlarges any proper maximal radical, a contradiction. The radical is therefore
  the unit ideal, and `Algebra.exists_smooth_factorization_of_singularIdeal_map_eq_top`
  supplies the smooth factorization.
- `RingHom.geometricallyRegular_of_regular_field`: identify the residue field of the zero
  ideal of the base field with the field, transfer each finite purely inseparable extension
  to that residue field, and use tensor base-change cancellation to recover geometric
  regularity of the original target.
- `RingHom.field_ind_smooth`: the trivial purely inseparable extension gives regularity of
  all prime localizations. In characteristic zero, Mathlib gives separability of each
  finitely generated subextension of the residue field; apply the separable resolution
  theorem. In positive characteristic apply the characteristic-p resolution theorem.
  The maximal-ideal helper and the factorization criterion give the field colimit.

Apply `popescu_reduce_to_field` at universes `u, u` to obtain the general algebra colimit.
`HasRingHomProperty.Spec_iff` gives smooth affine stages. The equivalence with rings under
R and preservation of connected colimits by the under-category forgetful functor give the
required colimit in commutative rings.

Added proof-only imports of Mathlib's connected under-category colimits, filtered-category
connectedness, minimal primes, and separably generated extensions. Every original
proof-dependency import is used by the argument; the route and dependency nodes remain
unchanged, so no node copy is needed.

Searches: LeanFinder for regular maps as filtered colimits returned smoothness/descent
lemmas, not Popescu's theorem; Loogle for `Algebra.Smooth` returned its class and basic
properties; the logged grep for Popescu/Neron/desingularization returned only the unrelated
Gabriel-Popescu theorem. Searches of both library roots found the planned dependency
modules and no shorter proof. Read the source proof at
https://stacks.math.columbia.edu/tag/07GC, which uses exactly the field reduction,
Noetherian induction, final solve, and characteristic-specific resolutions implemented here.

## Proved and sorry left

Closed: `RingHom.popescu_smoothing` (node `lem-weil-pbc-popescu-smoothing`), one of one
original holes. Added holes: none. Sorry left in the delivered module: none.

The three private helpers are proved without sorry. The proof uses the existing named
statements `popescu_reduce_to_field`,
`CommAlgCat.exists_filtered_colimit_of_factorization`,
`Algebra.exists_smooth_factorization_of_singularIdeal_map_eq_top`,
`Algebra.canBePopescuResolved_of_regularLocalRing_separable`, and
`Algebra.canBePopescuResolved_of_char_pos`; their existing sorries are separate items and
are not changed or duplicated. This closes the upper hole from existing dependencies;
it does not certify that its transitive dependencies are already sorry-free.

Local compilation passes without errors or warnings. The delivery dry run performs the
server compile, axiom probe, signature checks, and stage-3 preflight.

## No longer needed

Removed proof-only imports `Sheaf.FieldTheory.SeparableExtension`, `Sheaf.RingTheory.PopescuResolution`,
`Sheaf.RingTheory.SingularIdeal`, and `Mathlib.RingTheory.Ideal.MinimalPrime.Basic`; all declarations
remain available transitively from the modules that are still imported. No dependency nodes or modules
are pruned, and no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy was found. The local checkout does not contain
`literature/stacks-project/smoothing.tex`; the corresponding original source proof was read
on the Stacks Project website instead. The universe-compatible field reduction and
resolution signatures fit at `u` throughout, so no statement or definition adaptation was
necessary.


## Second reading by A3

1. I compared the delivered module with the repository version. The public theorem signature,
all existing declaration statements, and its docstring are unchanged byte for byte; only its proof,
proof-only imports, and private helper proofs differ. Verdict: pass.

2. I compiled the module with `lcompile.py`; it succeeds without errors or warnings. The module
contains no `sorry`, axiom, unsafe, opaque, extern, or implemented_by declaration. An axiom probe
shows only the permitted base axioms for the public theorem; remaining `sorryAx` comes solely from
its imported open dependencies. Verdict: pass.

3. The proof follows the six-step Popescu route: reduction to a field, factorization criterion,
resolution at minimal primes in characteristic zero or positive characteristic, Noetherian maximal
ideal argument, final smooth factorization, and transport to commutative rings. The helper statements
are private intermediate reductions, not restatements or new public holes. The maximal-ideal and
minimal-prime facts, separable-generation fact, and connected under-category colimit facts were
checked against Mathlib declarations and the source theorem 07GC. Verdict: pass.

4. The route preserves the unit's planned ingredients and uses every remaining proof dependency.
Four redundant proof-only imports were removed after a successful compile; the corresponding DAG
proof dependencies remain because they describe the source route and are available transitively.
No statement or definition was changed. Verdict: pass.

5. The DAG node `lem-weil-pbc-popescu-smoothing` still matches the theorem and its proof origin;
no new nodes were added, and `realized` unit data is unaffected. The source theorem was spot-checked
at the Stacks Project tag 07GC, including its hypotheses and six proof steps. Verdict: pass.

Changed in second reading: removed the four unused proof-only imports and corrected this report's
pruning record; no Lean statements or definitions required repair.

## What changed

Proved `CategoryTheory.tor_one_change_of_rings_surjective` in
`Sheaf.Algebra.TorOneSurjectiveChangeRings`, preserving its signature, universes,
and visibility. The second reader narrowed imports as described below. Added a fully proved private helper
`CategoryTheory.epi_homology_one_of_right_exact`. The proof uses only Mathlib APIs.
Updated the theorem's proof description and its node's proof, proof dependencies
and origin to record the actual argument.

Scalar extension preserves the right-exact augmented pair. The helper constructs
maps from target resolution degrees zero and one into the base-changed complex,
and a right inverse up to homotopy in those degrees. After the additive tensor
functor, the composite on cycles differs from the identity by a boundary. This
proves that the map on first homology is epi, hence surjective. The argument is
valid for any coefficient module, including zero, any ideal (zero or unit), and
any ring homomorphism; no flatness, injectivity or nonzero assumptions are used.
All auxiliary morphisms are obtained by Mathlib's proved projective lifting
constructions, with no witness chosen from an unproved theorem.

The change is below unit `sk-thm-p1`; its realized statement and proof route are
untouched. The same Tor-surjectivity node continues serving its original callers.

## Proved and sorry left

Closed: `CategoryTheory.tor_one_change_of_rings_surjective`
(node `lem-weil-pbc-tor-one-surjective-change-rings`), one of one original holes.
The private helper is also fully proved. No `sorry` remains, and no holes were
added or split off. This is a complete proof, not a decomposition.

Local compilation is clean. `#print axioms` for the public theorem reports
exactly `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

The second reader removed the direct public imports
`Mathlib.CategoryTheory.Monoidal.Tor` and
`Mathlib.Algebra.Category.ModuleCat.Projective`, replacing them with the smaller
`Mathlib.CategoryTheory.Preadditive.Projective.Resolution` and
`Mathlib.LinearAlgebra.FreeModule.Basic` needed by the public signature.
`Mathlib.CategoryTheory.Abelian.Projective.Resolution` is a plain proof import.
No Sheaf/WeilConjectures dependency module is pruned.

The proof does not need the original route's nodes
`lem-weil-pbc-free-module-base-change-free`,
`lem-weil-pbc-module-tensor-cancel-base-change`,
`lem-weil-pbc-free-module-projective`, or
`lem-weil-pbc-tor-map-via-resolution-lift`. These are Mathlib matches rather than
unproved project modules. No auxiliary all-degree free resolution or Tor
resolution-comparison construction is needed.

`def-weil-pbc-free-module` and `def-weil-pbc-tor-modules` are no longer proof
dependencies; they remain relevant to the unchanged freeness hypotheses and Tor
interpretation, respectively. Do not prune their statement uses. The proof keeps
`lem-weil-pbc-tensor-right-exact` and `def-weil-pbc-exact-sequence`, and uses the
existing Mathlib leaf `def-weil-pbc-projective-module` for lifting.
No actual imported project modules are claimed to have been pruned.

## Where the brief, the DAG or earlier work was wrong

The old five-step plan is mathematically viable but unnecessarily long. A partial
homotopy right inverse in degrees zero and one suffices. The original Lean
statement already expresses the source as the tensor of the base-changed
complex, so tensor cancellation is not needed in its proof. Projectivity of G
is part of `ProjectiveResolution`; its explicit freeness hypothesis and that of F
are stronger than this proof needs. Both hypotheses are preserved verbatim.
The right-exact presentation is the step used from Stacks 00MN; the partial
comparison proof is written by T2 and is marked as such in `proof_origin`.

## New nodes

None. The private helper is proved in full as local proof infrastructure for the
existing node. No public statement or definition changed. The narrowed public imports are
recorded in `coord/changes/TorOneSurjectiveChangeRings-imports.md`.
No forced adaptation is required.


## Second reading by T2

1. **Unchanged statements: pass.** Read the complete repository/sandbox Lean
   diff and node diff. The sole existing theorem's signature, from `theorem`
   through `:= by`, is byte-for-byte identical, including universe `u`, both
   freeness hypotheses, the arbitrary chain map `φ`, its augmentation equation,
   and the precise first-homology map. No definitions or target statements changed.
   The changed theorem docstring accurately explains the new proof. The private
   helper is fully proved proof infrastructure and adds no public interface.
   The import narrowing is declared in the change record above.
2. **Proof and trust: pass.** Compiled the delivered module locally with
   `lcompile.py`. In a scratch copy, printed axioms of both the public theorem
   and private helper: each uses exactly `propext`, `Classical.choice`, and
   `Quot.sound`. Scanned the delivered source: no `sorry`, forbidden declaration,
   hidden axiom, or data definition. Read `Projective.factorThru`, the exact-pair
   lifting API, and the projective-resolution exactness used by the proof.
   The maps `b₀`, `b₁`, `s₀`, `s₁` are choices supplied by proved projective
   lifting, never arbitrary data from a holed existence theorem. Checked the
   subtraction identity before `s₁`, cancellation into `iCycles`, and the final
   factorization of the epimorphic homology projection.
3. **Split statements: pass, none.** No hole or public statement was split off.
   The private helper requires precisely a right-exact augmented pair with epi
   augmentation, a projective resolution of the same object, a compatible map,
   and an additive functor. Its cycle calculation does not assume that the
   source is exact in positive degrees or that the functor preserves kernels.
   Zero modules, zero/unit ideals, the zero ring, identity and nonflat ring maps
   introduce no extra assumption; for the unit ideal the tensor target is zero.
4. **Shortest route and pruning: pass after import repair.** Read Stacks Tag
   [00MN](https://stacks.math.columbia.edu/tag/00MN),
   `lemma-surjective-on-tor-one-trivial`, including its common-cycles argument.
   The Lean statement retains all its hypotheses and expresses the same map
   using the tensor base-change identification already explained in the module.
   Searched with a new LeanFinder query about an additive functor on a
   right-exact augmented complex and a grep query about epi homology/lifting;
   searched project sources for homology epis and upstream for Tor comparisons.
   The hits require degreewise epis, short exact sequences, or full resolutions;
   none replaces this partial lifting argument. Read Mathlib's resolution
   comparison API; its homotopy equivalence requires two resolutions, whereas
   `K` need not be one. All six old proof dependencies omitted by the new
   argument are listed under No longer needed. Read `dag/units/sk-thm-p1.json`
   `realized`: this algebraic auxiliary node is not a realized unit statement or
   step. The unit route and this node's callers remain in place.
5. **DAG agrees: pass.** Read the item node and the existing exact-sequence,
   projective-module, and tensor-right-exactness leaves. Step 1 matches the
   cokernel preservation proof. Steps 2 and 3 match the four projective lifts;
   step 4 matches the displayed cycle identity and epi factorization.
   `proof_deps` is exactly the union of the steps' `uses`; its three leaves
   express the exactness, lifting, and scalar-extension properties used here.
   `proof_origin` distinguishes the agent's partial comparison from Stacks'
   alternative-resolution proof. Other node fields are unchanged, and there
   are no new nodes to validate.

Changed in this second reading: narrowed the two oversized public imports,
added the proof-only `exact₀` import, wrote the import change record, and
corrected this report's import claims. The proof itself needed no repair.
Compiled the unchanged source of the sole direct importer
`Sheaf.RingTheory.FlatOfLocalCriterionBaseChange` (held by Q1) in a scratch
module overlay against the revised imports; it compiled cleanly and is not
part of this delivery. Net holes: one closed, zero added; no project module pruned.

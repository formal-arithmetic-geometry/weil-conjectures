## What changed

Completed `AlgebraicGeometry.IsCurve.exists_artinSchreier_pullback_rows` in
`Sheaf.AlgebraicGeometry.Curve.ArtinSchreierPullbackRows`, keeping its signature and
existing docstring unchanged. The proof constructs the adjoint sheaf morphism by
pulling back regular functions, proves its naturality from the pullback square,
and transports its compatibility with powers and subtraction through the
inverse/direct image adjunction.

For the constant inclusion, the proof compares the composite constant-sheaf
adjunction with the adjunction on the new base. The left-adjoint uniqueness
identity identifies the canonical constant-sheaf comparison. Evaluation at the
terminal object then reduces the required square to naturality, the specified
constant-presheaf units, and preservation of natural-number casts by ring maps.
The short exact complex is transported along this comparison isomorphism.

Added one proof-only import,
`WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver`, for
`CategoryTheory.constantSheafAdj_homEquiv_apply`. No existing signatures,
visibility, or definitions changed. The second reading narrowed the imports
as recorded below. No new declarations or nodes.
The existing node's four proof steps and three proof dependencies still describe
the implemented route; no node edit is needed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.IsCurve.exists_artinSchreier_pullback_rows`
(node `lem-pbc-artin-schreier-pullback-rows`).

Holes closed: 1. Holes added: 0. No `sorry` remains in the delivered module.
The complete proof compiles through `lcompile.py` without warnings.

## No longer needed

Removed `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`;
its topological-invariance and cohomology results are unused. Replaced it with the
proof-only import `WeilConjectures.ConstructibleSheaf.Defs`, which supplies the
constant-sheaf comparison directly. The public Kummer import already supplies
the inverse/direct-image definitions needed in the signature. No old proof
dependency node is pruned: all three remain used, namely inverse/direct image,
sheafification, and pullback of constant
sheaves. The proof adds no intermediate theory to prove or prune. The unit route
in `sk-thm-p1` is preserved.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt had an unfinished constant-inclusion compatibility
proof and a non-compiling naturality calculation. The naturality calculation now
simplifies the equality of section maps in its hypothesis before applying it;
this avoids an elaboration mismatch from rewriting an already unfolded pullback.
The constant calculation uses the terminal-object section comparison and explicit
adjunction identities; its final rewrites specify the source terminal object.
Removed the earlier transparency options and diagnostic `trace_state`.
No mathematical error in the brief or DAG was found.

## Second reading by D4

1. Compared the delivered module with the repository using `diff`, then checked
   the complete existing theorem signature byte for byte with an assertion.
   Verdict: unchanged statement, visibility, docstring and definitions; all
   substantive edits are in its proof or imports. The public-import removal is documented in
   `coord/changes/ArtinSchreierPullbackRows-imports.md`.
2. Read the whole proof and compiled the delivered file with `lcompile.py`.
   Compiled a scratch copy with `#print axioms` for
   `AlgebraicGeometry.IsCurve.exists_artinSchreier_pullback_rows`: exactly
   `propext`, `Classical.choice`, `Quot.sound`. Verdict: a complete kernel-checked
   proof, with no sorry, new axiom, forbidden command or hollow definition.
   The adjoint is explicitly constructed from section pullback; the only other
   chosen morphism is the existing canonical constant-sheaf isomorphism.
3. There are no new statements or split-off holes. Verdict: not a decomposition;
   the single original hole is closed and no hole is added. Checked the empty
   scheme and identity-base-change cases conceptually: the construction uses
   only functorial restriction and terminal-object isomorphisms, with no point
   or nonemptiness assumption. The prime and short-exactness hypotheses stay
   exactly as given; no characteristic assumption is silently introduced.
4. Searched `lean/Sheaf` and `lean/WeilConjectures` for Artin--Schreier pullback,
   naturality, and constant-sheaf adjunct compatibility. Read
   `constantSection_adjunct_pullback`, the existing constant-sheaf homEquiv
   formula, and the definition of `upperStarConstantSheafIso`. No shorter
   applicable theorem replaces this argument: the existing section helper
   concerns a different terminal presentation and would still need the
   sectionwise computations. Verdict: the direct adjunction argument is sound.
   Removed the unused broad TopologicalInvariance import and imported
   ConstructibleSheaf.Defs only for the proof. The remaining public imports
   support the signature. All three old proof dependencies are still used;
   `## No longer needed` records the removed module. Read the `sk-thm-p1`
   realized fields: this local construction preserves its Artin--Schreier route.
5. Read `lem-pbc-artin-schreier-pullback-rows` and the Lean records of its three
   proof dependencies. Verdict: the four existing proof steps, their union of
   dependencies, and the stated proof origin agree with the implementation.
   The constant-sheaf adjunction calculation is the sheafification universal
   property in step 3. No node edit or new node is required.

Second-reading changes: narrowed the topological-invariance import to the
proof-only constant-sheaf definitions import, removed trailing whitespace,
and corrected the report's import/pruning account. No proof repair was needed.

The first dry run required a change record for removing a public import. Added
`coord/changes/ArtinSchreierPullbackRows-imports.md` with all 105 transitive
importers and their current holders. The sole direct importer independently
publicly imports TopologicalInvariance, so the removal does not change what its
importers see. Compiled its unchanged source against the narrowed module in a
scratch sandbox; both files pass. No downstream adaptation is needed. The
removed import is not claimed as a globally unreachable module: its downstream
import remains. This records local import pruning only.

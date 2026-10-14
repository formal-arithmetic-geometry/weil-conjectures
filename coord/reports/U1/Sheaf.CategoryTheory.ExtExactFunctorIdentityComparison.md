## What changed

Simplified the proof of CategoryTheory.Abelian.Ext.exactFunctorIdentityComparison
in the assigned module. Compose NatIso.mapHomologicalComplex e with
Functor.mapHomologicalComplexIdIso before checking compatibility with shifts;
this replaces two degreewise compatibility proofs with one. The subsequent
localization and single-complex cancellation argument stays intact. Updated
the existing node's first proof step and proof_origin to describe this proof.
All declaration signatures, visibility, public imports and docstrings stay identical.
The private commShift_of_localization is retained: the original
Sheaf.AlgebraicGeometry.HigherDirectImageRawPullbackIdentity imports it with
import all and calls it at line 56. No caller adaptation is needed.

This is the listed upstream review #1424 repair in coord/repairs.txt. The
baseline already contains a complete direct localization proof, so this is
proof simplification, not newly closed proof debt. The requested alternative
mapExactFunctor_eq_of_iso + mapExactFunctor_id cannot be used in the pinned
library: both names are absent from Mathlib and WeilConjectures.

## Proved and sorry left

CategoryTheory.Abelian.Ext.exactFunctorIdentityComparison compiles with a complete
proof. CategoryTheory.Abelian.Ext.commShift_of_localization remains proved.
Original holes: 0. Holes closed: 0. Holes added: 0. Split off: 0.
No sorry remains, and no new declaration or module is added.
The rewritten module compiled cleanly with lcompile.py in 2.1 seconds.
The delivery dry run checks the axioms of all delivered declarations.

## No longer needed

None. The sole public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
is required by the theorem's statement. No import, node or module is newly
pruned relative to the current baseline. The exact-functor factorization and
localized Ext proof dependencies remain. No statement or proof step realized
by dag/units/sk-thm-p1.json is bypassed. In particular, the private localization
helper must not be removed despite not occurring in the main theorem's proof.

## Where the brief, the DAG or earlier work was wrong

The dispatch describes a module containing sorry, but the baseline contains
none; coord/repairs.txt identifies it as an upstream review repair. The suggested
mapExactFunctor_eq_of_iso and mapExactFunctor_id do not occur in the pinned
Mathlib or source library. Fresh msearch.py searches were run with LeanFinder,
Loogle and grep. Loogle returns id_mapExactFunctor and
mapExactFunctor_comp_mk₀_natTransApp in online Mathlib; neither is present in the
pinned Ext/Map.lean. Reading the pinned file and the source extension
WeilConjectures/Mathlib/Algebra/Homology/DerivedCategory/Ext/Map.lean confirms that
these cannot replace the direct localization argument here.

The previous H3 return documents an attempted removal of the private helper
that broke HigherDirectImageRawPullbackIdentity. That deletion is not repeated.
No statement is disputed or changed. The source literature directory is absent
on this machine; this delivery uses the existing fully checked Lean argument
and adds no source-dependent intermediate assertion.

## Second reading by U1

1. Compared the only delivered Lean module with the repository using diff. The
   entire change is inside exactFunctorIdentityComparison's proof: the two
   termwise isomorphisms are composed before their shift check. The theorem's
   signature (including HasExt universe, exactness assumptions, arbitrary n,
   and the two degree-zero comparison components), private helper signature,
   docstrings, visibility and sole public import are byte-for-byte unchanged.
   No definitions or target statements change. Verdict: pass.
2. Read the whole proof and compiled the delivered file independently with
   lcompile.py (2.3 seconds, no warnings). A scratch copy with #print axioms
   for exactFunctorIdentityComparison and commShift_of_localization compiled:
   both use exactly propext, Classical.choice and Quot.sound. There are no
   sorries, axioms, unsafe declarations, opaque declarations or external
   implementations. Verdict: pass.
3. No statements, definitions, nodes or holes are split off or added. Thus
   there is no new statement requiring edge-case repair or a duplicate-node
   search. The existing argument includes n = 0, zero objects and arbitrary
   natural isomorphisms; off-degree single-complex components are compared
   using isZero_single_obj_X, rather than any nonzero-object assumption.
   Verdict: pass.
4. Read pinned Mathlib Ext/Map.lean, the source library's Ext/Map extension,
   and LocalizerMorphism.equiv_smallShiftedHomMap. A fresh msearch grep for
   id_mapExactFunctor, mapExactFunctor_comp_mk₀_natTransApp and the proposed
   mapExactFunctor_eq_of_iso/mapExactFunctor_id returned no matches; a source
   search of lean/Sheaf and lean/WeilConjectures found no replacement theorem.
   The proof specializes the localization comparison to the identity, checks
   the single-complex components hx, derives inverse cancellation hy, then
   rewrites Ext composition and cancels. Composing η first removes one whole
   degreewise shift proof. The sole import is required for mapExactFunctor in
   the public statement. Checked HigherDirectImageRawPullbackIdentity: its
   import all and line 56 use the private helper, so retaining it is necessary.
   Compared old proof_deps: both remain used, hence No longer needed is
   complete. Read sk-thm-p1.json's realized statement and all step lists:
   this auxiliary comparison is below those nodes and bypasses none of them.
   Verdict: pass; no additional proof edit needed.
5. Compared the delivered node with the repository. Only proof and
   proof_origin change. The first step now describes the composite η shift
   check and identity localization specialization exactly; the second step
   describes hx, hy and final cancellation. proof_deps is unchanged and is
   precisely the union of the steps' uses (exact-functor derived factorization
   and Ext). Read both dependency nodes and their Mathlib matches. The lean
   statement record still matches the unchanged theorem. Verdict: pass.

Second reading changed only this report by adding the independent checks.
No Lean or node repair was necessary. This is an already-proved repair item:
0 original holes, 0 closed, 0 added, 0 split off, and no modules pruned.

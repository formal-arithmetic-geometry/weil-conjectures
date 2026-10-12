## What changed

Proved AlgebraicGeometry.Scheme.Modules.H.globalFreeExtComparison without changing its
signature, visibility, or public import. The private topFreeComponent and topFreeIso
construct the top-open free-sheaf/constant-integer-sheaf isomorphism. Fully proved private
Ext helpers establish postcomposition compatibility and inverse-image compatibility.
The generic extComparison combines these identities before specialization to sheaves,
avoiding repeated reduction of concrete derived-category definitions. Updated the DAG
proof and proof_deps to match this direct argument.

## Proved and sorry left

Closed the sole local hole: AlgebraicGeometry.Scheme.Modules.H.globalFreeExtComparison
(node lem-pc-global-free-ext-comparison). No new holes; no sorry remains in the delivered
module. All four private helpers and the generic private theorem are fully proved.
The actual module compiled cleanly through lcompile.py in 38.1 seconds.
deliver3.py --no-push printed OK (dry run), commit 4d532723f2: compilation and
preflight passed except for the second-reading section, reserved for the independent
second reader. The local axiom probe raised no forbidden-axiom findings. Nothing pushed.

## No longer needed

H.openFreeShortComplex_shortExact (node lem-pc-free-mayer-vietoris-short-exact) is not
used as a proof dependency. The MayerVietorisFreeComplex module remains a public import
because its H.openFreeSheaf definition occurs in the unchanged statement. No imports
were removed and no whole module is claimed to leave the targets' closure.
The former general derived open-restriction/extension-by-zero argument and cartesian
open-subscheme coefficient comparisons are unnecessary for the top-open case.

## Where the brief, the DAG or earlier work was wrong

The former proof plan uses a general open-subset comparison unnecessarily: Modules.H
is already Ext from the constant integer sheaf. For every scheme, including the empty
scheme, Hom(U, top) is a singleton, giving the required constant-sheaf presentation.
Zero coefficients and degree zero require no extra hypotheses.

Earlier retries were blocked first by the missing compiled MayerVietorisFreeComplex
module and then by the 60-second compile limit. The dependency is now available. The
unchanged signature compiles in 4.3 seconds, and the concrete equivalence construction
was the expensive part. The generic fully proved helper reduces repeated unfolding.
Removed the unchanged dependency copy from the delivery and removed duplicate premature
second-reading sections; the independent second reader writes that section.

Second reading updated the theorem docstring to describe the direct top-open proof.
The environment-change record is coord/changes/MayerVietorisGlobalExtComparison-proof.md.

## Second reading by H2

1. Compared the sole delivered module against the repository with diff and compared
   its public theorem signature byte for byte: identical. No existing definition,
   hypothesis, conclusion, visibility, or import changed. The only environment addition,
   open Opposite, is declared in the existing change record and only assists elaboration.
   No other module is delivered. Verdict: pass.
2. Read the singleton free-group construction, naturality on generators, sheafification,
   and both Ext identities. The equivalences are explicit constructions, not arbitrary
   witnesses obtained from unproved existence theorems. The module compiled cleanly in
   40.0 seconds through lcompile.py. Scanning the delivered source found no sorry or
   forbidden declaration mechanism. The independent scratch #print axioms check compiled in 35.8 seconds and showed
   exactly propext, Classical.choice, and Quot.sound for globalFreeExtComparison.
   The delivery also runs its all-declaration axiom probe. Verdict: pass.
3. No statement was split off and no new holes or nodes were added. All five private
   declarations are proved. Hom(U, top) is a singleton even on the empty scheme;
   the generic associativity and inverse cancellation argument also covers degree zero
   and zero coefficients. No additional nonemptiness or flatness assumption is used.
   Verdict: pass.
4. Independently searched lean/Sheaf, lean/WeilConjectures, and Mathlib's Ext sources.
   EulerChar.lean contains the same singleton free-presheaf construction inside a proof,
   not a reusable comparison theorem; the delivery uses Mathlib's existing free-group
   equivalence, Ext.precompAddEquiv, composition, and mapExactFunctor lemmas directly.
   The sole public import supplies openFreeSheaf in the signature and must remain.
   The old proof dependency removed is exactly lem-pc-free-mayer-vietoris-short-exact,
   already listed under No longer needed. Read sk-thm-picard-rr.json: this auxiliary
   node is not a realized unit statement or step; the unit record and route are unchanged.
   No whole module is pruned. Verdict: pass.
5. Compared the delivered node with its repository version: only proof, proof_deps,
   and proof_origin differ. The two steps match the explicit top-open isomorphism and
   generic Ext comparison; the sole proof dependency is the unchanged coefficient,
   scalar-action, and base-change definitions of def-pc-flat-cohomology-comparison.
   Statement, stmt_deps, and Lean signature are unchanged. Verdict: pass.

Changed the theorem's outdated docstring: it described the former derived
open-restriction argument rather than the delivered proof. Replaced it with the
singleton construction, explicit Ext equivalences, scalar associativity, and
constant-comparison cancellation actually used. No proof code needed repair.

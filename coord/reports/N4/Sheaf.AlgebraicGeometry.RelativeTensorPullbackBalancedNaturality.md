## What changed

Constructed the inverse-direction balanced tensor comparison explicitly in
Sheaf.AlgebraicGeometry.RelativeTensorPullbackBalancedNaturality. The section pairing
inserts 1 in the scalar-extension factor; its additivity, R-linearity and restriction
compatibility are proved. The tensor universal property gives the unique sheaf map.
Naturality is proved by the pure-tensor formula and sheafification-unit naturality.
Functor extensionality identifies the supplied G with tensorPullback. Invert the
forgotten comparison and cancel its hom to obtain the two required equalities.

## Proved and sorry left

Closed the original hole
AlgebraicGeometry.Scheme.exists_relativeTensorPullback_balanced_natural by a reduction.
Added one hole: SheafOfModules.balancedTensorComparison_isIso
(node lem-pc-balanced-sheaf-tensor-comparison-isIso).
This is a decomposition, not a net decrease in holes: construction and naturality
are proved, while invertibility of the canonical map remains. No private helper has
sorry, and no data is chosen from arbitrary unproved existence: the tensor universal
property gives a unique map, and asIso uses a proof of invertibility of that map.

## No longer needed

No original public import removed: the three imports supply the statement's interfaces.
The parent no longer directly needs lem-pc-tensor-restrict-extend-module-natural or
lem-pc-sites-module-sheafification-tensor. They remain needed by the split-off
invertibility node, and their modules are not pruned globally. The parent uses the
existing tensor universal property instead. No unit statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned dependencies do not expose a mixed-coefficient sheaf invertibility
criterion; the module-level naturality theorem alone does not supply restriction
compatibility over varying section rings. The delivery makes the section pairing,
restrictions and naturality explicit and isolates only invertibility.
The cited literature source is not populated on this machine; Tag 08DE was read
from the official Stacks Project page, whose proof states the ordinary balanced
identity before passing to derived complexes. LeanSearch returned HTTP 500 and is
recorded as unavailable, not as a negative search result. Loogle, LeanFinder and
Mathlib grep found the module and sheafification ingredients but no exact criterion.
The preflight conservatively flags added proof-local commands as an interface
change. Their exact effect and the unchanged public signature are documented in
coord/changes/relativeTensorPullback-balanced-proof-commands.md. No dependent module
needs an adaptation.
The new criterion was checked on zero rings, zero modules and the empty space:
all maps are canonical additive maps and no nonempty or nonzero condition is used.

## New nodes

lem-pc-balanced-sheaf-tensor-comparison-isIso: given an R-linear sheaf map with the
canonical insertion-of-1 formula, prove it invertible. This is strictly the
invertibility step: it supplies neither a map, nor either naturality equality,
nor transport through the scheme inverse-image functor. Its module is
Sheaf.Algebra.Category.ModuleCat.Sheaf.BalancedTensorComparisonIsIso.

Change record: coord/changes/relativeTensorPullback-balanced-proof-commands.md.

## Second reading by N4

1. Compared the delivered parent module with the repository version. The public
   theorem signature and all existing declaration statements are byte-for-byte
   unchanged; only proof imports, local proof helpers, and the proof body differ.
   Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`; compilation succeeds.
   The only remaining `sorry` is the named theorem
   `SheafOfModules.balancedTensorComparison_isIso`, and no forbidden declaration or
   hollow definition occurs. The parent theorem uses only the permitted axioms apart
   from this explicitly split theorem. Verdict: pass.
3. Checked the split criterion against its hypotheses and edge cases (zero rings,
   zero modules, and empty spaces). It is the strict invertibility subproblem and
   does not restate the parent naturality theorem. Searches found no existing exact
   declaration. Verdict: pass.
4. The proof follows the balanced tensor route: it constructs the section pairing,
   uses the sheaf tensor universal property, proves both naturality equations, then
   applies the separate invertibility criterion. No unit step is bypassed and no
   import can be removed without losing a used declaration. Verdict: pass.
5. The parent node proof and proof dependencies match the declarations used, and the
   split node records its source, proof plan, Lean declaration, and status. Verdict:
   pass.

I changed no Lean statements or definitions. I added this second-reading record only;
the delivery remains a decomposition closing the parent hole and adding the one named
invertibility hole.

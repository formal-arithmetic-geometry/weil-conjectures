## What changed

Retire the duplicate Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientFactors under the
listed retirement assignment. Its sole current direct importer, RawModuleScalarCoefficientSquare,
publicly imports the canonical WeilConjectures twin. Both coefficient-map bodies are identical;
the module factor's named and expanded endpoints are definitionally equal. The definition node
now names the two canonical upstream declarations. No upstream source file is edited.

Repair the coefficient-square proof's expensive derived-category conversions with explicit,
kernel-checked congruences and the existing raw-complex endpoint equations. The mathematical
shift-square calculation is unchanged. Remove the redundant private unshifted restatement and
use its existing public theorem directly.

Expose raw module and abelian classes at their actual derived Hom types through concrete
identity functions, with a proved heterogeneous computation rule for module classes. A
concrete typed view constructs its two explicit factors at the named raw-complex endpoints,
with a proved reflexive equality to the canonical coefficient morphism. Six consumer equations explicitly use these views. Every original binder, universe parameter,
degree convention and mathematical equality is retained. The combined pullback calculation
uses associativity; the Hom composite reuses the combined pullback formula. Source and target
formulas retain their existing categorical arguments. All affected existing modules are
unclaimed. The six node statements explicitly name the equivalent presentations, with
statement_change records auditing every existing citer; every use remains valid. No target
statement or target-used data construction changes.

The complete old and new signatures and consumer inventory are in
coord/changes/V3-retire-raw-module-scalar-coefficient-factors.md and
coord/changes/V3-native-raw-class-morphisms.md.

Validation: lcompile.py compiled all nine delivered Lean modules against the sandbox
dependency overlay. The combined pullback formula took 51.5 seconds, the Hom composite
20.9 seconds and the final source formula 41.9 seconds. The square with direct proof
constructors compiles in 54.4 seconds. The delivery tool runs its independent
compile and preflight checks before pushing.

## Proved and sorry left

The assigned definition-retirement item began with zero sorries. Holes closed: 0.
Holes added: 0. Holes remaining in the delivered Lean files: 0. Split off: 0.
No theorem is counted as newly proved merely because its proof was adapted. No public
or private theorem is left with sorry. Every new definition has its complete concrete data
construction.
No object is chosen from an existence theorem.

Scratch compatibility proofs identify both old coefficient factors with the canonical
upstream maps by rfl. For AlgebraicGeometry.Etale.moduleCoefficientFactor and
AlgebraicGeometry.Etale.abelianCoefficientFactor, #print axioms reports only
propext, Classical.choice and Quot.sound.

## No longer needed

Withdraw lean/Sheaf/AlgebraicGeometry/RawModuleScalarCoefficientFactors.lean via deleted.txt.
Keep its node, all mathematical dependencies and all parent routes: the node's Lean
attachment moves to the canonical upstream module. No DAG node or unit proof is removed.
No quarantined Lean module imports the withdrawn copy.

The square no longer privately imports
WeilConjectures.AlgebraicGeometry.HigherDirectImageOverMapCoefficient; its conversion helper
is local. No public declaration in that source module is removed or changed.
The Hom composite uses the combined pullback formula instead of repeating its module
factorization. The two pullback-formula modules obtain the canonical factor definitions
without importing the coefficient-square theorem, which neither uses. Their node statement dependencies now name the
definition node. The two pullback-formula modules remove their unused
RawModuleAbelianHomMap import,
importing RestrictedOverAbelianComplexData directly for the coefficient sheaf definition.
Their statement dependencies now record that actual data node. No other existing module
or mathematical dependency is withdrawn.

## Where the brief, the DAG or earlier work was wrong

This is a listed zero-hole retirement/definition repair rather than an unfinished theorem.
The retirement TSV's consumer snapshot predates later retirements: both twins now have the
same upstream-only direct imports, and the old Sheaf module-formula consumer is already
absent with no rework row or archive. The unit sk-lem-failure-field has no realized statement
or proof step attached to this definition. Its canonical mathematics stays available.

The untouched coefficient-square proof also times out against the current published library.
The original combined pullback statement alone exceeds the single-file limit in a scratch
statement-only diagnostic. Explicit native class values reduce that statement check to about
21 seconds, and the named coefficient endpoints reduce it further to 13.1 seconds.
These diagnostics identify conversion of raw Yoneda carriers and repeated derived
instance presentations as the resource problem. The limit is unchanged; no proof is split
into unproved statements and no upstream source boundary is crossed.

The source-library search found the exact existing coefficient maps. Mathlib searches found
only the generic shift, represented Hom and associativity constituents. The proved upstream
module pullback formula was also checked: importing it collides with the distinct current
Sheaf pullback-comparison interface, so it cannot directly replace the local calculation.
No additional mathematical result or assumption is required.

## New nodes

- def-sbc-raw-class-native-morphisms: the two concrete identity functions and the proved
  heterogeneous computation rule, in RawModuleScalarClassMorphisms. There are no holes.
- def-sbc-module-coefficient-native-endpoints: the concrete coefficient composite at named
  endpoints, its proved equality to the canonical factor and its explicit computation rule,
  in RawModuleScalarCoefficientNative. There are no holes.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

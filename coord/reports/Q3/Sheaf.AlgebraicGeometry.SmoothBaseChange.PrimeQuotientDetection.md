## What changed

Replaced the sole `sorry` in
`Sheaf.AlgebraicGeometry.SmoothBaseChange.PrimeQuotientDetection` by a complete Lean
proof from one general module/abelian higher-direct-image comparison. The original
theorem's signature and docstring are unchanged.

The private theorem `AlgebraicGeometry.Etale.quotient_retract` proves the algebraic
part without any new holes: the proper principal ideal gives a nontrivial quotient,
its characteristic is the prime, and Mathlib's linear-functional lemma splits its
unit vector. The source coefficient is exactly the quotient of the universe-lifted
prime ring appearing in the original statement, identified with `ZMod r` through
its zero principal ideal.

The private theorem
`AlgebraicGeometry.Etale.preservesSheafification_forget_modules` explicitly proves
the typeclass needed by `constantCommuteCompose`. It expresses forgetting as
restriction from Lambda to integer modules followed by their equivalence with
abelian groups; the coextension adjunction makes this functor left adjoint. This
avoids the generic typeclass-search timeout without increasing compilation limits.

The main proof maps the additive retract through constant abelian sheaves and
single/derived-pushforward/homology. It transfers the zero object through the two
comparison isomorphisms, proves that the retract's identity is zero, and reflects
this zero identity through the faithful module-coefficient forgetful functor.
Preservation of zero morphisms is verified objectwise.

Added one statement module,
`Sheaf.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison`, for
step 3 of the original argument. Its sole theorem concerns an arbitrary module
sheaf and arbitrary coefficient ring; it contains no prime, quotient, nonunit, or
vanishing hypotheses, so it is a distinct comparison step rather than a renamed
version of the item. Updated the original DAG proof and added its node.

Both modules compile locally without errors or warnings. The quotient proof uses
only Mathlib and the standard axioms. The original theorem still depends on the
new comparison's `sorry`; this is a decomposition, not an axiom-free completion.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.isZero_prime_cyclic_higherDirectImage_of_quotient`
(node `lem-sbc-prime-quotient-detection`). No `sorry` remains in the item's module.

Added exactly one hole:
`AlgebraicGeometry.Etale.nonempty_higherDirectImage_forget_iso`, in
`Sheaf.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison`
(node `lem-sbc-higher-direct-image-forget-comparison`). Its body is exactly
`:= by sorry`. Its source and full acyclic-resolution proof are in its docstring
and node. The theorem is only the module/abelian comparison in step 3; the
quotient splitting and all categorical glue are proved in the item.

Counts: one original hole closed, one comparison hole added, net zero holes.
This delivery is a decomposition with the coefficient algebra and retract
argument proved, rather than a complete proof using only the permitted axioms.

## No longer needed

Removed the direct proof import
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: it supplied no separately
needed result and remains available through the existing statement dependencies.
No DAG node or additional statement module is pruned.

Retained `Sheaf.AlgebraicGeometry.InjectiveModuleDirectImageAcyclic` and node
`lem-weil-pbc-injective-module-direct-image-acyclic`, because that node realizes a
step of `dag/units/sk-thm-p1.json`. Its unit route must stay imported even though
the actual arbitrary-ring comparison is now isolated in the new module. The
new comparison's planned imports remain for the worker proving that theorem.

## Where the brief, the DAG or earlier work was wrong

The original plan's step 3 does not follow by a direct application of either
existing dependency: the injective acyclicity theorem is a vanishing result,
not an isomorphism comparing module-valued and abelian derived images. Its
`SheafOfModules` interface also takes `R : Type u` through `ULift`, whereas
this item permits an arbitrary `Lambda : Type (u + 1)` over `Scheme.{u}`.
The new theorem states precisely the missing comparison in the required
universes, without changing either existing signature.

The constant-sheaf Mathlib leaf is usable, but bare instance synthesis at this
site timed out. An explicit coextension adjunction resolves it and compiles.
Forgetting is not assumed to preserve injectives: the remaining comparison
uses acyclicity of underlying injective module sheaves, as in Tag 03FD.

Edge cases were checked mathematically before stating the comparison: negative
degrees vanish on both sides, degree zero is ordinary direct image, and the zero
ring, zero sheaf, and empty scheme satisfy the same comparison. It needs neither
torsion nor flatness of Lambda over the integers. In the quotient argument the
nonunit hypothesis already rules out the zero ring, and prime r supplies the
field and characteristic hypotheses explicitly.

## New nodes

`lem-sbc-higher-direct-image-forget-comparison`, in
`dag/nodes/sec-smooth-base-change/lem-sbc-higher-direct-image-forget-comparison.json`,
states the isomorphism between forgetting `R^q h_* F` and abelian `R^q h_*` of
its underlying sheaf. Its proof follows Stacks Tags 03FD and 072W, using an
acyclic underlying injective resolution and exactness of forgetting. The node
records LeanFinder, Loogle, grep, and the unavailable LeanSearch service. It
inherits the item's chapter and unit. No definitions or existing statements
changed, so no change record is needed.

## Second reading by Q3

1. **Public contract: pass.** Compared the complete item module against the
repository with `diff -u`. The original theorem signature and docstring are
byte-for-byte unchanged; the differences are proof imports, two proved private
helpers, and the replacement proof. No existing definition changes. The other
Lean module is new, and its recorded signature matches its Lean statement.
No change record is required.

2. **Proof and trust: pass as a decomposition.** Compiled both delivered modules
in import order through `lcompile.py`, without errors or warnings. A scratch copy
with explicit `#print axioms` commands confirms that both private helpers use only
`propext`, `Classical.choice`, and `Quot.sound`; the original theorem and new
comparison additionally use `sorryAx`, as reported. Scanned both delivered modules:
exactly the one named comparison theorem contains `sorry`, and none contains a
forbidden trust declaration or a holed definition. Read the quotient, linear
functional, constant-sheaf, mapped-retract, and faithful-forgetful arguments.

3. **Split statement: pass.** Read the new comparison's complete docstring proof
and node, and verified Stacks Tags 03FD and 072W directly. The comparison is valid
for arbitrary commutative coefficient rings and arbitrary scheme morphisms;
negative degrees are zero, degree zero is ordinary pushforward, and zero ring,
zero sheaf, and empty schemes cause no exception. It isolates the coefficient
comparison, with neither the quotient nor the vanishing implication of the item,
so it is strictly one part of the argument rather than a restatement. Fresh
LeanFinder, Loogle, and local grep searches used derived pushforward, exact
forgetful functors, acyclic resolutions, and derived base change. They found no
matching higher-direct-image comparison. In particular, read the existing
`EtaleModuleCohomologyForget` and `EtaleModuleInjectiveForgetAcyclic`: they concern
global cohomology and do not directly close the displayed arbitrary-pushforward
comparison. Closing that hole requires further formal acyclicity and comparison
work, not a few-minute application of an existing theorem.

4. **Route and pruning: pass.** The item uses Mathlib directly for the coefficient
retract and constant-sheaf comparison. All old proof dependencies remain used or
explicitly retained under the standing unit-route rule; thus the report's list
of no pruned DAG nodes is complete. Checked `sk-lem-universal-datum` (the item's
unit) and `sk-thm-p1` (which realizes the retained injective direct-image node).
No unit statement, step, or `realized` record changes. The new theorem's plain
imports are its stated proof plan. Tested removing its second public import;
Lean requires it to expose `rightDerivedLowerStarPlus` in the signature, so
restored it. The item adds only plain proof imports.

5. **DAG agreement: pass.** The existing node changes only `proof`, `proof_deps`,
and `proof_origin`. Its steps describe the actual private helpers and categorical
proof, and identify the retained unit-route dependency explicitly. The new node
has its source, complete steps, union of step dependencies, search records,
creation and blueprint provenance, inherited chapter and unit, and verbatim Lean
statement. No statement is weakened and no hollow data is introduced.

**Changes made by the second reading:** added this review record only. The tested
import removal was reverted because it is required by the public signature.
One original hole is closed and one comparison hole is added; net zero, with the
comparison still open. No proof or statement repair was necessary.

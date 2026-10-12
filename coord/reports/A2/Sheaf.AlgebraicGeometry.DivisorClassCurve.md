## What changed

Proved AlgebraicGeometry.Scheme.exists_divisorClassGroup_addEquiv_pic_associatedModule
without changing its signature or its existing docstring. The proof supplies the integral,
Noetherian, structure-map and relative-dimension instances; obtains the existing point-ideal
quotient equivalence from Curve.Picard; rewrites its computation rule; and compares its
representative with the explicit divisor module.

Added Sheaf.AlgebraicGeometry.DivisorPicRepresentative, with the remaining geometric
comparison separated from the already implemented kernel, surjectivity and quotient argument.
This is strictly a part of the argument: it mentions neither the divisor class group nor an
equivalence, injectivity or surjectivity. It compares two constructions at each divisor.
No properness assumption is added. Its natural-language proof handles zero, negative and
positive divisors through positive/negative parts, local multiplication and effective-divisor
agreement. These mathematical edge cases were checked before stating it.

Local compilation of both modules in dependency order succeeds without warnings.

## Proved and sorry left

Proved: AlgebraicGeometry.Scheme.exists_divisorClassGroup_addEquiv_pic_associatedModule
(node lem-sc-divisor-class-curve); 1 of 1 original sorries eliminated.

Remaining new sorry:
AlgebraicGeometry.Scheme.Divisor.nonempty_toPic_iso_module
(node lem-sc-divisor-toPic-representative), in the new module DivisorPicRepresentative.
This isolates the representative comparison; the source-library equivalence is already
implemented and is reused, not copied or replaced by a new sorry.

The source equivalence and the local-rings theorem may themselves depend on existing sorries.
Those dependencies remain the next items; this delivery does not claim the target's entire
axiom closure is finished.

## No longer needed

Removed direct proof imports from the item's module:
- Sheaf.AlgebraicGeometry.DivisorModule
- Sheaf.AlgebraicGeometry.FunctionField
- Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings
- WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
- WeilConjectures.AlgebraicGeometry.Modules.Invertible
- WeilConjectures.AlgebraicGeometry.PicardFunctor

Their statement-facing declarations remain available through the unchanged public imports
and the new proof imports. This delivery does not assert that these modules are globally
unreachable: they still occur in the imported source-library proof or in the representative
comparison's mathematical dependencies.

The old node's separate well-definedness, kernel, homomorphism and surjectivity construction
is no longer reimplemented here: the existing Curve.Picard theorem supplies these parts.
The parent's direct proof edges to def-sc-divisor, def-sc-function-field,
def-sc-picard-group, def-sc-invertible-module, lem-sc-pic-group,
lem-sc-line-bundle-rational-section and lem-sc-divisor-module-local are replaced by the two
precise dependency nodes. The local-generator and effective-agreement nodes remain needed
below the comparison; no whole unit or unit step is bypassed. No global node pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The original node's lean_candidates entry says the source equivalence is sorry on the older
71d63dcf checkout. In the current adopted library its body is a complete Lean proof (possibly
using existing sorry dependencies). Its map is Divisor.toPic, and it does not itself identify
that map's representative with the explicit divisor module, so using it alone would miss an
essential clause. This delivery retains that clause as a genuine geometric comparison.

LeanSearch was unavailable twice (Internal Server Error); this is recorded as unavailable,
not as a negative search verdict. LeanFinder, Loogle and direct source searches were used.

The literature payload is absent from this clone; the original node retains the detailed
proof and source citations. The comparison's natural-language proof is marked as agent-written
from those recorded proof steps and the effective-agreement node.
WANTED: literature/blueprint/master/blueprint/sec-curve-estimates/sk-def-pic/
lem-sc-divisor-class-curve.md, Proof, for lem-sc-divisor-toPic-representative.
WANTED: literature/blueprint/master/blueprint/sec-picard-framework/sk-thm-picard-rr/
lem-pc-divisor-line-bundle-agrees-sc.md, Proof, and Stacks Divisors Tag 02SL,
for lem-sc-divisor-toPic-representative.

The unit sk-def-pic has no realized node or step entries. Its divisor-class identification
is retained: the source implementation still constructs the same quotient homomorphism and
proves the kernel and surjectivity; the comparison ensures the prescribed module is used.

## New nodes

lem-sc-divisor-toPic-representative: one new statement module comparing the point-ideal
Picard representative with O(D) for every signed divisor. Its proof plan uses the existing
effective agreement and local generators; this is the sole new sorry.

lem-sc-divisor-class-toPic-equivalence: records the existing source-library theorem
AlgebraicGeometry.Scheme.exists_divisorClassGroup_addEquiv_pic. No new Lean declaration or
sorry is added for this node. It records the precise weaker representation-specific result
used by the parent, avoiding an ambiguous self-dependency on the parent's old candidate.

No statements or definitions were changed; no change record is required.

## Second reading by A2

1. Compared the only existing delivered module with the repository using diff, and
   compared the declaration text before `:= by` byte for byte. PASS: the signature,
   its hypotheses, conclusion, definitions and existing docstring are unchanged.
   DivisorPicRepresentative is a new module and adds only one named theorem.
2. Compiled both modules in dependency order with lcompile.py. PASS: no errors or
   warnings. Compiled scratch copies with `#print axioms` for both declarations:
   each uses only propext, Classical.choice, Quot.sound and sorryAx. The only new
   sorry is Divisor.nonempty_toPic_iso_module; no definition contains a sorry and
   there are no axiom, unsafe, opaque, implemented_by or extern declarations.
   The original theorem's axiom closure is still open; elimination of its own
   sorry is not a claim that the entire closure is proved.
3. Read the new comparison against Divisor.sectionCondition, module_local,
   divisorLineBundle_agrees_sc, Divisor.toMul_toPic_mapRange_sub and
   Divisor.mapRange_toNat_sub. PASS: O(D) uses v(g)+D >= 0, so a positive point
   has representative I_P dual, a negative point I_P, and zero the structure
   module; mixed coefficients follow the positive/negative decomposition.
   The same argument applies on a nonproper curve. Local multiplication is
   compatible with restriction and is invertible in the common uniformizer
   trivializations. module_local supplies invertibility and the zero case.
   This comparison asserts no quotient map, kernel or surjectivity and is
   strictly smaller than the original equivalence. Its docstring gives the
   complete remaining argument and its DAG node matches the Lean statement.
   Independent LeanFinder search for tensor products of valuation-bounded
   divisor sheaves found structure-sheaf and analytic-meromorphic results,
   not this comparison. Loogle does not index the upstream Pic declaration.
   Direct rg over lean/Sheaf and lean/WeilConjectures found only the effective
   comparison and the source toPic equivalence, not an arbitrary signed-divisor
   comparison. The split-off lemma cannot be closed in a few minutes: the
   module multiplication/sheaf isomorphism still needs formal construction.
4. Read the complete kernel/surjectivity/quotient proof of
   exists_divisorClassGroup_addEquiv_pic in Curve.Picard and the unit record
   dag/units/sk-def-pic.json. PASS: the shorter existing proof is reused,
   with the essential representative comparison retained. The unit's realized
   statement and step lists are empty, and no recorded realized node is bypassed.
   Existing public imports are unchanged; the new module's two public imports
   supply its signature. Added plain imports DivisorLineBundleAgreesSC and
   DivisorModuleLocal for the stated remaining proof plan. All eight old direct
   proof dependencies were checked: lem-sc-smooth-connected-curve-local-rings
   remains direct; the other seven are precisely the edges listed under
   No longer needed (including lem-sc-divisor-module-local). They remain
   available below the two new dependencies; no global node pruning is claimed.
5. Compared the parent proof steps and dependency union with its Lean proof.
   PASS: local-rings instances, source equivalence, then representative comparison
   are the three steps actually used. The new comparison node has matching
   hypotheses, declaration, source, complete proof plan and creation fields.
   The existing-source equivalence node records the actual reused theorem.
   Repaired its Lean statement record to include the surrounding implicit
   field, scheme, Over and SmoothOfRelativeDimension binders, and corrected
   its branch to sheaf-dag. No mathematical statement was changed.

Second reading changed: added the comparison's two plain proof-dependency
imports and corrected the source-equivalence node's complete Lean signature
record and branch. No proof, existing signature or definition was rewritten.

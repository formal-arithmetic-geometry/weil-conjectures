## What changed

Proved `AlgebraicGeometry.coherentFormal_pushforward_of_closed_support` in
`Sheaf.AlgebraicGeometry.FormalSystemClosedSupportPushforward`, preserving its entire
signature, public imports, and existing docstring. Added proof-only imports and four
proved private helpers. Coherence is transported through the open-image isomorphism
and the existing coherent-pushforward theorem. Annihilation is detected using the
pullback–pushforward adjunction and the ideal-power image theorem. Quotient transport
is constructed from the supported adjunction unit, the existing pullback quotient
comparison, and the quotient of the invertible counit. Its projection equation is
proved using adjunction naturality and the triangle identity; the actual inverse-system
transition equation follows by functoriality.

Reused `powerQuotientIso`, `powerQuotientIso_π`, and `quotientMap_π` through proof-only
`import all Sheaf.AlgebraicGeometry.FormalSystemsPullback`, and the product monicity
and zero-under-monomorphism helpers through proof-only `import all` of the already
publicly imported `CoherentFormalModule`. These imports do not change public signatures
or definitions. Updated the item's DAG proof, proof dependencies, and proof origin.
No other module was adapted and no new definition or public statement was added.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.coherentFormal_pushforward_of_closed_support`
(node `lem-weil-pbc-formal-system-closed-support-pushforward`).

Added 0 holes; split off 0 statements. No `sorry` remains in the delivered module.
All four private helpers are proved:
`coherent_pushforward_closed_support`, `powerProduct_pushforward_zero`,
`supported_restriction_unit_isIso`, and `powerQuotient_pushforward_iso`.
This is a proof from existing library declarations, not a decomposition into new holes.

The module compiles without errors or warnings using the prescribed single-file compiler.
An explicit `#print axioms` check reports the standard three axioms plus transitive
`sorryAx` from existing dependencies, so this delivery does not claim that the entire
import closure is already sorry-free. No axiom or new admission was introduced.
The helpers work for empty schemes and support, zero modules and ideals, and quotient
exponent zero; the target retains the specified positive exponents and every original
transition map.

## No longer needed

None. No original import was removed, and every originally planned proof-dependency
node is still used. The added imports supply coherence transport, closed-support
control, stalk quotient epimorphy, the existing pullback quotient comparison, and the
local isomorphism criterion. No unit statement or realized unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The DAG plan is valid. Its restriction and module-category nodes are recorded directly
in Mathlib rather than in modules named after their node identifiers. The precise
projection-respecting pullback quotient comparison already exists as proved private
helpers in `FormalSystemsPullback`; reusing it avoids a new intermediate statement.
The LeanFinder, Loogle, and grep searches found no direct theorem for the whole target;
local library search found the helpers used above. No statement correction was needed.


## Second reading by R3

1. **Interfaces: pass.** Compared the entire delivered module with the repository
   using `diff -u`. The sole existing theorem's signature and docstring are byte
   for byte unchanged: both Noetherian hypotheses, the open immersion, ambient
   ideal, actual inverse system, fixed closed T contained in the image, every
   level's nonzero-stalk support bound, and the coherent-formal hypothesis remain.
   Its conclusion is still the coherent-formal property of the actual composite
   functor, including its given transition maps. Public imports are unchanged.
   The only additional declarations are four proved private theorems; no data
   definition or public interface was altered. No change record is needed.
2. **Kernel proof: pass.** Independently compiled the delivered module with
   `lcompile.py --all`, without errors or warnings. Scanned the delivered Lean
   for admissions and forbidden declarations: none. Compiled a fresh exact
   scratch copy with `#print axioms` for the target and all four private helpers.
   Only the standard axioms and transitive `sorryAx` occur. The module introduces
   no admission. The supported restriction-unit proof uses the open image and
   T's complement as a cover; both complement restrictions vanish by section
   extensionality. Quotient support follows from the surjective stalk projection.
   The quotient isomorphism is explicitly composed from the unit, the existing
   constructed pullback quotient comparison, and the counit; its projection
   equation follows from naturality and the triangle identity. Choosing an
   adjunction introduces no arbitrary module witness: adjunction uniqueness
   determines its comparisons, and the quotient object is the fixed cokernel.
3. **Split statements: pass, none.** No new sorry theorem or node is split off.
   Reviewed all four private helper statements. Empty schemes and T, zero
   modules, and zero/unit ideals cause no exception. Exponent zero in the
   general helpers is valid (the zeroth ideal power acts as the whole module);
   the target consistently uses n+1. The supported-unit helper does not require
   coherence. The annihilation helper uses adjunction injectivity only for maps
   into an actual direct image, so does not assume that restriction detects all
   morphisms. No missing hypothesis or restatement of the target was found.
4. **Route and pruning: pass.** Read the existing pullback quotient construction
   and its projection lemmas in `FormalSystemsPullback`, the formal-object
   definition and product helpers in `CoherentFormalModule`, and the support,
   coherence and ideal-power image dependencies. Repeated a Loogle search for
   an open-immersion unit isomorphism and searched the library and Mathlib with
   alternative unit/quotient/pushforward terms. The apparent nearby results
   concern derived categories, nested-open restrictions, or proper push-pull;
   none provides this module's supported quotient comparison more directly.
   Every added import supplies a declaration used in the proof, and both
   `import all` declarations are proof-only access to already proved helpers.
   All old proof dependencies remain used; `No longer needed: None` is complete.
   Checked `dag/units/sk-thm-p1.json` and its `realized` steps: none is replaced
   or bypassed by this auxiliary argument. Read the source paragraph of
   [Stacks 088E](https://stacks.math.columbia.edu/tag/088E) and the two-open proof
   of [Stacks 0CYJ](https://stacks.math.columbia.edu/tag/0CYJ), since the cited
   local literature file is absent on this machine. This proof establishes the
   adic conditions of the direct-image system used in that paragraph.
5. **DAG: pass.** The node differs only in `proof`, `proof_deps`, and
   `proof_origin`. Its statement, statement dependencies, Lean signature record,
   chapter and unit remain unchanged. The dependency list equals the union of
   step uses. Matched each dependency to its recorded Lean declaration/module;
   the five proof steps accurately describe the four helpers and final assembly.
   There are no new nodes to validate.

Second reading changed only this report, adding the independent review and its
verification evidence. No repair of the Lean or DAG was warranted. Closed 1
original hole, added 0 holes, split off 0, pruned none.

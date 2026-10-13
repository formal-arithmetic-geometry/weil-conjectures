## What changed

Proved `AlgebraicGeometry.schemeTensorHomUncurry_localized_evaluation` from a new
single-component naturality theorem. Its statement and every existing definition
remain unchanged. Added the proof-only import
`Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryComponentNaturality`.

The private `uncurry_chain_natural` proof applies the existing summand equations,
the tensor-map summand formula, and coproduct extensionality. The public proof
then uses lax monoidal naturality of `DerivedCategory.Q`, naturality of the
K-injective augmentation, cancellation of its localized isomorphisms, and
associativity. The original node now records this route.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.schemeTensorHomUncurry_localized_evaluation`
(`lem-pc-tensor-hom-uncurry-localized-evaluation`). Its module has no remaining sorry.

Added one hole:
`AlgebraicGeometry.schemeTensorHomUncurryComponent_natural`
(`lem-pc-tensor-hom-uncurry-component-naturality`), in the new module
`Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryComponentNaturality`.
This is a decomposition, not a net reduction in holes. The remaining statement
is an equality on one degree pair; it contains no coproduct extension,
chain-map extensionality, derived localization, tensor comparison, or inverse
augmentation. The combining proofs in the item's module are complete Lean.

The existing imported theorem
`AlgebraicGeometry.schemeTensorHomUncurryGraded_comm` remains a dependency;
this delivery does not change it or add a new hole for differential compatibility.

The component calculation was investigated using `homComplex_exists`,
`homComplex_projections_exists`, the three source sheaf tensor-Hom naturality
lemmas, and braiding naturality. The ordinary sheaf uncurrying naturality proof
compiled. I did not finish connecting the chosen projection formulas to the
explicit component: repeated equality matching unfolded the large chosen
Hom-complex construction. The unfinished attempts are retained only in the
sandbox scratchpad; the delivered hole has its own complete mathematical proof
and is strictly the component part of the argument.

Edge cases checked mathematically: identities preserve evaluation; zero maps
in each of the three variables produce zero; all integer degrees and unbounded
complexes use the same single-pair equation and coproduct universal property.
No K-flatness assumption is introduced. Validation is by the single-file
compiler and the delivery dry run.

## No longer needed

No original imports or modules are pruned. The direct proof dependency
`def-pur-hom-complex` is now used beneath the new component node rather than
in the localized theorem's combining proof; it remains needed transitively.
No unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The DAG's first step contains a
projection-to-uncurrying glue calculation without a separately stated theorem
for one degree pair. This delivery makes that component step an independent
item and implements the remaining extension and localization steps.

LeanSearch was unavailable (Internal Server Error); this is recorded as
unavailable, not as evidence of absence. The Stacks source files are absent
from this checkout; Tags 0A90 and 08DJ were read online at their recorded URLs.

## New nodes

`lem-pc-tensor-hom-uncurry-component-naturality` states naturality of the existing
explicit component under simultaneous chain maps, for integers p,q,n with
q+p=n. Its module is
`lean/Sheaf/AlgebraicGeometry/CanonicalTensorHomUncurryComponentNaturality.lean`.
It is sourced to Stacks Tags 0A90 and 08DJ, with a complete componentwise proof
in both its docstring and node. It inherits the item's chapter, unit, and
blueprint ancestry. No existing public interface is changed; no change record
or forced adaptation is needed.

## Second reading by S2

1. **Interface — pass.** Read the complete diff against the repository module and
   compared the text from `theorem schemeTensorHomUncurry_localized_evaluation`
   through its signature programmatically: byte-for-byte identical. The original
   public import, declaration visibility, definitions and docstring are unchanged.
   The only added import is proof-only. The new component module publicly imports
   the model because its statement uses its definitions. No change record is needed.
2. **Proof — pass.** Compiled both modules together through `lcompile.py --all`:
   component module 3.2 seconds, localized module 26.9 seconds, no errors or warnings.
   Read `uncurry_chain_natural`: degreewise coproduct extensionality reduces the
   equation using `schemeTensorHomUncurry_component` and
   `ι_mapBifunctorMap_assoc`, with `q+p=n` obtained from `p+q=n` by arithmetic.
   The public proof uses `Functor.LaxMonoidal.μ_natural` and the naturality of
   `toKInjectiveResolution`; the two augmentation maps become isomorphisms under Q,
   so the cancellation proving `hres` is legitimate. All final steps reassociate
   these equalities. There is exactly one delivered sorry, the reported public
   component theorem, and no forbidden declaration or data definition is added.
   A scratch #print axioms audit of both public theorems returned exactly
   propext, Classical.choice, Quot.sound and sorryAx, with no other axiom.
   The axiom audit is also performed by the delivery tool's all-declaration probe;
   `sorryAx` is expected from the component and pre-existing open dependencies.
3. **Split statement — pass as a decomposition.** Read the component definition,
   `homComplex_exists`, `homComplex_projections_exists`, and the three
   `SheafOfModules.tensorHomEquiv` naturality lemmas. The map formula projects at
   Hom degree p, source degree q and target degree n, exactly with q+p=n.
   Inverse currying gives the order b tensor a; braiding naturality changes it to
   a tensor b as stated. The hypothesis and all three variances match. Identity
   maps recover the component; zero a, b or c gives zero; negative degrees and
   unbounded complexes require no extra condition. This is strictly a component
   subargument, with neither totalization nor derived localization in its conclusion.
   Read [Stacks 0A90](https://stacks.math.columbia.edu/tag/0A90) and
   [Stacks 08DJ](https://stacks.math.columbia.edu/tag/08DJ): the first supplies the
   functorial Hom-total-tensor calculation, the second the derived context.
   Independently searched via msearch Loogle for `"uncurry_natural"`, LeanFinder
   for `evaluation naturality tensor internal hom complex degree projection`,
   and rg for projection/map and tensorHomEquiv naturality. Mathlib's ordinary
   uncurrying naturality is an ingredient, not a duplicate of the chosen component.
   `HomTensorCurryNaturalPure` concerns nested Hom and a pure-tensor condition,
   not this component. No duplicate statement found. The new node has a full
   docstring proof, source, creation record, searches and verbatim Lean statement.
4. **Route and pruning — pass.** Read `dag/units/sk-thm-picard-duality.json` and
   the old/new proof steps. This replaces only the component subargument of the
   existing evaluation route; no unit statement or step is bypassed or edited.
   Every original direct proof dependency except `def-pur-hom-complex` remains
   direct. That node remains transitively used beneath the component node and
   is explicitly accounted for under `No longer needed`. Both imports are needed:
   differential supplies the chain map/summand equation, component naturality the
   summand identity. No original module can be pruned by this delivery.
5. **DAG agreement — pass.** The localized node's first step records component
   naturality followed by coproduct and chain-map extensionality; its second
   records precisely tensor-comparison and inverse-augmentation naturality.
   Its proof_deps are the union of the steps' uses. The new node isolates the
   projection/currying/braiding calculation and retains the parent's chapter,
   unit and blueprint ancestry. Existing node changes are confined to the
   stage-3-owned proof fields; all Lean statement records agree with their files.

Changes by the second reader: added this review and clarified the verification
and dependency accounting. Tried to close component naturality with the existing
projection wrapper and inverse-currying naturality; the chosen-projection matching
hit the 60-second compile limit. Restored the original delivered component theorem
and retained that unsuccessful attempt only in scratchpad. No delivered Lean or
node change was necessary. One original hole closed and one new hole added remains
a decomposition, with zero net holes closed.

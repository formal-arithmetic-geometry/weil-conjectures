## What changed

Proved `AlgebraicGeometry.Etale.baseChange_source_image_limit_descent` in
`Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent`, preserving its statement,
universes, hypotheses, visibility and original public import.

Constructed the canonical higher-direct-image diagram and limit cocone using
`higher_image_over_transition_coherence`. Applied
`nonempty_isColimit_higher_image_affine` and
`nonempty_isColimit_of_affine_etale` directly at the sheaf level, then transported the
colimit through inverse image along p and the stalk at x. The canonical bounded-below
homology-commutation isomorphism identifies this colimit with the source stalk.
`Concrete.isColimit_exists_rep` supplies the stage representative.

Private compatibility lemmas combine the existing base-change transition identity,
coefficient naturality and the homology-commutation isomorphism's naturality. A private
congruence procedure follows the existing kernel-checked method in
`HigherDirectImageOverMapCoefficient`: it constructs HEq congruence proofs and converts
them to Eq. It supplies explicit conversions of derived functor compositions; it adds
no mathematical premise and does not bypass kernel checking. Private comparison
isomorphisms are constructed from the existing canonical isomorphism, not chosen from
an existence theorem.

Proof-only imports add the three sheaf-colimit ingredients. Affine-transition limit
geometry and filtered ModuleCat colimits are exposed by the existing public import.
Updated the existing DAG node's proof, proof dependencies and proof origin to match
this route. Negative degrees are handled by the same colimit argument.

The scope of the local attributes, elaboration options and private helpers is recorded
in `coord/changes/BaseChangeSourceImageLimitDescentProofContext.md`; all 111 downstream
modules keep the same public interface and mathematical meaning. No adaptation is
required. The final source compiled without warnings and passed the delivery tool's
local axiom probe.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.baseChange_source_image_limit_descent`
(node `lem-sbc-source-image-limit-descent`). No holes added or split off; no `sorry`
remains in the delivered Lean module. The proof uses existing library declarations
and their recorded dependencies; those are not new holes of this delivery.

## No longer needed

Removed the redundant proof imports
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.Transition` and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`; the public stalk-transition
interface already exposes their declarations. No whole module is claimed unreachable
from the targets.

The proof does not use the canonical-point stalk-continuity wrapper
`sbc-lem-higher-image-pulledback-stalk-continuity`
(`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.Transition`,
`higherDirectImage_limit`). Its sheaf-colimit ingredients are used directly, so no
comparison between the geometric point x and a canonical point of S is needed.
The wrapper remains reachable through existing public transition imports; this
report does not claim that its whole module becomes unreachable from the targets.

Second reading also removed redundant proof imports
`Mathlib.AlgebraicGeometry.AffineTransitionLimit` and
`Mathlib.Algebra.Category.ModuleCat.FilteredColimits`: both are publicly re-exported
through BaseChangeStalkTransition → FailureOverField.Transition → Locality → Mathlib.
No module was pruned from the targets’ import closure.

## Where the brief, the DAG or earlier work was wrong

The original proof plan cites higher-image continuity at a canonical point of S.
That statement alone does not identify the arbitrary source stalk at x after inverse
image along p. The sheaf-colimit construction underlying that continuity theorem
provides the required statement before taking either inverse image or a stalk.
The library provides `Functor.mapDerivedCategoryPlusHomologyFunctorIso`,
which gives the required canonical comparison. No statement or definition was
weakened or changed. The unit's failure under limits step is preserved.


## Second reading by S1

1. **Interface — pass.** Compared the complete delivered module with the repository
   file. The existing theorem signature is byte for byte identical, including all
   section variables, universes and typeclass assumptions; its visibility and sole
   public import are unchanged. All added declarations are private. The scoped
   attributes and options have the proof-only scope described in
   `coord/changes/BaseChangeSourceImageLimitDescentProofContext.md`.
2. **Proof — pass.** Read the full construction and compatibility proof. The
   original delivered source compiled without errors or warnings (56.9 seconds).
   There is no `sorry`, forbidden axiom mechanism, or hollow definition. The two
   private comparison isomorphisms use the canonical homology isomorphism.
   `hB.some` chooses the universal-property proof for an explicitly constructed
   cocone, not an arbitrary mathematical object. The metaprogram only assembles
   congruence, proof-irrelevance, HEq and Eq proofs checked by Lean's kernel.
   A scratch copy of the final source compiled with `#print axioms` (57.3 seconds):
   the theorem depends only on `propext`, `Classical.choice`, `Quot.sound` and
   inherited `sorryAx` from still-open library dependencies. This is closure of
   the local hole, not an assertion that its entire dependency closure is proved.
   The final delivery dry run compiled without warnings and passed the axiom
   probe and preflight: `OK (dry run)`, review class CODEX for the node edit,
   proof-context record and scoped commands.
3. **Split statements — pass.** No statement was split off and no hole was added.
   Checked nonempty cofiltered indices, empty schemes, zero coefficients and
   negative degrees: no stronger assumption is silently needed. Independent
   LeanFinder search for filtered-colimit representatives confirms the existing
   `Concrete.isColimit_exists_rep`; Loogle confirms `NatIso.naturality_1`.
   Searched the library's source-transition and homology-isomorphism declarations:
   the sheaf-level construction is needed for the arbitrary pulled-back stalk.
4. **Route and pruning — pass.** The proof constructs the canonical higher-image
   cocone from the three imported library results, then preserves its colimit and
   uses Mathlib's representative theorem. Read the transition and coefficient
   naturality identities and checked every comparison orientation. The unit
   `sk-lem-failure-field` keeps its higher-image continuity argument for limits;
   no other step is bypassed. Its existing empty `realized` entries are unchanged.
   The only removed old proof dependency is
   `sbc-lem-higher-image-pulledback-stalk-continuity`, listed above. No whole module
   is newly unreachable. Removed two additional redundant Mathlib proof imports.
5. **DAG — pass.** Only `proof`, `proof_deps` and `proof_origin` differ from the
   existing node. The new dependency list is exactly the union of step `uses`,
   and every listed declaration is used by the Lean proof. No new nodes or
   statement-change records are needed.

Second reading changed the two redundant Mathlib imports, restored the original
public theorem docstring, corrected the report's unsupported claim about that
docstring, and updated the proof-context record's import count. The mathematical
proof and existing public interface are unchanged.

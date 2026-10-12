## What changed

Changed `Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde` and the proof route of
`lem-pc-affine-derived-pullback-tensor-tilde`. All six public theorem signatures are unchanged.
The natural affine pullback comparison is now obtained from the chosen derived-pullback
counit, its invertibility on K-flat tilde complexes, and the degreewise natural
`exists_tensorPullback_tilde_iso` comparison. The ordinary functor in the chosen construction
is identified with tensorPullback using its recorded object and morphism equations.
The categorical module K-flat predicate is converted into preservation of acyclicity through
the already proved homotopy-category criterion.

Both object formulas are proved by transporting along the given resolution: the factorization
from `exists_affineQCohDerivedEquivalence` makes `Q.map (tilde.map s)` invertible; apply derived
pullback or tensor with the second complex to its inverse, then compose with the corresponding
K-flat natural comparison. The tensor object formula therefore still depends on the existing
named natural tensor statement below. No new public statement, definition, or sorry was added.
Private helpers are fully proved. Natural comparison declarations were moved before the object
formulas so that the formulas can use them.

## Proved and sorry left

The following three original declarations now have complete Lean proofs from the existing
library statements:

- `AlgebraicGeometry.derivedPullback_tilde_kFlat_natIso`.
- `AlgebraicGeometry.derivedPullback_tilde_iso`.
- `AlgebraicGeometry.derivedTensor_tilde_iso`.

The following original declarations still have `sorry`, all belonging to
`lem-pc-affine-derived-pullback-tensor-tilde`:

- `AlgebraicGeometry.derivedPullback_openRestriction_iso`.
- `AlgebraicGeometry.derivedTensor_openRestriction_iso`.
- `AlgebraicGeometry.derivedTensor_tilde_kFlat_natIso`.

No new sorries or nodes are delivered. The proofs still use existing statements such as
`isKFlat_tilde` and the affine derived equivalence; this is a reduction in the stage-3 sense,
not a claim that their transitive axiom closure is already sorry-free.

## No longer needed

Removed direct proof imports `Sheaf.Algebra.Homology.KFlat`,
`Sheaf.Algebra.Homology.KFlatPullback`, `Sheaf.Algebra.Homology.KFlatResolution`, and
`Sheaf.AlgebraicGeometry.Modules.AffineTildeTensor`. Their declarations are not used directly in the
three completed proofs. K-flat interfaces needed by the statements are already available
through the preserved public imports. Resolution existence is unnecessary for the affine
object formulas because a resolution is supplied explicitly in their hypotheses.

No node or module is globally pruned: resolution and pullback preservation remain in the
restriction plan, and affine tilde/tensor remains in the unfinished natural tensor plan.
The DAG retains those dependencies for the remaining named sorries. No blueprint unit or step
is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original node's tensor step said that preservation of finite direct sums suffices.
An unbounded total tensor has potentially infinite diagonals. The route now requires
preservation of all small direct sums, available from the tilde/global-sections adjunction
`lem-weil-pbc-affine-tilde-gamma-adjunction`. The theorem statements need no correction.

The shared category of sheaves used in these statements and `Scheme.Modules` have different
category instance expressions. Lifting the ordinary affine pullback comparison explicitly
in each degree avoids an unintended choice of category instance. The delivered proof uses
the original shared category throughout.

An attempted natural tensor reduction separated the argument into an ordinary total-complex
tilde comparison and a general K-flat derived-tensor model comparison. The two auxiliary
statements compiled separately, but the combined proof repeatedly exceeded the compiler's
60-second limit, including with the affine pullback proof temporarily removed. That attempt
is not delivered: no unverified composition or unused auxiliary sorry enters this delivery.
The next worker can pursue the natural tensor computation or the restriction comparisons.

## Second reading by A3

1. Compared the delivered module against the repository with `diff`, and extracted each
   original declaration's signature with the project's declaration parser. All six signatures
   are byte for byte identical. No definition, public import, or public declaration was changed
   or added. The only added declarations are two private, completely proved proof helpers.
   Verdict: unchanged public statements and definitions.
2. Compiled the delivered file with `lcompile.py`: exit 0, no warnings, 52.6 seconds.
   Compiled a scratch copy with `#print axioms` for all six public theorems and both private
   helpers: exit 0, 56.7 seconds. Only `propext`, `Classical.choice`, `Quot.sound`, and
   `sorryAx` occur; the categorical K-flat helper uses only the three standard axioms.
   The other completed proofs depend on still-open library statements, as the report says.
   Exactly the three named original theorems listed above retain whole-proof `sorry`.
   No forbidden declaration or hollow definition occurs. Verdict: valid partial reduction.
3. No statement was split off and no new node or sorry was introduced. Read the remaining
   original theorem docstrings and their matching node. Checked the actual reduction:
   the pullback counit is inverted only after proving K-flatness of the tilde model;
   degreewise base change respects differentials and maps; the object formulas invert
   `Q(tilde(s))` and compose with the appropriate natural comparison at the supplied model.
   Zero complexes, the identity ring map, identity resolution maps, and unbounded inputs
   require no additional hypotheses. The tensor formula's use of the original natural tensor
   theorem is a component plus transport, with its remaining obligation explicitly retained.
   Verdict: no new restatement or unchecked auxiliary obligation.
4. Searched the library and upstream sources for alternative tilde/quasi-isomorphism and
   derived affine comparisons, and used `msearch.py` with degreewise tilde and natural-iso
   queries. The existing homotopy K-flat criterion and ordinary tensor-pullback comparison
   already supply the short route taken here; no ready-made derived affine comparison was
   found. Each retained proof import is used, and the public imports supply statement types
   or their instances. Verified all four removed imports and their exact paths. No old
   proof dependency is obsolete for the whole node: resolution and pullback preservation
   remain in the open restriction proof plan, and ordinary tilde/tensor remains in the open
   natural tensor plan. Read `dag/units/sk-thm-picard-f-representable.json`; its `realized`
   entries are empty on the base, and this delivery changes no unit or chapter route.
   Verdict: pruning report complete; no unit step bypassed.
5. Compared the node diff, read all proof steps, and checked that `proof_deps` is exactly
   their `uses` union. The implemented counit comparison and resolution transport are
   recorded, the unfinished restriction and natural tensor plans remain identified, and
   the correction from finite sums to arbitrary small sums has its adjunction dependency.
   All other node fields, including the statement and Lean record, are unchanged.
   Verdict: node agrees with the partial Lean proof.

Second reading changed only this report: corrected the removed affine tilde/tensor module's
path to `Sheaf.AlgebraicGeometry.Modules.AffineTildeTensor` and added this review. No Lean
repair was needed. No new split-off statement was available to close in this delivery.

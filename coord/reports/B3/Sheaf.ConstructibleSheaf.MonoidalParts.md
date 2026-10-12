## What changed

Replaced both proofs in `Sheaf.ConstructibleSheaf.MonoidalParts` without changing either
statement. Added proof-only imports of `Mathlib.RingTheory.TensorProduct.Finite`,
`WeilConjectures.ConstructibleSheaf.Pullback`, and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal`.

Local constancy uses the fibre-product refinement of the two trivializing covers, as planned.
The two pullbacks are constant by pullback preservation and the composition isomorphisms;
the pullback tensorator then identifies their tensor with the restriction of the tensor sheaf.
A proved private helper establishes that constant module sheaves tensor to a constant sheaf:
use the tensorator of sheafification and the objectwise isomorphism between the tensor of two
constant presheaves and the constant presheaf at the tensor product.

Finiteness uses the existing lifted geometric-stalk tensor isomorphism, Mathlib's
`Module.Finite.tensorProduct`, and `ModuleCat.isFinitelyGenerated_iff`. The lifted/unlifted
stalk comparison transports both hypotheses and the conclusion. No new nodes or intermediate
sorries are needed; both DAG plans are followed unchanged, and neither node realizes a unit
statement or step. Import-cycle checks passed for both added source-library imports.

Searches: LeanFinder for tensor products of locally constant sheaves returned general monoidal
sheaf structures, but no preservation theorem; Loogle for `Module.Finite` returned finite-module
APIs. Direct source searches located the common-cover proof in ConstructibleSheaf.Biproduct,
the pullback comparison in ConstructibleSheaf.Pullback, the stalk comparison in StalkMonoidal,
and Mathlib.RingTheory.TensorProduct.Finite's tensor finite-generation instance.

## Proved and sorry left

- `AlgebraicGeometry.Scheme.IsLocallyConstantSheaf.tensorObj_part`
  (node `lem-weil-pbc-flc-tensor-locally-constant-part`): complete proof.
- `AlgebraicGeometry.Scheme.IsFiniteSheaf.tensorObj_part`
  (node `lem-weil-pbc-flc-tensor-finite-part`): complete proof.
- Private helper `constant_tensor`: complete proof.

No sorry remains in the module and no sorry is added elsewhere. The local compile succeeds
without warnings. No assumptions on connectedness, nonzero coefficients, or nonempty covers
are introduced: the common-cover construction also handles the empty scheme and the
finite-generation argument includes zero modules.

## No longer needed

No dependency nodes or modules are pruned. The public import of
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal` is replaced by a plain
proof import, with `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs`
publicly imported to supply the tensor structure needed in the unchanged statements.
`Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed` remains public because the global
sheaf tensor structure requires the closed coefficient category. Each proof import is used.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The DAG steps have no named proof dependencies, but their
arguments can be fully implemented with existing source-library and Mathlib declarations.
The finite-sheaf definition uses unlifted stalks while the monoidal stalk API uses lifted stalks;
the existing `uliftSheafFiberIso` supplies the required bridge.

## Second reading by B3

1. Compared the sole delivered Lean module with the read-only repository using `diff`.
   Both existing signatures, section variables, and docstrings are byte for byte unchanged.
   No definition, target, or statement is altered. The import exposure correction has the change record listed below.
2. Compiled the revised module in a scratch copy through `lcompile.py`: no errors or warnings.
   Explicit `#print axioms` for both public theorems and the private `constant_tensor` helper
   gives exactly `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` occurs.
   No `sorry`, axiom declaration, unsafe code, opaque declaration, or external implementation
   occurs in the delivered module. The pullback comparison directions and the lifted/unlifted
   stalk transports were read and checked against their definitions.
3. No statements are split off and no new sorry is introduced. The private proved helper uses
   genuine constant objects obtained from the essential-image witnesses, and sheafification's
   tensorator; it is not a restatement of local constancy. Independent searches with
   `constantSheaf.*tensor|tensor.*constantSheaf|IsConstant.*tensor` and direct searches of
   Mathlib and both library roots found no ready-made constant-tensor theorem to replace it.
   The common-cover construction requires neither nonempty covers nor connectedness and
   handles the empty scheme. The finite tensor instance applies also to zero modules and
   arbitrary commutative coefficient rings.
4. The proofs follow the shortest available routes found: common trivializing cover and
   monoidal pullback; stalk tensor comparison and `Module.Finite.tensorProduct`. All proof
   imports supply used APIs. Corrected the proof-only public `StalkMonoidal` import by exposing
   only `GrothendieckAbelian.Monoidal.Defs`. Both old `proof_deps` are empty, so no node is
   omitted from the pruning report. Read `dag/units/sk-thm-p1.json`: neither item node is
   in `realized`, and the unit route is preserved.
5. Read both DAG nodes alongside the Lean: their existing statements, one-step proof plans,
   empty proof dependencies, and blueprint proof origins agree with the implemented arguments.
   There are no new nodes or changed routes to record.

Changed only the import exposure described above and added a docstring to the new private
helper. Both mathematical proofs were retained as written. The delivery tool additionally
checks every declaration's axioms and compiles the file on the server before pushing.

Import-exposure change record: `coord/changes/monoidal-parts-proof-imports.md`.
Preflight required this record because the public import set changed; the sole direct
importer independently exposes `StalkMonoidal`, so no downstream adaptation is necessary.

## What changed

Proved `AlgebraicGeometry.Scheme.Modules.tensorGradedKernel_locally_ideal` in
`Sheaf.AlgebraicGeometry.TensorGradedKernelLocalIdeal`, with its signature and visibility
unchanged. Added five proved private helpers: local lifting along module epimorphisms,
local tensor representatives, tensor-image ideal membership, local membership for the
multiplication image, and the graded-kernel factorization through that image.

Added proof-only imports of `TensorGradedDegreeData`, `ClosedImmersionUnitKernel`, and
Mathlib's local-surjectivity, abelian-group, and abelian-sheaf infrastructure, plus
the source library's colimit-preservation instances for the underlying abelian sheaf. The original
public import is unchanged. Updated the theorem docstring and its node's proof route.
No definitions or existing statements changed; no adaptations or new modules are needed.
The static checker requires a record for changed top-level elaboration commands:
`coord/changes/tensorGradedKernel-local-proof-commands.md` documents their local scope,
the unchanged public interface, and the declaration users.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Modules.tensorGradedKernel_locally_ideal`
(node `lem-sc-tensor-graded-kernel-local-ideal`). No sorry remains in the delivered module,
and no hole was added or split off. This is a proof from existing declarations, including
the closed-immersion kernel theorem, rather than a claim that all its dependencies are
already free of sorry.

The entire file compiled with `lcompile.py`; all five private helpers are proved.
The proof covers arbitrary L and immersion ideal, uses no multiplication law or
invertibility hypothesis, handles zero tensors explicitly, and is vacuous on an empty
scheme because the hypotheses supply a point.

## No longer needed

Removed the redundant direct import of Mathlib.Topology.Sheaves.LocallySurjective; its required declarations remain available through the other imports, and the module compiles cleanly without it.

Removed planned proof dependencies of this node:

- `lem-pc-stalk-direct-sums`, module `Sheaf.Topology.StalkDirectSums`: tensor
  sheafification and local epimorphism lifting avoid stalk direct-sum representatives.
- `lem-weil-pbc-closed-immersion-unit-quotient`, module
  `Sheaf.AlgebraicGeometry.ClosedImmersionUnitQuotient`: only its kernel statement is
  required; use `ClosedImmersionUnitKernel` directly, without the cokernel isomorphism.

Neither planned module was imported by the original file, and neither is imported now.
No baseline import was removed. The explicit proof import of
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification` is necessary
for preservation of epimorphisms on underlying abelian sheaves (removing it fails
instance synthesis for `Epi (F.map f)`). These are local proof-dependency removals, not
a claim of global unreachability. The unit's
realized statement and steps are preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The planned stalk reconstruction is
unnecessary: categorical image functoriality handles the degreewise coefficient ideals,
and local surjectivity of tensor sheafification supplies the finite tensor argument.
The first local compile lacked the newly landed `TensorGradedAlgebraData.olean`; the
ordinary cache refresh resolved this, without compiling or changing any dependency.
The first dry run compiled but conservatively classified the scoped notation and local
instance commands as an interface change; the change record above documents that no
importer sees a changed declaration or global registration.

## Earlier second reading (a previous round; superseded)

1. **Repository-visible declarations:** diffed the delivered module against the repository
   version. The public theorem signature, visibility, and all existing declarations are
   unchanged; only proof-local imports, helpers, and the theorem proof were added.
   **Verdict: pass.**
2. **Proof soundness:** compiled the module and the sandbox import closure with
   `lcompile.py`; searched delivered Lean and node files for `sorry`, axioms, unsafe or
   opaque constructs. No such construct remains, and the proof uses only ordinary
   categorical and sheaf lemmas. **Verdict: pass.**
3. **Statements and dependencies:** checked the sole target against node
   `lem-sc-tensor-graded-kernel-local-ideal`, including its unchanged hypotheses and
   conclusion. The private helpers are strictly intermediate reductions, carry no new
   public statement, and the node proof route and dependencies match the imports used.
   **Verdict: pass.**
4. **Pruning and route:** verified that the proof does not use stalk direct-sum
   reconstruction or the closed-immersion quotient isomorphism; the unit's realized
   statement and steps remain intact. Removed dependency claims are recorded under
   `## No longer needed`, and all proof-only imports are necessary for elaboration.
   **Verdict: pass.**
5. **DAG and documentation:** checked the node's `proof`, `proof_deps`, and
   `proof_origin` against the implemented factorization and local lifting proof, and
   checked the scoped elaboration changes against
   `coord/changes/tensorGradedKernel-local-proof-commands.md`. **Verdict: pass.**

Changed only the report by adding this second-reading record; no Lean declarations or
node statements required repair.

## Second reading by Q3

1. **Unchanged interface — pass.** Independently diffed the sole delivered Lean module
   against the repository and compared the existing theorem signature byte for byte.
   Its binders, hypotheses, conclusion, namespace, visibility and public import are
   unchanged. There are no new definitions or forced adaptations. The added notation,
   local instances and restricted irreducibility attributes affect elaboration only;
   the existing change record accurately documents them.
2. **Proof and axioms — pass.** Compiled the complete sandbox with `lcompile.py --all`
   without errors or warnings (15.6 seconds). Compiled a scratch copy with explicit
   `#print axioms` commands for `epi_local_lift`, `tensor_local_lift`, `tensor_image_mem`,
   `image_locally_ideal`, `gradedKernelFactor` and
   `AlgebraicGeometry.Scheme.Modules.tensorGradedKernel_locally_ideal`.
   Every result lists exactly `propext`, `Classical.choice` and `Quot.sound`; in
   particular, no `sorryAx` is reachable in this compiled proof. A token scan found
   no sorry, axiom, unsafe, opaque, implemented_by or extern in the delivered module.
   No data definition or arbitrary witness construction has been introduced.
3. **Intermediate statements — pass.** There are no split-off statements or new holes.
   Read all five proved private helpers, the graded degree-data theorem, and the
   closed-immersion unit-kernel theorem. The factorization correctly transfers units
   between adjunctions by an isomorphism and descends through the kernel coproduct.
   Local lifting makes no claim of surjectivity on an arbitrary whole open. Tensor
   induction explicitly covers zero and addition; zero ideals and the degree-zero
   summand cause no exception. Intersecting two neighborhoods supplies a common
   affine neighborhood, and the empty scheme has no input point. A fresh LeanFinder
   query about a quotient sheaf kernel generated by ideal multiplication and `rg`
   searches for local lifting and ideal membership found no replacement for the
   complete theorem. Related existing local-lifting helpers are private or impose
   additional finite-local-freeness hypotheses, or give only a germ equality.
4. **Shortest route, imports and pruning — pass.** The image-factorization argument
   avoids reconstructing finite degree supports on stalks. Individually removing
   `Mathlib.Algebra.Category.Grp.EpiMono`, `Mathlib.Algebra.Category.Grp.Abelian` or
   `Mathlib.CategoryTheory.Sites.Abelian` in scratch copies makes compilation fail
   in local surjectivity, for the missing factorization or balanced-sheaf instance.
   The remaining proof imports supply the degree coproduct, unit-kernel formula and
   colimit-preservation instance. All added imports used only by proofs are plain
   imports. `No longer needed` lists both old proof dependencies omitted by the new
   proof: stalk direct sums and the unit quotient. This is dependency pruning, not
   a claim that either module becomes globally unreachable. The unit record
   `dag/units/sk-thm-curveestimate.json` realizes its statement by
   `thm-sc-proper-cohomology` and has no realized steps; this below-unit reduction
   changes none of that route.
5. **DAG agreement — pass.** Compared both node versions: only `proof`, `proof_deps`
   and `proof_origin` differ. The four proof steps match degreewise kernel
   factorization, local image/tensor lifting, ideal membership by tensor induction,
   and intersection of neighborhoods. Their dependency union is exactly the
   recorded `proof_deps`. Node statement, statement dependencies, Lean signature,
   chapter, unit and all other fields are unchanged. No new node is needed.

Second reading changed only this report, adding the independent checks and explicit
axiom results. No Lean proof, statement, definition, import or node required repair.
Holes closed: `AlgebraicGeometry.Scheme.Modules.tensorGradedKernel_locally_ideal`
(one of one). Holes added: none. Split off: none.

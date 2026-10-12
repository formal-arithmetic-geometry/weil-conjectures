## What changed

Replaced the hole in `AlgebraicGeometry.formalFunctions_finite_quotient_iso_b` with an
assembly from sheaf quotient identifications and adjacent cohomology compatibility.
The existing theorem signature and docstring are unchanged. The assembly obtains
quasi-coherence from coherence on the locally Noetherian source, identifies the tensor
pullback with Mathlib's pullback by adjoint uniqueness, and uses the affine cohomology
edge isomorphism. Source naturality proves invertibility and the quotient-unit equation.
A proved private scalar identity computes the local-ring action through the finite
quotient; Mathlib's restriction-of-scalars composition isomorphisms handle the scalar
transport. Componentwise invertibility and `NatTrans.ofOpSequence` assemble the result.

Added the modules `Sheaf.AlgebraicGeometry.FormalFunctionsFiniteSheafQuotient` and
`Sheaf.AlgebraicGeometry.FormalFunctionsFiniteQuotientTransition`. These isolate the
sheaf construction and the adjacent transition identity, respectively. Neither restates
the original cohomology-system isomorphism. The sheaf isomorphism is uniquely determined
by its composite with the epimorphic quotient projection. The transition theorem applies
to arbitrary sheaf maps factoring the units and does not assume their invertibility.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.formalFunctions_finite_quotient_iso_b`
(node `lem-weil-pbc-formal-functions-finite-quotient-iso-b`). There are no holes left in
the item's module. The private theorem `finite_scalar` is proved directly.

Added two holes:

- `AlgebraicGeometry.formalFunctions_finite_sheaf_quotient`, node
  `lem-weil-pbc-formal-functions-finite-sheaf-quotient`.
- `AlgebraicGeometry.formalFunctions_finite_quotient_transition`, node
  `lem-weil-pbc-formal-functions-finite-quotient-transition`.

This is a decomposition: one upper hole closed and two strictly smaller holes added,
not a proof without remaining dependencies. Both new statements have source citations,
complete proof instructions, and matching DAG nodes. Existing dependency holes are
unchanged. The edge cases checked in words are n = 0, p = 0, the zero module, and empty
fibres. The transition argument cancels only the sheaf quotient projection, never its
potentially nonsurjective map on higher cohomology.

## No longer needed

Removed four direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.QuotientBaseChangeIdeal`;
- `Sheaf.AlgebraicGeometry.ClosedImmersionUnitQuotient`;
- `Sheaf.AlgebraicGeometry.TensorPullback`;
- `Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`.

The quotient and closed-immersion modules are imported by the new sheaf obligation.
The tensor-pullback construction and adjunction remain accessible through the public
imports of `FormalFunctionsFinitePullback`. None of these modules is globally pruned.

Compared with the old item's `proof_deps`, the following are no longer direct proof
nodes: `def-nagata-extended-ideal`, `def-pc-fibre-product`, `def-pc-module-pullback`,
`lem-weil-pbc-closed-immersion-unit-quotient`,
`lem-weil-pbc-quotient-base-change-closed-immersion-ideal`, and `pqf-def-affine-morphism`.
The first five remain in statement dependencies or the lower obligations; the affine
morphism notion remains in the affine-edge theorem's interface. No node or module is
claimed as globally pruned. The unit's realized statements and steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

The original node gave the entire finite-level construction as one step. Its existing
lemmas supply the general closed-immersion quotient and cohomology functoriality, but
there was no declaration identifying this particular finite-fibre immersion with the
quotient by the recursively constructed sheaf ideal power. There was also no declaration
stating the adjacent-level identity for the particular adjunction-defined FMaps.
The two new nodes make those missing applications explicit.

The cited local Stacks source tree is absent on this machine. The sources were read on
the official Stacks pages for Tags 02OD, 04CJ, 01F7 and 01FB. LeanSearch returned an
Internal Server Error, recorded by the required search tool; Lean Finder and local
Mathlib searches found supporting geometry, not either complete new assertion.

## New nodes

`lem-weil-pbc-formal-functions-finite-sheaf-quotient` records the finite closed immersion
and the uniquely specified sheaf quotient isomorphism, before applying cohomology.
Its module is `Sheaf.AlgebraicGeometry.FormalFunctionsFiniteSheafQuotient`.

`lem-weil-pbc-formal-functions-finite-quotient-transition` records adjacent compatibility
of the cohomology h-maps associated to sheaf maps factoring the finite units. It gives
neither existence nor invertibility of these maps. Its module is
`Sheaf.AlgebraicGeometry.FormalFunctionsFiniteQuotientTransition`.

The original node's proof and proof dependencies now describe the assembly. No existing
public statement or definition was changed. Elaboration options are declaration-local;
there is no interface change and no change record is needed.

## Earlier second reading (a previous round; superseded)

The proof compiles against the sandbox build. The original target signature is unchanged;
the two added intermediate statements are strictly smaller finite-level sheaf and transition
claims, and the unit route is retained. The remaining `sorry`s are exactly those two named
intermediate obligations.

## Second reading by U2

1. **Interfaces: pass.** I compared the three sandbox modules against the repository.
   Only `FormalFunctionsFiniteQuotientIsoB` already exists. Its entire theorem signature,
   including the properness, locally Noetherian and coherence hypotheses, all five let
   bindings, the scalar restriction, the existential system isomorphism and the pointwise
   quotient-unit equation, is byte-for-byte identical. Its docstring is unchanged.
   The other two modules introduce statements rather than alter existing ones. There
   are no new definitions or adaptations. I scoped the two file-wide transparency
   options to declarations and removed the now-unnecessary proof-options change record.

2. **Proof and trust: pass as a decomposition.** All three modules compile through
   `lcompile.py --all`, with no compiler errors or warnings. After the option repair the
   assembly compiles again in 45.6 seconds. A scratch copy with `#print axioms` compiled
   in 44.3 seconds: `finite_scalar` uses precisely `propext`, `Classical.choice` and
   `Quot.sound`; the assembly and the two intermediate theorems additionally use
   `sorryAx`. The only two local holes are the named intermediate theorems listed above.
   I checked that no forbidden declaration or holed definition was introduced.
   Source naturality with the identity identifies the finite cohomology map with the
   composite of the cohomology of `e_n` and the affine edge map; both are isomorphisms.
   The private scalar calculation uses the first pullback projection and Gamma-Spec
   naturality, then completion evaluation, with the direction of the ring maps correct.
   Both restriction-of-scalars isomorphisms preserve the underlying additive map.
   `NatTrans.ofOpSequence` has the correct opposite-index orientation. The final source
   naturality equation is evaluated on `z`, proving the original quotient-unit equation.
   Choosing `e_n` from its open theorem is legitimate: the cokernel projection is epi
   and its specified composite determines `e_n.hom`, hence the isomorphism. Likewise,
   the linear lift is determined by its underlying additive map. No arbitrary data
   object is chosen from mere unproved existence.

3. **Intermediate statements: pass.** I read the official Stacks proofs at
   [02OD](https://stacks.math.columbia.edu/tag/02OD),
   [04CJ (1)](https://stacks.math.columbia.edu/tag/04CJ),
   [01F7](https://stacks.math.columbia.edu/tag/01F7) and
   [01FB](https://stacks.math.columbia.edu/tag/01FB), and opened the actual declarations
   of `quotientBaseChange_closedImmersion_ideal`,
   `quotientBaseChange_extendedIdeal_mul_pow`, `closedImmersion_unit_quotient`,
   `exists_tensorPullbackAdjunction`, `formalFunctionsFiniteFMap`,
   `formalFibreTransitionFMap`, and the cohomology source-naturality/composition lemmas.
   The sheaf obligation is the base-changed quotient construction for arbitrary modules:
   properness and coherence are unnecessary at this step. The transition obligation
   assumes a family factoring the units; uniqueness after precomposing with the epi
   sheaf quotient projection gives its sheaf square, and cohomology functoriality gives
   the displayed equality. It never cancels the map on higher cohomology. Neither
   obligation supplies the original A-linear system isomorphism on its own.
   In degree zero these are the usual module quotient maps. Level `n = 0` uses the first
   power, not the zeroth power. If the maximal ideal is zero, each fibre map identifies
   the same local base change and all quotient maps are identities. For the zero module
   or an empty fibre the relevant modules are zero; the same epi cancellation works.
   I searched again with the registered Lean Finder query on nested-immersion cokernel
   naturality, Loogle's `cokernel.π_desc`, and the registered grep query, and directly
   searched Mathlib, upstream WeilConjectures and both library roots. The hits supply
   composition and cokernel tools, not either full new statement. Neither hole has a
   short direct specialization proof available from those hits; both remain explicit.

4. **Shortest route and pruning: pass after report repair.** The assembly uses the
   existing coherence criterion, Mathlib's ordinary quasi-coherent pullback (identified
   with tensor pullback by adjoint uniqueness), the existing affine edge theorem and
   cohomology h-map properties. The new modules are only the geometric quotient and
   adjacent naturality obligations left by that route. Existing public imports are
   unchanged; new proof-only imports are plain imports. The sheaf module's public
   closed-immersion import is needed by its statement. I completed `No longer needed`
   with both removed tensor imports and every removed direct node dependency. These
   are movements or transitive uses, not global pruning. I read
   `dag/units/sk-thm-p1.json`: no realized statement or proof step is replaced or edited.

5. **DAG agreement: pass after metadata repair.** Each node's proof dependencies equal
   the union of its steps' uses; the original node now describes exactly the three
   assembly phases (sheaf comparisons and quasi-coherence, scalar-linear isomorphisms,
   naturality and the unit equation). New nodes have their source, proof in words,
   creation, search, chapter/unit and exact Lean statement records, with no cycles back
   to the item. I made their prose statements self-contained in TeX, explicitly naming
   the finite fibres and pulled-back coefficients. Blueprint searches for `quotient
   infinitesimal` and `formal functions` found no duplicate imported statement.
   The automatic ancestor lookup returns `None` because the existing created-item
   chain passes through a module name. I instead followed the recorded ancestry of
   `lem-weil-pbc-formal-functions-finite-quotient-iso` to the imported
   `thm-weil-pbc-henselian-idempotent-lifting`, and corrected the two new nodes' ancestor,
   intervening nodes and proof place, adding `same_as: []`. Existing ancestry fields
   outside the stage-3-owned fields were left unchanged. Failed LeanSearch entries in
   the new nodes now explicitly say `verdict: unavailable`.

Second reading changed declaration-local elaboration options, trailing whitespace,
pruning documentation and new-node statement/ancestry/search metadata; removed an
unnecessary change record. No theorem signature or mathematical proof body changed,
and no further hole was closed or added. The result remains one original hole closed,
two strictly smaller holes added, and no globally pruned modules (local net -1).

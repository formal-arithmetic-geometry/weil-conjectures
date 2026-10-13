## What changed

Replaced the whole-proof sorry of
`AlgebraicGeometry.grothendieckDevissage_secondAdicSystem_lift_data` with a complete
Lean assembly proof, keeping its signature and visibility unchanged. The proof uses the
existing `closedSupported_formal_algebraization` to algebraize each supported quotient
system on V(K^(e+1)). It chooses these algebraizations within the existential proof,
builds the inverse system with `Functor.ofOpSequence`, checks all three defining adic
conditions, and assembles the pointwise comparisons with `NatTrans.ofOpSequence`.
Componentwise isomorphisms give the required double-system comparison.

The conclusion places no condition on δ, so δ is the zero morphism. Consequently α,
θ, and hθ are not needed in this data-only proof. The existing signature is preserved;
a declaration-scoped unused-variable linter setting accounts for these hypotheses and
the unused names of the existential binders. No definitions or other existing modules
were changed. The residual adjacent-transition step is independently stated in a new module. Two other
new modules prove the quotient system's I-adic conditions completely, using the existing
canonical quotient interchange and the multiplication/cokernel lemmas.

All four delivered modules compile without warnings through lcompile.py. The preserved
original theorem's proof is complete; its dependencies still include one new hole after the second reading.
Read the proof source at https://stacks.math.columbia.edu/tag/088A; the referenced local
coherent.tex file is absent in this checkout. LeanSearch was attempted twice and returned
an internal service error. LeanFinder and Mathlib/library source searches found module
adic-completion lemmas but no matching coherent sheaf theorem. Searches also found and
reused `ClosedSupportedFormalAlgebraization`; no duplicate algebraization statement was
introduced. Whole-blueprint phrase searches found no matching quotient or transition node.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.grothendieckDevissage_secondAdicSystem_lift_data`
(node `lem-weil-pbc-devissage-second-adic-system-lift-data`).

Also proved the new theorem
`AlgebraicGeometry.formalSecondIdealQuotient_coherent`
(node `lem-weil-pbc-formal-second-ideal-quotient-adic`). Its proof verifies coherence,
I-power annihilation after the epi K-quotient projection, and the actual adjacent
transition equation by the canonical quotient-interchange projection identity.

Also proved in the second reading
`AlgebraicGeometry.formalSecondIdealQuotient_supported`
(node `lem-weil-pbc-formal-second-ideal-quotient-supported`). It reuses the existing
`power_inclusion_iso` and `product_inclusion_iso` private helpers through `import all`
of `ThickeningSystemPushforwardAdic`, and `idealModuleProduct_quotient_zero` through
`import all` of `CoherentFormalModule`. This closes the recursive-power/ideal-data bridge
without introducing another statement.

Added exactly one hole, a public named theorem with whole proof `by sorry`:

- `AlgebraicGeometry.formalSecondIdealAlgebraization_transitions`
  (node `lem-weil-pbc-formal-second-ideal-algebraization-transitions`): annihilation of
  closed pushforwards and lifting adjacent transitions, with their quotient isomorphisms
  and specified completion squares. This statement constructs no global inverse system
  and no global comparison; those are assembled in the item's proof.

This remains a decomposition, not a sorry-free proof of the target closure.
Relative to the repository: holes closed: 1; holes added: 1; net: 0.
During the second reading, the proposed support hole was also closed.
There is no sorry left in the item's module, no sorry in any definition, and no arbitrary
module data defined by choosing a witness from a holed existence theorem. The supported
algebraizations are determined up to the compatible isomorphisms used downstream by the
completion equivalences; adjacent maps are determined uniquely by their completion squares.

Edge cases checked in the statements: K=0 gives the original terms and identity-type
quotient transitions; K=top gives zero quotients and empty closed thickenings; I=0 gives
constant formal systems and ordinary K-quotients; I=top forces the I-adic terms to vanish.
For e=0 the power is K^1, never K^0. The transition uses thickenings of powers e+2 and
e+1, both covered by hthick. Annihilation is scheme-theoretic, not merely support on the
underlying closed set. The zero formal module and empty scheme impose no extra
nonemptiness assumption. The supplied pointwise comparisons, together with the
completion equivalences, determine the algebraizations up to compatible isomorphism.

## No longer needed

Removed the item's redundant direct imports of
`Mathlib.CategoryTheory.Functor.Currying` and
`Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`. Their declarations are available
through the new statement modules and the existing closed-supported algebraization
module. These Mathlib modules remain in the transitive import closure; no whole library
module is claimed pruned.

No existing mathematical node is made globally unnecessary by this delivery. The
closed-immersion coherent equivalence remains needed through the existing supported
algebraization theorem and through the remaining transition lemma. The α-lifting part
of the original informal plan is unnecessary for this data-only conclusion. No unit
statement or realized unit step was bypassed.

## Where the brief, the DAG or earlier work was wrong

The item's DAG had one step citing closed-immersion equivalence, but that equivalence
alone does not assert that the second-ideal quotients are I-adic or give their algebraized
adjacent transitions. The delivered route separates those steps and writes the final
assembly in Lean. Its node's proof, proof_deps, and proof_origin now match that route.
The original data theorem's conclusion does not state any compatibility for δ and σ,
so its hypotheses α, θ, and hθ do not have to be used. Its signature is unchanged.

STATEMENT-DISPUTED: the neighboring declaration
`grothendieckDevissage_secondAdicSystem_lift_compatibility` asserts its square for arbitrary
δ and σ without assuming they are the lifts of α. Take a nonzero coherent module over
Spec of a field, I=K=0, M and N its constant completion systems, α the identity,
σ and θ the canonical comparisons, and δ=0. The claimed equation identifies the identity
with zero. The Tag 088A construction proves compatibility for chosen lifts, not for
arbitrary maps. This delivery does not import, apply, or edit that independently held
module. Its issue should be repaired by its holder; nothing about the current existence
statement requires that false universal compatibility claim.

## New nodes

`lem-weil-pbc-formal-second-ideal-quotient-adic`, in
`lean/Sheaf/AlgebraicGeometry/FormalSecondIdealQuotientAdic.lean`, is proved. It records the
termwise second-ideal quotient's I-adic conditions and the quotient-interchange argument.

`lem-weil-pbc-formal-second-ideal-quotient-supported`, in
`lean/Sheaf/AlgebraicGeometry/FormalSecondIdealQuotientSupported.lean`, is the proved
scheme-theoretic annihilation statement, strictly independent of algebraization and
transition choices. The second reader closed it using existing power/product helpers.

`lem-weil-pbc-formal-second-ideal-algebraization-transitions`, in
`lean/Sheaf/AlgebraicGeometry/FormalSecondIdealAlgebraizationTransitions.lean`, is the
residual adjacent lifting statement for coherent modules already chosen on the
thickenings, with given pointwise completion isomorphisms. It supplies local adjacent
maps and their equations, rather than restating the existence of N and σ.

All three nodes are in dag/nodes/sec-proper-base-change/ and have source, full proof
steps, search records, and exact Lean signatures. No change record is required: every
existing declaration's interface and every public import of the item stay unchanged.

## Second reading by W4

1. **Interfaces:** Compared the only existing delivered module with the repository using
   `diff -u`. Its theorem signature and docstring are byte for byte unchanged; only proof
   imports, scoped options, an explanatory comment and the proof changed. The other three
   modules are new. No definition or target statement changed and no change record is needed.
2. **Proof and trust:** All four modules compile cleanly through `lcompile.py --all`.
   The original proof genuinely constructs the sequence, proves all three adic conditions,
   and constructs its natural comparison. The second reading closes
   `formalSecondIdealQuotient_supported`; only `formalSecondIdealAlgebraization_transitions`
   remains `by sorry`. Explicit scratch `#print axioms` checks show only `propext`,
   `Classical.choice`, `Quot.sound` and the permitted dependency `sorryAx`. There are no
   forbidden declarations or data holes. The existential choices of algebraizations are
   characterized up to isomorphism by completion equivalences, and the transition square
   uniquely characterizes each chosen transition by full faithfulness.
3. **Residual statements:** Read [Stacks Tag 088A](https://stacks.math.columbia.edu/tag/088A),
   especially the construction of G_e and its canonical quotient transitions. The remaining
   theorem assumes the pointwise algebraizations and comparisons already exist, then lifts
   only adjacent maps; it does not restate existence of N or the global comparison. Its
   annihilation clause holds for closed pushforwards; full faithfulness on V(K^(e+2)) lifts
   the conjugated double-system transition. Factoring by K^(e+1) and reflecting the
   completed quotient isomorphism on V(K^(e+1)) proves the other clause. Indices e=0 use
   K and K², both covered by hthick. Checked zero module, empty X, K=0, K=top, I=0 and
   I=top: there is no extra nonemptiness or reduced-support assumption. Independent
   LeanFinder queries for quotient annihilation and fully faithful completion lifting found
   only ring-module completion results; source searches for ideal powers, kernels,
   annihilation and quotient maps found the existing private helpers used to close support.
4. **Route and pruning:** Verified the canonical quotient-interchange argument in the
   adic proof and the `ofOpSequence` assembly in the original proof. α, θ and hθ are
   unused because the preserved conclusion imposes no equation on δ; δ=0 is legitimate
   for this data statement. The original proof dependency
   `lem-weil-pbc-closed-immersion-coherent-equivalence` is no longer a direct application,
   but remains required through supported algebraization and the residual transition step;
   no existing node or whole module is globally pruned. The two removed direct Mathlib
   imports are recorded above. Read `dag/units/sk-thm-p1.json`: its statement and all four
   realized step lists remain unchanged, and the route retains the closed-immersion and
   completion equivalences rather than bypassing a unit.
5. **DAG:** Read all four delivered node records against the corresponding signatures,
   proof bodies and docstrings. Their sources, creation/blueprint records and recorded
   searches are present. The item's proof and dependencies describe quotient formation,
   supported algebraization, adjacent lifting and sequence assembly. Updated the support
   node's proof, proof_deps and proof_origin to record the actual cokernel annihilation and
   reused power/product helpers. All new node signatures remain unchanged.

Changed the support theorem from sorry to a complete proof, added its two private proof
imports, updated its DAG proof route, and corrected the report's remaining-hole count from
2 to 1. The original theorem and the other correct Lean proofs were not rewritten.

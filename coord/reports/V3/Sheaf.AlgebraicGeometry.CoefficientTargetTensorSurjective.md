## What changed

Replaced the proof of `AlgebraicGeometry.Scheme.Modules.coefficientTarget_tensor_surjective`
with a reduction to two geometric intermediate statements, each in its own module.
The proof first places the base-ring span of supported unit generators in the range of c,
then uses finite generation over the intersection section ring and scalar transport to put
an arbitrary target section in that range. The existing theorem signature and public
imports are unchanged. The two new theorem imports are private.

The second reader restored the original signature's `letI`, used plain `let` only in the
proof body to remove its linter warning, removed redundant BigOperators imports from the
new modules, retained the geometric proof-plan imports privately, and repaired the nodes.
No definition, existing statement, target, or other group's module changes.

## Proved and sorry left

Closed one existing hole: `AlgebraicGeometry.Scheme.Modules.coefficientTarget_tensor_surjective`
(node `lem-pc-coefficient-target-tensor-surjective`). Its new body has no sorry.

Added two named holes:

- `AlgebraicGeometry.Scheme.Modules.coefficientTarget_section_generators`, in
  `Sheaf.AlgebraicGeometry.CoefficientTargetSectionGenerators`, node
  `lem-pc-coefficient-target-section-generators`.
- `AlgebraicGeometry.Scheme.Modules.coefficientTarget_scalar_span`, in
  `Sheaf.AlgebraicGeometry.CoefficientTargetScalarSpan`, node
  `lem-pc-coefficient-target-scalar-span`.

This is a decomposition, not a completed geometric proof: one hole closed, two added,
a local hole-count net of -1. Neither intermediate has been closed by the second reader.
The overall target still depends on sorryAx through these intermediates. No whole-library
or target-closure ledger improvement is claimed.

## No longer needed

Removed the target's direct private imports of
`Sheaf.AlgebraicGeometry.ModulePullbackAffineSections` and
`Sheaf.AlgebraicGeometry.FiniteAffineCechIntersectionBaseChange`; the section-generator
module retains both privately, and the scalar-span module retains the second privately.
Thus no module is claimed pruned from the target import closure.

Of the old target `proof_deps`, these five are no longer direct proof dependencies:

- `lem-pc-finite-affine-cech-intersection-base-change`
- `lem-weil-pbc-module-pullback-affine-sections`
- `lem-weil-pbc-affine-tilde-gamma-adjunction`
- `lem-weil-pbc-open-immersion-module-pullback-restriction`
- `lem-weil-pbc-conjugate-iso-unit-equation`

The generation plan retains affine pullback sections, intersection base change, and
adjoint/restriction unit compatibility. The affine tilde/Gamma argument is supplied inside
the existing affine section theorem, rather than reapplied by the target. The old
coefficient-comparison dependency remains direct because its support isomorphism and unit
generator are explicitly used. Removed redundant BigOperators imports from the new files;
notation and finite-sum infrastructure are already available through the statement imports.

## Where the brief, the DAG or earlier work was wrong

The worker changed the target signature from `letI` to `let` without declaring it; restored
byte for byte. Its target node still recorded the old geometric argument and none of the
new theorem applications. Its new nodes had vague non-self-contained statements, prose in
`lean.statement` instead of the Lean signature, copied searches unrelated to this work,
and identical proof plans for two distinct claims. Repaired all of these. The original
report omitted three removed direct DAG dependencies and did not identify the negative
hole-count net; corrected above.

## New nodes

`lem-pc-coefficient-target-section-generators` states only generation over C=Gamma(I,O),
where I=W intersect fprime inverse image B. It makes no claim that generation is over
R=Gamma(B,O), and mentions neither c nor its surjectivity. Its proof plan applies the
existing affine pullback section theorem and transports its unit via adjoint uniqueness
and the actual restriction isomorphism.

`lem-pc-coefficient-target-scalar-span` concerns only a single C-multiple of a unit section.
It asserts no generation of arbitrary module sections. Its proof uses the affine ring
identity C=R tensor_A D and the equation sending (r tensor d)*u(s) to r*k(d*s).
This needs no module-section surjectivity theorem. Both nodes carry self-contained
statements, verbatim Lean signatures, independent search records, source/docstring proofs,
and ancestry through the original item. No change record is required.

## Second reading by V3

1. Compared the delivered target module with the repository using `diff`. Restored the
   only accidental signature edit (`letI`); a separate exact text comparison confirms the
   existing signature is byte for byte unchanged. Public imports and the existing
   docstring are unchanged. Both extra modules are new declarations; there are no adapted
   modules or definition changes.

2. Read the full proof: hc places each k(s) in range(c), span_le extends this to the
   R-span, the generation lemma supplies a finite sum on the intersection, scalar_span
   puts each inverse-support image in range(c), and map_sum plus the support inverse law
   recovers y. No extra hypothesis or hidden witness construction occurs. The only
   remaining sorries are exactly the two named theorems above; no definition is holed and
   no forbidden axiom/unsafe/opaque/implementation declaration occurs. Compilation and
   explicit axiom checks are recorded below.

3. Read the two new statements against their docstrings, the actual definitions of
   coefficientPullbackGenerator and coefficientSupportIso, exists_tensorPullback_affine_sections,
   finiteAffineCech_intersection_baseChange, and the upstream PullbackTilde module.
   Read Stacks https://stacks.math.columbia.edu/tag/02KG (affine tensor computation),
   https://stacks.math.columbia.edu/tag/01IA (affine quasi-coherent reconstruction), and
   https://stacks.math.columbia.edu/tag/0097 (pullback composition).
   In the first claim hW gives I <= gprime inverse image V, V is isomorphic to affine Z,
   and affineness of W -> Tprime makes I affine over affine B. Thus the affine section
   theorem applies to F on X without adding a covering or flatness assumption. Transport
   of the adjunction unit gives precisely the displayed restricted generator.
   In the second claim the restricted cartesian square gives I=Z times_U B and hence
   C=R tensor_A D. Pullback-unit D-linearity gives u(d*s)=image(d)*u(s), while
   coefficientSupportIso_smul supplies R-linearity of the transported action. Finite tensor
   expansion proves the stated span membership. Neither statement alone moves the entire
   target into a new name: one generates over C, the other descends scalars on a single
   generator. Small cases checked on paper: Z empty, B empty, F zero, identity square,
   and a nonflat ring map. Zero sections admit the Fin 0 sum; a=0 gives zero span membership;
   for identity maps scalar transport is ordinary module multiplication. Tensor expansion
   never uses flatness. The added generation theorem really needs affineness and
   quasi-coherence; the scalar theorem is true with the stated, possibly redundant,
   quasi-coherence hypothesis.
   Repeated msearch with different wording: LeanFinder for generation by source sections,
   Loogle `Submodule.span, LinearMap.range`, and grep on Mathlib/AlgebraicGeometry/Modules.
   LeanSearch was attempted and unavailable. Also searched lean/Sheaf and lean/WeilConjectures
   for section generation, scalar span and pullback sections. The nearest spectral theorem
   is pullbackSpecΓEquiv_one_tmul, and the nearest affine-open theorem is the existing
   tensorPullback section comparison; both still require the chart/restriction/unit
   transports. coefficientTarget_generator_scalar concerns A-scalars, not arbitrary
   C-scalars. No duplicate or shortcut closing either geometric claim was found.

4. The final target proof is a short range-and-finite-sum argument. Both new lemmas are
   used, and the support/comparison import is required by the signature. Removed redundant
   new imports and kept geometric plan imports private. Enumerated every old proof_dep
   removed directly above; no import-closure module pruning is claimed. Read
   dag/units/sk-thm-picard-coherence.json: its realized statement and step lists are empty,
   and this reduction stays inside its affine coefficient calculation. It replaces no
   chapter or unit step; the unit record is untouched.

5. Rewrote the target proof/proof_deps/proof_origin to follow the actual four-step Lean
   argument, with the two new dependencies and coefficient support maps. Split the new
   nodes' previously identical plans into target-ring generation and scalar transport.
   Their dependency unions now match those plans. Filled full mathematical hypotheses,
   verbatim lean.statement, ancestry, and real new search records. Existing node changes
   are restricted to the permitted proof fields. No graph edge points back from a new
   node to the target in proof_deps or stmt_deps.

Changes made by second reading: restored signature, removed the proof-body letI warning,
removed redundant new imports, retained private geometric plan imports, repaired all three
node proof records and both new node statements/signature/search/ancestry records, and
corrected hole accounting and the pruning report. The working Lean argument was retained.

Validation: all three delivered modules compiled cleanly through lcompile.py --all.
A scratch copy with #print axioms for all three declarations compiled successfully; each
listed only propext, Classical.choice, Quot.sound, and sorryAx. Removed the scratch copy.
No Lean line exceeds 100 characters. All three lean.statement records exactly match their
Lean signatures, and the existing target node differs only in proof, proof_deps, proof_origin.

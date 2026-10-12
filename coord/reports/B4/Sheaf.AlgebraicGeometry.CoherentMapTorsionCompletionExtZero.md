## What changed

Closed `AlgebraicGeometry.coherentMap_torsion_completion_ext_zero` in
`Sheaf.AlgebraicGeometry.CoherentMapTorsionCompletionExtZero`, preserving its signature,
visibility and docstring. Added three proof-only imports: `CoherentArtinRees`,
`CoherentKernelCokernelLocallyNoetherian`, and `CoherentFiniteTypeLocallyNoetherian`,
all under `Sheaf.AlgebraicGeometry`.

The proof follows the existing node's Artin–Rees route. Coherent kernel closure and the
coherent/finite-type criterion establish quasi-coherence of the kernel. Choose exponent
`c+t` using the uniform Artin–Rees inclusion. Factor the kernel of the restricted quotient
map through the ideal product inclusion with Mathlib's `Abelian.monoLift`. Its sections
lie in the intersection supplied by Artin–Rees, hence vanish by the torsion hypothesis.
Cancel the kernel inclusion and apply `Abelian.mono_of_kernel_ι_eq_zero`.
The node's proof now records this explicit glue; its dependencies are unchanged.

Checked the source online because the local literature checkout is absent:
[Stacks 01YA](https://stacks.math.columbia.edu/tag/01YA),
[0889](https://stacks.math.columbia.edu/tag/0889), and
[088A](https://stacks.math.columbia.edu/tag/088A).
Ran LeanFinder, Loogle and grep searches through msearch, and searched both library roots
with rg. LeanFinder returned the affine `Ideal.exists_pow_inf_eq_pow_smul`; no exact
sheaf result was found. The existing sheaf Artin–Rees declaration supplies the needed fact.

Single-file lcompile passed without errors or warnings. All three added imports are used.
The positive-exponent arithmetic also covers c=0 and t=1. Zero kernel, empty scheme,
zero ideal and unit ideal impose no extra assumptions: the same Artin–Rees inclusion and
zero-object argument apply.

## Proved and sorry left

Closed one existing hole:
`AlgebraicGeometry.coherentMap_torsion_completion_ext_zero`
(node `lem-weil-pbc-coherent-map-torsion-completion-ext-zero`).
No sorry remains in the assigned module. No holes or new declarations were added.
This is a stage-3 proof from existing declarations, not a decomposition into new holes.
The proof uses the still-sorried existing dependency
`AlgebraicGeometry.Scheme.coherent_artin_rees`
(node `lem-weil-pbc-coherent-artin-rees`); this delivery does not prove that dependency.

## No longer needed

None. No import, dependency node or module was removed. The proof uses only the inclusion
clause of `coherent_artin_rees`, but still needs that theorem's module. The unit route is
unchanged and no unit-realizing node is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error found. The existing plan works using its stated
lemmas. The local `literature/stacks-project` sources are absent; their named Stacks tags
were read online. No statement or definition was changed, and no forced adaptation is needed.

## Second reading by B4

1. PASS: compared every delivered Lean module with the repository by diff. The only
   existing declaration has exactly the original signature, visibility and docstring.
   Only its proof and three private imports changed; no definition, public import,
   target statement or other module was changed. No change record is needed.
2. PASS: independently compiled the complete module with lcompile.py, without errors
   or warnings. Scanned the delivered source: no sorry, axiom, unsafe, opaque,
   implemented_by or extern, and no new definition or declaration. A scratch copy's
   #print axioms for coherentMap_torsion_completion_ext_zero reports only propext,
   Classical.choice, Quot.sound and sorryAx. The remaining sorryAx is from existing
   dependencies: coherent_artin_rees is still open, and the compiled coherent-kernel
   closure theorem also rests on sorryAx. The coherent/finite-type criterion reports
   only the three standard axioms. This closes the local hole, not the full axiom
   closure of the theorem.
3. PASS: there are no split-off statements, new holes or arbitrary witness definitions.
   The proof selects numerical bounds inside a theorem proof; it constructs no data
   definition from mere existence. Checked c=0, t=1, zero kernel, zero/unit ideal and
   empty scheme: c+t is positive, the subtraction identities hold, and the argument
   uses no nonemptiness or proper-ideal assumption.
4. PASS: read the proof top down and the existing dependency statements. Mathlib's
   monoLift supplies the actual factorization through the ideal product image; its
   composition identity puts each section in both ranges, so the Artin-Rees inclusion
   and zero source force the composite to vanish. Cancellation and the zero-kernel
   criterion then prove mono. Independent LeanFinder search for a power-annihilated
   subsheaf injecting into an ideal-power quotient found affine completion and
   ramification results, not a shorter sheaf theorem. Loogle for mono_of_kernel found
   the Mathlib criterion already used. Independent rg searches of both library roots
   and Mathlib confirmed no applicable duplicate. All three new private imports are
   used, all old proof_deps are still used, and No longer needed is complete. Read
   dag/units/sk-thm-p1.json realized: no unit statement or step is bypassed or altered.
5. PASS: compared the node JSON diff. Only proof and proof_origin changed, within the
   permitted stage-3 fields. The four proof_deps equal the union of the proof steps'
   uses and match the Lean argument. The statement, lean statement, source, unit and
   chapter remain unchanged. There are no new nodes to validate.

Second reading changed only this report: recorded the independent checks and clarified
that the coherent-kernel dependency also has transitive sorryAx. No mathematical,
proof, import or DAG repair was necessary. Rechecked the source argument against
[Stacks 01YA](https://stacks.math.columbia.edu/tag/01YA), with the uniqueness context in
[0889](https://stacks.math.columbia.edu/tag/0889) and
[088A](https://stacks.math.columbia.edu/tag/088A).

## What changed

Replaced the sorry in
`AlgebraicGeometry.Scheme.Modules.exists_finite_generatingSections_tensorPow_of_isAmple`
by a complete Lean reduction following EGA II, Proposition 4.5.5, p. 85.
The existing theorem's signature and all three public imports remain unchanged.
The second reader restored its original docstring; the reduction below implements
that same six-step argument.

Reused the proved `IsAmple.exists_finite_common_power_cover` from
`Sheaf.AlgebraicGeometry.AmpleFinitePowerCover`. Added a proved private helper,
`finiteType_tensor_invertible`, constructing local finite generating data for a tensor
product with an invertible module. It refines the generating cover by trivializing opens,
restricts the generators, and transports them through a tensor isomorphism. The source's
proved `isQuasicoherent_tensorObj` supplies quasi-coherence.

Split steps 3–5, the extension of local generators on a fixed affine section cover, into
`Sheaf.AlgebraicGeometry.AffineSectionCoverTwistGeneration`. The original theorem now
applies that strictly smaller result to each residue twist, takes a finite maximum,
checks the quotient bound by natural-number division, writes the degree as its quotient
and remainder, and transports finite generating families through the associator and
both tensor-power exponent isomorphisms. This is a decomposition, not a sorry-free
proof of global generation.

Updated the original DAG node's proof, proof_deps and proof_origin to this route, and
added the new intermediate node. No existing definitions, statements or visibility
were changed; no other group's modules were adapted.

Sources read: EGA II, Proposition 4.5.5, p. 85 (local copy of the PDF, converted in the
sandbox scratchpad), and [Stacks 01Q3](https://stacks.math.columbia.edu/tag/01Q3).
The EGA paragraph is the direct common-degree/local-generator/residue route used here.

Both delivered modules compile together with the required launcher compiler. The
compiler-guided checks included finite-type preservation, the natural/integer degree
bound, and preservation of finite generating indices under the tensor isomorphism.

## Proved and sorry left

Closed the original module's sole hole:
`AlgebraicGeometry.Scheme.Modules.exists_finite_generatingSections_tensorPow_of_isAmple`
(node `lem-weil-pbc-coherent-twist-global-generation`). Its proof contains no sorry.
Also proved the private helper `finiteType_tensor_invertible`, with no new hole.

Added exactly one hole:
`AlgebraicGeometry.Scheme.Modules.exists_finite_generatingSections_tensorPow_of_affine_section_cover`
(node `lem-weil-pbc-affine-section-cover-twist-generation`, in
`Sheaf.AlgebraicGeometry.AffineSectionCoverTwistGeneration`). Its proof is `by sorry`,
with its source and complete natural-language proof in its docstring and node.

Accounting: one upper hole closed, one strictly smaller hole added; net zero holes.
The remaining lemma only handles powers of a fixed module with a specified degree-one
finite affine section cover. It does not select a common power from ampleness or handle
residue classes; those steps, together with preservation of finite type and the final
isomorphism transport, are proved in the original module.

Edge cases checked: empty schemes and empty finite section families give epi maps to
the zero sheaf; zero modules allow empty generating families; k=0 uses the structure
sheaf tensor unit, not a positive-power nonvanishing identity. The common-power cover
lemma supplies m>0 even on an empty scheme, so division by m and Fin m are valid.
The lower bound d₀ is the nonnegative integer mB, a permitted witness of the original
integer existential. No arbitrary data is defined from an unproved existence theorem.

## No longer needed

Removed the direct proof import `Sheaf.Paper.NonvanishingSectionTrivializes`. Its node
`lem-weil-pbc-nonvanishing-section-trivializes` is no longer a direct dependency of
this theorem or of the new intermediate theorem: on the zero-locus complement the
proved `isFreeGenerator_app_one_of_le` and `isFreeGenerator_tensorPowSectionOne` in
`ClearDenominators` give the needed generator without that bridge theorem.
This does not claim the module leaves the whole targets' import closure.

Removed the direct imports `WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators`
and `Sheaf.AlgebraicGeometry.AffineFiniteTypeGeneratingSections` from the original
module, relocating the planned extension dependencies to the new intermediate module.
Their nodes, `lem-pc-section-clearing-denominators` and
`lem-weil-pbc-affine-finite-type-generating-sections`, remain needed there; neither is
globally pruned.

Removed the duplicate direct import
`WeilConjectures.AlgebraicGeometry.Modules.Invertible`; the statement's public import
`Sheaf.AlgebraicGeometry.Ample` already exposes it. The invertible-module and tensor
notions remain needed. Added the direct private import
`WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula` for the proved
quasi-coherence and local tensor-isomorphism lemmas.

No unit statement or realized unit proof step is bypassed. This node is below the
unit's realized steps and retains the EGA argument.

## Where the brief, the DAG or earlier work was wrong

The original DAG's step 6 labels locality of finite type elementary, but it needs
explicit cover refinement and transport of finite generators in the current API.
That glue is now proved, rather than left implicit. The common-power affine cover
already had a proved reusable theorem not listed among the original proof imports.

LeanSearch returned an Internal Server Error; this is recorded as unavailable, not as
a negative search result. LeanFinder, Loogle and local Mathlib grep were available and
found generating-family primitives but no affine-section-cover twisting theorem.

## New nodes

`lem-weil-pbc-affine-section-cover-twist-generation`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-affine-section-cover-twist-generation.json`:
fixed-cover eventual finite generation, exactly steps 3–5 of the original EGA proof.
It is stated in the new module
`lean/Sheaf/AlgebraicGeometry/AffineSectionCoverTwistGeneration.lean`, with one public
theorem and one sorry. Its proof uses the existing affine finite-generator and
clearing-denominators results and records the finite maximum, further multiplication,
and local-surjectivity argument in full. A whole-blueprint search found no equivalent
node; the projective Serre A node has a different projective-space hypothesis.
There are no change records, since no existing interface changed.
The second reader removed the new module's redundant public import of
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`: its remaining public
`ZeroLocus` import already exposes these signature notions.


## Second reading by E4

1. **Interfaces — pass.** Compared the original module with the repository by `diff`.
   The sole existing theorem's signature is byte for byte unchanged; all three existing
   public imports, visibility, namespace and universe are unchanged. No existing
   definition, instance, target or other group's module is edited. The additional
   helper is private and proved. Restored the original theorem docstring, avoiding an
   unnecessary edit of existing documentation. The new module has no repository version.

2. **Proof and axioms — pass as a decomposition.** Independently compiled both modules
   in dependency order through `lcompile.py --all`, with no errors or warnings. Read
   the local-cover refinement, restriction of generating families, trivialization
   transport, finite maximum, integer/natural bound and every tensor isomorphism.
   The private helper constructs local generators inside a theorem proof and has no
   hole. Scratch-copy `#print axioms` shows exactly `propext`, `Classical.choice` and
   `Quot.sound` for that helper. The upper theorem and new intermediate theorem show
   only these three plus `sorryAx`, as expected from the named open theorem. There is
   exactly one textual sorry in the delivered set, the whole proof of the named
   intermediate theorem; no forbidden declaration or hollow definition occurs.
   Scratch probes were removed before delivery. One upper hole closed and one lower
   hole added is net zero; this is not a completed proof of global generation.

3. **Split statement — pass.** Read EGA II 4.5.5, p. 85, in the sandbox source text,
   and checked https://stacks.math.columbia.edu/tag/01Q3 and
   https://stacks.math.columbia.edu/tag/01PW. The split fixes a degree-one finite
   affine section cover and proves only its extension/generation step. It omits
   both the common-power construction from ampleness and the residue-class argument,
   which the upper proof really performs. It is not a renamed restatement.
   Its docstring and node give a complete proof: finite affine generators, denominator
   clearing, maximum exponent, further multiplication, local trivialization, finite
   union and local epimorphism. Checked empty X, an empty cover (forcing X empty),
   zero G, empty generator families, and k=0. No arbitrary object is defined by
   choosing from an unproved existence theorem. Choosing bounds and generating
   families while proving an existential proposition creates no such definition.
   Repeated searches with new queries using LeanFinder, Loogle, launcher grep and
   `rg` on Mathlib and both source roots; recorded them in the new node. The upstream
   Serre A theorems require a field base and finite presentation and do not apply.
   Formalizing the remaining extension/local-epimorphism step is substantial work,
   not a small repair that could be closed in a few minutes.

4. **Route and pruning — pass.** The proof uses the already proved common-power
   cover and quasi-coherence results, and proves the finite-type and residue glue.
   New proof-only imports are plain `import`. Removed the new module's redundant
   public Quasicoherent import, already exposed by ZeroLocus; retained the imports
   supporting the remaining named proof plan. Every removed original proof dependency
   is accounted for: the nonvanishing bridge is replaced by proved free-generator
   lemmas; affine generators and clearing denominators move to the lower theorem.
   Read `dag/units/sk-thm-p1.json` including `realized`; this node is below its realized
   statement and steps. No realized unit step or chapter route is bypassed or edited.
   No claim is made that any module leaves the whole targets' import closure.

5. **Nodes — pass.** The existing node differs only in `proof`, `proof_deps` and
   `proof_origin`. Its steps match the actual upper proof; each dependency union
   matches its listed `uses`. The new node has its matching verbatim Lean signature,
   source, complete proof, statement/proof dependencies, searches, split status,
   creation data, blueprint origin, chapter, unit and Lean record. Its planned
   dependencies are the affine-generation, restriction and clearing-denominators
   tools plus the local-surjectivity criterion, not the discarded bridge theorem.

Changes in this reading: restored the existing docstring; removed one redundant
public import in the new module; added independent search evidence to the new node;
made the two relocated dependency ids explicit in the pruning report; appended this
review. No proof body, theorem signature, definition or hole count was changed.

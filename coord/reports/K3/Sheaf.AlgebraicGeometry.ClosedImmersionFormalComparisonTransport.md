## What changed

Replaced the sole sorry in
`AlgebraicGeometry.exists_closedImmersionFormalComparisonTransport` by a complete
Lean reduction with its signature and visibility unchanged. Constructed N from the
existing closed formal equivalence and a by the explicit composite of the given
source isomorphism, pushed alpha and inverse target comparison. Chose the actual
ideal J = (L ^ t).map j; its strict containment is proved using support_map,
support_pow, closedness and injectivity of the closed immersion.

Proved the proper-support conclusion from module_support_proper_over_base and the
existing closed formal equivalence/completion comparisons. The support theorem
supplies H ~= i_*F with F quasi-coherent and finite type. F is coherent on the
Noetherian closed subscheme T. Whiskering the completion comparison for i and
composing pushforwards identifies N with the supported formal image of the
completion of F under i followed by j. The proved helper annihilated_of_system_iso transfers annihilation using the
existing public formalModuleQuotient_factor at m=n=1. Its factorization through the
zero target ideal-module product makes the source inclusion zero after composition
with the isomorphism component. Cancel that component and apply
IsZero.of_mono_eq_zero. Removed the duplicate private multiplication_naturality and
idealModuleProduct_zero_of_mono declarations entirely; neither is restated or renamed.

Added proof-only imports of CoherentFiniteTypeLocallyNoetherian and the new
ClosedImmersionFormalKernelAnnihilation. Added one new statement module and its DAG
node, and updated the parent proof route. No public dependency import, definition,
existing signature or other group's module changed. No forced adaptations.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.exists_closedImmersionFormalComparisonTransport`
(node lem-weil-pbc-closed-immersion-formal-comparison-transport). No sorry remains in
the item's module. All three remaining private helpers are proved.

Added exactly one hole:
`AlgebraicGeometry.closedImmersion_formalKernel_annihilated`, in
Sheaf.AlgebraicGeometry.ClosedImmersionFormalKernelAnnihilation,
node lem-weil-pbc-closed-immersion-formal-kernel-annihilation.
This isolates the annihilation assertion for a supplied commuting pushforward
square. It neither constructs the comparison, proves strict ideal containment,
nor proves proper support. Thus this delivery is a decomposition: one upper hole
closed, one strictly smaller hole added, net zero before any closure pruning.
The existing closedImmersion_coherentFormal_equivalence is proved in the current
repository from its termwise and completion results. It is used, not duplicated
or modified; its transitive open dependencies remain outside this delivery.

The two delivered modules compile together through lcompile.py. The arbitrary
chosen equivalence determines N up to the specified underlying-system isomorphism;
no data are defined from an undetermined existential witness. The support module
F is likewise determined up to isomorphism by H and full faithfulness of the
closed pushforward. There are no new definitions and no hollow constructions.

## No longer needed

Removed the duplicate private helpers AlgebraicGeometry.multiplication_naturality
and AlgebraicGeometry.idealModuleProduct_zero_of_mono from the returned delivery.
The existing public AlgebraicGeometry.formalModuleQuotient_factor in the already
imported CoherentFormalModule supplies their needed consequence at exponent one.
No helper theorem with either duplicate statement remains.

Removed the direct proof import
Sheaf.AlgebraicGeometry.CoherentFormalModulesAbelian. The parent proof no longer
uses node lem-weil-pbc-coherent-formal-modules-abelian directly: the ambient Abelian
structure is already a hypothesis. That node remains a dependency in the new
kernel-annihilation proof plan, so this is not a claim that its module leaves the
whole targets' closure.

Removed parent proof dependency
lem-weil-pbc-closed-subset-proper-over-base-properties and its module
Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties: the parent proof uses
the support theorem's closed pushforward presentation and the existing completion
comparison instead. The support theorem itself still uses these properties; this
is only pruning of the parent's direct plan, not global closure pruning.

No further existing import or unit realization was bypassed. The parent is not a
node in dag/units/sk-thm-p1.json's realized lists; those lists and the unit route
are unchanged. No globally unreachable module is claimed.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated two private theorems of CoherentFormalModule.
Their private visibility explains why they could not be called, but does not
justify proving them again. This repair deletes both duplicates and uses the
existing public ideal-power factorization theorem instead. The parent DAG now
records lem-weil-pbc-formal-module-ideal-power-factor as a proof dependency. No
existing interface or other module needed adaptation. The old second reading
predated this repair and has been removed for a fresh independent reading.

The original plan provides no Lean interface for its categorical-kernel transport
and inverse-image annihilation step. The existing formal equivalence alone does
not expose preservation of ambient kernels, and evaluation does not preserve
formal kernels in general. The new lemma explicitly uses categorical kernel forks
and must be proved using the affine finite-completed-module description and local
exactness; it makes no termwise-kernel identification claim.

The remaining steps can be implemented without a new completion-annihilation hole:
the support theorem's pushforward presentation and existing completion comparisons
suffice. The strict ideal containment also follows directly from the supports of
actual ideal sheaves and needs no separate existence theorem for a lifted ideal.

blueprint_refs.py ancestor on the parent reports None because created.item is a
module name rather than a DAG id. Its existing blueprint.from record explicitly
names thm-weil-pbc-finite-etale-lifting and its via chain. The new node inherits that
record with the parent prepended, rather than inventing a different unit route.
Whole-blueprint searches for formal kernel annihilation and completion annihilation
closed immersion returned no matches.

The local literature/stacks-project/coherent.tex file is absent. Read the official
Stacks pages for Tags 088E, 087T, 087W and 087X. Those provide the original comparison,
closed coherent equivalence, affine completed-module equivalence, and categorical
kernel/local-exactness argument. LeanSearch returned an internal-server error and
is recorded as unavailable; LeanFinder returned adic-completion exactness and
ordinary kernel lemmas, not this formal transport. Loogle and Mathlib/source-root
rg searches found no existing matching theorem.

## New nodes

lem-weil-pbc-closed-immersion-formal-kernel-annihilation:
Sheaf.AlgebraicGeometry.ClosedImmersionFormalKernelAnnihilation contains the one
remaining public theorem, with its source and a full natural-language proof. Its
hypotheses supply an arbitrary commuting square, so it applies to targets other
than completions as well; its conclusion is only annihilation of the fixed kernel
by the concrete lifted ideal. The parent constructs the square and independently
proves all other conclusion clauses.

Edge cases checked mathematically: t=0 means the unit ideal kills k.pt, hence its
kernel is zero, and the lifted ideal is top. For L=bottom and t>0 the conclusion
reduces to the defining ideal killing a categorical kernel between objects
supported on Z. For j=id it reduces to invariance of kernel annihilation under
isomorphisms. Empty Z makes G, D and their kernels zero; all terms are zero. No
properness, finite-type map to a base, or nonempty complement is needed for the
new lemma. The original theorem retains its positive exponent and nonempty-open
hypotheses, which are used to prove strict containment.

No change record is needed: existing interfaces are unchanged.

## Second reading by K3

1. Interface preservation: compared the complete parent module with the repository
version by diff and checked the original theorem signature byte for byte. It is
identical, including visibility, every hypothesis and all three conclusion clauses.
There are no definition changes, forced adaptations or changed target statements.
The only new public interface is the separately named kernel-annihilation lemma.
Verdict: pass.

2. Proof and trust: both modules compiled cleanly with lcompile.py in import order.
Read all three private helper proofs: exponent-one formalModuleQuotient_factor
transfers zero ideal products along each system isomorphism; completion comparisons
and pushforward composition supply the supported target; support_map, support_pow,
closedness and injectivity give strict containment. The explicit comparison map
satisfies the required square by cancellation. There is exactly one textual sorry,
the whole proof of closedImmersion_formalKernel_annihilated; no prohibited trust
construct or hollow definition occurs. Scratch #print axioms checks and the delivery
probe verify the permitted trust basis, with sorryAx only for open dependencies.
Choosing E(D) is legitimate: eta specifies its underlying system up to isomorphism.
The support witness is used only inside this existential proof, and its F is
specified up to isomorphism by the supplied pushforward comparison.
Verdict: pass as a decomposition, not a net proof gain.

3. Split statement: read the new Lean signature, docstring and node against Stacks
087T, 087W, 087X and 088E. Locally the completed modules for the pushed systems have
the same underlying limit and restricted scalar action. Their categorical kernel
is the same finite module; reductions commute with restriction of scalars because
the extended adic ideal has the same action. This identifies the pushed limiting
fork with the ambient formal kernel. The inverse-image ideal acts through L^t,
so the given termwise annihilation passes to that kernel. This does not assume
that evaluation preserves kernels. Checked t=0 (zero kernel), L=bottom with t>0
(defining-ideal annihilation), j=id (isomorphism invariance), empty Z, and Q=top
(zero systems). The lemma omits completion, strict containment and proper support,
so it is a strict part of the original argument, not a renamed restatement.
Independent LeanFinder search for restriction of scalars preserving kernels of
adic systems returned completion scalar structures only. Loogle queries for
kernel-preservation and kernel isomorphisms could not resolve those identifiers;
no absence claim is based on that service. Independent rg searches for preserved
kernels, annihilated kernels and supported kernels in both Lean roots found the
existing affine/local-exactness and annihilated-iff results, but none states this
closed transport for the given fork, fixed exponent and commuting square.
Closing the new hole requires the affine/local comparisons, beyond a short repair.
Verdict: pass; one true, needed, strictly smaller open statement.

4. Route and pruning: the parent uses existing completion comparisons, support
presentation and public ideal-power factorization rather than restating private
lemmas. Proof imports are plain imports; public imports provide signature notions.
Both old proof_deps absent from the new parent plan are explicitly covered in
No longer needed: coherent-formal-modules-abelian and closed-subset-proper-over-base-
properties. Their transitive uses are correctly distinguished from global pruning.
The parent is absent from sk-thm-p1.json's realized lists; no unit statement, step
or realization is removed, and the inherited blueprint route is preserved.
Verdict: pass; no globally pruned module claimed.

5. Records: checked the parent node's four proof steps against the map construction,
strict-ideal helper, new kernel lemma and proper-support helper. proof_deps is their
union and proof_origin records this route. Only proof, proof_deps and proof_origin
of the existing node differ. The new node has the matching Lean signature, source,
self-contained statement, proof steps, dependency union, search records, creation
record, inherited ancestor/via, chapter/unit and lean_audit fields. Its public
sorry has the source and full natural-language argument in its docstring.
Verdict: pass.

Second-reading changes: corrected the stale report assertion that the closed formal
equivalence itself still has a sorry; it now has a proof from existing termwise and
completion declarations. Added this independent review. The Lean proofs and node
records required no repair. Net holes: one closed and one added; global pruning none.

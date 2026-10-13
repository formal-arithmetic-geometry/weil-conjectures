## What changed

The signature of CategoryTheory.Functor.exists_rhom_hom_derived_roof is unchanged.
Its proof now uses a natural additive map normalized on injective complexes, proves
bijectivity on every D+ object by transporting along an injective representative, and
obtains the arbitrary-resolution roof by naturality and explicit cancellation of the
quotient comparison isomorphisms. Two proof-only imports were added.

RHomInjectiveCocycleBijective is fully proved from Mathlib. Its proof identifies
Hom-complex classes with derived Hom via K-injectivity, and identifies their boundaries
with the range subgroup in the concrete homology quotient. The only remaining task is
the construction and naturality of the additive map in RHomNaturalCocycleMap.

## Proved and sorry left

Closed: CategoryTheory.Functor.exists_rhom_hom_derived_roof (the original one hole),
by reduction to the strictly smaller additive-map construction.
Added and fully proved: CategoryTheory.Functor.rhom_injective_cocycle_map_bijective,
node lem-sc-p1-rhom-injective-cocycle-bijective. Its module has no sorry.
Added hole: CategoryTheory.Functor.exists_rhom_natural_cocycle_map,
node lem-sc-p1-rhom-natural-cocycle-map. This asks only for additive homomorphisms
with injective cocycle normalization, not bijections or arbitrary-resolution roofs.
The delivery is a decomposition, with one upper hole closed and one lower hole added;
it does not claim a net decrease in sorry count or an axiom-free upper theorem.

## No longer needed

No existing import is removed: each supports the unchanged public statement or its
proof. In both new helper modules, Yoneda.Limits is replaced by Yoneda.Basic: the
statements require the additive coyoneda functor, not its limit preservation. No original proof dependency is globally pruned: the K-injective bijection
and bounded-below K-injectivity are used in the proved local lemma. At the parent
node, lem-weil-pbc-bounded-below-injectives-kinjective and
lem-weil-pbc-kinjective-hom-derived are no longer direct proof dependencies: both
are replaced by lem-sc-p1-rhom-injective-cocycle-bijective. They remain dependencies
of that local lemma and the natural-map construction, so neither is globally pruned. No separate lemma for arbitrary-resolution
independence is needed: naturality computes every roof directly. No declaration or
module was added for that step. No unit realization is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement discrepancy was found. The original DAG has ingredients but no Lean
interface for the natural additive cocycle map. The new node isolates that missing
construction, while the local quotient bijection and resolution transport are proved.
Mathlib searches used LeanSearch (unavailable: Internal Server Error), leanfinder,
loogle, and grep; local sources for the returned
HomComplex, SmallShiftedHom, ShortComplex.Ab, and PlusSingle declarations were read.
Stacks Tags 06XR (1) and 070I were read on their official pages because the cited
literature checkout is absent on this machine. The new local assertion was checked
without a degree restriction: negative n and the zero complex use the same kernel and
quotient arguments. All existing signatures and public imports are preserved, and
there are no forced adaptations or interface changes.

## New nodes

lem-sc-p1-rhom-natural-cocycle-map: natural additive homomorphisms with the formula
only on an injective complex. One new module and one remaining named sorry, with its
source and full construction in the docstring. It deliberately does not assume or
assert bijectivity, roofs for arbitrary resolutions, or shift compatibility.

lem-sc-p1-rhom-injective-cocycle-bijective: a fixed-complex local assertion that a
homomorphism with the cocycle normalization is bijective. Fully proved. It assumes
neither a natural family nor any resolution-independence statement. Together with
naturality and injective representability, it proves bijectivity on every D+ object.

No change record is needed: no existing interface changed.

## Second reading by N3

1. Interface preservation: compared RHomDerivedRoof.lean with the repository using
   diff. The sole existing theorem has exactly the same signature, including both
   derived-category universes, all integer degrees, every resolution choice, the
   supplied boundedness and degreewise injectivity, and every comparison isomorphism.
   Its docstring and all existing public imports are unchanged. Only two private
   imports and its proof body were added. There are no definitions or adaptations.
   Verdict: pass; no interface change record is needed.

2. Kernel and holes: compiled all three modules in import order with lcompile.py,
   without errors or warnings. Scratch copies with #print axioms showed
   rhom_injective_cocycle_map_bijective uses exactly propext, Classical.choice,
   Quot.sound. The roof theorem and exists_rhom_natural_cocycle_map additionally
   use sorryAx, as reported. The latter is the only sorry in the delivery and is
   an entire named theorem with its source, construction proof, and matching node.
   No axiom declaration, unsafe, opaque, extern, implemented_by, or hollow data
   definition occurs. The representative choices in the roof proof come from
   proved library results; the unproved additive map is used only inside a theorem.
   Verdict: pass as a decomposition, not an axiom-free proof of the roof theorem.

3. New statements: read Stacks Tag 06XR (1), the injective-resolution computation,
   and Tag 070I, the K-injective localization bijection, on their official pages:
   https://stacks.math.columbia.edu/tag/06XR and
   https://stacks.math.columbia.edu/tag/070I. Read HomComplexSingle's constructors,
   subtraction formula, and boundary criterion, DerivedCategory.KInjective's
   equivOfIsKInjective, ShortComplex.Ab's kernel/range quotient, and PlusSingle's
   invertible-unit computation. For the local theorem, E is the localization
   bijection and T is a surjection onto the derived cohomology source. Equal beta
   values imply equal E classes; the boundary criterion puts x-y in the precise
   range subgroup killed by homologyπ. This proves injectivity, while cocycle
   representatives and E prove surjectivity. For the open natural-map theorem,
   boundaries map to zero; chain-map postcomposition respects this quotient;
   the fully faithful injective-object equivalence transports that map, and its
   counit together with the derived unit proves naturality and normalization.
   Read the actual injectiveObjectEquivalence and
   rightDerivedFunctorPlusIsoInjectiveObject construction in the upstream library.
   Checked n negative, M zero, I zero, and a two-term complex with identity
   differential: the same kernel/range argument applies, and an acyclic injective
   complex gives zero on both sides. No n>=0 or nonzero assumption is introduced.
   Independent searches used leanfinder for natural transformations from derived
   Hom cohomology, loogle for CohomologyClass.toHom, and grep for homologyAddEquiv
   and derived/coyoneda comparisons. Also searched lean/Sheaf, lean/WeilConjectures,
   and the upstream CategoryTheory sources. Returned comparisons concern fixed
   complexes or object resolutions; none supplies the all-D+ natural normalized
   map. The proved local theorem supplies a real quotient/boundary argument;
   the remaining map assertion omits bijectivity and arbitrary-resolution roofs,
   so it is strictly part of the original argument. Verdict: pass.

4. Route and pruning: read the original proof dependencies and the unit
   sk-thm-picard-duality, whose realized statement and step lists are empty.
   No unit realization is replaced. The roof proof transports local bijectivity
   along e and e.inv by naturality, then expands the fully faithful inclusion's
   image of the resolution inverse and cancels the shifted comparison pair.
   This computes the formula for every supplied resolution without another hole.
   All old dependencies remain directly or through the new helper nodes; the
   two removed direct dependencies are explicitly named under No longer needed.
   The original limits import is required by rightDerivedComplexWithResolution's
   finite-limits instance. In the new modules only additive coyoneda is needed,
   so replaced Yoneda.Limits with Yoneda.Basic and recompiled the set.
   Verdict: pass; no globally pruned module, one smaller open construction.

5. DAG agreement: checked each new node's id, source, self-contained statement,
   statement dependencies, proof steps and their union proof_deps, proof_origin,
   recorded searches, created/group/item data, blueprint record, chapter/unit,
   and verbatim Lean signature. The original node changes only proof,
   proof_deps, and proof_origin. Its first step now cites both helpers and the
   injective representative; its second describes the actual map_preimage and
   cancellation calculation. The new local node's steps match E and T and the
   concrete boundary argument; the open construction node matches its docstring.
   Verdict: pass.

Changes by this second reader: replaced the unnecessary Yoneda.Limits public
import with Yoneda.Basic in both new modules, explicitly listed the two old
parent proof dependencies that are now indirect, and added this independent
review. No proof, signature, definition, node statement, or unit route was changed.

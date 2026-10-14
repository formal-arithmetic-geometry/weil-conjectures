## What changed

Replaced the sorry in `RingTheory.dvr_tame_tensor_factor_formallyUnramified` with a
compiling proof from two strictly smaller local conclusions of Abhyankar base
change. The existing signature, visibility, public imports, and definitions stay
identical. Added proof imports of `Mathlib.RingTheory.Unramified.LocalRing`,
`Sheaf.RingTheory.DvrTameTensorFactorMaximalIdeal`, and
`Sheaf.RingTheory.DvrTameTensorFactorResidueSeparable`.

The proof first obtains the maximal-ideal equality, derives that the canonical
map is local, obtains separability of its residue-field algebra, installs the
assumed finite module structure, derives essential finite type after localization,
and applies `Algebra.FormallyUnramified.of_map_maximalIdeal`.
The node's route now records these steps. Each new theorem has its own module,
node, source, and complete natural-language proof. There are no new definitions,
changed statements, or forced adaptations.

All three delivered modules compile without warnings using `lcompile.py --all`.
The source was checked online at Stacks Tags 0BRM and 09E7; the local criterion
was read in Mathlib. The unit's trait/tame-normalization route is retained.

## Proved and sorry left

Closed the single original hole in
`RingTheory.dvr_tame_tensor_factor_formallyUnramified`
(node `lem-sbc-dvr-tame-tensor-factor-unramified`). No sorry remains in the item.

Added exactly two holes:

- `RingTheory.dvr_tame_tensor_factor_map_maximalIdeal`, node
  `lem-sbc-dvr-tame-tensor-factor-maximal-ideal`.
- `RingTheory.dvr_tame_tensor_factor_residue_isSeparable`, node
  `lem-sbc-dvr-tame-tensor-factor-residue-separable`.

This is a decomposition, not an axiom-free proof of the original mathematical
result. Neither new theorem states formal unramifiedness: one states only the
maximal-ideal identity, the other only residue separability. Both are needed by
the real local-criterion proof. Hole accounting: one closed, two added, net -1.
The explicit local-hom parameter of the residue theorem supplies the canonical
Lean residue algebra; the main proof constructs it from the other invariant.

Edge cases: n=0 is excluded. When n=1 the inputs force the original local
extensions to be unramified; both conclusions hold. Trivial E/Frac(B) and A=B
specialize to the expected normalization statements. An empty family of Q over
the closed point gives vacuous conclusions. A finite faithful DVR base extension
may be inseparable on fraction fields; 0BRM permits any finite base extension,
so no separability assumption on Frac(A)/Frac(B) was silently added.

## No longer needed

None. No existing imports, nodes, or modules are pruned. The original direct
proof dependency `lem-weil-pbc-noetherian-normal-separable-integral-closure-finite`
is removed from the item's direct `proof_deps` and is still needed inside both
new local-invariant nodes; it was relocated, not pruned from the dependency
closure. Its recorded Mathlib declaration supplies finiteness directly. It matches `IsIntegralClosure.finite` in Mathlib.

## Where the brief, the DAG or earlier work was wrong

The original plan's Abhyankar step had no named Lean dependency. Mathlib's local
unramified criterion supplies the final step but does not provide that Abhyankar
calculation. The two new modules make its separate required conclusions explicit.
No mathematical error or statement dispute was found. No changes to existing
interfaces are needed.

## New nodes

`lem-sbc-dvr-tame-tensor-factor-maximal-ideal` states the index-one consequence as
an equality of extended local maximal ideals. Its module is
`Sheaf.RingTheory.DvrTameTensorFactorMaximalIdeal`.

`lem-sbc-dvr-tame-tensor-factor-residue-separable` states only separability of the
canonical residue-field extension. Its module is
`Sheaf.RingTheory.DvrTameTensorFactorResidueSeparable`.

Both inherit chapter `sec-smooth-base-change` and unit `sk-prop-input-spreading`,
record all three required kinds of Mathlib search, and retain the separable
normalization-finiteness dependency. No change records were required.


## Second reading by S1

1. **Interfaces: pass.** Read the three delivered Lean files and diffed the
   existing module against the repository. The sole existing declaration,
   `RingTheory.dvr_tame_tensor_factor_formallyUnramified`, has a byte-identical
   signature and docstring. Only its proof and three plain proof imports changed.
   No existing public import, definition, target, or other module is altered.
   No relevant change record was found in the repository.

2. **Proof and trust: pass as a decomposition.** Recompiled all three modules
   with `lcompile.py --all`: no errors or warnings. A scratch copy of the item
   with `#print axioms` for all three declarations reports only `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. The latter remains because
   exactly the two reported new theorems have `:= by sorry`. There are no new
   definitions, arbitrary witnesses chosen from existence theorems, or forbidden
   declarations. The scratch copy was removed before delivery. The final proof
   uses maximal-ideal equality to install the local map, installs canonical
   residue separability, derives essential finite type from the finite module
   hypothesis and localization, and applies the actual Mathlib criterion.

3. **New statements: pass.** Read Stacks Tags
   [032L](https://stacks.math.columbia.edu/tag/032L),
   [0BRM](https://stacks.math.columbia.edu/tag/0BRM), and
   [09E7](https://stacks.math.columbia.edu/tag/09E7).
   Finite faithfulness embeds B in A; normality and integrality identify A with
   its fraction-field normalization. The displayed ideal identity supplies
   base ramification index n. The finite separable normalization C has DVR
   localizations; its residue degrees divide the invertible n, so their
   inseparable parts are trivial, and their ramification indices are prime to
   the residue characteristic. Thus 0BRM applies even when Frac(A)/Frac(B) is
   inseparable. Its adic smoothness conclusion gives each separate invariant
   by 09E7. The quotient F is a generic field factor since E embeds in F and
   incomparability makes A -> F injective. Integrality transitivity identifies
   its A-normalization with the required B-normalization; localization selects
   the prime in 0BRM. The finite S/A assumption ensures the needed local DVR.
   The residue theorem's explicit local-hom proof only supplies the canonical
   residue algebra, and proof irrelevance makes the conclusion independent of
   that proof. Neither theorem asserts the whole original conclusion.
   Checked n=1 (both e and f are one), E=Frac(B), the identity base extension,
   residue characteristic zero, and a tame root extension of index dividing n.
   The case n=0 is excluded by the existing hypothesis. Both new statements
   have their own source, full docstring argument, and matching node.

   Independently searched LeanFinder for "normalization of tensor product of
   tamely ramified DVR extensions has ramification index one and separable
   residue field", Loogle for `Algebra.IsSeparable, IsLocalRing.ResidueField`,
   and rg over project RingTheory and Mathlib ramification/unramified sources.
   Results provide unramified criteria, tower formulas, and consequences of
   already-unramified maps; none establishes these tame normalized-factor
   invariants. The canonical residue-separability instance requires formal
   unramifiedness and would be circular here. Neither remaining hole has a
   short closure from the located APIs.

4. **Route and pruning: pass.** The item uses Mathlib's
   `Algebra.FormallyUnramified.of_map_maximalIdeal` for the final local step;
   each new theorem supplies precisely one of its two mathematical inputs.
   All three proof imports are used and their visibility is correct. Existing
   public imports support the unchanged interface. The former direct
   normalization-finiteness dependency is explicitly accounted for above: it
   moved to both new nodes, rather than leaving the closure. No module is
   pruned. Read `dag/units/sk-prop-input-spreading.json`: the trait/tame
   normalization route remains, and no realized statement or step is bypassed.

5. **DAG: pass.** Parsed all three node files and compared every recorded Lean
   statement verbatim with its declaration signature. Each `proof_deps` equals
   the union of its proof steps' `uses`. The existing node changes only
   `proof`, `proof_deps`, and `proof_origin`; these describe the actual local
   criterion proof. Both new nodes carry the required source, searches,
   provenance, Lean attachment, chapter, unit, and blueprint ancestry.

**Changes made by this reader:** clarified the removed direct proof dependency
in `## No longer needed` and added this independent reading. No repair of the
Lean proof, statements, imports, or nodes was required. Hole accounting remains
one original hole closed and two strictly smaller holes added (net -1), a
permitted decomposition rather than an axiom-free proof of Abhyankar's lemma.

## What changed

Replaced the sorry in AlgebraicGeometry.smoothProper_tensor_perfect_case_core with a
categorical reduction following Stacks Tag 0A9T. No existing signature or visibility changes.
The proof obtains both exact pairings from perfect_tensor_hom_duality on Y, maps the pairing
by the supplied monoidal pullback, and conjugates its tensorator under composite adjunctions.
Mathlib proves that conjugation preserves isomorphisms. The private projection_isIso helper
uses the normalization identity below to prove that the canonical projection map is invertible.
Its inverse supplies the requested pf with the specified inverse equation by reflexivity.

For every quasi-coherent E the proof explicitly composes nine Hom equivalences (including
full-subcategory inclusion equivalences). The chain passes through tensor duality on X,
the restricted direct-image adjunction, the projection comparison for the dual, tensor
duality on Y, the right unitor, and the right adjunction again. The second coherence identity
identifies this chain with postcomposition by the required mate. Yoneda then proves IsIso.

New proof-only imports: Sheaf.CategoryTheory.MonoidalProjectionConjugate,
Sheaf.AlgebraicGeometry.PerfectRightAdjointTensorHomComparison, Mathlib.CategoryTheory.Yoneda.
Compiled the entire three-module delivery in import order. Intermediate experiments remain
outside lean/ in scratchpad and are not delivered.

## Proved and sorry left

Closed: AlgebraicGeometry.smoothProper_tensor_perfect_case_core
(lem-sc-smooth-proper-tensor-perfect-case-core), from the proved monoidal projection normalization, one new coherence identity
and the existing perfect_tensor_hom_duality. The item has no remaining sorry.
This is a decomposition, not a completed proof of the entire import closure: one hole closed,
one hole added, net zero. The private projection_isIso is fully proved.

Additionally proved: CategoryTheory.monoidal_projection_conjugate
(lem-sc-monoidal-projection-conjugate); this new lemma has no sorry.

Added holes:
- AlgebraicGeometry.perfect_rightAdjoint_tensor_hom_comparison
  (lem-sc-perfect-right-adjoint-tensor-hom-comparison): equality of the explicitly composed
  Hom chain with postcomposition by the specified mate.

The remaining hole is in its own new module with exactly `:= by sorry`, a source
and a proof in words. The normalization module is now fully proved.
Neither asserts existence of the original pf or invertibility of the original mate.
The first is an equality in arbitrary monoidal categories; the second assumes projection
isomorphisms already constructed and proves an equality of maps, not their invertibility.
No new definition, arbitrary chosen data, or axiom was added.

## No longer needed

Removed import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections.
Its projection theorem only concerns invertible sheaves and their higher direct images;
it supplies neither the derived canonical comparison nor the mate calculation here.
The declaration recorded for lem-pc-projection-formula in that module is not used in this
proof; dualizability and monoidal conjugation replace it. Whether the module is still
reachable through other targets is for the maintainer's import-closure calculation.
All public imports are retained to preserve the existing exposed interface.
PerfectTensorHomDuality remains necessary. The unit realization is empty, so no realized
unit statement or step is bypassed. The original core node has no proof_deps to prune.

## Where the brief, the DAG or earlier work was wrong

The core node originally had no actual numbered proof plan or dependencies, just a statement
that the geometric details remained as a hole. The parent docstring cites a projection
formula declaration in Sections that only states the invertible-sheaf higher-direct-image
case. It cannot be directly applied to the derived perfect-complex statement.

The source file literature/stacks-project/duality.tex is absent on this machine. Read the
source at https://stacks.math.columbia.edu/tag/0A9T instead. It proves the result by exactly
the tensor-Hom chain used here. No source-free intermediate theory is introduced.

LeanSearch was attempted for projection formula dualizable object monoidal adjunction,
but the service returned Internal Server Error (recorded unavailable).
Searches: leanfinder for projection formula for monoidal left adjoint at dualizable object;
loogle for CategoryTheory.ExactPairing; msearch grep for projectionFormula/projection_formula;
rg in both library roots and Mathlib's monoidal and adjunction files. These locate tensor
adjunctions, mapped exact pairings, and conjugation but not either normalization equality.

Edge checks of new statements: both are purely formal adjunction identities, hence apply
also to zero objects and empty schemes. Identity functors give the ordinary dual-pair
triangle identities and the right unitor. Arbitrary adjunction choices are explicitly
included in each formula; no chosen geometric normalization is silently assumed. The
second theorem requires canonical inverse equations for both projection isomorphisms,
so an unrelated isomorphism cannot satisfy its hypotheses. No open-derived-category
instance on X is needed: the source exact pairing is mapped categorically from Y.

## New nodes

lem-sc-monoidal-projection-conjugate: general monoidal dual-pair conjugation normalization,
in Sheaf.CategoryTheory.MonoidalProjectionConjugate. Source: Stacks 0B54 and 0A9T; fully proved in the second reading.

lem-sc-perfect-right-adjoint-tensor-hom-comparison: counit/naturality equality for the
Hom chain in Tag 0A9T, in Sheaf.AlgebraicGeometry.PerfectRightAdjointTensorHomComparison.
Its assumptions specify both canonical projection inverses and quasi-coherence lifts.

The existing core node's proof, proof_deps and proof_origin now describe the actual Lean
reduction. No change records or forced adaptations are needed.

## Earlier second reading (a previous round; superseded)

The core theorem's signature is unchanged and its proof compiles from the two explicitly
imported coherence statements and perfect tensor-Hom duality. The two added statements are
strictly smaller categorical equalities, each matching its node and carrying no arbitrary
data. The unit route through Picard duality is retained; no realized unit step is bypassed.

## Second reading by Y2

1. Compared the delivered core module with the repository by diff and checked the entire
   declaration header through `:= by`: byte-for-byte unchanged, including the duplicated
   supplied monoidal structures and pullback adjunctions. No definitions or existing
   visibility were changed. The only new top-level helper in that module is private.
   Verdict: the exact original assertion is proved conditionally on the listed dependencies.
2. Compiled all three modules in import order using lcompile.py. Inspected every delivered
   declaration: no forbidden declarations or hollow definitions. The core proof constructs
   pfK as the inverse of a specified morphism using asIso, so its required inverse equality
   is rfl. The dual from perfect_tensor_hom_duality is determined up to isomorphism by its
   exact pairing, and is eliminated inside a proof; no arbitrary witness is made into a
   data definition. Repaired and fully proved monoidal_projection_conjugate: a local
   pairing_map calculation expands the mapped evaluation, uses monoidal coherence, and
   then transposition under the composite adjunction reduces the desired equality to
   the counit identity. The delivery's axiom probe checks all declarations; explicit
   #print axioms checks are also recorded below. One named new sorry remains, exactly
   perfect_rightAdjoint_tensor_hom_comparison. Verdict: valid decomposition, not an
   unconditional closure proof.
3. Read Stacks Tags 0A9T, 08EU and 0B54 online (the source checkout is absent).
   The remaining equality is the compatibility calculation for the displayed Hom chain
   in 0A9T, not an assertion of invertibility or existence. Its hypotheses explicitly
   retain both adjunctions, the chosen strong monoidal structure, the lifted tensor
   objects, and canonical inverse equations for pfK and pfD. For identity functors and
   the tensor unit it is the ordinary adjunction counit identity; rescaling an identity
   adjunction rescales its Hom equivalence and counit inversely, so does not invalidate
   it. The mapped pairing must be precisely ExactPairing.map, as the statement requires.
   Zero objects and empty schemes add no exceptions. The docstring gives the transpose,
   naturality, normalization and triangle-identity calculation needed to prove it.
   Independent msearch queries used different words: strong monoidal preservation of
   duality and its canonical projection mate; counit compatibility with tensor duality;
   Loogle conjugateEquiv and tensorLeftHomEquiv_naturality; grep for mapped Hom
   equivalences and conjugate tensor maps. Read the resulting Mathlib declarations and
   searched lean/ and the upstream categorical library. No existing theorem supplies
   the remaining full comparison equality. Verdict: true, needed and strictly smaller.
4. The first route is categorical: exact pairings, mapped duality, Mathlib conjugation
   preserving isomorphisms, and Yoneda. The explicit nine-equivalence chain uses the
   remaining coherence lemma only to identify its map. Sections supplies an invertible-
   sheaf higher-direct-image result, not this derived comparison, and is removed.
   The old core node has empty proof_deps, so there are no omitted old dependency nodes
   to list. Inspected dag/units/sk-thm-picard-duality.json: its realized statement and
   step lists are empty; this change replaces no realized unit step. Blueprint-wide
   searches for projection formula and tensor-Hom found projection results, but no
   equality of this Hom chain or dual-pair conjugate normalization. The existing
   exposed imports are retained; all new imports in the core are proof-only. Both
   new modules publicly import only modules needed to express their own signatures.
   Verdict: route preserved and unused proof dependency pruned.
5. Matched the three node records against the Lean. Core proof_deps names precisely
   perfect_tensor_hom_duality and the two comparison declarations applied in the proof.
   Replaced the two new nodes' lean.statement fields with the exact source signatures
   (one previously contained literal Unicode escapes). Updated the normalization's
   proof to its checked argument, corrected its misattributed projection source tag,
   and removed the remaining comparison node's spurious dependency on the normalization:
   its written proof sketch expands the canonical projection formulas directly and
   its module does not use that theorem. Marked the failed LeanSearch as unavailable
   and added empty same_as search-result fields. Verdict: records now follow the code.

Second reading changed: closed monoidal_projection_conjugate by repairing the first
worker's nearly complete scratch calculation (unfold tensorLeft before rewriting;
reassociate before the final definitional equality), kept the mapped-pairing helper
local to that theorem, corrected source and node metadata, and updated hole accounting.
The delivered core closes one of its one original holes and adds one lower hole; net
zero in this delivery before the maintainer's pinned import-closure ledger calculation.

Explicit axiom checks (scratch copies, removed before delivery):
- CategoryTheory.monoidal_projection_conjugate: propext, Classical.choice, Quot.sound only.
- AlgebraicGeometry.perfect_rightAdjoint_tensor_hom_comparison and
  AlgebraicGeometry.smoothProper_tensor_perfect_case_core: those three plus sorryAx,
  as expected for the named remaining hole and open imported dependencies.
The new nodes' informal statements were also made self-contained: monoidal categories,
exact pairings and adjunctions are introduced explicitly, and the geometric node cites
its derived-category, pullback, direct-image and tensor definition nodes.

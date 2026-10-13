## What changed

Replaced the sole sorry in Sheaf.Paper.ModuleCupCosimplicialAW by an explicit
CochainComplex.ofHom construction. The proof uses coproduct descent, checks
commutation on each tensor summand, treats negative source degrees by zero
objects, and proves the requested degree-zero restriction.

Added Sheaf.Paper.ModuleCupAWComponents with the actual front/back formula,
its degreewise coproduct descent, and proved restriction and zero-zero identities.
Added Sheaf.Paper.ModuleCupAWLeibniz with a complete proof of the local signed differential
identity on nonnegative bidegrees. All construction data are explicit; no object
is chosen from a sorried existence statement. Existing signatures and public
imports are unchanged; the new proof import is private.

## Proved and sorry left

Closed: AlgebraicGeometry.Scheme.Modules.moduleCup_cosimplicial_aw
(lem-sc-module-cup-cosimplicial-aw). No sorry remains in the item.

No holes added or left in delivered modules. Also proved:
AlgebraicGeometry.Scheme.Modules.moduleCup_awSummand_leibniz
(lem-sc-module-cup-aw-leibniz). Its private helpers prove all six simplex
front/back identities, naturality of the multiplication on a coface, the
left/right tensor differential terms, the finite-sum splitting and cancellation,
and transport along the extension isomorphisms. This closes the original hole
without adding any lower hole. The resulting AW theorem does not use the
sorried Godement existence theorem; its input is the arbitrary multiplication μ.

The components module contains no sorry. Its proved declarations are
moduleCup_ι_awComponent and moduleCup_awSummand_zero. The item also proves the
private tensor_summand_d helper directly from Mathlib's total differential API.
No holes were added inside definitions. Existing imported holes are untouched.

## No longer needed

No original imports or modules were pruned. The original proof dependency
lem-sc-module-cup-godement-cosimplicial-input was removed from the AW node's
proof_deps: its existence theorem is not invoked. Its module remains needed for
the cosimplicial complex, pointwise tensor and degree-zero pairing definitions
in the unchanged statement and explicit construction. The new components module
uses only Mathlib.Algebra.Homology.Monoidal for the tensor-complex API. The cosimplicial input module
still supplies the definitions in the unchanged statement. Its Godement
existence theorem is not used by this general AW proof. The unit route is kept.
The proof does not require associativity or braiding of the category of cochain
complexes; tensor_summand_d uses the total-complex API without those instances.

## Where the brief, the DAG or earlier work was wrong

The existing proof dependency supplies the cosimplicial definitions but not the
AW signed differential identity. The original node's single step concealed
that calculation. It is now a separate proved statement with its full cancellation
argument in the docstring and node.

The upstream CochainComplex.ιTensorObj_d requires global good-tensor instances
for triples of graded objects, unavailable from the item's assumptions. Its
proof works directly for HomologicalComplex.tensorObj, so the item repeats
that short proved calculation without adding assumptions.

Read Banerjee §1.1.4, printed p. 16, directly from arXiv:1004.1491v2. The paper
has precisely the two inclusions used in the definitions. The empty scheme,
zero objects and all negative degrees are handled without nonvanishing
hypotheses. In bidegree (0,0) the front and back inclusions are identities,
which is checked by Lean. For the local differential formula, the two middle
terms agree and have opposite signs also when r or s is zero. LeanSearch
returned Internal Server Error; the other searches returned only infrastructure.

The blueprint ancestor helper gives None for this module-created item.
Following the existing nodes gives lem-sc-module-cup-godement-aw and then
thm-sc-theorem-of-cube; the new nodes retain that ancestry and the same unit.

## New nodes

- def-sc-module-cup-aw-components: explicit summand and degreewise constructions,
  with proved summand restriction and degree-zero formula, in
  lean/Sheaf/Paper/ModuleCupAWComponents.lean.
- lem-sc-module-cup-aw-leibniz: the signed local differential equality on
  nonnegative summands, in lean/Sheaf/Paper/ModuleCupAWLeibniz.lean.

Both modules are proved, with no new work item containing sorry. They inherit
sec-abelian-varieties / sk-prop-av-cube and record the searches
actually run. The existing AW node now follows the construction and local
identity used by its Lean proof. No statement or definition was changed and
no change record is needed.

## Second reading by R4

1. Interface comparison: diffed ModuleCupCosimplicialAW against the repository.
   The sole existing public declaration moduleCup_cosimplicial_aw, its complete
   signature and docstring, and both original public imports are byte-for-byte
   unchanged. The added import of ModuleCupAWLeibniz is private. The new files
   introduce only new declarations; no existing definition is changed and no
   change record is required. Verdict: pass.
2. Proof and construction: compiled all three delivered modules in import order
   with lcompile.py, without errors or warnings (8.9, 5.1 and 5.7 seconds).
   Scanned their sources for sorry and forbidden trust mechanisms: none occur.
   A scratch copy with #print axioms checked moduleCup_cosimplicial_aw and all
   six new public declarations, including the generated reassociation theorem;
   every result lists only propext, Classical.choice and Quot.sound, no sorryAx.
   moduleCup_awSummand uses actual simplex maps and extension isomorphisms;
   moduleCup_awComponent uses coproduct descent. No data come from an arbitrary
   witness of an unproved existence theorem. Verdict: pass.
3. New results: no statements are left with sorry. Read Banerjee
   arXiv:1004.1491v2, printed page 16, section 1.1.4: its inclusions i ↦ i and
   j ↦ p+j are precisely the two subinterval maps in moduleCup_awSummand.
   The local Leibniz theorem has exactly the nonnegative summand hypotheses
   needed in the main proof, and is strictly smaller than constructing a total
   cochain morphism. Checked all six simplex identities, naturality of μ,
   finite-sum splitting, middle cancellation and the transport_pairing proof.
   At r=s=0 the middle terms cancel with opposite signs; when either degree
   is negative the main proof uses a zero source, including the boundary -1.
   Zero sheaves and the empty scheme require no extra hypothesis.
   Independent LeanFinder search for tensor products of cosimplicial cochain
   complexes and front/back differential inclusions found only coface and
   tensor/Hom differential infrastructure. Loogle's SimplexCategory.subinterval
   results concern interval edges and spines, not this AW identity; the grep
   search for cup/Whitney found no matching Mathlib construction. Also searched
   the upstream WeilConjectures tree and the repository's Sheaf modules.
   cechCupCochain_leibniz is a theorem on Čech section tuples, not arbitrary
   cosimplicial objects. Verdict: no duplicate or hidden restatement.
4. Route and pruning: coproduct descent and summand extensionality reduce the
   target directly to the proved local identity. The tensor_summand_d helper
   follows the upstream ιTensorObj_d calculation, but without the global
   good-tensor instances for triple graded objects required by that theorem.
   No shorter applicable library theorem was found. Both new modules' public
   imports provide vocabulary or construction data used in their public APIs;
   the Leibniz module's preadditive and Abel imports are proof-only. No original
   import can be removed while preserving the existing public interface.
   Inspected dag/units/sk-prop-av-cube.json: its realized fields are unchanged;
   this auxiliary argument replaces no statement or step of that unit.
   Verdict: pass, with the pruning report clarified as below.
5. DAG comparison: the existing AW node's statement and stmt_deps are unchanged.
   Its new proof steps assemble the explicit components, use the local signed
   identity, handle negative degrees by zero sources, and normalize degree zero,
   exactly as the Lean proof does. The new component definition node and local
   identity node have the required source, ancestry, chapter/unit, creation,
   searches and verbatim Lean signature records. Their proof dependencies match
   the construction and calculation; the Godement existence theorem is never
   used. Verdict: pass.

Second-reading changes: corrected No longer needed to explicitly name the old
proof dependency removed from proof_deps while explaining why its definition
module stays imported. No Lean repair was needed. Closed one original hole,
added zero holes; this is a proof, not a decomposition with open lower lemmas.

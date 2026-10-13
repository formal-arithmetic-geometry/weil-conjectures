## What changed

The original signature and all four existing definitions in
Sheaf.Paper.ModuleCupGodementCosimplicialInput are unchanged. Its existential theorem
now has a complete Lean proof from the construction and stalk contraction of concrete Godement
models. Three private, proved helpers transport flasqueness through a sheaf isomorphism,
prove it for zero module sheaves, and transfer it from the actual stalk products to
all terms of the extended alternating coface complex.

ModuleCupGodementModel constructs the product of the upstream module skyscrapers,
the germ unit, its map on morphisms, its iterates, and the recursive unit insertions.
The model predicate specifies actual terms, cofaces, and augmentation, without
assuming homology or flasqueness. All data are constructed directly; no definition
selects a witness from an unproved existence theorem.

ModuleCupGodementObjectFlasque proves flasqueness of the actual product of stalk
skyscrapers. Its proof uses product-preserving evaluation, the categorical product
comparison and Types.productIso, and an explicit section lift extended by zero.
ModuleCupGodementModelPairing and ModuleCupGodementStalkContraction separate construction
of the compatible cosimplicial objects from their stalk contracting homotopy. These are
strictly different parts of the supplied argument: the construction theorem asserts
no quasi-isomorphism or flasqueness, and the contraction theorem requires no pairing. ModuleCupGodementModelQuasiIso is
now proved: stalk exactness gives preservation of homology; naturality of the
homology comparison identifies the stalk homology maps with the maps of stalk
complexes; stalkwise bijectivity reflects them to sheaf isomorphisms.
The main theorem combines them and the proved flasqueness result.

Sources read: Stacks Project, Tag 0FKR, construction and Lemma 20.30.1 (0FKS),
and Banerjee, arXiv:1004.1491, section 1.1.4. The proof follows the supplied
Godement route and retains the separate Alexander--Whitney step downstream.
The unit record sk-prop-av-cube has no realized nodes or steps for this item;
no unit or chapter route was changed.

## Proved and sorry left

Original hole closed:
AlgebraicGeometry.Scheme.Modules.moduleCup_godement_cosimplicial_input
(lem-sc-module-cup-godement-cosimplicial-input).

New theorems proved:
AlgebraicGeometry.Scheme.Modules.moduleCup_godement_model_quasiIso
(lem-sc-module-cup-godement-model-quasi-iso), from the stalk contraction.
AlgebraicGeometry.Scheme.Modules.moduleCup_godement_object_flasque
(lem-sc-module-cup-godement-object-flasque).
The private helpers flasqueOfIso, flasqueOfZero and modelFlasque are proved.

Two holes added, each the entire proof of a named public theorem in its own module:
- AlgebraicGeometry.Scheme.Modules.moduleCup_godement_model_pairing
  (lem-sc-module-cup-godement-model-pairing).
- AlgebraicGeometry.Scheme.Modules.moduleCup_godement_stalk_contraction
  (lem-sc-module-cup-godement-stalk-contraction).

There are no sorries left in the item's module, no holes in any definition,
and no other added holes. This closes one upper hole by a decomposition into
two lower holes; it is not reported as a sorry-free proof of the Godement construction.

## No longer needed

No baseline module leaves the target import closure. All original public imports are retained.
The old proof dependency def-sc-module-cup-resolution-data is no longer a proof step;
it remains a statement dependency and its module provides tensor-section/signature
infrastructure through the original public import.
The new model module no longer imports ModuleCupResolutionData,
Mathlib.CategoryTheory.Monoidal.FunctorCategory, or Mathlib.Topology.Sheaves.Flasque.
The pairing module imports TensorSection and FunctorCategory directly; the object
flasqueness module imports Flasque and DerivedHomMayerVietoris (for moduleRings) directly.
The quasi-isomorphism proof imports Mathlib.Topology.Sheaves.Abelian privately
for the additivity of the abelian stalk functor, previously received transitively.
The original monolithic proof plan is replaced by the concrete model construction,
stalkwise exactness and proved flasqueness. No Alexander--Whitney, resolution
comparison, or derived cup-product module is imported for this proof.

## Where the brief, the DAG or earlier work was wrong

The node's only proof dependency was ModuleCupResolutionData, which defines cup
resolution data but provides no module Godement construction. The required
construction and exactness steps had no separately usable Lean statements.
This delivery creates their concrete interfaces instead of asserting a pairing
for arbitrary resolutions, which would be false. A preliminary universal-pairing
split was rejected during development and is not in the delivery.

Edge cases checked mathematically: the empty scheme and empty opens have empty
products, with only the zero section; zero sheaves use the same constructions;
negative terms of the extended complex are zero. The model predicate does not
force unsupported nonvanishing, injectivity or flatness hypotheses.

LeanFinder and Loogle found cosimplicial and individual skyscraper infrastructure,
and direct rg found the module skyscraper and its evaluation in the upstream
FlatPullbackStalk module. LeanSearch returned Internal Server Error and is recorded
as unavailable, not as a negative search result.

## New nodes

- def-sc-module-cup-godement-model: the actual stalk-product object, maps, iterates,
  unit insertion cofaces and the model predicate, in ModuleCupGodementModel.
- lem-sc-module-cup-godement-model-pairing: constructing the multiplicative
  cosimplicial model, in ModuleCupGodementModelPairing. Its docstring gives the
  monad and tensor-compatibility proof that remains to be formalized.
- lem-sc-module-cup-godement-model-quasi-iso: exactness of any augmented object
  satisfying the concrete Godement term/coface equations, in ModuleCupGodementModelQuasiIso.
  It is proved from stalk contraction, exactness and homology comparison.
- lem-sc-module-cup-godement-stalk-contraction: the homotopy equivalence at
  each individual stalk, in ModuleCupGodementStalkContraction. Its proof plan
  specifies the inverse and homotopy maps from evaluation and unit insertion.
- lem-sc-module-cup-godement-object-flasque: the proved flasqueness of the actual
  product of module stalk skyscrapers, in ModuleCupGodementObjectFlasque.

No existing interface, statement, definition, or visibility changed, so no
change record or forced adaptation is required.

Validation: all six delivered modules compile together without warnings; the
original five-file reduction also passed deliver3.py --no-push before the further
stalk-reflection proof. Final validation is repeated for the six-file delivery.


## Second reading by R4

1. **Interfaces: PASS.** Compared every delivered module against the repository.
   Only ModuleCupGodementCosimplicialInput exists there; the other five are new.
   All four existing definition bodies, all five existing declaration signatures,
   docstrings, visibility and original public imports are byte-for-byte unchanged.
   The three new imports of the item are plain proof imports. No change record or
   consumer adaptation is required.
2. **Proofs and data: PASS.** All six modules compiled in dependency order through
   lcompile.py, with no errors or warnings. The only two literal sorries are the
   entire proofs of moduleCup_godement_model_pairing and
   moduleCup_godement_stalk_contraction. No definition contains a hole or chooses
   an arbitrary witness from an unproved existence result. The product, maps and
   iterates are explicit categorical constructions. The flasqueness proof extends
   coordinates by zero; the homology reflection proof uses exactness and the
   natural homology comparison. Scratch copies with #print axioms check all public declarations and every
   private helper/instance: the constructed data, flasqueness theorem, transport
   helpers and stalk-reflection helpers use only propext, Classical.choice and
   Quot.sound. The two open lemmas, model quasi-isomorphism and original theorem
   additionally use sorryAx as expected. The delivery axiom probe checks every
   declaration again.
3. **Split statements: PASS.** Read both statements and their complete docstring
   arguments. The pairing constructs actual iterates/cofaces and gives no
   exactness or flasqueness; contraction concerns one coefficient sheaf at one
   stalk and gives no pairing. Thus each is a strictly separate part of the
   original argument, not a renaming of the original conjunction. Checked the
   empty scheme, empty opens, zero coefficients, first two cofaces, degree zero,
   and negative degrees. Verified the cited Stacks 0FKR/0FKS and Banerjee §1.1.4
   sources. Independent LeanFinder/Loogle/grep queries used extra codegeneracies,
   split cosimplicial complexes and lax monoidal stalk/skyscraper products.
   Mathlib ExtraDegeneracy.homotopyEquiv is useful simplicial infrastructure but
   does not supply the model-specific evaluation identities, the dual and
   extension transport, or the multiplicative construction. Upstream Cech.godement
   is an abelian presheaf Čech construction, not this module cosimplicial model.
   Neither open lemma could be closed in a few minutes using those results.
4. **Route and pruning: PASS after repair.** The original theorem is assembled
   from construction, stalk exactness and explicit flasqueness, preserving the
   separate downstream Alexander--Whitney step. Read dag/units/sk-prop-av-cube.json:
   its realized.statement is empty and its only realized step is empty; no unit
   route is changed. Original public imports support the unchanged interface.
   Removed broad or misplaced imports from the new model and moved required
   tensor/flasqueness imports to the modules whose public signatures use them.
   Listed the old unused proof dependency in No longer needed, while distinguishing
   its remaining use as statement infrastructure. No whole module is pruned.
5. **Nodes: PASS after repair.** Read all six node files and compared their proof
   steps/dependency unions with the Lean. New nodes have source, creation record,
   blueprint ancestry, recorded searches, and module/declaration records.
   Replaced collapsed new-node signatures with verbatim Lean signatures and
   removed the concrete model's spurious dependency on cup resolution data.
   The existing node changes only proof, proof_deps and proof_origin.

Second reading changed imports of four new modules, concrete-model dependency
metadata, new-node signature formatting, one extra pre-proof space in the existing
module, and this report. It changes no mathematical statement or definition.
One original hole is closed and two lower holes are added: a decomposition with
a delivery hole balance of -1 (not a computed global ledger result), not a completed Godement proof. No additional hole was added
by the second reading.

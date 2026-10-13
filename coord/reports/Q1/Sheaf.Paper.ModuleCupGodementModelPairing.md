## What changed

Replaced the single `sorry` in `Sheaf.Paper.ModuleCupGodementModelPairing` with a compiling reduction. Apply `moduleCup_godement_models_exist` separately to `F`, `G`, and `F ⊗ G`; apply `moduleCup_godement_pairing_for_models` to the resulting models; evaluate its morphism identity on tensor sections using `tensorHom_app_tmulSection`. The original theorem signature, docstring, and public imports are unchanged. Its two new proof imports are nonpublic.

Added `Sheaf.Paper.ModuleCupGodementCodegeneracies`, with explicit product/skyscraper definitions of monad multiplication, recursive multiplication insertions, and the predicate specifying codegeneracies. These are genuine constructions with no chosen existential witness and no proof holes. Added separate modules for the single-model existence obligation and for pairing given models. Updated the original node's proof route to match the Lean proof.

## Proved and sorry left

Closed the original textual hole in `AlgebraicGeometry.Scheme.Modules.moduleCup_godement_model_pairing` (node `lem-sc-module-cup-godement-model-pairing`). The proof that assembles three models and derives the section identity from a morphism identity is complete. This delivery is a decomposition, not an axiom-free proof of the full Godement construction: one original hole closed, two new holes added (net -1).

Remaining new holes, each the entire proof of a named public theorem in its own module:

- `AlgebraicGeometry.Scheme.Modules.moduleCup_godement_models_exist`: node `lem-sc-module-cup-godement-model-pairing-models-exist`, module `Sheaf.Paper.ModuleCupGodementModelsExist`. Constructs one augmented model, including its canonical codegeneracies; no pairing conclusion.
- `AlgebraicGeometry.Scheme.Modules.moduleCup_godement_pairing_for_models`: node `lem-sc-module-cup-godement-model-pairing-pairing`, module `Sheaf.Paper.ModuleCupGodementPairingForModels`. Constructs the multiplication for given models with canonical codegeneracies and proves a degree-zero morphism identity; no model-existence conclusion.

No holes remain in the item's module or in the new codegeneracy definitions. All modules compiled with `lcompile.py --all`; the section-level conclusion is checked by Lean, including the degree-zero identifications.

## No longer needed

None. All three original public imports are needed by the unchanged statement. The only added imports of the item are the two construction lemmas actually used. The original direct proof dependency `def-sc-module-cup-godement-model` is now used transitively through the two new obligations and remains required by the unchanged statement; it is not a pruned node or module. The concrete codegeneracy definition module is used transitively by both new obligations.

## Where the brief, the DAG or earlier work was wrong

No established error in the original statement. Its predicate fixes terms and cofaces but does not fix codegeneracies. Therefore a new pairing theorem for arbitrary witnesses of that predicate alone would assert more than the monad argument supplies. The delivery avoids that assumption by constructing and requiring the canonical multiplication insertions in a separate predicate. This strengthens only the new intermediate construction statements; no existing statement or definition is changed.

The unit record `sk-prop-av-cube` has no realized nodes for this subargument, and this reduction stays within its existing unit and chapter. The Stacks construction preceding Lemma 20.30.1 and Banerjee §1.1.4 were inspected. Searches found skyscraper and tensor infrastructure but no completed Godement construction; LeanSearch was unavailable and is recorded as such. Empty schemes and zero coefficient sheaves use the same product and tensor formulas. The pairing lemma specifies both generating types of simplex morphisms, so there is no missing degeneracy-naturality assumption.

## New nodes

`def-sc-module-cup-godement-codegeneracies`: explicit monad multiplication, recursive collapse maps, and the codegeneracy predicate, in `Sheaf.Paper.ModuleCupGodementCodegeneracies`. Its data are fully constructed and compiled.

`lem-sc-module-cup-godement-model-pairing-models-exist`: construction of one augmented model with canonical codegeneracies, in `Sheaf.Paper.ModuleCupGodementModelsExist`. Its node and docstring give the stalk/product adjunction, monad identities, simplex generators, and augmentation construction.

`lem-sc-module-cup-godement-model-pairing-pairing`: coordinatewise tensor construction for three given models with canonical codegeneracies, in `Sheaf.Paper.ModuleCupGodementPairingForModels`. Its node and docstring give the recursive tensor multiplication, unit and evaluation compatibility, transport through term equalities, and degree-zero morphism identity.

## Second reading by Q1

1. Compared the item module and its node with the repository using `diff`. Verdict: pass. The existing theorem signature and docstring are byte-for-byte unchanged, and the existing public imports are unchanged. The only item-module changes are two nonpublic proof imports and the proof body. The existing node changes only `proof`, `proof_deps`, and `proof_origin`; there are no existing definition or statement changes and no forced adaptations.

2. Compiled all four delivery modules with `lcompile.py --all`. Examined every declaration and scanned for forbidden constructs: the only two `sorry`s are the entire proofs of `moduleCup_godement_models_exist` and `moduleCup_godement_pairing_for_models`. A scratch-copy axiom probe showed `propext`, `Classical.choice`, and `Quot.sound` for multiplication, collapse, and the codegeneracy predicate; the item and the two open lemmas additionally use `sorryAx`. Verdict: pass as a decomposition, not an axiom-free proof. There is no hollow definition or arbitrary witness chosen in a definition.

3. Read both new theorem statements and their complete docstring arguments, and compared the multiplication formula with `skyscraperHomEquiv`, `toSkyscraper`, and `skyscraperStalkEval`. Verdict: pass. Single-model existence is strictly the model-construction part of the original assertion; the pairing theorem concerns already supplied models, and does not supply their existence. Neither merely renames the original assertion. The codegeneracy hypothesis is necessary for the argument on all simplex generators. Its term equality witnesses agree with those in the model predicate by proof irrelevance. At n=0 collapse is monad multiplication; at n=1 the two collapses are multiplication on T(F) and T of multiplication on F. On an empty scheme products are terminal zero modules; for zero sheaves every stalk and iterate is zero. On a one-point scheme the maps are the stalk/skyscraper adjunction maps. These cases impose no extra nonemptiness or flatness hypothesis. Rechecked Stacks 0FKR and Banerjee arXiv:1004.1491 §1.1.4. Independent searches used leanfinder for unit/multiplication insertion from an endofunctor monad, loogle for skyscraperStalkEval, and grep for cosimplicial/Monad/skyscraperHomEquiv, plus direct searches of upstream, Sheaf, and Mathlib category-theory and simplicial sources. Results supplied only general infrastructure or consumers of this theorem, no existing construction proving either new obligation. Neither construction hole can be closed by a short existing-lemma application.

4. Read the proof top down: construct the three individual models, obtain their multiplication, and evaluate the morphism equality on pure tensor sections. Verdict: pass. The unit `sk-prop-av-cube` has `realized.statement = []` and `realized.steps = [[]]`, so no realized unit step was bypassed. All item imports are needed by its unchanged statement or by the displayed proof. Narrowed the new pairing module's public import from `TensorSection` to `Invertible`, which supplies the monoidal instance used in its statement. No node or module is pruned; clarified that the original direct proof dependency remains transitively needed rather than disappearing.

5. Checked all four node records against the Lean declarations, the union of proof-step uses, source, creation, blueprint, search, and Lean fields. Verdict: pass. The original node records precisely the two theorem applications and section evaluation. Each new node matches its declaration and describes the actual product/skyscraper construction or its outstanding obligation. No change record is required because no existing interface changed.

Second reading changed the new pairing module's import to the smaller statement dependency, clarified the dependency account under `## No longer needed`, and added this independent review. The Lean proof and mathematical statements required no repair. One original textual hole is closed, two holes are added; net closure progress is -1, with no fully axiom-free Godement construction claimed.

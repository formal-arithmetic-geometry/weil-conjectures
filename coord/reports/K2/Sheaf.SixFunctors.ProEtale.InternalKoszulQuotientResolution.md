## What changed

Replaced the proof hole in
`AlgebraicGeometry.ProEtale.InternalCompletionTransport.koszul_quotient_resolution`
by extracting zero residue from the specified generating sections, then an
explicit assembly from compatible finite augmentations and a one-level
acyclicity theorem. The assigned statement, binders, universes and public imports
are unchanged. No existing definition or source-library declaration is modified.

The Lean proof first takes an actual generator of the kernel ideal on each slice.
Its subtype property and the proved `ConstantCompletion.kernelIdeal_existsUnique`
sections formula show that a has zero residue. It then constructs a natural
transformation with `NatTrans.ofOpSequence`,
transposes its components to a chain map of towers, identifies its evaluations
with the finite augmentations, and applies
`HomologicalComplex.quasiIso_iff_evaluation`. The ordinary-limit unit identity is
proved degreewise by `limMap_π`, two applications of `limit.lift_π`, and the finite
unit equation. An isomorphism with identity degreewise components accounts for
the `CochainComplex.of` model of the source tower; no equality of its conditional
differentials is assumed.

Added two modules with separate obligations:

- `InternalKoszulFiniteAugmentation`: construction of the finite maps, their
  specified zero components, unit normalization and successor compatibility on
  arbitrary complexes. It assumes only that a has zero residue, rather than
  that a generates the residue kernel. It has no K-flatness or
  quasi-isomorphism assertion.
- `InternalKoszulFiniteAcyclicity`: quasi-isomorphism of a supplied normalized
  augmentation at one fixed level. It constructs no maps and asserts no tower
  naturality or inverse-limit equation. The zero-summand condition specifies the
  augmentation, rather than making an unsupported claim about arbitrary maps.

Both use the actual internal coefficient reductions and the existing total-tensor
summand inclusions. There is no new data definition and no witness selected into
a definition. Removed the existing option disabling transparency respect from the
assigned file. Both new proof imports in the assigned file are private. The explicit
`Mathlib.Algebra.Homology.Functor` proof import was removed as redundant: the
public ringed Koszul import already supplies the evaluation lemma.

## Proved and sorry left

Original holes: 1. Closed in the assigned module:
`AlgebraicGeometry.ProEtale.InternalCompletionTransport.koszul_quotient_resolution`
(node `lem-sfb-internal-koszul-quotient-resolution`). No sorry remains in that module.

Added holes: 2, each the complete body of a named public theorem:

- `AlgebraicGeometry.ProEtale.InternalCompletionTransport.koszul_finite_augmentation`
  (node `lem-sfb-internal-koszul-finite-augmentation`).
- `AlgebraicGeometry.ProEtale.InternalCompletionTransport.koszul_finite_augmentation_quasiIso`
  (node `lem-sfb-internal-koszul-finite-acyclicity`).

This is a decomposition, not a net proof gain. The construction, one-level
homological assertion, and proved tower/limit assembly are distinct parts of the
original argument. Neither new theorem alone has the original conclusion. Each
remaining hole has its source and complete proof in words in its docstring and node.

## No longer needed

No existing module is withdrawn and no original public import is removed.
The redundant added Mathlib proof import was removed as described above. No
mathematical dependency has been shown globally unnecessary.

The coefficient realization, normalized integral limit, constant-completion
criterion and regular-sequence Koszul theorem are no longer direct proof steps
of the assigned theorem. They remain in the new finite-augmentation and
finite-acyclicity nodes as appropriate. Their obligations are retained; they
are not claimed as globally pruned. The assigned node now directly uses the
two finite lemmas, the strict quotient-tower definitions, the ringed Koszul
system, and the ideal/generating-section definitions. The only proof used from
`ConstantCompletionEquivalence` is its already proved kernel sections formula;
its equivalence theorem and other unproved comparisons are not applied. The unit record and its realized route are unchanged.

## Where the brief, the DAG or earlier work was wrong

The listed dependencies supply coefficient descriptions and general definitions,
but none supplies a chain map from the specified dual singleton tensor complex
to the actual internal finite quotient, with its nonzero-degree components
specified. The existing constant-module, cone and completed Roos comparisons use
different objects. In particular a derived equivalence or a statement about a
Roos fibre is insufficient to identify a strict finite augmentation.

The search examined `RegularSequenceKoszulRegular`, `ConstantCompletionEquivalence`,
`IntegralConstantCompletion`, `IntegralConstantModelRealization`,
`RegularQuotientCompletionUnit`, `PrincipalKoszulQuotientTowers`,
`KoszulQuotientTensorAugmentation` and `CompletedKoszulQuotientRoosAugmentation`,
as well as the actual `DerivedCompletion` and transport modules. LeanFinder,
LeanSearch, Loogle and Mathlib grep queries are recorded in the new nodes.
Blueprint searches for “Koszul quotient augmentation” and “finite Koszul” found
no matching blueprint node.

The source read is the current blueprint
`sec-six-functors-basics/sk-thm-sf-pf-adic/sk-thm-sf-pf-adic-open.proof.md`,
especially its reduction-by-the-uniformizer paragraph, together with Stacks
`proetale.tex`, Section derived-completion-noetherian and Lemma naive-completion
(099L, 099M), and `algebraization.tex`, Lemma derived-completion-koszul (0A0E).
The regularity step also uses Tag 062F. The specialized finite argument is
written by the agent and marked accordingly in `proof_origin`.

Edge cases checked mathematically: zero P, empty X, level n=0 (exponent one),
a locally replaced by a unit times the uniformizer, and unbounded K-flat P.
The construction needs no K-flatness and also applies to a=0, since it
asserts only existence of maps and their formulas. The acyclicity assertion
retains the generating-list and K-flatness hypotheses.
Regularity is justified locally, not by assuming that every generator of a
principal ideal in an arbitrary ring is regular. No arbitrary zero-divisor
version is asserted and no termwise-flatness condition is added.

## New nodes

`lem-sfb-internal-koszul-finite-augmentation` states the actual finite augmentation
maps for a residue-zero section, with their zero-component, unit and successor
formulas. This is the map
construction of the original plan, independent of its homological argument.

`lem-sfb-internal-koszul-finite-acyclicity` states the single-level homological
argument for any supplied augmentation with those component formulas. It uses
regularity and K-flatness and is independent of transitions and inverse limits.

The existing node's `proof`, `proof_deps` and `proof_origin` now describe the Lean
assembly. No statement or definition changes, so no change record is required.
Compiler and delivery validation are run through the prescribed launcher tools.

Validation: both lower modules compiled in the import-ordered packet (44.4 s
and 40.9 s). After the model-conversion corrections, the assigned module
compiled successfully on its own against those artifacts in 14.6 s. The
delivery command performs the required final preflight and axiom checks.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

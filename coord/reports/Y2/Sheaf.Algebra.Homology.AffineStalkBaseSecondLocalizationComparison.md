## What changed

Filled `AlgebraicGeometry.exists_affineStalkBaseSecondLocalizationComparison` in
`Sheaf.Algebra.Homology.AffineStalkBaseSecondLocalizationComparison`, without changing
its signature or any public definition. Added only the two proof imports planned by
the node: `BaseDerivedTensorRestrictedRingComparison` and
`DerivedTensorBaseSecondLocalizationModels`.

Proved private helpers identify identity restriction on complexes and homology,
upgrade the restricted-ring comparison to tensor-algebra linearity, and transpose
its ordinary square to the localized square. The main proof establishes the
canonical stalk scalar towers, applies base-and-second localization to the same
stalk complex, and identifies beta inverse followed by every allowed tau with the
canonical equality-of-coefficient-maps isomorphism by unit-tensor extensionality.

The existing node records this Lean realization. Its statement, source, unit and
Lean attachment remain unchanged. The unit record has no designated realized
nodes bypassed by this proof. Local irreducibility attributes keep chosen models
abstract during elaboration; the explicit equations remain their API. No library
definition was changed. Sources checked: Stacks Tags 0DJ8 and 06Y6.

Change record: `coord/changes/affine-stalk-base-second-local-proof-directives.md`.
The static checker requests it for the local attribute commands; it documents
their scope, the unchanged public signature, and the unaffected downstream caller.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.exists_affineStalkBaseSecondLocalizationComparison`
(node `new-affine-stalk-base-second-localization-comparison`). Its proof combines
existing declarations and proved private helpers. Added holes: zero. Remaining
holes in delivered Lean files: zero. Split-offs: zero. This is a proof of the
assigned item from its planned existing dependencies, not a decomposition.

Validation: `lcompile.py` compiled the final module without warnings in 33.7 seconds.
A byte comparison confirms the public theorem signature is unchanged. The delivery
dry run also checks every delivered declaration for disallowed axioms and direct holes.

## No longer needed

None. Both added proof imports are used. Both original public imports are needed
by the statement. The three existing proof-dependency nodes are retained; no
module or node is claimed pruned. No first-factor localization theorem or
additional derived-resolution module is imported.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found in the statement or the planned route. The prior
split chain can be closed at this item: the two existing planned theorem APIs are
sufficient, including the universe bridge and comparison compatibility. Lean
requires explicit model instances when the same rings carry chosen derived
categories in two universes, and explicit canonical algebra instances for the two
presentations of the spectrum stalk rings. These are local proof details, not
interface changes. No new nodes, changed statements, hollow definitions, or
forced adaptations are needed.

## Second reading by Y2

1. PASS: compared the delivered module and node with the repository versions.
   The existing theorem signature is byte-for-byte identical, including every
   hypothesis, let-bound coefficient structure, universe and conclusion. Its
   docstring and original public imports are unchanged. All added helpers are
   private. The change record accurately describes file-local instance and
   reducibility attributes and the declaration-local heartbeat setting; no
   existing definition, statement or exported attribute is changed.
2. PASS: independently compiled the delivered module without errors or warnings
   (32.2 seconds). Compiled a scratch copy with `#print axioms` for the public
   theorem and all eight private declarations (31.4 seconds). Every declaration
   uses only `propext`, `Classical.choice` and `Quot.sound`; none uses `sorryAx`.
   There are no direct holes, forbidden declarations, or hollow definitions.
   The coefficient-map isomorphism is constructed by `eqToIso`. The existing
   tensor map is determined by its two restrictions, and the chosen model and
   its existence theorem have no unproved axiom in this compiled proof.
3. PASS: there are no split-off statements, added holes or new nodes. Read the
   identity restriction, tensor-linearity, adjunction and pure-tensor helpers.
   Their arguments allow zero complexes and identity localizations; a zero
   fourth ring has no prime. Searched Mathlib with different identity-homology
   wording and searched the project for model comparisons. The existing
   quasi-isomorphism comparison uses one derived-category universe and does
   not replace the required two-universe bridge. The ordinary ring comparison
   adds arbitrary coefficient transports; the proof's identity specialization
   of the planned restricted-ring API avoids those transports.
4. PASS: followed the proof from the conclusion through the unit-tensor chain
   equality, localization square, and universe comparison. Both added imports
   are used only by proofs and are plain imports. The original imports supply
   statement notions. Every original proof dependency is retained and used,
   so `No longer needed: None` is complete. The unit
   `sk-thm-picard-semicon` has empty statement/step `realized` lists; this proof
   changes no unit route. Checked the localization identity in
   [Stacks Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8) and the independence
   of derived choices in [Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6).
5. PASS: the node's three steps describe the actual Lean argument in order;
   `proof_deps` is exactly the union of their `uses`. Only `proof`, `proof_deps`
   and `proof_origin` differ from the repository node. The statement, Lean
   signature attachment, source, blueprint, chapter and unit are unchanged.

Second-reading changes: added this review and its independent compile/axiom
evidence to the report. No Lean proof or node repair was needed. Closed holes:
`AlgebraicGeometry.exists_affineStalkBaseSecondLocalizationComparison` (one).
Added holes: none. Split-offs: none. Pruned modules or nodes: none.

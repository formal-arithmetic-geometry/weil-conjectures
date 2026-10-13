## What changed

Proved `AlgebraicGeometry.Scheme.root_normalization_stalk_maximalIdeal_isPrincipal`
in `Sheaf.AlgebraicGeometry.Morphisms.RootNormalizationStalkPrincipalIdeal` without
changing its signature, public imports, or docstring. Added only proof imports and two
proved private helpers. Updated the existing node's proof, proof dependencies and origin.

The base root-prime stalk is a DVR: the monic root algebra is flat, multiplication by
`g` remains regular after localization, and `t^n = g` makes the maximal-ideal generator
nonzero. Regularity supplies domainhood. Normality of the normalized stalk follows
from smooth normal ascent, the existing relative-normalization normal-stalk theorem,
and the existing normalization/stalk-base-change comparison. The pullback projection
is a flat preimmersion, so its stalk map is bijective and normality transports back.
Finiteness gives Noetherian stalks and quasi-finite incomparability bounds their dimension
by one. The existing normal-local criterion and Mathlib's cotangent criterion conclude
principalness, including a possible field stalk.

Proof imports added: `Mathlib.RingTheory.Flat.TorsionFree`,
`Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite`,
`Sheaf.AlgebraicGeometry.Morphisms.NormalizationStalkBaseChange`,
`Sheaf.AlgebraicGeometry.Morphisms.RelativeNormalizationNormalStalks`,
`Sheaf.RingTheory.SmoothNormalRing`,
`WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat`, and
`WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs`.

The private smooth-chart argument follows the proved private helper in
`PuncturedDvrNormalizationStalkDomain`; the localization comparison here additionally
transports integral closedness using the flat preimmersion stalk isomorphism.
The dimension calculation follows the contraction argument already used in
`RegularLocalSurfaceDepthTwoFlat`. Neither of those whole modules is imported.

Single-file compilation passes cleanly within the 60-second limit. No other modules
or interfaces are changed. Empty covers yield no points; `n = 1` uses the same proof;
no assumption on tame ramification, torsors or invertibility of `n` is introduced.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.Scheme.root_normalization_stalk_maximalIdeal_isPrincipal`
(node `lem-sbc-root-normalization-stalk-principal-ideal`).

The two private helpers `normal_stalks_of_smooth_integral_base` and
`normal_stalk_over_dvr` are proved. No `sorry` remains in the delivered module.
No holes are added, and nothing is split off.

## No longer needed

No original imports or original proof-dependency nodes are removed. All three planned
inputs are retained. No project module is claimed as pruned. The proof does not require
new lemmas for a separable field-factor decomposition or for a ramification index.
Redundant explicit Mathlib DVR and flat-localization imports tried during development
were removed: these declarations are already publicly exposed by the retained imports.

## Where the brief, the DAG or earlier work was wrong

The original proof plan omitted the smooth normal-ascent input needed after localization;
the updated DAG includes its existing node. It also implicitly used the proved
regular-local-domain and principal-maximal-ideal DVR criteria and the DVR dimension
lemma, now listed explicitly. The node's original three dependencies are usable.
The comparison plus a flat preimmersion avoids having to explicitly identify the
punctured cover as a product of finite separable field extensions. No mathematical
statement correction or forced adaptation was necessary.

## Second reading by R4

1. Compared the delivered Lean module with the repository version. The target theorem's
   signature, docstring, and existing public imports are byte-for-byte unchanged; only
   proof-only imports, private helpers, and the proof body were added.
2. Compiled the module with `lcompile.py` and checked the target with `#print axioms`.
   Compilation is clean and the axioms are only `propext`, `Classical.choice`, and
   `Quot.sound`; there are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
   `implemented_by` declarations.
3. Read the proof and checked the split status and dependencies. No new public statement
   or split-off hole was added; the existing node statement is proved directly, and its
   updated proof steps and `proof_deps` match the imports and declarations used.
4. Checked pruning and the route against the unit record. All retained proof-dependency
   nodes are used by the proof, and no imported project module can be removed without
   bypassing the unit's normalization/base-change route. The proof handles the field
   stalk case through the cotangent criterion and does not add a ramification hypothesis.
5. Reviewed edge cases noted by the source statement: empty covers contribute no points,
   `n = 1` is accepted, and no invertibility or tameness assumption on `n` is introduced.

The second reading found no statement or mathematical defect. I added this review record
and made no code changes after the worker's proof.

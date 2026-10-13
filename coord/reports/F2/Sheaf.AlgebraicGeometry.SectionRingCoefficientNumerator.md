## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_sectionRing_coefficient_numerator`
in `Sheaf.AlgebraicGeometry.SectionRingCoefficientNumerator`, with its signature and
existing docstring unchanged. Added proof-only imports of
`Sheaf.AlgebraicGeometry.SectionRingVeroneseFractions` and
`Sheaf.AlgebraicGeometry.SectionFractionRestrictionMap`.

The coefficient function is the composite of the existing Veronese additive equivalence,
the existing section-fraction restriction map, and the inverse structure-module sections
identification. The proof derives its numerator equation from the tensor formula by
naturality and the left unitor. Three proved private lemmas and a private explicit
isomorphism identify homogeneous powers with tensor powers; these follow the existing
helpers in `SectionRingLocalizationBijective`. No public interface was changed.
The node's proof and dependencies now describe this route.

Both existential maps used here are determined by their formulas: homogeneous fractions
exhaust the localization, and tensoring by the free generator is bijective. The proof
introduces no object selected from an unconstrained existence theorem.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.Scheme.Modules.exists_sectionRing_coefficient_numerator`
(node `lem-sc-section-ring-coefficient-data-numerator`). No holes added or split off.
No `sorry` remains in the delivered module. This is a proof from existing declarations,
not a new decomposition. The existing imported
`AlgebraicGeometry.Scheme.Modules.sectionRing_veronese_fraction_core` and
`AlgebraicGeometry.Scheme.Modules.sectionRing_veronese_fraction_formula` still contain
`sorry`; their modules are unchanged. The restriction-map declaration is already proved.

Local compilation passed without warnings. The argument includes exponent zero and does
not require a nonempty open; the same maps and unitor identities apply on the empty open.
The positive-degree assumption is preserved, although this construction does not need it.

## No longer needed

None of the original imports or dependency nodes can be removed: the section-ring and
free-generator definitions remain necessary. No modules are claimed pruned.
The direct coefficient descent and separate cross-multiplication calculation in the old
plan are supplied by the reusable fraction-presentation and restriction-map declarations.
No separate new nodes for these calculations are needed. The localization-bijectivity,
nonvanishing equivalence, and compactness/affineness arguments are not imported.

## Where the brief, the DAG or earlier work was wrong

The old plan did not name the existing Veronese fraction equivalence and section-fraction
restriction map. They provide the quotient construction without duplicating its descent
proof. No false statement or signature correction was found; the unit route is preserved.
The existing Veronese wrapper uses a chosen equivalence from its core and a separate
formula theorem. Its formula determines the equivalence, but the core and formula remain
open upstream obligations, not an axiom-free completion of the full dependency closure.

## Second reading by F2

1. **Unchanged public contract — pass.** Compared the sole delivered module and node
   against the repository with `diff -u`. The existing theorem signature, its positive-degree
   and free-generator hypotheses, its quantified numerator equation, its visibility, and its
   docstring are byte-for-byte unchanged. Only two plain proof imports, four private helpers,
   and the proof body were added. No change record or forced adaptation is needed.

2. **Proof and constructions — pass, conditional on existing upstream holes.** Independently
   compiled the module without errors or warnings. A scratch copy with `#print axioms` for
   all five delivered declarations reports only `propext`, `Classical.choice`, and `Quot.sound`
   for the private helpers; the main theorem also reports `sorryAx`, from imported open
   obligations. There is no local `sorry`, forbidden declaration, or hollow definition.
   `veroneseIso` explicitly composes an exponent equality with `tensorPowMulIso`.
   The proof takes `eA` from the theorem that specifies its value on every homogeneous
   fraction, not from the bare `Nonempty` core. `Away.mk_surjective` makes this specification
   unique. Likewise the restriction-map tensor formula determines every value because
   tensoring with the free generator's powers is injective. The local coefficient function
   therefore uses determined maps. The upstream wrapper's bare choice and separate open
   formula theorem remain upstream proof obligations; this delivery neither changes that
   wrapper nor introduces a definition choosing an arbitrary witness of its bare core.

3. **Split statements and edge cases — pass.** No statement or hole was split off.
   Checked the private power induction at zero (the graded unit) and successor (tensor
   multiplication, with `d + d*n = d*(n+1)`), and the component extraction using the range
   definition of `sectionRingGrade`. The proof of `hs'` is exactly restriction of the given
   degree-d section. No compactness, affineness, quasi-coherence, nonempty-open assumption,
   or cancellation of a possibly vanishing global section is used. For `n = 0` the tensor
   unit and left unitor give the asserted degree-zero equation. Empty opens cause no
   exception, since the same module isomorphisms and linear identities apply.

4. **Shortest route, imports, and unit route — pass.** Read the existing Veronese and
   restriction-map declarations and their proofs, and compared the helpers with the private
   helpers in `SectionRingLocalizationBijective`; these are inaccessible there and cannot
   be imported as public lemmas. Independent Loogle search for
   `HomogeneousLocalization.Away.mk` found the constructor, surjectivity, and generic map
   formulas; LeanFinder search for homogeneous localization and free-generator division
   returned Proj structure-sheaf maps, which do not give this map for an arbitrary scheme
   and invertible module. Repository/upstream/Mathlib searches also found the upstream
   `ProjectiveSpace.sectionRatio_smul`; it handles an individual coefficient, not descent
   of all homogeneous fractions. No shorter complete replacement was found.
   Both new imports are actually used and are correctly plain imports. The original
   statement imports and both original `proof_deps` remain used, so the pruning list is
   complete (none). Read `dag/units/sk-thm-curveestimate.json`: its realization remains
   `thm-sc-proper-cohomology`, with no unit steps replaced. The proved restriction-map node
   `lem-sc-p1-section-fraction-restriction-map`, filed under `sk-thm-picard-duality`, is used
   solely as a generic quotient/division tool, not as a replacement unit argument.
   The source checkout does not include the literature bodies on this machine; read the
   official [Tag 01N8](https://stacks.math.columbia.edu/tag/01N8) local quotient construction,
   [Tag 01PW](https://stacks.math.columbia.edu/tag/01PW) canonical fraction map, and
   [Tag 0B5L](https://stacks.math.columbia.edu/tag/0B5L) presentation online. Only construction
   of the map is used; the compactness hypotheses for its bijectivity are not imported.

5. **DAG agreement — pass.** Only `proof`, `proof_deps`, and `proof_origin` differ in the
   delivered node. Step 1 is exactly `hA` from the recorded Veronese node. Step 2 is `hf`
   from the recorded restriction-map node with `M = L.tensorPow d` and the structure
   module. Step 3 is the fully proved power/component calculation. Step 4 applies the
   left unitor to `hf`, uses naturality and inverse cancellation, and finally the
   injectivity of `veroneseIso.hom.app U`. The listed dependencies are precisely the
   union of the steps' cited nodes; no new node or altered unit realization is needed.

Changes made by the second reader: added this independent review, the explicit axiom
results, the search comparison, and the cross-unit tool explanation to the report.
The Lean proof and node were correct as delivered and were left unchanged.

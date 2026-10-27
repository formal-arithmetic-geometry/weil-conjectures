## Worker report

This delivery binds lem-sfb-lfp-unique-infinitesimal-lifts-etale to the existing
`AlgebraicGeometry.lfp_unique_infinitesimal_lifts_etale` in
`Sheaf.AlgebraicGeometry.LfpUniqueInfinitesimalLiftsEtale`
(`lean/Sheaf/AlgebraicGeometry/LfpUniqueInfinitesimalLiftsEtale.lean`, line 48).
The module was already landed for lem-per-lfp-unique-infinitesimal-lifts-etale.
I read the complete local module and fetched the current server source with
`scompile.py --source Sheaf.AlgebraicGeometry.LfpUniqueInfinitesimalLiftsEtale`;
the signatures agree. The existing theorem has a postponed `sorry` proof.
No module, definition, proof, dependency, or natural-language statement is changed.
Only this item's `lean` attachment is added. Sharing this declaration does not
add a dependency on the old node or change this item's accepted proof route.

Clause-by-clause correspondence:

- Schemes W and Z and their morphism c: `{W Z : Scheme.{u}} (c : W ⟶ Z)`.
- Local finite presentation: `[LocallyOfFinitePresentation c]`.
- Every pair of affine test schemes: `∀ (T₀ T : Scheme.{u})`, with
  `[IsAffine T₀] [IsAffine T]`. Both affineness assumptions occur inside the
  lifting hypothesis, not as restrictions on W or Z.
- Every first order thickening: `(j : T₀ ⟶ T)` and
  `(hj : IsFirstOrderThickening j)`. This is the recorded closed immersion
  with square-zero defining ideal sheaf, without an additional choice of ideal.
- Every pair of maps a₀ and b: `(a₀ : T₀ ⟶ W) (b : T ⟶ Z)`.
- The commuting square c a₀ = b j: `a₀ ≫ c = j ≫ b →`.
- Exactly one morphism a: `∃! a : T ⟶ W`.
- Its first triangle a j = a₀: `j ≫ a = a₀`.
- Its second triangle c a = b: `a ≫ c = b`.
- Conclusion that c is étale: `Etale c`.

Every scheme is in the explicitly bound universe u; the test schemes use the
same universe as W and Z, not an independent smaller universe that could make
lifting tests vacuous. All term variables are explicitly bound in the existing
signature. Composition is written in Lean's diagrammatic order.

Dependency declarations read and used:

- def-pc-scheme: `AlgebraicGeometry.Scheme` and `Scheme.Hom` in
  `Mathlib.AlgebraicGeometry.Scheme`: locally ringed spaces locally isomorphic
  to spectra, with locally ringed-space morphisms.
- def-sbc-locally-finite-presentation:
  `AlgebraicGeometry.LocallyOfFinitePresentation` in
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: finite presentation
  of the induced ring maps on affine opens.
- def-sbc-first-order-thickening:
  `AlgebraicGeometry.IsFirstOrderThickening` in
  `WeilConjectures.AlgebraicGeometry.Thickening`:
  `IsClosedImmersion j ∧ j.ker ^ 2 = ⊥`.
- def-weil-etale-morphism: `AlgebraicGeometry.Etale` in
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`, affine-locally étale ring maps.
  Its equivalence with flatness, formal unramifiedness, and local finite
  presentation is `Etale.iff_flat_and_formallyUnramified` in that module.
- Affineness is the existing `AlgebraicGeometry.IsAffine` from
  `Mathlib.AlgebraicGeometry.AffineScheme`, already available via the imports.

The original four statement dependencies are sufficient and all have usable
interfaces. In particular the old dependency record names the actual current
`Etale` declaration, so the deprecated `IsEtale` alias is unnecessary.

Source check: read `literature/stacks-project/more-morphisms.tex`,
`definition-formally-etale` (Tag 02HG, lines 1508ff) and
`lemma-etale-formally-etale` (Tag 02HM, lines 1706ff).
The former tests exactly affine square-zero closed thickenings with unique
commuting lifts; the latter asserts the converse from local finite presentation.
No global base assumptions, separation, quasi-compactness, or Noetherian
hypotheses occur. The node is not a blueprint unit's own statement and needs
no correction. No STATEMENT-DISPUTED flag or dependency fault was found.

Edge cases checked mathematically before recording:

- The identity has the unique lift b, so the lifting hypothesis is inhabited
  and the conclusion has the expected étale case.
- Empty W is allowed: a map T₀ → W forces T₀ empty, and a first order
  thickening has the same underlying points, so T is empty too. The test
  has its unique empty lift. The empty morphism is étale.
- Identity thickenings (zero defining ideal) are included; the triangle
  equations still determine the lift and are not discarded.
- For affine-line projection, maps sending its coordinate to 0 and ε over
  k[ε]/(ε²) give distinct lifts of the same closed fibre: uniqueness has content.
- For Spec F_p → Spec Z, testing Spec F_p → Spec(Z/p²) over Spec Z prevents
  a lift; existence has content even for an unramified closed immersion.
- No field or characteristic restriction is present, and Spec of the zero
  ring is included among affine test schemes.

Searches (2026-10-24; full wrapper results are in sandbox searches.jsonl):

- msearch.py leanfinder, query "A locally finitely presented morphism of schemes
  with unique lifts against affine first order thickenings is etale": eight
  scheme étaleness definition, forward implication, and cancellation hits;
  none states this converse.
- msearch.py loogle, query
  "AlgebraicGeometry.Etale, AlgebraicGeometry.LocallyOfFinitePresentation":
  two hits, `Etale.of_formallyUnramified_of_flat` and
  `Etale.iff_flat_and_formallyUnramified`; neither is the lifting criterion.
- msearch.py grep, query `FormallyEtale|formally_etale|unique.*lift`,
  subdirectory AlgebraicGeometry: four unrelated valuative/limit hits.
- rg of `FormallyEtale|formallyEtale|unique.*[Ll]ift|IsFirstOrderThickening`
  in both project AlgebraicGeometry trees identified the exact existing
  `lean/Sheaf/AlgebraicGeometry/LfpUniqueInfinitesimalLiftsEtale.lean`.
- rg for the item ID in lean/WeilConjectures returned no hit. The full-tree
  declaration/module search found its existing DAG attachment at
  dag/nodes/sec-deligne-laumon-a1/lem-per-lfp-unique-infinitesimal-lifts-etale.json.
  That attachment and the live source were read; the entire theorem signature,
  including both triangles and uniqueness, is identical to the assigned node.

Validation: the existing declaration is checked through an explicit sandbox
probe via scompile.py; deliver2.py also generates its own existing-declaration
probe and runs the server preflight. No new Lean source needs compilation.

## Second reading by Q10

I re-opened the node and the full existing theorem after preparing the record.
This is a second pass by the same worker, not a claimed independent-agent review;
the assignment prohibits starting other agents. The maintainer independently
reviews the delivered record. I checked W, Z, c, local finite presentation,
both affine test schemes, square-zero closed immersion, both maps, the square,
unique existential, both triangle equations, and the Etale conclusion against
the Lean signature. Each occurs exactly once in the expected scope. No mismatch
was found. The existing record omits `file` as required for existing attachments;
the module is referenced without copying or editing it.

## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.integralConstructiblePullIso_comp`
in `Sheaf.Paper.ContinuousIntegralPullComposition`, retaining its statement and visibility.
The proof implements the existing three-step DAG plan. Updated that node's `proof` and
`proof_origin` to identify the checked helper calculations; its dependencies and route
are unchanged. Private, proved helpers establish:

- the underived restriction/pushforward composition square;
- factorization of the right-derived comparison through its specified units, and the derived
  square by cancellation on K-injective representatives;
- the conjugation pasting identity and identification of the specified pullback composition
  with the conjugate right-derived pushforward composition;
- identification of the bounded constructible comparison with its ambient derived map.

Added proof-only imports of
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate` and
`WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction`.
No existing definitions or public signatures changed. No new modules or split obligations. The added K-injective preservation helper is
registered as a local instance only inside the proof-helper section.

Validation: the complete module compiles through `lcompile.py` without warnings
in 51.4 seconds, within the unchanged 60-second limit. The unchanged direct consumer
`Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct` also compiles against the new
module (29.4 seconds). `#print axioms integralConstructiblePullIso_comp` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`. The theorem signature was
compared with the original and is identical; all lines satisfy the 100-character limit.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.ProEtale.CondensedRing.integralConstructiblePullIso_comp`
(node `lem-weil-pbc-continuous-integral-pull-composition`).

Added 0 holes. There are no remaining `sorry` declarations in the delivered module.
All private helpers are proved. This is a proof, not a decomposition.

## No longer needed

Removed the proof-only import `Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse`:
the statement uses the existing small continuous coefficient rings, and the proof works
for arbitrary condensed coefficient rings through the existing module-object framework.
No declaration of that universe-interface module is used here.

Removed the redundant direct import `Sheaf.Paper.ContinuousIntegralScalarExact`.
Its exactness theorem remains necessary and is available through the public import
`Sheaf.Paper.ContinuousIntegralComparisons`; this removal does not prune that module
from the dependency closure.

The second reader compared the complete source import closures: removing the universe
interface also removes its otherwise unused dependency
`WeilConjectures.CategoryTheory.RingObjects.ContinuousMap` from this item's closure.
This does not assert that either module is absent from every target's closure.
No nodes are withdrawn. The existing unit route and three-step argument are retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or proof-plan correction was needed. The previously missing
derived normalization is now proved using the specified comparison units, rather than
assumed or split off again. The direct universe-interface import was unnecessary.

The first dry run requested a change record for the added proof-scope commands.
Added `coord/changes/continuous-integral-pull-composition-proof-scopes.md`, documenting
all eight downstream users and the unchanged public interface. Changed the initially
global private instance registration to a proved private lemma with an explicitly local
registration; no global instance is added.

## Second reading by C2

1. **Visible interface: PASS.** Read the repository module and the entire delivered
   module and compared their diff. The complete signature of
   `AlgebraicGeometry.ProEtale.CondensedRing.integralConstructiblePullIso_comp`,
   including its coefficient and characteristic section variables, is byte for byte
   unchanged. The original docstring and sole public import are unchanged. Every added
   declaration is private. `derived_square` explicitly composes existing isomorphisms;
   it selects no witness from an existence theorem. The K-injective instance attribute
   is local to `section Underived`. The scope change record explains the proof setup;
   no public definition or statement requires adaptation.

2. **Proof and trust: PASS.** Independently compiled the delivered module through
   `lcompile.py`: no errors or warnings, 46.9 seconds. Read each helper and the final
   proof. `comp_map_fac` uses the actual exact-functor comparison factorization;
   `comp_fac` uses `rightDerivedNatTrans_fac`. `square_fac` normalizes the concrete
   four-factor comparison, and `square_comp` cancels an invertible unit only after
   passing to K-injective representatives. Its underived equality is lifted degree by
   degree, then through the homotopy quotient; naturality supplies each intervening
   square. There are no `sorry` or forbidden declarations. The independent scratch
   copy with `#print axioms` compiled in 51.7 seconds and reported exactly `propext`,
   `Classical.choice`, and `Quot.sound`. The delivery also runs its all-declaration
   axiom probe.

3. **Split statements and hypotheses: PASS.** No statements were split off and no
   holes were added. Read ChangeOfCoefficients.lean, Derived/UpperLowerStar.lean,
   RightDerivedFunctor/CompConjugate.lean, the derived-adjunction transport theorem,
   and ContinuousIntegralComparisons.lean. The exactness assumption needed for scalar
   restriction to preserve K-injectives is explicit in the generic helpers and comes
   from `integralScalarExtension_exact` in the final application. Pullback exactness
   gives pushforward K-injective preservation. Nothing assumes properness, a cartesian
   square, or a nonzero object. Identity maps, the zero complex, and empty schemes are
   included by the unchanged hypotheses and the purely functorial calculations.

4. **Shortest route, imports and unit: PASS.** Repeated searches with different words:
   LeanFinder query "Composition coherence of right derived functors with an exact
   change of coefficients functor" returned natural-transformation composition and
   localizer comparison infrastructure, not this coefficient-change composition law;
   Loogle found `Functor.rightDerivedNatTrans_fac`, which the proof already uses.
   Searched lean/ and Mathlib's category theory sources for derived coefficient-change
   composition, comparison squares and conjugation compatibility. The similar
   comp-unit/factorization helpers in DerivedLerayComp.lean are private and cannot
   replace these helpers. Both added proof imports supply used theorems and are absent
   from the original import's transitive closure. The two removed direct imports are
   fully accounted for under No longer needed; all four old proof dependencies remain
   used. Read `dag/units/sk-thm-properbasechange.json`, including `realized`, and its
   blueprint section: no unit statement, step or realization is bypassed or changed.

5. **DAG and sources: PASS.** The node differs only in `proof` and `proof_origin`.
   Its unchanged `proof_deps` is exactly the union of the three steps' `uses`.
   Step 1 is `comap_lowerStar_comp`; step 2 is the unit-normalized `square_comp`
   instantiated in `derived_comap_comp`; step 3 is `derived_lowerStar_conjugate`,
   `pull_comparison_pasting`, and the bounded inclusion calculation. The final
   `Iso.ext`/`ObjectProperty.hom_ext` argument proves the exact node equality.
   Read Bhatt--Scholze Remark 6.8.15 in the local PDF text: it supplies the derived
   six-functor and adjunction framework; the specific coherence equality is proved
   here from the canonical constructions, rather than quoted as an explicit formula
   from that remark. Read the statements of the four dependency nodes and the Lean
   declarations they identify; the DAG's three-step route is faithfully implemented.

**Changes in the second reading:** no Lean or node repair was necessary. Added this
independent review and its validation evidence to report.md, and completed the pruning
account by naming the transitive ContinuousMap module removed from this item's closure. The existing change record
is `coord/changes/continuous-integral-pull-composition-proof-scopes.md`.

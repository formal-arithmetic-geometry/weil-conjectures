## What changed

Proved `Algebra.exists_popescu_separable_preparation_core` without changing its signature.
The proof constructs the actual polynomial quotient, applies the already proved
improve-presentation theorem, composes finite-type maps, and obtains finite presentation
over the Noetherian polynomial base. It then assembles the common exponent and proves the
universal evaluation, factorization identity, singular-ideal inclusion, and radical
comparison explicitly in Lean. New definitions contain no holes and choose no witnesses
from unproved existence theorems.

Two strictly smaller obligations are isolated in new modules: smoothness and finite
presentation of the explicit quotient, and a common strictly standard exponent for a
finite family of smooth opens with free differentials. The item and both new modules
compile together without warnings. The unit route is unchanged.

## Proved and sorry left

Closed the original hole in `Algebra.exists_popescu_separable_preparation_core`.
Added two holes:

- `Algebra.popescuPolynomialQuotient_smooth`, node
  `lem-weil-pbc-popescu-polynomial-quotient-smooth`.
- `Algebra.exists_common_strictlyStandard_power`, node
  `lem-weil-pbc-common-strictly-standard-power`.

This is a decomposition: one upper hole closed and two lower holes added, not a completed
axiom-free proof. The remaining statements have complete source-based proofs in their
docstrings. The quotient has no receiving algebra and no lifting property; the common
exponent lemma has no polynomial quotient, retraction, or Popescu-ideal assertion.

## No longer needed

Removed the direct proof imports `Sheaf.RingTheory.SingularIdealLocalizationSmooth`,
`Sheaf.RingTheory.SmoothFreeDifferentialsStrictlyStandardPower`, and
`Sheaf.RingTheory.SingularIdeal` from the item. The singular-ideal declarations remain
used through `Sheaf.RingTheory.PopescuPolynomialQuotientSmooth`; only their redundant
direct import was removed.
Every removed entry of the original item's `proof_deps` is listed here:

- `lem-weil-pbc-singular-ideal-localization-smooth`
- `lem-weil-pbc-polynomial-ring-smooth`
- `lem-weil-pbc-smooth-ring-map-base-change-composition`
- `lem-weil-pbc-smooth-ring-map-principal-localization`
- `lem-weil-pbc-smooth-ring-map-local-on-cover`
- `lem-weil-pbc-smooth-free-differentials-strictly-standard-power`

The first five steps are retained as proof dependencies of the explicit quotient node;
the last is retained as the source route of the common-exponent node, pending correction
of its Lean interface. They are no longer direct dependencies of the upper proof, rather
than mathematically discarded results. No whole dependency branch or globally unreachable
module is claimed as pruned. The improve-presentation step remains directly used.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the existing declaration
`Algebra.smooth_free_differentials_strictly_standard_power` in
`Sheaf.RingTheory.SmoothFreeDifferentialsStrictlyStandardPower` has a missing pair of
parentheses in `hstable`. Lean parses `Nonempty (Ω × (Fin s →₀ S) ≃ₗ[S] (Fin t →₀ S))`
as `Nonempty (Ω × ((Fin s →₀ S) ≃ₗ[S] (Fin t →₀ S)))`, not a linear equivalence
from the product module. A compiler attempt to construct the intended equivalence failed;
constructing its hypothesis as a structure asked for `Prod.fst` and `Prod.snd`, confirming
the parse. Its hypothesis is automatically satisfiable with s=t=0, independent of
stable freeness. The intended statement must instead parenthesize `(Ω × (Fin s →₀ S))`
before `≃ₗ`. I did not use this defective declaration or change its unheld module.
The correct finite-family specialization is stated separately with its actual smooth/free
hypotheses and left for proof from the repaired 07EZ(e) interface or its source argument.

## New nodes

`lem-weil-pbc-popescu-polynomial-quotient-smooth`: the concrete quotient, its actual base
map, finite presentation over that base, and smoothness of its generator and variable opens.
The proof includes empty generator families, zero localizations and d=0.

`lem-weil-pbc-common-strictly-standard-power`: a positive common exponent for a finite
family of elements whose localizations are smooth with free differentials. Finite
presentation makes the differentials finite; the empty family has exponent one. No
existing statements or definitions are changed, and no change records are needed.

## Second reading by S3

1. **Interfaces: pass.** Compared the delivered item with the repository using `diff -u`.
   The only differences are proof imports and the body of
   `Algebra.exists_popescu_separable_preparation_core`; its signature and existing
   docstring are byte for byte unchanged. Both other modules are new. No existing
   definition, target, public import or other module's signature changes, so no change
   record or forced adaptation is required.
2. **Kernel and data: pass as a decomposition.** Compiled all three modules together
   with `lcompile.py --all`, with no errors or warnings. In a scratch copy checked
   `#print axioms` for the main theorem, both remaining theorems and all three quotient
   definitions. The definitions use only `propext`, `Classical.choice`, `Quot.sound`;
   the three theorem results also use `sorryAx`, as expected from the remaining holes
   and open upstream proofs. The only literal holes delivered are the two named public
   theorems listed above. No forbidden declarations or hollow definitions occur. The
   quotient, relations and base map are explicit; the chosen generators come from
   proved Noetherian finite generation, and the improve-presentation theorem has a
   concrete symmetric-algebra proof. No definition chooses arbitrary data from an
   unproved existence statement.
3. **New obligations: pass.** Read Stacks 07FE's first two paragraphs and 07EZ(e), and
   checked each hypothesis against the Lean signatures. The quotient lemma has the
   actual quotient, finite presentation and its two classes of smooth opens, with no
   receiving algebra or universal lifting conclusion. Inverting a generator solves
   the relations separately for each corresponding Z variable; inverting X makes the
   generator ideal the unit ideal because n is positive. For d=0 the X conditions are
   vacuous; for m=0 an inverted X is nilpotent and its localization is zero. The common
   exponent lemma only concerns finite families of smooth opens with free
   differentials. Finite presentation gives finite differentials, so freeness implies
   the stable freeness needed in 07EZ(e); finitely many thresholds have a common upper
   bound, and the empty family permits exponent one. Zero localizations are included.
   Both statements are strictly smaller than the item and have source-based proof
   docstrings and matching nodes. Independent LeanFinder search for smooth
   localizations/free cotangent modules/Jacobian powers found standard-smooth and
   basis results, not either obligation; Loogle `MvPolynomial, Algebra.Smooth` and
   msearch grep for the new predicates/names found no match. Additional `rg` of
   Mathlib and both library roots found the polynomial smoothness ingredients, but
   no existing explicit quotient or correct common-exponent theorem. Independently
   compiled the reported defective parenthesization with a witness
   `⟨⟨0, LinearEquiv.refl _ _⟩⟩` at s=t=0; thus the old interface cannot certify the
   intended source argument and is deliberately unused. Neither remaining obligation
   has a short proof from the currently usable interfaces.
4. **Route and pruning: pass after reporting repair.** Read the proof from its target
   downward. It constructs B, applies improve-presentation, obtains finite
   presentation using the Noetherian base, and applies the finite-family exponent
   statement. The remaining evaluation proof explicitly kills the defining relations,
   verifies the base-map and A-map identities, and maps the singular-ideal inclusion
   before applying radical monotonicity. No shorter existing route was found. Imports
   in the upper proof are used, and public imports in the new modules support their
   signatures or actual definitions. Read `dag/units/sk-thm-p1.json`, including every
   `realized` entry: none is changed or bypassed by this below-unit reduction. The
   original report omitted the complete list of six removed direct DAG dependencies;
   that list is now explicit under `## No longer needed`, without claiming global
   module pruning.
5. **DAG agreement: pass.** Read all three delivered node records against the Lean.
   The item's steps and `proof_deps` describe finite generation, quotient smoothness,
   improve-presentation, finite presentation, common exponent, evaluation and radical
   comparison. Their union agrees with the named uses, and `proof_origin` identifies
   the source construction. The new nodes have their own statements, source, proof
   steps, dependency unions, search records, creation/blueprint records and Lean
   signatures; their chapter and unit match the item's. The defective upstream
   interface is explicitly recorded as awaiting repair in the exponent node's plan.

Second reading changed only this report: completed the six-node pruning inventory and
added the independent source, compilation, axiom, edge-case and dependency review.
No Lean proof, definition, signature or node needed repair. This delivery closes one
upper hole and adds two lower holes; it is not an axiom-free completion or a net hole
reduction.

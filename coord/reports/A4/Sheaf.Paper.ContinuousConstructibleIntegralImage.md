## What changed

The signature and visibility of
`AlgebraicGeometry.ProEtale.CondensedRing.continuousConstructible_integral_image_triangulated`
are unchanged. Its proof constructs zero and shift witnesses and proves cone closure by lifting a
rational arrow after multiplying by a power of ℓ. Multiplication by that power is proved invertible
on the actual rational derived category, using continuous functions, coefficient pullback, tensor
with the regular module, and homology. The integral Serre theorem supplies the triangulated source
category. No fullness of integral scalar extension is used.

Four new modules record genuine parts of the argument:

- `ContinuousIntegralCoefficientTelescope`: proved telescope of the actual pulled coefficient
  ring, including normalized leg equations. It reuses the explicit continuous-function diagram
  proved in `ContinuousIntegralScalarExact` through `import all`, without changing that API.
- `ContinuousConstructibleIntegralDenominators`: proved tensor comparison and unit equation,
  exact derived adjunction transport, and denominator clearing from finite-stage factorization.
- `IntegralConstructibleSequentialHom`: proved reduction from bounded constructible sources to
  constructible sheaf sources. The Hom-colimit property is triangulated by the proved filtered
  long exact Hom argument. The existing `DerivedCategory.prop_of_bounded` supplies Postnikov
  devissage. Concrete filtered-colimit representatives then give a finite stage and the exact
  original cocone leg; naturality removes the zero shift.
- `IntegralConstructibleSheafHom`: the remaining geometric sheaf-source continuity input for
  ordinary uncompleted integral coefficients and a common cohomological lower bound.

The target adds a normal proof import of the denominator module. New modules expose only imports
required by their statements. No existing definition or public signature changed. Generic transport
lemmas and local irreducibility avoid unfolding large derived-functor constructions; explicit local
exactness instances avoid repeatedly elaborating them. No time or heartbeat limits were raised.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.ProEtale.CondensedRing.continuousConstructible_integral_image_triangulated`.
Its proof contains no `sorry`.

Also proved with complete Lean proofs:
`AlgebraicGeometry.ProEtale.CondensedRing.integralCoefficient_localization_telescope`,
`AlgebraicGeometry.ProEtale.CondensedRing.continuousConstructible_clear_denominators`, and
`AlgebraicGeometry.ProEtale.CondensedRing.integralConstructible_hom_sequential_colimit`.

Added exactly one hole:
`AlgebraicGeometry.ProEtale.CondensedRing.integralConstructible_sheaf_hom_colimit`, node
`lem-weil-pbc-integral-constructible-sheaf-hom`. Its entire proof is `by sorry`.
It still needs the integral constructible sheaf case of Bhatt--Scholze 6.8.12: bounded-below qcqs
cohomology continuity, the finite integral model/perfect comparison on strata, and the open-closed
argument. Its docstring and node give the complete mathematical argument and the telescope passage
from bounded-below coproduct continuity to the stated canonical sequential comparison.

Existing finite-free Hom continuity and open-closed APIs have generic coefficient versions, but the
ready-made constructible-sheaf Hom continuity theorem takes rational finite-field coefficients.
That theorem cannot be applied to O_E. The new hole has a sheaf in degree zero as source; the
bounded-complex Postnikov passage, finite-stage extraction, coefficient localization and triangle
argument are already proved. This is one upper hole closed and one strictly geometric lower hole
added, a decomposition rather than a claimed ledger decrease. Existing imported holes, including
the integral kernel input to the Serre theorem, are unchanged.

Concrete existing inputs for the remaining geometric proof are
`AlgebraicGeometry.ProEtale.condensed_qcqs_pushforward_continuity` and
`AlgebraicGeometry.ProEtale.condensed_qcqs_globalSections_continuity_shift` in
`Sheaf.Paper.CondensedQcqsPushforwardContinuity`,
`AlgebraicGeometry.ProEtale.condensed_finite_free_hom_continuity` in
`Sheaf.Paper.CondensedFiniteFreeHomContinuity`,
`AlgebraicGeometry.ProEtale.CondensedRing.condensed_open_closed_recollement` in
`Sheaf.Paper.CondensedOpenClosedRecollement`, and
`CategoryTheory.homColimitProperty_extensions` in `Sheaf.CategoryTheory.HomColimitExtension`.
The new sheaf node records these geometric proof dependencies. The finite-free theorem uses a
common termwise lower bound and the chosen colimit cocone, so good truncation and cocone transport
are still necessary before applying it. These declarations are not unused proof imports in this
delivery; they are available inputs for the remaining node. The integral finite-model comparison
and extension from finite-free to finitely presented local models remain to be formalized.

Validation uses only `lcompile.py` and the required `deliver3.py --no-push` dry run. The second
reader should inspect the single remaining sheaf-source lemma as the next proving item.

## No longer needed

Removed `lem-weil-pbc-integral-constructible-bounded-below-compactness` from this item's direct proof
dependencies. Its completed coefficient category is not used. Its bounded-below compactness idea
survives in the ordinary-coefficient sheaf-source input. This removal does not assert that the old
node is globally unreachable from other targets. It has no attached Lean module to withdraw.

No original public import or Lean module was removed. The second reader removed the redundant
public import of `Mathlib.Algebra.Homology.HomologicalComplexLimits` from the two new Hom
modules, and the redundant proof import of
`WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory`
from the denominator module (already publicly imported by its adjunction dependency). The Serre input and actual integral coefficient
definitions remain needed. No rational full-faithfulness theorem, completed-category comparison,
essential-surjectivity theorem, or unbounded compact-object assertion is imported. The proper-base-
change unit's own statements and steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

The planned compactness dependency has `lean: null`, so its plan cannot simply be imported as a
Lean declaration. It also uses completed integral coefficients and additional geometric hypotheses,
whereas this item uses the ordinary derived category and only assumes topological Noetherianity.
The replacement records the exact ordinary-coefficient geometric input; all formal reductions from
it to the item are implemented.

The derived-category adjunction API gives its elementary unit formula through the homotopy category
localization. Its composite is canonically isomorphic to Q rather than definitionally equal. The
denominator proof localizes the exact complex adjunction directly along Q and proves the required
unit equation, retaining the comparison isomorphisms.

Mathlib's essential-image triangulated instance requires fullness. Integral scalar extension is not
full. The proof lifts arrows after a power of ℓ and uses the corresponding source automorphism in
the distinguished-triangle comparison.

The Hom-colimit property uses an indexing category in the Hom universe. The proof transports the
ordinary natural-number sequence along `AsSmall.equiv`; the representative returns a genuine
natural-number stage with the supplied original cocone leg.

## New nodes

`lem-weil-pbc-continuous-integral-coefficient-telescope` records the proved scheme coefficient
localization telescope and its leg equations. Both its construction and colimit are proved; no
unproved existence theorem supplies coefficient data.

`lem-weil-pbc-continuous-constructible-integral-denominators` records the proved tensor, exact
adjunction, and finite-stage denominator calculation.

`lem-weil-pbc-integral-constructible-sequential-hom` records the proved bounded-complex-source
reduction and concrete finite-stage extraction, using the existing bounded devissage API.

`lem-weil-pbc-integral-constructible-sheaf-hom` records the one remaining geometric hole, with a
constructible sheaf source in degree zero and all target shifts. The common cohomological lower
bound is explicit. Zero ranks, empty schemes, constant sequences and arbitrary colimit cocones
satisfy the formulas; unbounded compactness is not asserted.

The existing image-closure node's proof, proof dependencies and proof origin follow the Lean proof.
No definition, existing public signature, target or unit record changed. The change record `coord/changes/A4-continuous-constructible-integral-image.md` explains
the proof-local commands detected by the static interface check. No forced adaptation is needed.

## Second reading by A4

1. **Existing interfaces: PASS.** Compared every delivered module with the repository.
   Only `ContinuousConstructibleIntegralImage` exists there. Its sole public theorem's
   signature and original docstring are byte for byte unchanged; no existing definition
   changed. Its new helpers are private. The only changed existing node fields are
   `proof`, `proof_deps`, and `proof_origin`. The change record describes the local
   elaboration attributes, scopes and ambient-variable relocation; no consumer adaptation
   is needed. The four other modules and their declarations are new.

2. **Proofs and data: PASS, with the declared geometric hole.** Read all five modules.
   The telescope sequence, cocone and comparison isomorphisms are concrete constructions,
   reusing the proved continuous-function localization construction through `import all`.
   The denominator proof identifies the zeroth leg with the actual adjunction unit,
   transports that equation through localization along Q, and factors the adjoint of the
   specified arrow. `denominator_transfer` retains both representative and functor
   comparison isomorphisms. The image proof uses the integral Serre input, genuine
   source automorphisms and `isoTriangleOfIso₁₂`; it assumes no fullness. There is exactly
   one new direct `sorry`, the entire proof of the public named sheaf-source theorem.
   No new definition contains a hole or chooses data from unproved mere existence.
   No forbidden declaration or attribute is present. All files compiled locally.
   Explicit `#print axioms` checks in scratch copies give only `propext`,
   `Classical.choice`, and `Quot.sound` for the coefficient telescope. The other
   four public declarations additionally use `sorryAx`, from the declared open
   geometric input and existing imported holes; no other axiom occurs.

3. **Remaining statement and source: PASS after expanding its explanation.** Read
   Bhatt--Scholze Definition 6.8.10, Proposition 6.8.11(3), Lemma 6.8.12, the proof of
   Lemma 6.3.14, and Proposition 6.8.14(2) in the sandbox's paper text. The sheaf-source
   assertion uses ordinary O_E coefficients and a common *cohomological* lower bound;
   completion and a bound on the cohomological dimension are not assumed. Every shift
   is required because the Postnikov argument uses distinguished extensions. Checked
   zero sheaves, rank-zero presentations, empty X, torsion modules such as O_E/(ℓ),
   constant sequences and replacement of the colimit cocone: none requires a stronger
   hypothesis or an exceptional case. This is strictly the geometric sheaf case, not a
   restatement of image closure. The first sketch compressed the comparison between
   local finite presentations and fixed finite integral models. Expanded its docstring
   and node with the specialization, finite-component and continuous Smith-pivot
   argument; finite free DVR resolutions then also handle torsion. This comparison is
   part of the remaining proof obligation, not an established consequence of the
   kernel theorem's public statement. Independent searches with msearch LeanFinder,
   Loogle and grep, plus rg in lean/Sheaf, the upstream constructible sheaf library and
   Mathlib's triangulated API, found no ready-made integral continuity theorem. The
   rational `isIso_constructible_condensed_sheaf_hom_colimit` and finite-free generic
   continuity theorem were read; their coefficient and source restrictions prevent a
   direct application. Closing the geometric hole is not a few-minute consequence of
   those interfaces.

4. **Top-down proof and pruning: PASS after import cleanup.** The existing image
   theorem is reduced to denominator clearing, then to the explicit coefficient
   telescope and finite-stage Hom factorization. The latter uses the proved
   `DerivedCategory.prop_of_bounded` and `homColimitProperty_extensions`, rather than
   adding another Postnikov hole. Concrete filtered-colimit representatives and
   shift-zero naturality give the exact supplied cocone leg. Mathlib's essential-image
   triangulated instance requires fullness, so it does not shorten the cone argument.
   Removed the two redundant public complex-limit imports and the redundant direct
   derived-functor comparison import listed above. All remaining public imports supply
   statement syntax or definitions; the implementation imports are ordinary imports.
   The old compactness node is the only old proof dependency removed, and is listed in
   `No longer needed`. It concerns different completed coefficients and has no Lean
   module attached. The proper-base-change unit's `realized` statements and all three
   steps remain unchanged; this argument refines a tool below that unit's route.

5. **DAG and accounting: PASS.** Matched each new node's statement, coefficient ring,
   hypotheses, lower bound, canonical maps and Lean declaration with its module.
   Checked all required creation, source, search, blueprint, chapter, unit and Lean
   record fields and that each `proof_deps` is the union of the proof steps' `uses`.
   The existing node records Serre closure, denominators and triangle comparison;
   the new telescope, denominator and sequential-factorization nodes have Lean proofs.
   The sheaf node records the one unproved geometric input and its full proof plan.
   No unit record or target is edited. One original hole closed and one lower hole
   added is a decomposition with zero net hole decrease, as reported above.

Second-reading changes: removed three redundant imports; expanded the remaining geometric
hole's finite-model argument and source references in its docstring and DAG node; added
independent search records and this review. No theorem signature or proof body changed.

Final validation: `deliver3.py A4 Sheaf.Paper.ContinuousConstructibleIntegralImage --no-push`
printed `OK (dry run)` and passed compilation, declaration probes and preflight. Its
review class is CODEX (new nodes/modules, the declared remaining hole and the documented
local proof commands). The authorized delivery command follows this successful dry run.

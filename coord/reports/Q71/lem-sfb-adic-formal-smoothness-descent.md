## Worker report

This delivery adds the statement module
`Sheaf.RingTheory.AdicFormalSmoothnessDescent`, whose declaration is
`Algebra.formallySmoothAdic_iff_of_smoothCompleteLocalMap`.  The declaration has
the proof `sorry`, as required at stage 2.  The module imports the upstream
`WeilConjectures.RingTheory.FormallySmoothAdic` definition and the Mathlib
Noetherian, maximal-ideal, and adic-completeness interfaces.  It also imports
the available modules named by the proof dependencies so that the documented
stage-3 proof plan is visible in the file's import list.

The theorem binds three explicit commutative rings `R`, `C`, and `H`, each with
`IsLocalRing` and `IsNoetherianRing`.  The maps are explicit ring homomorphisms
`f : R →+* C` and `g : C →+* H`, each with its `IsLocalHom` instance.  Thus the
word “local” in the source is rendered by the exact local-homomorphism classes,
and the composite map is `g.comp f`.  The assumptions
`IsAdicComplete (IsLocalRing.maximalIdeal C) C` and
`IsAdicComplete (IsLocalRing.maximalIdeal H) H` render completeness of `C` and
`H`; there is no completeness hypothesis on `R`.

The formal-smoothness hypothesis is
`@FormallySmoothAdic C H _ _ g.toAlgebra (IsLocalRing.maximalIdeal H)`,
which renders that `C → H` is formally smooth for the maximal-ideal-adic
topology.  The result is an iff.  Its left side is
`@FormallySmoothAdic R C _ _ f.toAlgebra (IsLocalRing.maximalIdeal C)`,
rendering formal smoothness of `R → C` for the `C` maximal-ideal topology.  Its
right side is
`@FormallySmoothAdic R H _ _ (g.comp f).toAlgebra
(IsLocalRing.maximalIdeal H)`, rendering formal smoothness of `R → H` for the
`H` maximal-ideal topology.  `RingHom.toAlgebra` is used for each displayed
map, so the statement adds no unmentioned scalar-tower or residue-field
separability assumption.

The dependency declarations were read in full:

- `def-weil-pbc-noetherian-ring`: Mathlib declaration
  `IsNoetherianRing` in `Mathlib.RingTheory.Noetherian.Defs`, the predicate that
  every ideal is finitely generated.
- `def-weil-pbc-adic-completion`: Mathlib declarations `AdicCompletion` and
  `IsAdicComplete` in `Mathlib.RingTheory.AdicCompletion.Basic`; the latter is
  the adic completeness class used on the maximal ideals here.
- `def-weil-pbc-formally-smooth-adic`: upstream declaration
  `Algebra.FormallySmoothAdic` in
  `WeilConjectures.RingTheory.FormallySmoothAdic`; its lifting condition
  quantifies over square-zero ideals and maps killing a positive ideal power.

The five numbered proof steps in the docstring record the source argument:
the forward direction is the
two successive square-zero lifts; the reverse direction completes `R`, uses
the completion comparison and complete-source-target result, applies the
complete-local regularity criterion and regularity permanence through the
faithfully flat local map, and then applies the geometrically regular closed
fibre criterion.  The final quotient approximation in the completion returns
the lift to the original `R → C` problem.  The corresponding named proof
dependencies are all imported, including the Mathlib leaves that have
`mathlib_match` rather than `lean` records:

- `Mathlib.RingTheory.AdicCompletion.LocalRing` supplies the local completion
  instance, `AdicCompletion.maximalIdeal_eq_map`, and
  `AdicCompletion.isAdicComplete_self` for the local-completion and mod-ideal
  nodes.
- `Mathlib.RingTheory.AdicCompletion.Completeness` supplies
  `AdicCompletion.pow_smul_top_eq_ker_eval` for the mod-power node.
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra` supplies
  `Module.FaithfullyFlat.of_flat_of_isLocalHom` and
  `PrimeSpectrum.comap_surjective_of_faithfullyFlat`.
- The upstream proof modules supply `AdicCompletion.isNoetherianRing`,
  `Algebra.exists_formallySmoothAdic_completeSourceTarget`,
  `RingHom.isRegular_of_formallySmoothAdic`,
  `RingHom.flat_of_formallySmoothAdic`,
  `RingHom.isRegular_of_isRegular_comp`, `RingHom.IsRegular`, and
  `RingHom.formallySmoothAdic_of_flat_closedFiber`.
- `Sheaf.RingTheory.GeometricallyRegularLocalFieldAdicSmooth` supplies
  `Algebra.formallySmoothAdic_of_isGeometricallyRegular`.

I opened the local Stacks sources: `more-algebra.tex`,
`lemma-formally-smooth-completion` (07ED), `lemma-regular-permanence` (07NT),
and `proposition-fs-regular` (07PM), together with the second proof paragraph
of `stacks-geometry.tex`, `lemma-characterize-smoothness` (0DZS).
They give precisely the completion and regularity descent argument used here.

No new definition node or dependency repair module is needed: all notions in
the statement are supplied by the three recorded dependencies and Mathlib.
There is no statement correction and no `STATEMENT-DISPUTED` flag.

Edge cases checked before writing include: `R` may be noncomplete; no
separability condition is present; the local maps need not be injective; the
maximal ideals may be zero (for a field); and the definition's positive power
condition starts at `k ≥ 1`, exactly as in `Algebra.FormallySmoothAdic`.  Mixed
and equal characteristic cases are both covered.

Searches performed:

- `msearch.py ... leanfinder` for "Formal smoothness for the maximal ideal
  adic topology ascends and descends along a formally smooth local map of
  complete Noetherian local rings": eight hits on completion lifting,
  discrete formal smoothness and localization, but no exact theorem.
- `msearch.py ... loogle` for `FormallySmooth`, `AdicCompletion`: only
  `Algebra.FormallySmooth.exists_adicCompletionEvalOneₐ_comp_eq` matched, which
  is a different completion lifting lemma.
- `msearch.py ... leansearch` for "Adic formal smoothness is equivalent before
  and after a formally smooth local map of complete noetherian local rings":
  eight results about discrete smoothness and completion lifting, none stating
  this theorem.
- `msearch.py ... grep` with
  `FormallySmooth.*[Aa]dic|[Aa]dic.*FormallySmooth|IsSmoothAt` and with
  `formallySmooth.*completion|completion.*formallySmooth|FormallySmoothAdic`:
  returned 21 and one hits respectively; Mathlib contains no declaration of
  this local-ring ascent/descent statement.
- `rg` over `WeilConjectures/` and `Sheaf/` for the item id and for
  `FormallySmoothAdic` found the upstream definition and unrelated lemmas, but
  no duplicate theorem with this statement.

Validation: `scompile.py Q71 lem-sfb-adic-formal-smoothness-descent` compiled
`lean/Sheaf/RingTheory/AdicFormalSmoothnessDescent.lean` cleanly against the
live published build.  `set_option autoImplicit false` is enabled and all
universes are explicit.

The current example `Sheaf.CategoryTheory.CompactObject` is withdrawn; I read
its node and the upstream `WeilConjectures.CategoryTheory.CompactObject`
declaration instead. No item repair note is present. The first delivery dry
run found two metadata errors (missing `lean.branch`, trailing `:=` in
`lean.statement`); both were repaired. Only the item's `lean` field changes.
The independent delivery review is performed by the maintainer, as specified
in this worker's brief; no additional agent was started.

## Second reading by Q71

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

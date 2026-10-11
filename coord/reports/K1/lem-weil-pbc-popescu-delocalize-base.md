## Worker report

Item: `lem-weil-pbc-popescu-delocalize-base`.
Module: `lean/Sheaf/RingTheory/PopescuDelocalizeBase.lean`.
Declaration: `Algebra.exists_factorization_isElementaryStandardElement_of_localized_smooth`.
This is a statement only, with its one proof `sorry`; no definition or auxiliary theorem is added.
The declaration docstring describes all eleven proof steps and names their DAG inputs.
The node copy changes only `lean`.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The commutative rings R, A, Λ are `{R : Type u} {A : Type v} {Λ : Type w}` with
  `[CommRing R] [CommRing A] [CommRing Λ]`. Their universes are independent and explicit.
- A and Λ are R-algebras: `[Algebra R A] [Algebra R Λ]`.
- A has a finite presentation: `[FinitePresentation R A]`. The displayed polynomial quotient
  in the node is an explanation of this property, not a fixed additional presentation datum.
- The R-algebra homomorphism α is `(α : A →ₐ[R] Λ)`.
- The multiplicative subset of R is `(S : Submonoid R)`, including its unit and product closure.
- S⁻¹R is `Localization S`. S⁻¹A is `Localization (algebraMapSubmonoid A S)` and
  S⁻¹Λ is `Localization (algebraMapSubmonoid Λ S)`. The submonoids are exactly the images
  of S under the two algebra maps. Mathlib supplies their canonical localized-base algebras
  and scalar towers; no arbitrary or incompatible algebra structures are introduced.
- B' is `{B' : Type x} [CommRing B'] [Algebra (Localization S) B']`.
- Its smoothness is `[Smooth (Localization S) B']`.
- β' and γ' are the two explicitly bound `→ₐ[Localization S]` homomorphisms between
  the exact localized rings and B' in the node.
- S⁻¹α is `IsLocalization.mapₐ S (Localization S)
  (Localization (algebraMapSubmonoid A S)) (Localization (algebraMapSubmonoid Λ S)) α`.
  This is Mathlib's induced algebra map on the localizations, sending a/u to α(a)/u.
- The premise γ' ∘ β' = S⁻¹α is `hfactor : γ'.comp β' = IsLocalization.mapₐ ... α`.
- The conclusion supplies `∃ (B : Type (max u v w x)) (_ : CommRing B)
  (_ : Algebra R B) (_ : FinitePresentation R B) ...`. These existentially bound structures
  are used by the subsequent homomorphisms and elementary-standard predicate.
  The common upper universe permits the finite polynomial quotient over R from the proof
  (lifted to that universe if needed); it restricts none of the input rings or intermediates.
- The factorization maps are `(β : A →ₐ[R] B) (γ : B →ₐ[R] Λ)`.
- Their composite equals α: `γ.comp β = α`.
- There is a denominator s ∈ S: `∃ s : S` (membership is built into the subtype).
- Its image in B is elementary standard over R:
  `IsElementaryStandardElement (R := R) (algebraMap R B s.val)`.
  This is part (1) of the recorded dependency, not part (2), strictly standard.

Dependency declarations read and used:

- `def-weil-pbc-smooth-ring-map`: `Mathlib.RingTheory.Smooth.Basic`, `Algebra.Smooth`.
  Read its full class and docstring. Its recorded equivalence to the naive-cotangent criterion
  makes this the correct smoothness assumption.
- `def-weil-pbc-strictly-standard-element`: `Sheaf.RingTheory.StrictlyStandardElement`,
  `Algebra.IsElementaryStandardElement` (listed in the node's `lean.declarations`). Read both
  full predicate definitions and docstrings. The chosen predicate uses a finite presentation,
  an initial Jacobian minor and the remaining-relations ideal-square condition.
- `def-weil-pbc-finitely-presented-algebra`: the Mathlib leaf's `mathlib_match` names
  `Algebra.FinitePresentation`, `Mathlib.RingTheory.FinitePresentation`. Read its class and
  docstring; a missing `lean` record on this Mathlib leaf requires no dependency replacement.
  This module is imported transitively by both Smooth.Basic and StrictlyStandardElement.
- `def-weil-pbc-module-localization`: `Mathlib.Algebra.Module.LocalizedModule.Basic`,
  `LocalizedModule`. Read its full abbreviation and docstring. For rings we use the existing
  multiplicative specialization `Localization`, with its inherited ring structure, instead
  of trying to equip an arbitrary localized module with a ring. Mathlib's private
  `example_localization_eq_localizedModule` in the recorded module confirms
  `Localization S = LocalizedModule S R` definitionally. Localization.Algebra imports the
  recorded module transitively and supplies `IsLocalization.mapₐ` and its scalar-tower setup.
  Read the full signature and docstring of `mapₐ`, and the canonical localization algebra
  instance in Localization.Basic. No new localization notion is defined.

Source check: `literature/stacks-project/smoothing.tex` is absent on this machine, so I read
https://stacks.math.columbia.edu/tag/07F4 directly, including its proof. The statement agrees
with the node; finite presentation of B is explicit in the constructed finite quotient.
The fuller eleven-step proof in the DAG node is carried into the declaration docstring.
There is no statement correction and no STATEMENT-DISPUTED issue.

Edge cases checked before writing:

- S cannot be empty since it is a submonoid, which matches the source's multiplicative set.
- S may contain zero. No nonzero-denominator assumption is added; the zero localization
  remains allowed. The elementary-standard condition at zero imposes no nonvanishing.
- Trivial rings are allowed: no `Nontrivial` or domain assumptions.
- S = {1} is allowed; the premise then represents a smooth factorization over the original
  base. It is not replaced by smoothness of A or of Λ.
- Presentations with no generators or relations and c = 0 remain included in the existing
  elementary-standard definition. Fin n and Fin m may be empty; the 0-by-0 minor is 1.
- All characteristics are allowed. There are no Noetherian, field, injectivity, surjectivity,
  finiteness or nonzero assumptions on Λ or on the two factorization maps.
- Input universes u, v, w, x are explicitly bound; no test-object quantification can become
  vacuous through a smaller independent universe.

Searches for an existing statement (all remote searches recorded in searches.jsonl):

- `msearch.py leansearch`, query: "A smooth factorization over a localized base descends to a
  finitely presented algebra with an elementary standard element". Service unavailable,
  Internal Server Error. This gives no mathematical search verdict.
- `msearch.py leanfinder`, same query. Eight hits: finite-presentation localization and
  local smooth-locus results (`Algebra.FinitePresentation.of_span_eq_top_target_of_isLocalizationAway`,
  `IsLocalization.Away.finitePresentation`, `Algebra.FinitePresentation.of_isLocalizationAway`,
  `RingHom.finitePresentation_holdsForLocalizationAway`,
  `Algebra.IsSmoothAt.exists_notMem_isStandardSmooth`,
  `RingHom.finitePresentation_ofLocalizationSpanTarget`,
  `RingHom.finitePresentation_localizationPreserves`, `Algebra.IsSmoothAt.exists_notMem_smooth`).
  None descend the specified two-map factorization with an elementary-standard denominator.
- `msearch.py loogle`, query `Algebra.Smooth, IsLocalization`: no hits.
- `msearch.py grep`, query `delocaliz|[Ee]lementaryStandard|[Ss]trictlyStandard`,
  subdirectory `RingTheory`: no Mathlib hits.
- `rg -n` with the same expression in the source `WeilConjectures` and the project
  `lean/Sheaf`: source has no hits; the project has only the existing element definitions.
- `grep -rn lem-weil-pbc-popescu-delocalize-base` in source `WeilConjectures`: no hits.
- Full proposed declaration-name search in `dag/lean_names_upstream.json`, Mathlib,
  source `WeilConjectures`, and `lean/Sheaf`: no hits.

Validation: `scompile.py K1 lem-weil-pbc-popescu-delocalize-base` on the module passed,
exit code 0, compiled in 1.5 seconds, no warnings. The delivery dry run follows; the independent
second reading is intentionally left to the second worker.

## Second reading by K1

I reread the Stacks Project Smoothing Ring Maps, Lemma 07F4 (the `lemma-delocalize-base`
statement and lines 1946--1997) and matched every item of the node with the Lean signature.
The objects and hypotheses render as follows, with all verdicts **match**:

- `R`, `A`, and `Λ` are commutative rings with `Algebra R A` and `Algebra R Λ`.
- `A` is finitely presented over `R`, rendered by `[FinitePresentation R A]`.
- `α : A →ₐ[R] Λ` is the given homomorphism.
- `S` is a multiplicative subset, rendered by `S : Submonoid R`; the three localizations
  are `Localization S`, `Localization (algebraMapSubmonoid A S)`, and
  `Localization (algebraMapSubmonoid Λ S)`.
- `B'` is a commutative `Localization S`-algebra with `[Smooth (Localization S) B']`.
- `β'` and `γ'` have exactly the localized source, intermediate, and target types in the node.
- The factorization premise is exactly `γ'.comp β' = IsLocalization.mapₐ ... α`, whose
  fraction action is the stated `a/u ↦ α(a)/u` map.
- The conclusion existentially supplies a finitely presented `R`-algebra `B`, maps
  `β : A →ₐ[R] B` and `γ : B →ₐ[R] Λ`, the equality `γ.comp β = α`, and an `s : S`
  whose image satisfies `IsElementaryStandardElement (R := R) (algebraMap R B s.val)`.
  The universe `Type (max u v w x)` permits every input and intermediate universe.

The eleven proof clauses in the node are reflected in the declaration docstring in order:
standard-smooth retract, generators and relations, standard presentation, rescaling,
localization and denominator clearing, the `s₀` relation, the `sⱼ` and `s'ⱼ` relations,
construction of `B`, and both elementary-standard conditions. No clause is omitted or added.
The dependency declarations were checked: `Algebra.Smooth`, the project's elementary/strictly
standard predicates, `Algebra.FinitePresentation`, and `LocalizedModule`/localization APIs
provide the notions cited by the node; the two 07CH/07EY lemmas are used only in the recorded
proof steps.

Edge cases remain covered: `S` may contain zero or equal `{1}`, trivial rings are allowed,
zero generators or relations and `c = 0` are allowed, all characteristics are allowed, and
no domain, Noetherian, nontriviality, or map-surjectivity assumptions were introduced.
The independent universe binders and the maximum conclusion universe do not exclude any case.

I repeated the LeanSearch/LeanFinder/Loogle and grep searches recorded in `searches.jsonl` for
the theorem and its declaration name in Mathlib, `WeilConjectures`, and `lean/Sheaf`; they found
no existing theorem. Compilation with `scompile.py` succeeds with only the intentional `sorry`.
No mismatch was found, so no source, statement, dependency, or module change was required.

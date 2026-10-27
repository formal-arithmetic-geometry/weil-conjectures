## Worker report

States `AlgebraicGeometry.punctured_picard_local_extension_criterion` in
`Sheaf.AlgebraicGeometry.PuncturedPicardLocalExtensionCriterion`. One theorem,
with `sorry`; no new definitions or nodes, dependency repairs, or statement changes.
The module docstring cites EGA IV4 21.13.10, 21.13.8 and 21.13.1. Its theorem
docstring records all seven steps of the accepted proof, including the generic
noninvertibility obstruction, stalk comparison, spreading a rank-one basis, and gluing.

Hypothesis and conclusion correspondence:

- Scheme: `(X : Scheme.{u})`, using `AlgebraicGeometry.Scheme` from
  `Mathlib.AlgebraicGeometry.Scheme`. The universe `u` is explicitly declared.
- Locally Noetherian: `[IsLocallyNoetherian X]`, the recorded class from
  `Mathlib.AlgebraicGeometry.Noetherian`, equivalent there to a Noetherian affine cover.
- Every stalk an integrally closed domain: `hX : ∀ x : X,
  IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)`.
  This is exactly the recorded inline normal-domain form, using
  `IsIntegrallyClosed` from `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`.
  No integrality or connectedness condition is imposed on X itself.
- Closed subset: `(Z : Set X) (hZ : IsClosed Z)`, without a subscheme structure.
- Local dimension at least two at each point of Z: `hdim : ∀ z : X,
  z ∈ Z → 2 ≤ ringKrullDim (X.presheaf.stalk z)`; uses the recorded
  `ringKrullDim` from `Mathlib.RingTheory.KrullDimension.Basic`.
- Punctured local spectrum: the existing upstream `puncturedSpectrum` from
  `WeilConjectures.AlgebraicGeometry.PuncturedCurveBranches`, whose definition
  at line 33 is the open complement of `IsLocalRing.closedPoint R` in `Spec R`.
  Only `CommRing R` and `IsLocalRing R` are required for this definition; the
  strictly henselian/excellence assumptions of later results in that module
  are not required. Here R is the original stalk at z.
- Every invertible module on that puncture trivial: `hpic` quantifies over
  each `z ∈ Z` and every module L on that exact punctured scheme, assumes
  `L.IsInvertible`, and concludes `Nonempty (L ≅ SheafOfModules.unit _)`.
  Uses the dependency's `AlgebraicGeometry.Scheme.Modules.IsInvertible` from
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: locally isomorphic
  to the structure sheaf on Zariski neighbourhoods. No arbitrary Picard group
  or local-ring Picard group substitutes for the punctured scheme.
- Every open H: `∀ H : X.Opens`. Its complement of Z is encoded as the open
  `H.ι ⁻¹ᵁ (⟨Zᶜ, hZ.isOpen_compl⟩ : X.Opens)` of H.toScheme. Its points
  are precisely pairs `(x ∈ H, x ∉ Z)`. This is H minus Z with the induced
  open subscheme structure, not an arbitrary open or map.
- Canonical restriction: `Scheme.Modules.pullback` along the preceding open's
  `.ι`. `Scheme.Opens.toScheme` and `.ι` are the Mathlib open subscheme and
  open immersion from `Mathlib.AlgebraicGeometry.Restrict`, with
  `IsOpenImmersion` imported from the dependency's recorded module
  `Mathlib.AlgebraicGeometry.OpenImmersion`.
- Full faithfulness, including all module morphisms rather than only
  isomorphisms: for every A, B on H with `A.IsInvertible` and `B.IsInvertible`,
  `Function.Bijective (fun f : A ⟶ B ↦ (Scheme.Modules.pullback ...).map f)`.
  Surjectivity is existence of a lift of each restricted morphism, and
  injectivity gives uniqueness. This is exactly full faithfulness on the
  full subcategory of invertible modules; pullback preserves invertibility
  by the upstream `IsInvertible.pullback` instance.
- Essential surjectivity: for every invertible L on H minus Z, there exists
  `M : H.toScheme.Modules` with `M.IsInvertible` and a nonempty type of
  isomorphisms from its canonical restriction to L.

Source verification: read the online English EGA translation at
https://jcreinhold.github.io/ega/iv/34-ch4-21-divisors.html using Python urllib
and HTMLParser after the web reader refused the page's size. Definition 21.13.1
explicitly states the Hom bijection and essential-surjectivity clauses for every
open. Proposition 21.13.8 identifies local parafactoriality with the Hartogs
condition and punctured Picard triviality, with depth at least two in the
Noetherian case. Proposition 21.13.10 gives the closed-pair local criterion.
The node's normal Noetherian dimension-at-least-two specialization supplies
that Hartogs condition, as in its accepted reflexive-extension proof.
No correction or disputed statement was needed.

Dependency imports: all seven statement dependency modules are public imports;
the existing puncturedSpectrum helper's module is also public. Every proof
dependency with a current Lean record or Mathlib match is imported plainly
unless already a public statement import. For Mathlib matches with several
files, the recorded module is imported and the relevant integral-closure and
Noetherian modules are already public. Three proof-only nodes have no recorded
Lean interface: `lem-sfb-normal-reflexive-open-equivalence`,
`lem-sfb-affine-reflexive-module-comparison`, and
`lem-trf-finite-presentation-stalk-basis-spread`; no import exists yet for these,
and none is needed to state the theorem. Their proof steps are preserved in
the theorem docstring; no dependency statement is assumed as a new hypothesis.

Edge cases checked before writing: Z empty makes both pointwise hypotheses
vacuous and restriction is along the whole open; H empty and X empty give
categories of modules on the empty scheme and the usual unique empty module.
There is no Nonempty assumption on any scheme or open. If Z=X with X nonempty,
the dimension condition fails at a generic point of an integral normal chart;
thus the empty-target restriction does not assert a false extension result.
A field stalk or dimension-one stalk in Z is excluded exactly by the node's
dimension hypothesis. Disconnected normal schemes and non-quasi-compact X
are allowed. Nontrivial local Picard groups on the punctured spectrum are
excluded by hpic, rather than being confused with Pic(Spec of a local ring).

Searches actually run:

- msearch.py leanfinder: "On a normal locally Noetherian scheme invertible modules
  extend uniquely across a closed subset if all missing local rings have dimension
  at least two and punctured spectra have trivial Picard group". Eight hits:
  `CommRing.Pic.instSubsingletonOfIsLocalRing` and unrelated section/localization
  statements. The local-ring Picard statement is about Spec R, not the puncture;
  no match for this extension theorem.
- msearch.py loogle: `"IsInvertible", "pullback"`. Two vector-field pullback hits;
  neither concerns scheme modules.
- msearch.py grep: `parafactorial|punctured.*[Pp]icard|[Pp]icard.*punctured`.
  Zero Mathlib hits.
- msearch.py leansearch: "Line bundles and morphisms extend uniquely across a
  closed subset of a normal locally Noetherian scheme with trivial punctured
  local Picard groups". Eight hits concerning closed immersions, integral
  morphisms and topological trivializations; no match.
- Direct rg of WeilConjectures and Sheaf with the same parafactorial/punctured
  Picard expression finds the related principal-cycle theorem and the smooth
  nongeneric-punctured-line theorem's proof reference to this item; neither
  states this closed-pair extension criterion. A search for the intended Lean
  name in both roots and dag/lean_names_upstream.json finds no declaration.
- Direct item-id search in WeilConjectures finds no declaration. Search for
  `def puncturedSpectrum` finds the usable existing upstream definition read
  above. Existing source declarations are reused; none is redefined.

Validation: scompile.py NH lem-sfb-punctured-picard-local-extension-criterion
compiled the sole delivered module against the live server library, both sandbox
and canonical module passes, cleanly (3.1 s and 2.2 s). Both autoImplicit and
relaxedAutoImplicit are disabled; there are no unbound variables or universes.
All Lean lines have at most 100 characters. The node copy changes only lean,
and its statement record is the verbatim theorem signature before `:=`.

## Second reading by NH

No second worker was started, as instructed by the dispatcher. The worker delivers
directly; the maintainer's independent delivery review is the independent reading.
The clause mapping above is the worker's own final audit, not a claim of independent review.

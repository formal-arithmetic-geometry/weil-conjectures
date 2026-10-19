## Worker report

Repair of the returned stage-1-only delivery 207b2a4e1510. This delivery adds
`lean/Sheaf/Paper/RingedPushforwardCompletion.lean`, with the single statement
`CategoryTheory.ringedPushforward_completion` and its `sorry` proof. It copies the
current item node and changes only `lean` and additions of already recorded
statement dependencies. In particular `split_report.summary` is untouched. No
citations.json is claimed or needed: the source locations are identified below.

Source checked directly: literature/stacks-project/algebraization.tex,
lemma-pushforward-derived-complete (Tag 099J, starting at line 982), and
lemma-pushforward-commutes-with-derived-completion (Tag 0A0G, starting at line
1507). Also read the current blueprint main-20261015 scalar-extension proof,
which is the ancestor recorded on this node. Both the module docstring and the
theorem docstring name the blueprint id and Tags 099J/0A0G. The theorem docstring
contains all twelve current DAG proof steps, including each cited dependency,
the transition and unit squares, and the empty-list case.

Hypothesis and conclusion correspondence:

- Small sites: `C`, `X : Type u`, their `SmallCategory` instances, and
  `J`, `K : GrothendieckTopology` present the target and source. The same
  ambient set universe contains both small sites and their coefficient sheaves;
  `wX`, `wY` independently specify the derived morphism universes. The explicit
  derived-category instances for all slices are the localization-size data
  required by the recorded local completeness predicate. They impose no
  boundedness, Noetherian, finite cohomological dimension, or constructibility
  condition.
- Commutative ring sheaves: `RY : Sheaf J CommRingCat`,
  `RX : Sheaf K CommRingCat`. The standard `sheafCompose ... (forget₂ ...
  RingCat)` is only the coefficient conversion required by the recorded
  `ringedSiteModules` and `RingedToposMorphism`; it defines no alternative
  ringed-site or module category.
- Arbitrary ringed-topos morphism: `f : RingedToposMorphism RX RY`, with the
  displayed coefficient conversions. Its `inverse`, `direct`, `adj`,
  `leftExact` and `ringMap` encode exactly inverse image, direct image,
  their adjunction, finite-limit preservation and the structural ring map.
  `f.modules`, its `underlying` isomorphism and `module_linear` clause specify
  the module pushforward and the coefficient action induced by that ring map.
  This is the landed general-topos interface, not a site functor or an
  arbitrary additive functor. The recorded module-adjunction theorem is
  imported and supplies its tensor pullback adjunction for the proof.
- Target ideal: `IY`, `ιY : IY ⟶ SheafOfModules.unit ...`, `[Mono ιY]`
  encode an ideal subsheaf of `RY`; `[IY.IsFiniteType]` is the existing
  locally finitely generated module-sheaf predicate.
- Source image ideal: `IX`, `ιX`, `[Mono ιX]`, and `hImage`. For every
  ideal subsheaf `j : N ⟶ RX`, `hImage` equates factorization of
  `f.inverse.map (underlying ιY) ≫ f.ringMap` through the underlying sheaf
  of `j` with inclusion of `IX` in `N`. Taking `N = IX`, `j = ιX`
  gives containment of the structural image; the forward direction gives
  minimality, and the reverse direction follows from containment. This is
  exactly the generated ideal, including the sheaf-local nature of membership.
  It does not assert sectionwise generation before sheafification, nor assume
  the source ideal finite type separately. The displayed predicate uses only
  standard sheaf/module morphisms and factorization; no helper definition or
  arbitrary chosen map is introduced.
- Total unbounded right derived image: `Rf`, `ρ`, `hRf` state the total
  right derived functor of the specific `f.modules` on cochain complexes,
  along the quasi-isomorphism localization `DerivedCategory.Q`.
  `hCompute` states that its comparison is invertible on every K-injective
  complex. These specify the `Rf_*` named by the node, rather than impose
  an extra property on the ringed morphism. K-injective resolutions exist by
  the recorded dependency; the module imports that dependency and its
  universe-general companion.
- Completion reflection: `ΛX`, `ΛY`, `ηX`, `ηY` are endofunctors and
  natural units. `hCompleteX/Y` say their values are locally complete.
  `hReflectX/Y` assert the bijection on maps into every complete object.
  These are exactly the left-adjoint reflection properties supplied by
  `exists_ringedExtendedCech_completion_model`; they allow every reflector
  representing that adjoint. They do not assume commutation with `Rf`,
  projection formulas, tower comparisons, or the conclusion. There is no
  choice from a non-unique existence theorem.
- Local meaning of completeness: every occurrence is the recorded
  `IsLocallyDerivedRingedIdealComplete`, whose definition quantifies over
  every site object and every ring section in the ideal, and tests `IsZero`
  of the derived internal Hom from the sheafified away-localization on the
  slice. Thus all restriction, localization and internal-Hom objects are
  the existing definitions. The current `derivedInternalHomOfUniverses`
  dependency publicly imports this same small-site internal-Hom construction;
  no replacement Hom functor is introduced.
- Preservation conclusion: the first conjunct quantifies over every
  `M : ringedSiteDerived RX` and sends its local completeness to local
  completeness of `Rf.obj M`.
- Natural isomorphism conclusion: `∃ γ : Rf ⋙ ΛY ≅ ΛX ⋙ Rf` has at `M`
  precisely `ΛY(Rf M) ≅ Rf(ΛX M)`. The functor isomorphism includes
  naturality in all derived morphisms, as well as inverses.
- Unit normalization: `ηY.app (Rf.obj M) ≫ γ.hom.app M =
  Rf.map (ηX.app M)` is the node's equation in Lean's diagrammatic order.
- Arrow uniqueness: the last universal quantifier ranges over **all** arrows
  `a : ΛY.obj (Rf.obj M) ⟶ Rf.obj (ΛX.obj M)`, and asserts `a = γ.hom.app M`
  whenever the same unit equation holds. This is stronger than uniqueness
  among isomorphisms only and is exactly the node's stated uniqueness.
- No omitted exclusions: `M` is arbitrary in the unbounded derived category;
  there are no boundedness, constructibility, Noetherian, flatness, or
  structural-ring-isomorphism assumptions.

Recorded statement dependency declarations read and used:

- `def-weil-sheaf-of-modules-category`: `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`.
- `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`.
- `def-pur-kinjective-complex`: `Mathlib/Algebra/Homology/HomotopyCategory/KInjective.lean`, `CochainComplex.IsKInjective`.
- `prop-pur-kinjective-resolutions-exist`: `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`, `SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`.
- `lem-weil-pbc-ringed-topoi-module-adjunction`: `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`, `SheafOfModules.module_pullback_pushforward_adjunction`.
- `lem-weil-pbc-extended-cech-completion-model`: `Sheaf.Paper.ExtendedCechCompletionModel`, `CategoryTheory.exists_ringedExtendedCech_completion_model`.
- `def-pur-derived-internal-hom`: `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`, `CategoryTheory.derivedInternalHomOfUniverses`.
- `def-weil-pbc-ringed-topos-morphism`: `Sheaf.CategoryTheory.RingedToposMorphism`, `CategoryTheory.RingedToposMorphism`.
- `def-weil-pbc-locally-derived-ringed-ideal-complete`: `Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete`, `CategoryTheory.IsLocallyDerivedRingedIdealComplete`.
- `def-weil-pbc-ringed-derived-restriction`: `Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral`, `CategoryTheory.ringedDerivedRestrictionGeneral`.

The first added dependency supplies the already recorded general ringed-topos
morphism. The other two name the local-completeness predicate and the derived
category/restriction interface already used through the completion theorem.
No dependency declaration needs repair, and no new node is introduced.

Edge cases checked by reading the signature and definitions: the zero ideal
uses the empty generating list and gives identity completion; the unit ideal
has only zero complete objects; zero complexes are admitted; the empty/degenerate
site is admitted; the identity ringed-topos map is admitted; a non-isomorphic
structural ring map is admitted. The least-ideal property works also for zero
and unit ideals and never turns ideal-image membership into a presheaf image.
Both derived Hom-size universes are bound explicitly and independently.
There is no mathematical dispute or source-statement correction.

Searches for an existing statement (all actual tool runs):

- `msearch.py ... leanfinder`: "Derived direct image of a morphism of ringed
  topoi commutes with derived completion for a finite type ideal sheaf".
  Eight results included ordinary module pushforward/composition and local
  cohomology diagrams; none states the completion comparison.
- `msearch.py ... leansearch`: "Derived direct image of sheaves of modules
  commutes with locally derived ideal completion". Eight results concern
  ordinary module pushforward and its adjunction/composition, not derived
  completion.
- `msearch.py ... loogle`: "Functor.IsRightDerivedFunctor, SheafOfModules,
  IsLocallyDerivedRingedIdealComplete". No result; the public search service
  does not know the derived-functor identifier in this project's pinned API.
- `msearch.py ... grep`: "completion|IsRightDerivedFunctor" in
  Algebra/Category/ModuleCat. Five matches are unrelated linear-category
  completion comments, not ideal completion.
- `rg` in the source WeilConjectures tree for pushforward/completion patterns,
  the exact blueprint id and the proposed declaration: no matching statement.
  `rg` in dag/lean_names_upstream.json likewise finds no exact declaration.
- `rg` in lean/Sheaf finds formal-scheme completion comparisons,
  CompletedCoefficientPushforwardComparison and completion-reflection modules;
  these are different coefficient categories or different statements. The
  current ringed-site completion and morphism interfaces above are reused.
- For the image-ideal encoding, LeanSearch returned `Ideal.comap` and
  scheme-specific `Scheme.IdealSheafData` declarations. `blueprint_refs.py
  search 'image ideal'` found `def-nagata-extended-ideal`, whose schemes and
  quasi-coherent ideal data do not describe arbitrary ringed topoi. The
  statement therefore expresses the standard least-ideal characterization
  directly in sheaf/module morphisms, without introducing another definition.

Proof imports: every currently recorded proof-dependency module is imported
without `public` unless also needed for the statement. The current records for
`lem-weil-pbc-ringed-internal-hom-exact-restriction` and
`lem-weil-pbc-ringed-strict-tower-projection-morphism` are imported as
`Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus` and
`Sheaf.Paper.RingedStrictTowerProjectionMorphism`, respectively. Three proof-only
nodes currently have no Lean record or Mathlib match and cannot yet be imported:
`lem-sfb-unbounded-sections-localization`,
`lem-weil-pbc-ringed-derived-slice-localization`, and
`lem-weil-pbc-ringed-presentation-transport`.
Their steps and ids remain in the theorem docstring and DAG unchanged.

## Second reading by NB

I reopened the node, the Lean file and Tags 099J/0A0G for a separate self-check.
No separate worker was started: the dispatcher brief forbids sub-agents, and
this delivery is subject to the maintainer's independent reading.

Checked the orientations: `f` goes from the ringed topos for `RX` to the one
for `RY`; `f.modules` and `Rf` go from source modules to target modules;
`Rf ⋙ ΛY` is `ΛY Rf` in the node's function-composition notation.
The normalization is composed with `ηY` on the left in Lean, and its right
side is `Rf.map (ηX.app M)`. The final quantifier asserts uniqueness of all
arrows, not only invertible arrows. Both complete-object preservation and
naturality are present independently of that uniqueness assertion.

Checked each hypothesis listed in the Worker report against the actual
binders: finite type is required only on `IY`; `IX` is exactly the least
ideal containing the structural image; `f` has an arbitrary ring map;
`Rf` is specified by its right-derived universal property and K-injective
comparison; the completion hypotheses are the reflector properties, with no
commutation assumed. In particular the empty generating family is not dropped.
There is one theorem and no data definition containing `sorry`. Its docstring
has the twelve steps; the item node retains its original statement, proof,
source and summary. The `lean.statement` is extracted verbatim from the file.

Repair checklist: H1 is repaired by the real Lean module and complete node
binding; H1/H11 by these two required report sections and the clause-by-clause
reading; H2 by taking the current base node and preserving its summary;
no nonexistent citations artifact is cited. Validation results follow below.

## Repair of returned head 3450d4723efd

The independent reader reported a 60-second timeout when compiling the library
module. The retained packet was inspected and the prescribed initial dry run
was run before repair. The repair preserves the natural-language node statement,
all hypotheses and conclusions, all definitions, and the complete proof docstring.

The file-wide `backward.isDefEq.respectTransparency false` option was removed.
Lean now respects the default transparency boundary during backward elaboration,
instead of unfolding the large imported derived and sheaf constructions while
inferring coefficients. The formerly inferred coefficient-ring arguments of
`SheafOfModules.toSheaf` and category arguments of `DerivedCategory.Q` are written
explicitly. These arguments are exactly the coefficients and categories already
fixed by the surrounding binders; this changes no mathematical hypothesis.
The theorem-local heartbeat budget and the per-file 60-second process limit are
unchanged. All required statement and stated proof dependencies remain imported;
two proof imports were refreshed to their current recorded modules, as listed
above. No dependency node is edited and no helper or new node is added.

I compared the retained node with the current shared main snapshot: only `lean`
and the three already recorded additional statement dependencies differ. All
other node fields agree. The delivery wrapper rebases the retained packet on the
current server main branch. The stored Lean signature was extracted again from
the final file, and its date refreshed from UTC.

Self-check: the explicit ring arguments are the target ring for every occurrence
of `toSheaf` applied to `IY` or `ιY`, and the source ring for `N` and `j`. The two
explicit localization categories are respectively the target and source module
categories, in the same order as `ρ`. The least-ideal equivalence, finite-type
assumption only on `IY`, both complete-object reflection properties, preservation
of completeness, natural isomorphism, unit normalization and uniqueness of all
arrows are otherwise textually retained. The zero ideal, unit ideal, empty
Koszul family, identity morphism and arbitrary structural ring map remain
admitted. The file has one named theorem with a `sorry` proof and no data definitions.

Validation: final `scompile.py` returned exit 0 for both the sandbox and
library module names with no warnings or errors. The reported library check
completed in 40.3 seconds; compilation used the unchanged 60-second process
limit. The exact extracted signature matches `lean.statement`, every Lean line
is at most 100 characters, and the only `sorry` is the named theorem's proof.
Delivery dry-run/preflight and final push results are recorded below.

Final dry run: `deliver2.py --no-push` returned OK for `ae1f32a250`: server
preflight passes and the retained final module compiles. The staged packet is
exactly the report, the item node and `RingedPushforwardCompletion.lean`.

## Retained-packet validation for returned head 7ddac7229289

On 2026-10-18 the prescribed first action after reading this report was
`deliver2.py NB lem-weil-pbc-ringed-pushforward-completion --no-push`.
It returned exit 0 and `OK (dry run): commit 70e078416c passes the preflight
and compiles; nothing pushed`. Both the sandbox module and the library module
compiled within the unchanged 60-second per-file limit. Per the repair brief,
the saved elaboration repair above is retained without further Lean changes.

For the required self-check I reopened the saved Lean signature and node,
the current shared base node, and the source statements and proofs in
algebraization.tex at Tags 099J and 0A0G. The signature stored in `lean.statement`
matches the file exactly before `:=`. Relative to the current shared node,
only `lean` and the three reported additional statement dependencies differ.
The complete-object preservation conjunct, natural isomorphism, unit equation,
and uniqueness among all arrows are present with the orientations described
in the second reading. The finite-type assumption remains only on the target
ideal, and the least-ideal condition specifies the source image ideal. There
is no new mathematical hypothesis, definition, statement correction, or proof.
All lines satisfy the 100-character limit; the sole `sorry` is the named
item theorem. The retained explicit coefficient and localization-category
arguments address the elaboration timeout without changing that signature's
mathematical meaning. The wrapper performs the current-base delivery rebase.

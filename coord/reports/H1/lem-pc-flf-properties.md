## Worker report

Module: `Sheaf.AlgebraicGeometry.FiniteLocallyFreeStructureSheaf`.
Declaration: `AlgebraicGeometry.finiteLocallyFree_structureSheaf_properties`.
One theorem with proof `sorry`; no new notions, dependency replacements, or statement changes.
Server compilation passed without warnings (2.5 seconds).

Hypothesis and clause correspondence:

- Schemes X and S and their morphism f: the explicitly bound section variables
  `{X S : Scheme.{u}} (f : X ⟶ S)`, included in the elaborated theorem.
- Nonnegative integer degree d: `(d : ℕ)`.
- Finite locally free of degree d: `[f.IsFiniteLocallyFreeOfDegree d]`, precisely the
  recorded source class extending finite, flat, locally of finite presentation and
  the fibre-degree equality at every point.
- f_* O_X as an O_S-module: `(Scheme.Modules.pushforward f).obj
  (SheafOfModules.unit X.ringCatSheaf)`.
- Locally free of rank d: `SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} ... d`.
  This is the recorded open-cover notion, not just freeness of individual stalks.
- Every s in S: `∀ s : S` in the second conjunct.
- Residue field κ(s): `K(s) = S.residueField s`; local ring is `R(s) = S.presheaf.stalk s`.
- Stalk of f_* O_X: `P(s) = (f.base _* X.presheaf).stalk s`, the same structure
  sheaf direct-image stalk as a ring. The module pushforward of the unit has exactly
  this underlying additive stalk. Its R(s)-action is induced by the stalk of `f.c`.
- Tensor over O_{S,s}: `P(s) ⊗[R(s)] K(s)`, with the residue-field algebra supplied
  by `(S.residue s).hom.toAlgebra`.
- Scheme-theoretic fibre: `f.fiber s`, the Mathlib pullback of f along
  `S.fromSpecResidueField s`, exactly the scheme base change of def-pc-base-change.
- Fibre structure-sheaf sections: `Γ(f.fiber s, ⊤)`.
- Canonical isomorphism: `∃ e : ... ≃+* ...` with its value on every pure tensor
  `germ(a) ⊗ k` equal to restriction of a along `fiberι` multiplied by the scalar
  coming from `fiberToSpecResidueField` and `ΓSpecIso`. Every stalk element is a germ,
  and pure tensors generate the tensor product. Thus these equations determine the
  canonical ring map uniquely. Since k acts by this scalar, it is also a κ(s)-module
  isomorphism. Expressing the invertible canonical map as a ring equivalence with its
  prescribed values does not add a conclusion: the original canonical map is a ring map.

The binders U and hs range over all neighbourhoods of s. The universally quantified
hU is the inclusion required to type restriction to the whole fibre via `appLE`.
It is always available for such a neighbourhood: every point of the fibre maps to s,
by `Scheme.Hom.range_fiberι`, and hs puts s in U. It is a proof argument in the
conclusion, not an extra hypothesis on f or on the input data. No test neighbourhood
is excluded. This also pins down the map for schemes without global affine coordinates.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `Scheme.Hom.IsFiniteLocallyFree`, `Scheme.Hom.IsFiniteLocallyFreeOfDegree`.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFreeOfRank`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, `Scheme.residue`;
  the dependency's `Scheme.Hom.residueFieldMap` signature was read but is not needed here.
- def-pc-base-change's record is a bundle of conventions: it explicitly records
  `Limits.pullback f T.hom` as scheme base change. We use its Mathlib specialization
  `Scheme.Hom.fiber` from `Mathlib.AlgebraicGeometry.Fiber`, not moduleBaseChange,
  which describes a different clause of that dependency and is not used by this item.
- def-pc-morphism-conventions has no declaration: the morphism classes it names
  enter via the recorded finite-locally-free class.

Edge cases checked: d=0 permits empty source, zero pushforward and zero fibre section
ring; tensor and ring equivalence include the zero ring. Empty base makes the fibre
clause vacuous and permits every d, as does local rank on an empty scheme. Identity
maps give rank one and the usual residue map. No reducedness, Noetherian, surjectivity,
nonemptiness, field characteristic, or affineness assumption has been added. All schemes
are in the same arbitrary universe u; stalks and residue fields retain that universe.

Searches:

- msearch leanfinder: "finite locally free morphism pushforward structure sheaf rank
  residue field stalk fibre sections canonical isomorphism". Eight hits, chiefly
  StructureSheaf.toPushforwardStalkAlgHom and its localization lemmas, plus rankAtStalk;
  no theorem covering both clauses on arbitrary schemes.
- msearch loogle: "AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFreeOfDegree".
  Unknown identifier in the search service; the source definition was read directly.
- msearch grep: "finite.*locally.*free.*pushforward|stalkPushforward", AlgebraicGeometry.
  Three unrelated stalkPushforward uses; no exact theorem.
- msearch leansearch: "finite locally free pushforward structure sheaf rank fibre stalk
  residue field". Unavailable (Internal Server Error), recorded by the tool.
- rg in the source library, project library, and upstream name index for
  `lem-pc-flf-properties|flf_properties|pushforward_unit.*[Rr]ank` found the source
  `Scheme.Modules.isFiniteLocallyFreeOfRank_pushforward_unit` in
  `Modules/FinitePushforward.lean`: it states only the rank clause, so is not an exact match.
  Project `FinitePushforwardLocallyFree.lean` states locally constant rank without the
  canonical fibre comparison. `FiniteAffineFibreSections.lean` is restricted to spectra.
- rg for stalk/tensor/fibre sections in the module APIs and Mathlib found the germ,
  `appLE`, residue and pushforward-stalk APIs used above, but no complete statement.
  The full new declaration name was checked against source and Mathlib/project searches.

Source availability: the recorded blueprint and local Stacks tex are absent in this
checkout. Read the node's complete statement and three proof steps and the official
Stacks Tag 02KB at https://stacks.math.columbia.edu/tag/02KB, including its affine proof.
The module docstring transcribes all three DAG proof steps and names their dependencies.
No STATEMENT-DISPUTED or node fault was found.

## Second reading by H1

Read the item node, all six statement-dependency nodes and their recorded declarations,
the delivered Lean, the base-change convention module, and the affine-fibre dependency
module. No new definition nodes, dependency replacements, or statement corrections are
in this delivery; H12, H13 and the correction/citer audit therefore do not apply.

Source check: the local literature directory contains citation lists but neither the
blueprint Markdown nor Stacks tex. Read the official `morphisms.tex` directly at
https://raw.githubusercontent.com/stacks/stacks-project/master/morphisms.tex,
section `section-finite-locally-free`, definition `definition-finite-locally-free`
and lemma `lemma-finite-flat` (Tag 02KB), together with
https://stacks.math.columbia.edu/tag/02KB. The section assumes arbitrary schemes.
The lemma requires finite, flat AND locally of finite presentation; locally Noetherian
is only the optional alternative allowing the last condition to be dropped. The source
lemma itself establishes local freeness; the canonical fibre comparison is the affine
calculation spelled out in this DAG node, rather than a separately displayed clause
of Tag 02KB. Nothing in these sources imposes nonemptiness or characteristic conditions.

Object/hypothesis/conclusion checklist, written from the node before checking the Lean:

- Objects X, S: `{X S : Scheme.{u}}`. Read `Scheme` and `Scheme.Hom` in Mathlib:
  locally ringed spaces with local affine charts and their locally ringed morphisms.
  Verdict: exactly the scheme dependency, arbitrary schemes.
- Morphism f: section binder `(f : X ⟶ S)`, retained by the theorem because f occurs
  in its type. Verdict: arbitrary morphism between those same schemes.
- Integer d >= 0: `(d : ℕ)`. Verdict: includes zero and every nonnegative degree.
- Finite locally free of degree d: `[f.IsFiniteLocallyFreeOfDegree d]`.
  Read `FiberDegree.lean` definitions: this extends `IsFiniteLocallyFree`, itself
  extending `IsFinite`, `Flat`, `LocallyOfFinitePresentation`, and supplies
  `∀ s, f.fiberDegree s = d`. Read `fiberDegree` and `fiberAlgebra`: finrank of
  `Γ(f.fiber s, ⊤)` over `S.residueField s` via the second projection.
  Verdict: exactly the dependency, with no extra structure assumed on X or S.
- Object f_* O_X as O_S-module: `((Scheme.Modules.pushforward f).obj
  (SheafOfModules.unit X.ringCatSheaf))`. Read Mathlib's module pushforward and
  its sections formula: sections at U are sections of the unit at f inverse U,
  with scalars restricted along f. Verdict: the actual direct image, not pullback.
- First conclusion, locally free of constant rank d:
  `SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} ... d`.
  Read the recorded class, its local generators data and equivalence with local
  free-module isomorphisms; also read the scheme restriction signatures in
  `WeilConjectures/Mathlib/AlgebraicGeometry/Modules/Sheaf.lean`.
  Verdict: an open cover trivializing to d copies of O_S, not merely free stalks.
- Quantifier for every point: `∀ s : S` after the first conjunct. Verdict: every
  point, with a comparison depending on that point as the node requires.
- Local ring O_{S,s}: `R(s) = S.presheaf.stalk s`. Verdict: actual local ring.
- Residue field kappa(s): `K(s) = S.residueField s`. Read `residueField` and
  `residue` in Mathlib: quotient of that local ring by its maximal ideal.
  Verdict: correct field and canonical R(s)-algebra via `S.residue s`.
- Stalk (f_* O_X)_s: `P(s) = (f.base _* X.presheaf).stalk s`.
  The unit direct image has this underlying additive stalk; its scalar action
  is induced by `(TopCat.Presheaf.stalkFunctor CommRingCat s).map f.c`, the
  first local algebra instance. Verdict: the same stalk and the correct action.
- Tensor over O_{S,s}: `P(s) ⊗[R(s)] K(s)` with those two local algebra instances.
  Verdict: correct tensor and order; no change of base or auxiliary field.
- Scheme fibre X_s: `f.fiber s`; read Mathlib's definition
  `pullback f (S.fromSpecResidueField s)` and its two projection definitions.
  Read `BaseChangeConventions.lean` against def-pc-base-change: this is exactly
  its scheme base change, not the separate module-base-change declaration.
  Verdict: scheme-theoretic fibre, not the underlying set or geometric fibre.
- Sections Gamma(X_s,O): `Γ(f.fiber s, ⊤)`. Verdict: structure-sheaf global sections.
- Second conclusion, canonical map is an isomorphism: `∃ e : ... ≃+* ...` with
  the displayed equation for every neighbourhood U of s, section a and scalar k.
  The right side restricts a along `fiberι` and multiplies by the image of k along
  `ΓSpecIso.inv` then `fiberToSpecResidueField.appTop`. Verdict: exactly the
  canonical comparison, with invertibility, rather than an arbitrary equivalence.
  Every stalk element is a germ, and pure tensors generate the tensor product,
  so these equations determine the map. Taking the germ of 1 specifies the
  residue-field action as well. The canonical comparison is a ring homomorphism;
  asserting its ring equivalence is equivalent to its being an isomorphism here.
- Apparent extra binder hU: `⊤ ≤ (f.fiberι s) ⁻¹ᵁ (f ⁻¹ᵁ U)` is universally
  quantified inside the conclusion. Read `range_fiberι`: every fibre point maps
  under f to s. Hence hs supplies this inclusion for EVERY neighbourhood.
  Verdict: a restriction-map typing proof, not an added hypothesis or vacuous
  specification. Proof irrelevance removes any dependence on its witness.

Edge cases: d=0 is admitted; for empty X the stalk, tensor and fibre section rings
are zero rings, which ring equivalences permit. Empty S makes the point clause
vacuous and permits local rank d for any d. Empty covers are allowed exactly when
they cover the empty base; no external index type is fixed. Zero modules and empty
fibres are included. Characteristic is unrestricted. u is explicitly bound and
arbitrary; all schemes/rings/stalks use the common ambient universe, which can be
chosen large enough for any input pair. There is no independently smaller universe
of test objects, no nontriviality requirement on the tensor or section ring, and no
Noetherian, affine, reduced, or surjective assumption.

Independent searches (different phrasing from the worker):

- msearch leanfinder: `finite morphism residue field tensor stalk direct image global
  sections of fibre`. Eight hits: pullback triplet tensor maps and fibre projection
  declarations; none states the two conclusions for arbitrary schemes.
- msearch loogle: `AlgebraicGeometry.Scheme.Hom.fiber, TensorProduct`.
  Successful search, zero hits.
- msearch leansearch: `finite flat morphism direct image structure sheaf locally free
  residue field comparison`. Service unavailable with Internal Server Error;
  no negative mathematical verdict inferred from this failure.
- rg independently in Mathlib, WeilConjectures and project AlgebraicGeometry for
  `stalk.*[Tt]ensor`, `[Tt]ensor.*stalk`, `fiber.*[Ss]ections`, `[Ss]ections.*fiber`,
  and the full new declaration name. Found fibre-section degree definitions,
  tensor pullback stalk comparisons, and the landed affine fibre theorem, but no
  exact statement. Opened the affine fibre theorem: restricted to Spec A/Spec B,
  so it cannot replace this statement. Opened the upstream
  `Scheme.Modules.isFiniteLocallyFreeOfRank_pushforward_unit`: only the rank
  clause, with no canonical fibre comparison. It therefore is not an exact match.

H5/H6/H8/H9: no hollow data, private definition or proved theorem. The two local
algebra instances are the actual stalk and residue maps. The sole theorem has `sorry`.
Its docstring names the source and blueprint id and records all three DAG proof
steps and their dependencies. All variables/universes are bound; the recorded
`lean.statement` equals the source signature verbatim. Imports supply the morphism
class/fibre operations, module pushforward, and the recorded local-rank predicate.

Mismatches found: none. Changed only this appended second-reading report; kept
all correct Lean, the node statement, dependencies and the Lean record unchanged.
Validation: server scompile passed in 2.5 seconds, exit 0, with no warnings.

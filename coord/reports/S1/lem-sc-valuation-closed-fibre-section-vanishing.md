## Worker report

The module `Sheaf.AlgebraicGeometry.ValuationClosedFibreSectionVanishing` states
`AlgebraicGeometry.Scheme.Modules.exists_nonzero_maximalIdeal_section_eq_zero`.
Its only proof is `sorry`; no definitions or other theorems are introduced.

Source read: Stacks Project Tag 0EX8, proof of
`lemma-triviality-generic-fibre-valuation-ring`, the paragraph expressing the residue
field as the filtered colimit of A/pi and applying Limits section descent.
The local literature file is absent on this machine, so the source was opened at
https://stacks.math.columbia.edu/tag/0EX8 . The extracted descent assertion needs only
finite presentation, not the properness and flatness used elsewhere in that proof.

Hypotheses and clauses, in order:

- The valuation ring A is `(A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]`.
  Mathlib's ValuationRing is a divisibility-total integral domain and supplies its local
  ring instance; `IsLocalRing.maximalIdeal A` is the specified maximal ideal.
- A is not a field is `hA : ¬ IsField A`.
- The scheme and morphism are `{X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))`.
  Finite presentation in the convention dependency means the three instances
  `[LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]`.
- The invertible module is `(L : X.Modules) [L.IsInvertible]`, using the recorded
  dependency declaration without a duplicate definition.
- The section is `(s : L.val.obj (op ⊤))`, the module's global sections.
- The closed fibre is the categorical pullback of f along the spectrum map of
  `Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)`; its projection to X is
  `pullback.fst f (Spec.map (CommRingCat.ofHom ...))`.
- `hs` states that the canonical tensor-pullback adjunction unit, applied to L and
  evaluated on the top open and s, is zero. Its codomain is the pushforward of the
  tensor pullback, evaluated on the top open; this is the section on the inverse
  image of the top open, i.e. the entire closed fibre. No choice of section map is
  a hypothesis: `Classical.choose (exists_tensorPullbackAdjunction ...)` is pinned
  by that theorem to the canonical sectionwise tensor formula.
- The conclusion `∃ π : A, π ≠ 0 ∧ π ∈ IsLocalRing.maximalIdeal A ∧ ... = 0`
  says exactly nonzero pi in the maximal ideal and zero restriction to the
  pullback along the quotient by `Ideal.span {π}`. This is A/pi, not localization
  or the reduced closed subset. The same canonical unit renders this restriction.

Dependency declarations read and used:

- `def-weil-scheme-morphism-properties` is a convention-only collection. Its
  finite-presentation clause directs to Mathlib's `AlgebraicGeometry.LocallyOfFinitePresentation`
  (`Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`), `QuasiCompact`, and
  `QuasiSeparated` (`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`). The latter
  says the diagonal is quasi-compact. No module belongs to the collection itself.
- `def-sc-invertible-module`: `WeilConjectures.AlgebraicGeometry.Modules.Invertible`,
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`; its signature and docstring were
  read, including its local triviality field.
- The existing `Sheaf.AlgebraicGeometry.TensorPullbackAdjunction` declaration
  `Scheme.Modules.exists_tensorPullbackAdjunction` is used for canonical section
  pullback. Its full signature and sectionwise unit formula were read.
- `Mathlib.RingTheory.Valuation.ValuationRing`, `ValuationRing`, with its integral
  domain prerequisite and inferred local ring instance, is used directly.

Edge cases checked: the empty scheme is allowed and both section restrictions are
zero; the nonfield assumption still guarantees a nonzero element of the maximal
ideal. Zero sections are allowed. Fields are expressly excluded as required (their
maximal ideal has no nonzero element). Arbitrary rank and nondiscrete valuation
rings and all characteristics are allowed; there is no uniformizer hypothesis.
Using the same universe for A and X imposes no geometric restriction by universe
lifting; there is no quantified test family in a smaller universe.

Searches actually run:

- msearch leanfinder: "section of invertible sheaf vanishes on closed fibre valuation
  ring then vanishes modulo nonzero maximal ideal element": eight hits about
  structure-sheaf evaluation/basic opens and tilde sections, no matching statement.
- msearch loogle: "ValuationRing, Ideal.Quotient.mk": zero hits.
- msearch grep: "closed.fibre|valuation.*section|section.*valuation" in
  AlgebraicGeometry: one residue-field documentation hit, no matching statement.
- msearch leansearch: "section vanishing on the closed fibre of a valuation ring
  vanishes modulo a nonzero element": service unavailable, Internal Server Error.
- rg in WeilConjectures and lean/Sheaf for valuation/closed-fibre section terms:
  no matching theorem; pullback-section searches found the existing upstream
  pullback API and the project's canonical tensor-pullback adjunction.
- grep -rn of the item id in WeilConjectures: no hit.
- rg in dag/lean_names_upstream.json for valuation and closed-fibre names: no
  declaration for the item.

Server validation: scompile.py compiled this module in 2.0 seconds with exit code 0,
no errors and no warnings. No node faults or statement corrections were needed.


## Second reading by S1

I independently opened the node, its two statement dependencies and their recorded
signatures, the delivered Lean module, the tensor-pullback and adjunction modules,
and Mathlib's valuation-ring, finite-presentation and pushforward definitions.
No new nodes or dependency modules are present. No statement correction is present.

Source checked: the local Stacks .tex checkout is absent. I read the actual TeX at
https://raw.githubusercontent.com/stacks/stacks-project/master/more-morphisms.tex,
label `lemma-triviality-generic-fibre-valuation-ring`, and the rendered
https://stacks.math.columbia.edu/tag/0EX8 and
https://stacks.math.columbia.edu/tag/01Z0.
The containing lemma assumes properness, flatness, generic triviality, an integral
closed fibre, and a generic global-sections condition. Those are used in other
steps; its section-descent sentence follows from 01Z0 for the qcqs base-change
system and a quasi-coherent module. Thus the extracted node correctly needs
finite presentation and invertibility, without those extra hypotheses.

Object/hypothesis/conclusion checklist (each verdict: matches):

- Valuation ring A: `(A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]`.
  The domain prerequisite is part of the valuation-ring notion, not an added
  hypothesis; `PreValuationRing.cond'` is total divisibility.
- Maximal ideal m: `IsLocalRing.maximalIdeal A`. The local-ring instance is
  `ValuationRing.isLocalRing`; no arbitrary ideal or extra chosen local structure.
- A not a field: `(hA : ¬ IsField A)`, before the geometric data.
- Scheme X and f to Spec A: `{X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))`.
- f of finite presentation: `[LocallyOfFinitePresentation f] [QuasiCompact f]
  [QuasiSeparated f]`. The convention dependency expressly means Stacks 01TP,
  including quasi-separatedness. These are exactly its constituent properties.
- Invertible O_X-module L: `(L : X.Modules) [L.IsInvertible]`, the recorded
  `Scheme.Modules.IsInvertible` from the source's Modules.Invertible module.
  Its `exists_isoUnit` field is local rank-one triviality, hence quasi-coherence.
- Global section s: `(s : L.val.obj (op ⊤))`; no generator or nonzero assumption.
- Closed fibre X_0: the pullback of f along `Spec.map (CommRingCat.ofHom
  (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))`. Spec is contravariant,
  so this has base-change direction Spec(A/m) to Spec(A).
- Restriction zero on X_0: `hs` evaluates the chosen adjunction's unit at L,
  `op ⊤`, and s, and equates it to zero. The existing
  `exists_tensorPullbackAdjunction` asserts the sectionwise canonical formula
  for its witness, so `Classical.choose` is not an unspecified restriction map.
  `pushforward_obj_obj` identifies its codomain with sections of the tensor
  pullback on the inverse image of top, i.e. the entire closed fibre.
- Existential element: `∃ π : A, π ≠ 0 ∧ π ∈ IsLocalRing.maximalIdeal A ∧ ...`.
  Both nonzero and maximal-ideal membership are present; π is chosen after s
  and its vanishing hypothesis, with no uniformity requirement.
- Zero on X times Spec(A/π): the final equality uses the identical canonical
  unit for `pullback.fst f (Spec.map (CommRingCat.ofHom
  (Ideal.Quotient.mk (Ideal.span {π}))))`. The quotient is by the principal
  ideal, not the radical or a localization; the equality is scheme-theoretic
  section vanishing, not merely vanishing at points.

Edge cases: X and its closed fibre may be empty; s may be zero; the zero module
is admitted wherever invertibility holds (in particular on the empty scheme).
The nonfield assumption excludes the empty nonzero-maximal-ideal index system
and guarantees the existential is possible for the zero section. No discrete
valuation, rank, Noetherian, characteristic, or nonempty-scheme hypothesis occurs.
There is no n or finite indexing family in the statement. The universe u is
explicit and arbitrary; A, its quotients, Spec and the schemes inhabit one ambient
universe, which can be enlarged for any given geometric data. No quantified test
objects live in an independent smaller universe. Every binder is explicit and
no universe/variable is unbound.

Independent searches, using wording different from the first worker:

- msearch leanfinder: "global section of line bundle zero after residue field
  base change descends to quotient of valuation domain". Eight hits, including
  Scheme residue evaluation and ModuleCat.Tilde section formulas, no match.
- msearch loogle: "ValuationRing, IsLocalRing.maximalIdeal". Two discrete
  valuation-ring equivalence theorems, neither a section-descent statement.
- msearch leansearch: "For a valuation domain not a field, a line bundle section
  zero on the residue fibre is zero after reduction modulo some nonzero nonunit".
  Service unavailable (Internal Server Error); no mathematical verdict inferred.
- msearch grep: "maximalIdeal.*section|section.*maximalIdeal|valuation.*vanish".
  Three unrelated polynomial/valuation-support hits, no match.
- rg in Mathlib/AlgebraicGeometry, WeilConjectures/AlgebraicGeometry and the
  project's lean/Sheaf/AlgebraicGeometry for section vanishing/residue/quotient,
  closed fibres and the proposed declaration. Hits concern Cartier zero loci,
  Henselian finite-etale fibres, residue evaluation and other local vanishing
  results. None states this valuation-ring quotient-descent assertion.

H4-H9 review: shared notions are imported, not copied. There are no definitions,
no hollow data and no proved auxiliary theorem; the only proof is `sorry`.
Module and declaration docstrings name 0EX8 and the exact blueprint id. The
proof docstring renders both DAG proof steps, including fixing a quotient stage
and invoking `lem-sc-valuation-limit-qcoh-section-descent`. Imports are used;
namespace, names and lines follow the conventions. The node's `lean.statement`
is verbatim the theorem signature. No mismatch was found; no Lean or node change
was needed. Only this independent second-reading section was appended.

Second-reader validation: scompile.py compiled the unchanged 54-line module on
the server in 2.0 seconds, exit code 0, with no errors or warnings.

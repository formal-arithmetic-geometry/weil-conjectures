## Worker report

The module states `AlgebraicGeometry.torsion_sections_generic`. It uses `X : Scheme` with
`[IsIntegral X]`, a module `F : X.Modules` with `[F.IsQuasicoherent]`, a nonempty open
`U : X.Opens`, and a section `s : F.val.obj (op U)`. Torsion at a point is rendered as an
`a : X.presheaf.stalk x` with `a ≠ 0` and scalar annihilation of the germ
`TopCat.Presheaf.germ F.val.presheaf U x x.property s`. The first clause is existence of such
an `x : U`; the second is universal quantification over `x : U`; the third is vanishing of the
generic germ, with generic-point membership obtained from `genericPoint_spec` and `[Nonempty U]`.
The fourth clause is rendered by the same generic-germ equality, since that is the canonical
value of the image in the generic-point pushforward.

Dependencies used are Mathlib `AlgebraicGeometry.IsIntegral`, the existing project declaration
`AlgebraicGeometry.RingedSpace.IsCoherent`/the `SheafOfModules.IsQuasicoherent` predicate from
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`, Mathlib's
`AlgebraicGeometry.Scheme.functionField` concept (the generic stalk), and Mathlib's stalk and
germ declarations `TopCat.Presheaf.stalk` and `TopCat.Presheaf.germ`. The module imports
`Mathlib.AlgebraicGeometry.FunctionField`, `Mathlib.AlgebraicGeometry.Modules.Sheaf`, and
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`.

Edge cases checked: `U` is explicitly nonempty, so the generic point lies in `U`; the torsion
witness requires a nonzero stalk element; the empty scheme is excluded by `[IsIntegral X]`; and
no finite-type or characteristic assumption is introduced.

Searches: `msearch.py leanfinder` and `loogle` for torsion sections/generic stalks found no
matching sheaf theorem; grep over Mathlib's AlgebraicGeometry and ModuleCat sheaf sources found
only generic stalk/function-field primitives and no four-clause theorem; `rg` over the source
repository and project found no existing declaration of this node.

## Proposed correction withdrawn

The first worker's proposed change to clause (4) was unnecessary. The existing upstream
`Scheme.Modules.skyscraper` and `toSkyscraper` give the sheaf and its canonical map. The
second reader restored the base node's original statement and removed `statement_change`.
There is therefore no statement correction in the delivery.

## Earlier second reading (a previous round; superseded)

The signature was compiled remotely with `scompile.py`; it has one named theorem and the only
` sorry` is its postponed proof. The four source clauses, all hypotheses, and generic-point
membership are represented in the signature.

## Second reading by K1

I read Stacks Divisors, `lemma-torsion-sections` (Tag 0AXR), in
`/home/ubuntu/c1-stacks-review/divisors.tex`, lines 1639–1665, including the preceding
section introduction. It assumes only an integral scheme, a quasi-coherent module, a
nonempty open, and a section. It states four mutually equivalent conditions, including
vanishing of the image in the generic-point pushforward. The source imposes no implicit
Noetherian, separated, finite-type, or characteristic hypotheses here.

Object/hypothesis/conclusion checklist, with the node and final Lean open:

- Scheme X: `(X : Scheme.{u})`, arbitrary universe u; matches.
- Integral X (`def-pc-integral-scheme`): `[IsIntegral X]`; matches. I read
  Mathlib `Properties.lean:240`: nonempty X and domain sections on every nonempty open.
  This is the recorded definition and agrees with the affine version of the node.
- Generic point η: `genericPoint X`; matches. Integral X is irreducible and sober, so
  choosing Mathlib's canonical generic point excludes no case: the generic point is unique.
- Quasi-coherent O_X-module F (`pqf-def-coherent`): `(F : X.Modules)` and
  `[F.IsQuasicoherent]`; matches. I read `Sheaf/AlgebraicGeometry/Coherent.lean` and Mathlib
  `Sheaf/Quasicoherent.lean:251`. The dependency explicitly reuses this Mathlib predicate
  (locally a cokernel of free modules) for its quasi-coherent clause, equivalent on schemes
  to the stated affine-associated-module description. Its named `IsCoherent` declaration
  is for a different clause of the same dependency and would impose the wrong hypothesis.
- Nonempty open U: `(U : X.Opens) [Nonempty U]`; matches. Nonempty as a subtype is exactly
  existence of a point in U, with no compactness condition.
- Section s: `(s : F.val.obj (op U))`; matches F(U), the presheaf of modules underlying F.
- Stalk and scalar ring (`def-weil-pbc-module-stalk`): I read Mathlib's module-stalk
  instance and `germ_ringCat_smul` in `ModuleCat/Stalk.lean:167–180`. The stalk of
  `F.val.presheaf` has the canonical action of `X.presheaf.stalk x`; matches, with no
  additional module instance or privately defined stalk.
- Torsion convention: `∃ a : X.presheaf.stalk x, a ≠ 0 ∧ a • germ(s) = 0`; matches
  annihilation by a nonzero local-ring element, allowing s_x = 0.
- Clause (1): first TFAE entry, `∃ x : U, ∃ a, ...`; matches the existential point test.
- Clause (2): second entry, `∀ x : U, ∃ a, ...`; matches the universal point test.
  The annihilator may depend on x; no uniform annihilator is required.
- Clause (3): third entry is the equality to zero of the generic germ. The supplied
  membership proof comes from `genericPoint_spec` and Nonempty U; matches, without an
  additional hypothesis. Its small membership tactic is not a postponed auxiliary theorem.
- k(X) (`def-sc-function-field`): I read its recorded module
  `Sheaf/AlgebraicGeometry/FunctionField.lean`, whose integral-scheme clause explicitly
  reuses Mathlib `Scheme.functionField`. I read `Mathlib/AlgebraicGeometry/FunctionField.lean:37`:
  this abbreviation is `X.presheaf.stalk (genericPoint X)` and its integral instance is a
  field. Thus the scalar annotation `[X.functionField]` is exactly the required ring.
- Clause (4): fourth entry is `(Scheme.Modules.toSkyscraper LinearMap.id).app U s = 0`,
  with the full generic-stalk linear-map type written explicitly; matches vanishing of the
  image as a SECTION in j_* F_η, not merely its value at one chosen point. I read upstream
  `FlatPullbackStalk.lean`: `SkyscraperSections` (84), `skyscraper` (175), `toSkyscraper`
  (277), and `toSkyscraper_app_apply` (294). Sections are `PLift (η ∈ U) → F_η`, scalars act
  by germs, restrictions are precomposition, and the canonical map assigns the generic
  germ. This is precisely the pushforward from the one-point scheme Spec k(X).
  The generic-point morphism is canonically determined, not an extra arbitrary morphism
  hypothesis. These are existing concrete upstream definitions, also used by the delivered
  sibling `TorsionSubsheafQuotient.lean`, not newly duplicated definitions.
- Mutual equivalence: `List.TFAE [condition1, condition2, condition3, condition4]`;
  matches every pair of conditions, in source order. I read Mathlib `Data/List/TFAE.lean`.

Edge cases: the empty scheme is excluded by the source's integrality, exactly as by
`IsIntegral`; the empty open is excluded by the source, exactly as by Nonempty U. The
zero module and zero section are included (1 is a nonzero annihilator). Spec of a field
is included: torsion means zero and all four conditions agree. For O_X over an integral
scheme nonzero sections fail all four tests. A torsion associated module over Spec Z and
a direct sum with O_X are included; the latter retains both torsion and nontorsion sections.
No natural-number parameter or index set occurs, so n = 0 and empty index sets introduce
no omitted cases. Any characteristic and any universe u are allowed. No finiteness,
coherence, affine, Noetherian, or separated assumption was added.

Independent searches (all `msearch.py` calls logged in `searches.jsonl`): LeanFinder query
“Quasi coherent module section killed by nonzero local scalar if and only if its generic
germ is zero” returned germ-zero neighbourhood results and tilde-localization primitives,
including `ModuleCat.Tilde.smul_stalk_no_nonzero_divisor`, but no four-condition theorem.
Loogle `TopCat.Presheaf.germ` returned germs and specialization lemmas, no torsion theorem;
an earlier string query was rejected and was not counted as a negative result. LeanSearch
“Four equivalent torsion tests for a section of a quasicoherent sheaf on an integral scheme”
returned HTTP 500, recorded as unavailable, not a successful negative search. Mathlib grep
`torsion.*section|section.*torsion|skyscraper` in AlgebraicGeometry found only an elliptic
curve torsion-polynomial section. I independently ran `rg` with
`torsion.*(section|generic)|((section|generic).*torsion)` on upstream WeilConjectures and
project Lean: no declaration states this node; the sibling torsion-subsheaf theorem cites it.
Searching `skyscraper|toSkyscraper` located the concrete upstream definitions described
above. The DAG already has `def-pc-ringed-module-skyscraper` (general ringed-space
functor); I read its signature and source description. No new definition node or dependency
module is needed: this delivery uses existing canonical scheme constructions.

Mismatches and repairs:

1. The first signature `A ↔ B ∧ C ∧ C` only related A to a conjunction, whereas the node
   requires all four conditions equivalent. Replaced it by `List.TFAE`.
2. Its fourth clause repeated the generic-germ equality and did not state zero of the
   pushforward image. Replaced it by zero of the canonical skyscraper-map section.
3. The proposed node correction claimed the original pushforward was untypable. The
   existing scheme skyscraper disproves that claim. Restored the ORIGINAL node statement
   and withdrew `statement_change`; no unit or source statement changes. I read the sole
   direct citer `lem-sc-torsion-subsheaf-quotient` (both its node and Lean), which uses the
   kernel of this very `toSkyscraper` map and remains valid. An exhaustive DAG search found
   only this direct citer (so there is no second direct citer to open); I also read the
   torsion step of `lem-sc-riemann-roch`, its ancestor/transitive citer, whose criterion
   is preserved. No `holds` correction records remain necessary.
4. The theorem docstring compressed the proof into one sentence, omitting the localization
   calculation, the two implications, and dependency references. Expanded it to the four
   node proof steps, with the cited dependency ids.
5. Added the conventional copyright/license/authors header, and imported the used upstream
   skyscraper module and Mathlib TFAE; removed the redundant direct Modules.Sheaf import.

The node's `lean.statement` is the final signature verbatim after whitespace normalization.
There is one named theorem, with its proof `sorry`, and no new definition or auxiliary
proved theorem. All variables/universes are explicitly bound, each line has at most 100
characters, source and blueprint docstrings are present, and every import is used.
Remote `scompile.py` compiled the final 67-line module cleanly in 2.2 seconds (exit 0),
with no warnings. No global build was run.

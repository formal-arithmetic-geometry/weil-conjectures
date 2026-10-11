## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity` states
`AlgebraicGeometry.Scheme.essSurj_pullback_finiteEtale_of_henselianRing`, with `sorry` as
its entire proof. No definition, additional node, dependency repair or statement correction
was needed. The server compiled the file cleanly in 1.8 seconds.

Hypothesis and clause correspondence:

- A commutative ring and ideal: `{A : Type u} [CommRing A] (I : Ideal A)`.
- The pair is henselian: `[HenselianRing A I]`, exactly the notion selected by the
  dependency's recorded note. This includes the Jacobson-radical condition and the
  root-lifting condition equivalent to the dependency's idempotent-lifting wording.
- `S = Spec A` and `S₀ = Spec (A/I)`: `Spec (.of A)` and `Spec (.of (A ⧸ I))`.
  The canonical closed immersion is
  `Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))`.
- The proper morphism `Y → S`: `(f : Y ⟶ Spec (.of A)) [IsProper f]`.
- `Y₀ = Y ×_S S₀`, its structure morphism and immersion into `Y`:
  `{Y Y₀ : Scheme.{u}}`, `(i : Y₀ ⟶ Y)`, `(f₀ : Y₀ ⟶ Spec (.of (A ⧸ I)))`,
  and `h : IsPullback i f₀ f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))`.
  This is the universal-property presentation of the fibre product, and forces `i`
  to be its first projection (hence a closed immersion). It introduces no additional
  assumption on the fibre: any chosen fibre product satisfies this square.
- Finite étale schemes over `Y` and `Y₀`:
  `(@IsFinite ⊓ @Etale).Over ⊤ Y` and `(@IsFinite ⊓ @Etale).Over ⊤ Y₀`.
  The infimum imposes both object properties; `⊤` imposes no condition on the
  morphisms beyond the built-in commutative triangle, as required by the node.
- Pullback `i*`: `MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ i`.
  Its object is the fibre product with second projection; its morphism map is the
  induced morphism of fibre products.
- For every finite étale `V → Y₀`, existence of finite étale `U → Y` and an
  isomorphism `U ×_Y Y₀ ≅ V` **over `Y₀`**: the conclusion `.EssSurj`.
  `Functor.EssSurj.mem_essImage` expands to existence of an object in the source
  and `Nonempty` of an isomorphism in the target finite étale over-category.
  Thus this is precisely all the node's existential clauses, including the
  compatibility with the structure maps, without full faithfulness or uniqueness.

Dependency declarations read and used:

- `def-weil-pbc-henselian-terminology`: the record in
  `Sheaf.RingTheory.HenselianTerminology` explicitly directs henselian-pair users to
  `HenselianRing` in `Mathlib.RingTheory.Henselian`; this is the binder used here.
  The strictly henselian local-ring definition is not needed.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsProper` from
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`. Its universally closed condition gives
  quasi-compactness, so its locally-of-finite-type field means finite type here.
- `def-pc-base-change`: the recorded module
  `Sheaf.AlgebraicGeometry.BaseChangeConventions` directs scheme-base-change users to
  Mathlib's `Limits.pullback` / `Over.pullback`. The cartesian square here uses
  `CategoryTheory.IsPullback`; the finite étale pullback functor uses that same chosen
  `Limits.pullback`. The dependency's module-pullback definition does not apply.
- `def-weil-pbc-finite-etale-category`: its `mathlib_match` specializes
  `CategoryTheory.MorphismProperty.Over` from
  `Mathlib.CategoryTheory.MorphismProperty.Comma` and
  `CategoryTheory.MorphismProperty.Over.pullback` from
  `Mathlib.CategoryTheory.MorphismProperty.OverAdjunction`, exactly as used here.
- The single import `WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale` supplies
  these declarations and the recorded existing instance
  `AlgebraicGeometry.isStableUnderBaseChange_isFinite_inf_etale`; no private instance
  or category definition is introduced. I read the stronger theorem
  `Scheme.isEquivalence_pullback_finiteEtale_of_henselianRing` there, but it is not
  exactly this node's statement: it additionally asserts full faithfulness.
- `CategoryTheory.Functor.EssSurj` and its docstring were read in
  `Mathlib.CategoryTheory.EssentialImage`.

Edge cases checked before writing:

- `I = 0`: the closed-fibre map is an isomorphism and the statement includes this case.
- Empty `Y` or empty cover `V`: allowed; no nonemptiness or surjectivity is imposed
  on finite étale covers, and empty covers lift.
- Zero ring: allowed by `CommRing`; its spectra and proper schemes over it are empty.
- `I = ⊤` with a nonzero ring is already excluded by the henselian-pair definition's
  Jacobson-radical condition, not by an extra hypothesis in the theorem.
- No local, Noetherian, G-ring, completeness, connectedness or characteristic assumption
  occurs. Those conditions occur only in intermediate proof cases.
- `u` is explicitly declared and arbitrary. The ring and schemes inhabit the same
  ambient universe, as in the existing theorem; no finite-size universe is fixed.
  All term variables are explicit binders and no auto-bound implicits are used.

Searches for an existing exact statement (performed by the supplied `msearch.py` and
recorded in `searches.jsonl`):

- LeanFinder: `Finite etale covers of the closed fibre of a proper scheme over a
  henselian pair lift to the proper scheme`: eight hits on étale morphisms, their
  categories and finite algebra results; none state this essential-surjectivity result.
- Loogle: `HenselianRing, CategoryTheory.Functor.EssSurj`: zero hits.
- Mathlib grep: `henselian|finiteEtale`, subdirectory `AlgebraicGeometry`: zero hits.
- LeanSearch: `Essential surjectivity of finite etale base change for a proper scheme
  over a henselian pair`: unavailable, Internal Server Error. No verdict is claimed
  for this unavailable service.
- `rg` of the source and `lean/Sheaf` for the item id and finite-étale lifting /
  henselian properness found `HenselianFiniteEtale.lean` and its stronger equivalence
  theorem, but no exact essential-surjectivity theorem. The item id has no source hit.
- `rg` of Mathlib, the source, `lean/Sheaf` and `dag/lean_names_upstream.json` for
  `essSurj_pullback_finiteEtale_of_henselianRing`: zero hits before writing.

Source verification: the local Stacks source file is absent on this machine, so I opened
[Stacks Tag 0GS2](https://stacks.math.columbia.edu/tag/0GS2), including its three
essential-surjectivity cases. The statement agrees. The docstring follows those cases
and names every node of the supplied proof. The imported proof's phrase "local base"
is inapplicable to a general henselian pair; the docstring instead states the source's
specialization argument using properness and the Jacobson-radical condition. Likewise,
the general case uses henselizations of pairs, not an extra local-ring assumption.
No statement fault or STATEMENT-DISPUTED claim was found.

## Second reading by E1

Independent verdict: the Lean signature says exactly what the node says. I opened the
sandbox node and module, all four statement-dependency nodes and their recorded source
signatures, and the upstream `HenselianFiniteEtale.lean`. No mathematical mismatch or
missing notion was found. I changed only this report; the module and node record remain
as written by the first worker.

Source reading: the local Stacks checkout is absent. I read the actual `pione.tex`
label `lemma-finite-etale-on-proper-over-henselian-pair` from
https://raw.githubusercontent.com/stacks/stacks-project/master/pione.tex and checked
[Tag 0GS2](https://stacks.math.columbia.edu/tag/0GS2). The ambient assumptions are only a
henselian pair and a proper scheme over its ring. The three extra sets of assumptions
in the proof are reductions, not hypotheses of the result. The item selects the
essential-surjectivity part of the source's equivalence theorem.

The objects, hypotheses and conclusion, listed independently from the node:

1. A commutative ring `A` and ideal `I`: `{A : Type u} [CommRing A] (I : Ideal A)`.
   Verdict: exact; no field, nonzero-ring or local-ring instance is added.
2. The pair `(A,I)` is henselian: `[HenselianRing A I]`. Verdict: exact via the
   dependency's explicit recorded convention in `HenselianTerminology.lean`.
   I read Mathlib's class: its fields are the Jacobson condition and monic simple-root
   lifting. The node's finite-algebra idempotent condition is equivalent to the usual
   henselian pair by [Tag 09XI](https://stacks.math.columbia.edu/tag/09XI), condition (3).
   Thus the Jacobson condition here is not an extra mathematical hypothesis.
3. The two base schemes are `Spec A` and `Spec(A/I)`: `Spec (.of A)` and
   `Spec (.of (A ⧸ I))`. Verdict: exact, with quotient-map immersion
   `Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))`.
4. A scheme `Y` with proper morphism to `Spec A`: `{Y : Scheme.{u}}`,
   `(f : Y ⟶ Spec (.of A)) [IsProper f]`. Verdict: exact. I read `IsProper` in
   `Mathlib.AlgebraicGeometry.Morphisms.Proper`; its separated, universally closed and
   locally finite type fields give precisely properness, since the universally closed
   instance supplies quasi-compactness (`UniversallyClosed.lean:167`).
5. The closed fibre `Y₀ = Y ×_S S₀` and its immersion `i`: `{Y₀ : Scheme.{u}}`,
   `(i : Y₀ ⟶ Y)`, `(f₀ : Y₀ ⟶ Spec (.of (A ⧸ I)))`, and
   `h : IsPullback i f₀ f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))`.
   Verdict: exact universal-property presentation, including both projections. A chosen
   fibre product always supplies this square; conversely it identifies any such square
   with that fibre product. Closed immersion of `i` follows by base change, so no
   independent hypothesis is missing. I read `BaseChangeConventions.lean`: its scheme
   clause explicitly uses Mathlib's `Limits.pullback` and `Over.pullback`. Its module
   pullback definitions are irrelevant here and are not privately copied.
6. Every finite étale `Y₀`-scheme `V`: the target of the displayed functor is
   `(@IsFinite ⊓ @Etale).Over ⊤ Y₀`. Verdict: exact. I opened `MorphismProperty.Over`
   in `Comma.lean:615` and its constructors: the object structure map satisfies both
   finiteness and étaleness; `⊤` allows every commuting `Y₀`-morphism. This is the
   specialization recorded by `def-weil-pbc-finite-etale-category`.
7. For each such `V`, a finite étale `Y`-scheme `U` exists: the conclusion is
   `(MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ i).EssSurj`.
   Verdict: exact quantifier order. I opened `Functor.EssSurj.mem_essImage` and
   `Functor.essImage` in `EssentialImage.lean`: they mean, for every target object `V`,
   there exists a source object `U` and `Nonempty (F.obj U ≅ V)`.
8. The isomorphism is `U ×_Y Y₀ ≅ V` over `Y₀`: I read the pullback functor's object
   and map in `OverAdjunction.lean:101-108`. Its object is the fibre product with
   `pullback.snd`, and its map is the induced pullback lift. The isomorphism above lives
   in the finite étale over-category, hence respects both structure maps. Verdict:
   exact; it asserts neither uniqueness nor full faithfulness nor naturality choices.

Edge cases: `I = 0`, the zero ring, empty `Y`, and the empty finite étale cover are
all allowed. For nonzero `A`, `I = ⊤` fails henselianity itself, rather than an extra
binder. There is no restriction on characteristic, connectedness, completeness,
Noetherianity or G-ring status. There is no index family or integer `n` in the statement;
`n = 0` in the docstring's thickenings is the original closed fibre. The universe `u`
is arbitrary and explicitly bound, with schemes and rings in a common ambient universe;
any collection of the schemes in the node can be placed in such an ambient universe.
All term variables are bound explicitly. The required pullbacks and base-change stability
are existing instances, including upstream's `isStableUnderBaseChange_isFinite_inf_etale`;
no additional instance hypothesis appears in the signature.

Independent searches, with queries different from the worker's (recorded in
`searches.jsonl` by `msearch.py`):

- LeanFinder: `Every finite étale scheme over the reduction of a proper scheme modulo a
  henselian ideal is the reduction of a finite étale scheme`: eight hits about standard
  étale algebras, étale loci and composition; no matching theorem.
- Loogle: `"EssSurj", "pullback"`: no hits.
- LeanSearch: `Lifting a finite étale cover from the reduction modulo a henselian ideal
  for a proper scheme`: service unavailable (Internal Server Error). No negative
  mathematical verdict is inferred from that failure.
- Mathlib grep in `AlgebraicGeometry`:
  `EssSurj.*(Etale|hensel)|(Etale|hensel).*EssSurj|henselian.*proper|proper.*henselian`:
  no hits.
- Independent `rg` across upstream `WeilConjectures/` and the project's `lean/Sheaf/`
  for finite étale lifting, henselian essential surjectivity, and the exact declaration
  name and item id: the related hits are topological invariance, Galois category
  essential surjectivity, and upstream `HenselianFiniteEtale.lean`. I opened that module:
  `Scheme.isEquivalence_pullback_finiteEtale_of_henselianRing` has the same binders but
  concludes `.IsEquivalence`, hence is strictly stronger than this node's statement.
  It is not an exact existing declaration for this delivery. There is no exact-name
  collision in Mathlib, upstream, the project's modules, or `dag/lean_names_upstream.json`.

Delivery review: there are no new definition nodes, dependency modules or statement
corrections to inspect. The single import supplies the notions and needed instances.
There is one named theorem whose entire proof is `sorry`, and no definitions, private
copies, hollow data or proved auxiliary statements. Header, namespace, topic directory,
line width and both source/blueprint docstrings follow the contract. The proof docstring
carries all four node steps and their dependency ids. In particular it correctly uses
properness plus the Jacobson condition for specialization to the closed fibre, rather
than the node proof's misleading phrase `local base`; it also correctly uses henselizations
of pairs in the general case. These are already correct in the worker's file, so no
rewrite is warranted. The node's `lean.statement` is verbatim the declaration signature.

Validation: `scompile.py E1 lem-weil-pbc-finite-etale-lifting-essential-surjectivity`
compiled the single delivery module on the server in 1.9 seconds, exit code 0,
with no errors or warnings.

## Reviewer R-fes1015 (FIX)

The delivered IsPullback/`Over.pullback … i` form was mathematically equivalent but spelled the
closed fibre differently from the landed sibling K1 bf4691187
(lem-weil-pbc-finite-etale-lifting-approximation), and imported the upstream module carrying the
parent's stronger `isEquivalence` theorem. Restated in K1's exact spellings: closed fibre
`pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))` with `pullback.fst`, finite
étale objects `(@IsFinite ⊓ @Etale).Over ⊤`, and for every `V` an `∃ U` with an isomorphism in
`Over Y₀` of `pullback.snd U.hom (pullback.fst f _)` with `V.hom` (the node's explicit
∀ V ∃ U form); imports as K1 (Mathlib plus the HenselianTerminology record module). The sibling
statement is then exactly this one plus `IsGRing A`. Recompiled clean (L sandbox, 1.8 s).

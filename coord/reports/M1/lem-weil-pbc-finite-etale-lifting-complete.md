## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteEtaleLiftingComplete` states
`AlgebraicGeometry.Scheme.exists_finiteEtale_lift_of_isAdicComplete`, with proof `sorry`.
It introduces no definitions and does not correct the node.

Hypothesis and clause correspondence:
- The commutative Noetherian ring A is `{A : Type u} [CommRing A] [IsNoetherianRing A]`.
- The ideal and adic completeness are `(I : Ideal A) [IsAdicComplete I A]`.
  This is the dependency's separated and complete notion, not only precompleteness.
- S is `Spec (.of A)`, and the proper structure morphism is
  `(f : Y ⟶ Spec (.of A)) [IsProper f]` for arbitrary `Y : Scheme.{u}`.
- The quotient closed immersion is the let-bound
  `j := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))`.
- `Y₀ := pullback f j` is exactly `Y ×_S Spec(A/I)`, and
  `i := pullback.fst f j` is its map to Y. The intermediate S_n and Y_n
  are notation in the node, not additional hypotheses or conclusions; the docstring gives
  their definitions with powers `I^(n+1)`. Only Y_0 is needed in the theorem signature.
- Every finite étale Y_0-scheme is quantified by
  `∀ (V : Scheme.{u}) (p : V ⟶ Y₀) [IsFinite p] [Etale p]`.
  These are precisely the object data of `(@IsFinite ⊓ @Etale).Over ⊤ Y₀`
  recorded by the finite-etale-category dependency, unbundled without a private definition.
- The lifted finite étale Y-scheme is
  `∃ (U : Scheme.{u}) (g : U ⟶ Y), IsFinite g ∧ Etale g ∧ ...`.
- Its restriction is `pullback g i`, with structure map `pullback.snd g i`.
- The isomorphism of Y_0-schemes is
  `∃ e : pullback g i ≅ V, e.hom ≫ p = pullback.snd g i`.
  The compatibility equation ensures this is over Y_0, rather than only an isomorphism of
  underlying schemes; the inverse compatibility follows from the isomorphism identities.
- There is no henselian, locality, connectedness, nonemptiness, or characteristic hypothesis.

Dependencies read and used:
- `Mathlib.RingTheory.AdicCompletion.Basic`: `IsAdicComplete` (including its full
  `IsHausdorff` and `IsPrecomplete` definitions).
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Sheaf.AlgebraicGeometry.BaseChangeConventions`: the full module and its declaration
  `Scheme.Modules.moduleBaseChange` were read. Its record explicitly directs scheme
  base-change citers to `Limits.pullback`, `pullback.fst`, and `pullback.snd`, used here.
  The module-pullback definition is not needed for this scheme-only statement, so that
  module is not imported unnecessarily; the underlying recorded pullback notions are used.
- `Mathlib.CategoryTheory.MorphismProperty.Comma`: `MorphismProperty.Over`, and
  `Mathlib.CategoryTheory.MorphismProperty.OverAdjunction`: `Over.pullback`, read in full
  at the relevant declarations. Their specialized object data are the finite and étale
  morphisms here; their object base change is exactly the chosen pullback and second projection.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`, and
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`, signatures and docstrings read.

The local Stacks checkout is absent. The source was read at
https://stacks.math.columbia.edu/tag/0GS2, specifically the complete Noetherian
essential-surjectivity paragraph. It agrees with the node. The docstring carries all eight
proof steps and names their principal dependency nodes.

Edge cases checked before writing: I = 0 gives Y_0 = Y and the trivial lifting; I = A
forces A to be the zero ring under separated adic completeness, so both base and Y are
empty. The zero ring, empty Y, empty V, disconnected Y and V, arbitrary characteristic,
and n = 0 are allowed. There is no proper-ideal or nontrivial-ring binder. A general
universe u is bound explicitly for the ring and schemes, as in the source scheme category;
there are no auto-bound variables.

Searches (actual tool calls; machine records in searches.jsonl):
- msearch.py leanfinder: "Finite etale covers of the closed fibre of a proper scheme over an
  I-adically complete Noetherian ring lift to finite etale covers". Eight hits concern
  étale composition, algebra descent and geometric-point lifts; none states this theorem.
- msearch.py loogle: "IsAdicComplete, AlgebraicGeometry.Etale". Zero hits.
- msearch.py grep: "algebraiz|finite.etale.*lift|lift.*finite.etale", AlgebraicGeometry.
  Hits are uses of the algebraize tactic; none states this lifting theorem.
- msearch.py leansearch: "Finite etale covers of a proper scheme over an adically complete
  Noetherian ring lift from its closed fibre". Service unavailable (Internal Server Error).
- rg of the source and lean/Sheaf for `I.adically complete|finite.etale.*lift|lift.*finite.etale|
  algebraization`, and source grep for the item id: only related henselian lifting results,
  no exact statement and no item-id match.
- Read the whole source `WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale`.
  `Scheme.isEquivalence_pullback_finiteEtale_of_henselianRing` states a categorical
  equivalence under a henselian hypothesis, not this complete Noetherian object-lifting
  statement. It is not recorded as an exact existing match.
- Read source `FundamentalGroup/FiniteEtale.lean`'s finite-etale definition and relevant
  Mathlib declarations. No duplicate notion is introduced.

No statement dispute or dependency defect was found.

## Second reading by M1

I independently read the item node, its eight proof steps, the delivered Lean file,
and all five statement-dependency nodes and their declarations. The local Stacks
checkout is absent, so I fetched the upstream `pione.tex` into the sandbox as
`pione-source.tex` and read lines 1748–1791, label
`lemma-finite-etale-on-proper-over-henselian-pair` (Tag 0GS2), including the enclosing
lemma and the complete Noetherian essential-surjectivity paragraph. I also checked
https://stacks.math.columbia.edu/tag/0GS2. The enclosing lemma assumes a henselian
pair; in this paragraph completeness supplies that property, rather than imposing
an additional independent hypothesis. No local-ring or G-ring assumption belongs
to this paragraph. The node correctly extracts only essential surjectivity.

My object/hypothesis/conclusion checklist, matched item by item:

1. A commutative Noetherian ring A: `{A : Type u} [CommRing A]
   [IsNoetherianRing A]`. Exact; there is no field or nontriviality requirement.
2. An ideal I of A with separated I-adic completeness: `(I : Ideal A)
   [IsAdicComplete I A]`. Exact. I read `IsHausdorff`, `IsPrecomplete`,
   `IsAdicComplete` and `AdicCompletion.of_bijective_iff` in the recorded Mathlib
   module: completeness is precisely bijectivity of the canonical completion map,
   and not just existence of limits. No extra topology is supplied.
3. S = Spec A: `Spec (.of A)`. Exact. I read `AlgebraicGeometry.Spec` and
   `Spec.map` in `Mathlib.AlgebraicGeometry.Scheme`; this is the recorded spectrum.
4. S_n = Spec(A/I^(n+1)), n >= 0: these are intermediate notation, not quantified
   input data or requested output. They occur with the exact exponent in proof
   step 1 of the docstring; the signature uses only the n = 0 quotient. Exact.
5. A scheme Y and its proper map f to S: `{Y : Scheme.{u}}
   (f : Y ⟶ Spec (.of A)) [IsProper f]`. Exact. The recorded `IsProper`
   extends separated, universally closed and locally finite type. I checked
   `UniversallyClosed` and its `QuasiCompact` instance, so this agrees with the
   node's finite-type convention; no extra quasi-compactness binder is needed.
6. Y_n = Y ×_S S_n, in particular Y_0, and its projection to Y: proof step 1
   gives Y_n; `j := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))`,
   `Y₀ := pullback f j`, `i : Y₀ ⟶ Y := pullback.fst f j` give Y_0 exactly.
   I opened `Sheaf.AlgebraicGeometry.BaseChangeConventions` and read its signatures
   and convention that scheme base change uses `Limits.pullback`, with these
   projections. Its module-pullback declaration is irrelevant here. No private
   copy of the scheme base-change notion has been introduced.
7. Every finite étale Y_0-scheme V with structure map p: `∀ (V : Scheme.{u})
   (p : V ⟶ Y₀) [IsFinite p] [Etale p]`. Exact, including non-surjective covers.
   I read `MorphismProperty.Over`, `Over.mk`, `Over.homMk`, `Over.isoMk`, and
   `Over.pullback` in the two recorded Mathlib modules. The objects of
   `(@IsFinite ⊓ @Etale).Over ⊤ Y₀` have precisely these unbundled data. I also
   read the definitions of `IsFinite` (affine with finite ring maps) and `Etale`
   (étale affine-local ring maps); neither introduces an unintended condition.
8. There exists a finite étale Y-scheme U with its map g: `∃ (U : Scheme.{u})
   (g : U ⟶ Y), IsFinite g ∧ Etale g ∧ ...`. Exact. The order is universal V,p
   followed by existential U,g. No uniqueness or full faithfulness is asserted.
9. There is an isomorphism U ×_Y Y_0 ≅ V over Y_0: `∃ e : pullback g i ≅ V,
   e.hom ≫ p = pullback.snd g i`. Exact: `Over.isoMk` uses exactly this
   compatibility equation. Inverse compatibility follows from the inverse
   identities, so no second equation is missing. The second projection is the
   structure map to Y_0; an arbitrary isomorphism of underlying schemes alone
   would have been weaker, but that is not what this signature says.

Edge cases: I = 0 is permitted and makes the closed-fibre inclusion an isomorphism;
I = A forces A to be a zero ring by the Hausdorff clause, and is not excluded.
The zero ring, empty Y and empty V, disconnected schemes, and covers with empty
fibres are included. The statement has no index family; its proof's tower starts
at n = 0, and the signature uses A/I, agreeing with I^(0+1). No characteristic,
locality, connectedness, surjectivity, or henselian binder is added. The explicitly
bound arbitrary universe u is the ambient universe of the scheme category, rings,
and covers. It is not fixed to Type 0; any larger ambient universe can be chosen
for all the data. All identifiers and universes in the signature are bound.

Independent searches (actual msearch calls recorded in searches.jsonl):

- LeanFinder: "Essential surjectivity of restriction of finite étale schemes along
  Spec(A/I) for proper schemes over complete rings". Eight results concern étale
  composition, standard étale ring algebras, and the category of étale schemes;
  none states this object-lifting theorem.
- Loogle: "IsAdicComplete, IsProper" reports an unknown IsProper identifier in
  that service, so it is not evidence of absence. Retried "IsAdicComplete":
  twelve results give the completeness class, its completion-map equivalences,
  and Jacobson-radical containment, with no scheme-cover lifting theorem.
- msearch grep: "essentiallySurjective|isEquivalence.*pullback|henselian" in
  Mathlib AlgebraicGeometry: no hits.
- LeanSearch: "Restriction to a closed subscheme is essentially surjective on
  finite etale covers of proper schemes over a complete Noetherian ring".
  Service unavailable (Internal Server Error); no absence verdict inferred.
- Direct rg over Mathlib, project `lean/Sheaf`, source `WeilConjectures`, and
  `dag/lean_names_upstream.json`, by completeness, restriction, lifting, and
  finite-etale spellings. The exact proposed name and item id are absent in the
  upstream name list/source. The related project `algebraize_finite_over_proper`
  was opened: it requires a compatible tower and concludes finiteness, not the
  finite étale lifting statement. I opened the source's
  `AlgebraicGeometry/HenselianFiniteEtale.lean` and checked
  `Scheme.isEquivalence_pullback_finiteEtale_of_henselianRing`: it assumes a
  henselian pair and asserts a categorical equivalence, not this exact node.
  I also read `AlgebraicGeometry/FundamentalGroup/FiniteEtale.lean`, whose
  `Scheme.FiniteEtale` is a full subcategory with the same object data; the
  delivery introduces no competing definition.

H5/H6/H8/H9: there are no definitions or auxiliary theorems in the delivery.
The only theorem has exactly one `sorry` proof. Both docstrings cite Tag 0GS2 and
the item id. The theorem docstring follows all eight node proof steps, including
nilpotent thickenings, topological invariance, finiteness, properness, algebraization,
etaleness along the closed fibre, the specialization/open-set argument, and the
conclusion, with dependency ids. All Lean lines are at most 100 characters, the
namespace and topic are appropriate, and the three imports provide notions used
in the signature. The node's `lean.statement` is byte-for-byte equal to the
signature from `theorem` to before `:=`.

No mathematical or formal mismatch was found. I changed only this report and
added independent search records; the correct Lean and node record were retained.
There are no new nodes, dependency modules, or statement corrections to review.
The server single-file scompile completed cleanly in 1.7 seconds with exit code 0
and no warnings.

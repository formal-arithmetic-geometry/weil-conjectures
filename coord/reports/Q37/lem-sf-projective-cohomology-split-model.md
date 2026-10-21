## Worker report

Item: lem-sf-projective-cohomology-split-model. Group Q37, stage 2, 2026-10-21.
Module: Sheaf.Paper.ProjectiveCohomologySplitModel.

The module states all clauses in three named theorems, each with proof `sorry`:
`WeilConjectures.sf_projective_cohomology_split_model`,
`WeilConjectures.sf_shifted_free_generator_bijective_natural`, and
`WeilConjectures.sf_bounded_above_projective_chain_representatives`.
Its five helper definitions give the coefficient forgetful functor specialization,
the actual split complex, its summand inclusions, the canonical cohomology map of a
shifted-free arrow, and the section-valued generator map. Every definition has real
data and uses existing Mathlib constructions. These are constructions belonging to
the item's own statement, not independently introduced notions. No new DAG nodes.

Hypotheses and clauses, matched individually:

- Scheme U: `{U : AlgebraicGeometry.Scheme.{u}}`.
- Small pro-etale site: `Scheme.ProEt.topology U` on `U.ProEt`, retaining its
  object universe u+1 and morphism universe u. The terminal object is the actual
  identity arrow `Scheme.ProEt.mk (𝟙 U)`.
- Evaluation sends every epimorphism of set sheaves to a surjection: `hEval`
  quantifies over all F, G of `Sheaf (Scheme.ProEt.topology U) (Type (max (u+1) v))`
  and all f, and says `Epi f → Function.Surjective (f.hom.app (op ...))`.
- C is an arbitrary sheaf of commutative rings: the section variable C has type
  `Sheaf (Scheme.ProEt.topology U) CommRingCat.{max (u+1) v}`. `sfSplitRings`
  only applies the canonical forgetful functor from commutative rings to rings.
  No constant-coefficient, field, affine, or nonempty hypothesis is introduced.
- The module category is exactly the recorded `CategoryTheory.ringedSiteModules`,
  transparently `SheafOfModules`, with module and coefficient universe max (u+1) v.
  Coefficients can be arbitrarily larger than the scheme/site. The imported existing
  `SheafOfModules.hasSheafify_coefficientUniverse` and
  `SheafOfModules.wEqualsLocallyBijective_coefficientUniverse` provide the usual
  small-model transport. No universe equality or extra sheafification assumption.
- Its unbounded derived category is `DerivedCategory` with a chosen
  `[HasDerivedCategory.{w} ...]`, exactly the recorded size/localization convention.
  w is explicitly declared and is not forced equal to the coefficient universe.
- N is any object of that category. `a b : ℤ` and `hab : a ≤ b` give the endpoints.
- Vanishing outside [a,b]: `hN` says `IsZero ((homologyFunctor _ q).obj N)` for
  every q not satisfying `a ≤ q ∧ q ≤ b`.
- Finite nonnegative ranks: `r : ℤ → ℕ`. Only values in [a,b] enter the model and
  theta; arbitrary values outside the interval are ignored. Extending interval data
  by an arbitrary function on its complement neither restricts nor augments it.
- Prescribed isomorphisms: `theta q hq` is an isomorphism from
  `SheafOfModules.free (ULift (Fin (r q)))` to `(homologyFunctor _ q).obj N`.
  ULift only places the finite index set in the ambient coefficient universe.
- Any representing complex Z: `Z : CochainComplex ... ℤ` and
  `e : DerivedCategory.Q.obj Z ≅ N` specify the representative identification.
  Without this identification, “exactly theta” would have no specified comparison.
- V is `sfSplitComplex C a b r`, with the indicated free term on the interval,
  categorical zero elsewhere, and literally all differentials zero.
- The asserted chain map is `∃ v : sfSplitComplex C a b r ⟶ Z`.
- Chosen maps on cohomology: for each q in the interval,
  `sfFreeCohomologyMap ... (Q.map (sfSplitCell ... ≫ v) ≫ e.hom) = (theta q hq).hom`.
  The actual single-term inclusion identifies H^q(V) with its q-th free summand;
  `singleObjHomologySelfIso` and `homologyFunctorFactors` fix both comparisons.
  Thus this specifies equality with theta, not just isomorphic cohomology objects.
- Quasi-isomorphism: `QuasiIso v` explicitly accompanies the chain map. Its image
  under Q, followed by e, is therefore the displayed derived isomorphism V ≅ N.
- Shifted free C^r[-q]: the Mathlib single complex in degree q, followed by Q;
  this is the same shift convention, since `[n]` moves degree zero to degree -n.
- The forward map to H^q(A)(U)^r is `sfShiftedFreeGeneratorMap`. It composes the
  inverse canonical single-complex homology isomorphism, the inverse localization
  factorization comparison, and H^q(f), then uses `freeHomEquiv` and evaluates
  its generator sections at the identity object of U. No arbitrary map or choice.
- For every A, integer q, and natural r, `Function.Bijective` of that specific
  forward map states the requested bijection. The naturality conjunct states its
  compatibility on each standard generator for EVERY derived arrow alpha : A ⟶ B.
- P bounded above: `d : ℤ` and `[P.IsStrictlyLE d]`. Projective terms are exactly
  Mathlib's lifting-property class `[∀ n : ℤ, Projective (P.X n)]`.
- No target bound: L is any integer cochain complex.
- Representation: every phi : Q(P) ⟶ Q(L) equals `Q.map f` for some chain map f.
- Uniqueness up to chain homotopy: `Q.map f = Q.map g ↔ Nonempty (Homotopy f g)`.
  Mathlib's `Homotopy.comm` is f = dh + hd + g, equivalently f-g = dh+hd,
  and its support field is exactly the degree-minus-one support condition.
- Top summand: for EVERY derived f from the single free top term to N whose
  `sfFreeCohomologyMap` equals theta_b, the final conjunct says
  `f = Q.map (sfSplitCell ... b ... ≫ v) ≫ e.hom`. Hence under the very splitting
  just constructed, it is exactly its degree-b inclusion, not an unrelated splitting.

Dependency declarations read and used:

- def-pc-scheme: Mathlib.AlgebraicGeometry.Scheme, `AlgebraicGeometry.Scheme`.
- def-weil-pbc-proetale-site: Mathlib.AlgebraicGeometry.Sites.Proetale,
  `AlgebraicGeometry.Scheme.ProEt`, `ProEt.topology`, and `ProEt.mk`.
- def-weil-sheaf-of-modules-category: Sheaf.CategoryTheory.RingedSiteModules,
  `CategoryTheory.ringedSiteModules`, transparently Mathlib `SheafOfModules`.
- def-weil-abstract-derived-category: Mathlib.Algebra.Homology.DerivedCategory.Basic,
  `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q`.
- def-weil-derived-cohomology-sheaves: the dependency's recorded mathlib_match,
  Mathlib.Algebra.Homology.DerivedCategory.HomologySequence,
  `DerivedCategory.homologyFunctor` and `homologyFunctorFactors`; no dependency-record change.
- Proof inputs: WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful,
  `CategoryTheory.moduleSheaves_colimits_forgetful`; Mathlib.CategoryTheory.Sites.EpiMono,
  `Sheaf.isLocallySurjective_iff_epi'`, and its transitive import LocallySurjective,
  `Sheaf.isLocallySurjective_iff_epi`; Mathlib.Algebra.Homology.HomotopyCategory.KProjective,
  `CochainComplex.isKProjective_of_projective`, and its importing derived KProjective module,
  `CochainComplex.IsKProjective.Qh_map_bijective`.
- Further canonical constructors: Mathlib Sheaf.Free `free`, `freeHomEquiv`;
  Single/SingleHomology `mkHomFromSingle`, `singleObjHomologySelfIso`; `Homotopy`.

Edge cases checked before writing and in the second pass:

The interval may be one degree (`a=b`). Every rank may be zero; Fin 0 and its ULift
are empty, free on it is zero, and the section tuple is the unique empty function.
The top rank can be zero even when lower ranks are nonzero. All ranks may be zero,
so the splitting is a quasi-isomorphism from the zero complex to any acyclic Z.
The zero ring sheaf is allowed. The empty scheme is allowed and is never excluded
by a point or nonzero-section assumption. The generator/homotopy calculation uses no
bound on A or L. Projectivity is the categorical epi lifting property; no enough
projectives assumption was added. The coefficient universe can exceed the scheme
universe and the derived morphism universe remains independent.

Searches (prescribed msearch.py, all on 2026-10-21; exact service responses also in
sandbox searches.jsonl):

- LeanFinder: “A complex of module sheaves with bounded finite free projective
  cohomology admits a quasi-isomorphism from its zero differential cohomology complex
  and maps from shifted free sheaves compute cohomology sections”. Eight hits,
  including `IsKProjective`, `isKProjective_of_projective`, the derived Hom-complex
  bijection and the projective single-object map lemma; none states this full node.
- Loogle: `"SheafOfModules", "free"`. Twelve hits, mostly PresheafOfModules.Free
  constructors; direct source inspection found the actual Sheaf.Free constructions
  used here. No prescribed-cohomology splitting or section-valued derived bijection.
- LeanSearch: “A bounded complex with projective cohomology splits as its cohomology
  complex”. Eight hits on ShortComplex.Splitting, short exact sequences and a
  single-object projective map lemma; none is the item's statement.
- Mathlib grep: `zero.*differential|homologyIso.*[Zz]ero|ofZero` in Algebra/Homology.
  Twenty-five hits, mostly short-complex homology data with zero arrows, plus CM5b;
  none is this module-sheaf theorem.
- Direct rg of lean/WeilConjectures and lean/Sheaf for splitting/cohomology and
  zero-differential constructions found CochainComplex.exists_quasiIso_from_zeroDifferential
  in WeilConjectures.RingTheory.ResidueCohomologySplit. Its full signature is over a
  FIELD, with vector-space dimensions, no prescribed theta, no sheaf coefficients,
  no shifted-free sections bijection and no top-cell clause: unusable as an exact match.
- Direct grep for this blueprint id in lean/WeilConjectures found no declaration.
- Direct rg of Mathlib, lean/WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json
  for the newly chosen declaration names found no previous declaration.

No mathematical statement correction or STATEMENT-DISPUTED flag is needed.
The initial compiler diagnostics exposed implicit-universe inference through max;
explicit `sfSplitRings.{u,v}` and finite-index ULift universes resolve this without
restricting universes. No new instance declaration is retained.

## Second reading by Q37

A second in-thread reading of the node and final module checked every hypothesis and
clause listed above. The dispatcher forbids starting other agents, so this is explicitly
a separate pass by the same worker; the maintainer's independent review remains pending.

This pass checked that sfSplitCell is an actual chain map with the identity as its
in-range component, that sfFreeCohomologyMap uses the canonical comparisons in their
correct directions, and that the splitting equality refers to the fixed e rather than
an arbitrary identification. It checked the naturality quantifier covers arbitrary
DERIVED alpha, not just chain maps, and the chain-representative theorem has no
unnecessary evaluation or N/amplitude assumption. The final top-cell equality refers
to the same existential v as the splitting clause. It also checked all zero-rank,
empty-scheme and independent-universe cases. The only drafting changes were explicit
universe arguments, a parenthesized dependent theta binder (to avoid arrow/iso parser
precedence), and 100-column formatting; the node statement itself is unchanged.

## Returned-delivery repair

H13 (immutable head eb5d4689a2f1): removed the unnecessary §1(B) repair of
`def-weil-derived-cohomology-sheaves`. Its sandbox node is now byte-identical to
the current live node, so this delivery does not rebind any dependency record.
The live record now names Mathlib's `DerivedCategory.homologyFunctor` (Q20);
the item continues using the node's already recorded Mathlib match directly.
The accepted item module and its node record are unchanged.

The repair pass reread the item and all eight declarations: the explicit split
complex, canonical comparison maps, prescribed cohomology, naturality for every
derived arrow, chain representatives modulo Homotopy, and top-cell uniqueness
remain exactly as in the independently reviewed returned module. The module's
SHA-256 is `f3371a931aa60bbba95361bf4f2d43ef2c03b2f91549b209db29a6b1f0b819c2`.
No mathematical statement, definition, theorem signature, import, or proof changed.

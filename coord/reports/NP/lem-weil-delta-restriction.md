## Worker report

Handoff report retained below. The final packet reuses the now-published pairing
module; see `## Second reading by NP` for the changes made during review.

The delivery states `lem-weil-delta-restriction` in
`Sheaf.Paper.DeltaRestriction`. It also includes the already delivered prerequisite
`Sheaf.Paper.DualityPairing`, retrieved from `deliver/Q29/lem-weil-duality-pairing`.
The live `scompile.py --source Sheaf.Paper.DualityPairing` lookup returned
"Module source unavailable", and the live dependency node had no `lean` record.
No statement correction or new definition node is needed.

The source node and the original blueprint file were read, including the original
proof's explicit limitation to slice restriction rather than closed immersions.
The original blueprint sources for this item and duality-pairing were retrieved
read-only from the project server because the local literature cache lacks them.

Hypotheses and clauses of the item:

- A field is `{k : Type u} [Field k]`; the finite commutative coefficients are
  `Λ : Type (u + 1)`, `[CommRing Λ]`, `[Finite Λ]`. Invertibility of the additive
  exponent is `[HasInvertibleExponent Λ (Spec (.of k))]`, the source's existing
  coefficient hypothesis. This includes the zero coefficient ring.
- The etale morphism is `(j : W ⟶ Y) [Etale j]`. Its k-linearity is expressed by
  the structure maps `aY` and `j ≫ aY`, so the structural triangle commutes exactly.
  Separatedness of both schemes is `[IsSeparated aY]` and
  `[IsSeparated (j ≫ aY)]`. Finite type means `LocallyOfFiniteType` together with
  `QuasiCompact` for each of these same structure maps. There is no properness,
  open-immersion, boundedness, constructibility, or perfectness hypothesis.
- The ordinary full derived categories are `Etale.DerivedCategoryModule Λ Y`
  and its W counterpart. The ringed-site RHom notion is realized by the existing
  `Etale.derivedHom (ModuleCat Λ) Y`, the right adjoint of precisely the recorded
  `Etale.derivedTensor`. This is the six-functor constant-module-sheaf encoding
  specified in the record of `def-weil-pbc-derived-categories`.
- `dualizingComplex (ModuleCat Λ) aY` is the ambient right adjoint evaluated at
  `constantComplex Λ (Spec k)`. Its definition in the source is a chosen right
  adjoint of the ordinary unbounded compact-support functor, with its actual
  adjunction. The W object uses `j ≫ aY`.
- `restrictionDualEvaluation` is the derived tensor-Hom counit preceded by Koszul
  symmetry, so its input order is DK tensor K. `restrictionDualDelta` is its
  actual adjoint transpose. `Etale.deltaRestrictionMap` specializes it using the
  existing descended braiding; neither arrow is an unconstrained parameter.
  `deltaRestrictionBraiding` selects the pairing theorem's witness, whose
  componentwise equality with the descended Koszul braiding determines it uniquely.
  This postpones only a proof, rather than choosing unspecified data.
- `deltaRestrictionDualizingIso` constructs theta by evaluating the unique
  counit-normalized natural isomorphism of
  `existsUnique_etaleAmbientAdjointLocalityIso` at the constant complex. The
  locally Noetherian and compact structures used inside this construction come
  from `LocallyOfFiniteType.isLocallyNoetherian` and
  `QuasiCompact.compactSpace_of_compactSpace`; they add no hypotheses. Separated
  cancellation supplies separatedness of j, and Noetherianity supplies its
  quasi-compactness. Nagata supplies the structure-map compactifications.
- `DualDeltaRestriction` quantifies an isomorphism of contravariant functors,
  `H.flip.obj Ω ⋙ r ≅ r.op ⋙ H'.flip.obj Ω'`. This is the asserted natural alpha.
  Its first conjunct fixes each component to the tensor-Hom adjunct of the
  restricted evaluation followed by theta. Its tensor comparison is the existing
  K-flat-derived pullback comparison transported through `L j* ≅ D j*`, explicitly
  constructed by `deltaRestrictionTensorIso`. Thus the existence assertion names
  the canonical comparison, rather than merely some isomorphism of objects.
- The second conjunct in `DualDeltaRestriction` is, in Lean's composition order,
  `r.map δ_K ≫ α_(DK) = δ_(rK) ≫ H'.map(α_K.op).app Ω'`. The occurrence of `.op`
  makes the contravariant variance explicit. Its third conjunct composes with
  the inverse of the latter Hom comparison, giving exactly the stated
  transported double-dual identity. The functor isomorphism supplies both
  invertible factors of that transport.
- `isIso_delta_iff_etale_cover` is the final if-and-only-if. Its covering data
  are an arbitrary index type, etale j_i, the same separated finite-type
  conditions on W_i, and
  `∀ y : Y, ∃ i x, (j i).base x = y`. The right side uses the canonical
  double-dual maps for the W_i dualizing objects and their actual pullbacks of K.
- `ProEtale.delta_restriction` states the same `DualDeltaRestriction` for
  `Sheaf (Scheme.ProEt.topology Y) (ModuleCat Λ)`, the ordinary constant finite
  coefficient category (not condensed coefficients). It allows every specified
  Ω in the full unbounded category; Ω_W is literally the inverse image and
  theta is `Iso.refl`. No exceptional adjoint on this category is assumed.
  This is the module-valued realization also used by the delivered pairing
  dependency, and the existing pro-etale tensor/Hom operations. The recorded
  `Scheme.proEtaleDerivedCategory` is the ringed-module presentation of the same
  ordinary constant-coefficient category, not the condensed ModuleObject category.
  Applying the general slice calculation to a compatible realization is precisely
  specialization to its given Ω; there is no extra realization hypothesis.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper` / `Separated`: `IsSeparated`.
  Properness is not assumed in this node; this dependency supplies separatedness.
- `Sheaf.AlgebraicGeometry.DerivedCategories` and
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `Etale.DerivedCategoryModule`, `Etale.constantComplex`.
- `Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint`:
  `Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification`;
  `WeilConjectures.SixFunctors.Etale.Derived.UpperShriek` / `Dualizing`:
  `rightDerivedUpperShriekAdjunction`, `dualizingComplex`.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses`, the recorded ringed-site
  construction; the source's `Etale.derivedHom` and `ProEtale.derivedHom`
  give the existing tensor-right-adjoint presentation on module-valued sheaves.
- `Sheaf.Paper.DualityPairing`: `CategoryTheory.dualityDoubleFunctor` and the
  `Etale.ambient_duality_pairing` formalism, canonical evaluation/transpose
  normalization and its ambient scope.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`: `Etale.derivedTensor`;
  the corresponding `ProEtale.Derived.Tensor` supplies its pro-etale counterpart.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `Scheme.proEtaleDerivedCategory`; the site is `Scheme.ProEt.topology`.
- `Sheaf.CategoryTheory.RingedDerivedRestriction`:
  `CategoryTheory.ringedDerivedRestriction`, the recorded exact-slice descent;
  the scheme inverse-image descents use the same `Functor.mapDerivedCategory`
  construction after the stated slice identifications.
- `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`:
  `existsUnique_etaleAmbientAdjointLocalityIso`, including its full counit
  normalization and all inputs, not just its name.
- Proof dependencies are directly imported when recorded as modules. The
  docstrings carry all seven natural-language proof steps: Noetherian/Nagata
  ambient locality, module-linear slice identification, RHom restriction,
  K-flat/K-injective evaluation models, transposition with Koszul sign,
  covering detection via every integer cohomology, and the pro-etale slice
  specialization. No import replaces the ambient pro-etale object by an
  unconditional pro-etale exceptional adjoint.

Edge cases checked: empty schemes; empty covering families (joint surjectivity
then forces Y empty); the identity etale map; zero objects and zero coefficients;
unbounded complexes, including those with infinitely many nonzero cohomology
sheaves; arbitrary specified Ω on the pro-etale site. Tensor symmetry uses
`(-1)^(pq)` and the contravariant comparison is inverted in the transported
formula. There is no independent small universe that makes a quantifier vacuous.

Searches for an existing statement:

- `msearch.py ... leanfinder "Etale restriction commutes with derived internal Hom
  and the canonical double dual evaluation morphism"`: eight hits, including
  `LightCondensed.ihomPoints_symm_comp`, `LightCondensed.ihom_map_val_app`, and
  `CategoryTheory.ExponentiableMorphism` evaluation/naturality lemmas; none is
  this ordinary etale/pro-etale unbounded restriction theorem.
- `msearch.py ... loogle "CategoryTheory.MonoidalClosed, CategoryTheory.Functor"`:
  twelve hits, including `MonoidalClosed.internalHom`, `MonoidalClosed.ofEquiv`
  and functor-category closedness; these are ingredients, not the statement.
- `msearch.py ... grep "bidual|doubleDual|derivedHom.*[Rr]estrict" CategoryTheory`:
  zero hits. Direct source/project `rg` finds underived module biduality,
  perfect-object biduality and a condensed geometric-operations package, none
  stating the ambient restriction identity. Searches for `deltaRestriction`,
  `delta_restriction`, `DualDeltaRestriction`, `restrictionDualDelta` in Mathlib,
  the upstream declaration index, source library and the side library give no
  duplicate of the new names. The item-id search in upstream is empty.
- The live source lookup and delivery-branch search found the pending Q29
  duality-pairing dependency, whose statements and constructions are reused
  with its mathematical statements unchanged. Two generic typed projections
  extract its uniquely normalized braiding witnesses for the main module.

No `STATEMENT-DISPUTED` issue was found. All theorem proofs remain `sorry`.

Validation: both delivered modules compiled cleanly through `scompile.py` with
the prescribed per-file limit, without errors or unexpected warnings. The
`deliver2.py --no-push` dry run checks the final packet; independent second
reading is left to the next worker.

## Dependency modules

`lem-weil-duality-pairing`: the live node has no usable recorded declaration yet.
The already delivered Q29 module states the ambient evaluation and its transpose,
with naturality, coherent shifts, and the morphism of distinguished triangles,
for ordinary constant coefficients on both sites. Its canonical normalization is
by the actual tensor-Hom adjunction and the descended Koszul symmetry. The module and the node's Lean record are included here so this item can
compile without waiting. The only added helpers are
`Etale.AmbientDualityPairing.braiding` and
`ProEtale.AmbientDualityPairing.braiding`, generic typed projections of the
uniquely normalized braiding witnesses. Their data are determined by componentwise
HEq with the existing descended Koszul braiding; they select no arbitrary object. Its mathematical statement, proof, dependency lists and every
non-Lean field are unchanged; the new `lean.note` records provenance and the
reason for including the prerequisite. The module contains real definitions and
one named postponed theorem carrying all six proof steps in its docstring.

## Second reading by NP

Read the complete sandbox node and module independently against the original blueprint
`sec-six-functors/sk-prop-sf-biduality-general/lem-weil-delta-restriction.md`, order
2124, and the pairing source, order 2122. The local source cache is
`weil-launcher-nt/literature/blueprint/master/blueprint/`. Also read Stacks
`sites-cohomology.tex`, Section `section-internal-hom`, including
`lemma-internal-hom` (08J9), `lemma-section-RHom-over-U` (08JA),
`lemma-restriction-RHom-to-U` (08JB), and `lemma-RHom-triangulated` (08JC),
and the preceding `section-hom-complexes`. These assume a ringed site and arbitrary
unbounded derived objects. In particular 08JB is slice restriction, not restriction
along a general closed immersion. No source-based statement correction is needed;
the node has no `statement_change`.

The following is my object/hypothesis/conclusion checklist, in the node's order.

1. Field k: `{k : Type u} [Field k]`. Finite commutative A:
   `Λ : Type (u + 1)`, `[CommRing Λ] [Finite Λ]`. The existing
   `HasInvertibleExponent Λ (Spec (.of k))` asserts a positive annihilating
   integer invertible on Spec k. For a finite ring this is equivalent to
   invertibility of its additive exponent, including the zero ring. Verdict: exact.
2. Schemes Y,W and etale k-morphism j: `{W Y : Scheme.{u}} (j : W ⟶ Y)
   (aY : Y ⟶ Spec (.of k)) [Etale j]`; the W structure map is `j ≫ aY`.
   Thus k-linearity is built into the same composite, not omitted or replaced by
   a second unrelated map. `[IsSeparated aY]` and `[IsSeparated (j ≫ aY)]`
   are exactly separatedness over k. Each structure map has
   `[LocallyOfFiniteType ...] [QuasiCompact ...]`, exactly finite type.
   Read the Etale, FiniteType, QuasiCompact and Separated class signatures in
   Mathlib, against the three recorded morphism nodes. Verdict: exact; there
   is no properness hypothesis.
3. Ordinary unbounded constant-coefficient categories: `DerivedCategoryModule Λ Y`
   and its W analogue are the recorded six-functor encoding from
   `def-weil-pbc-derived-categories`, namely derived categories of
   `Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)`. Read that module and
   `Etale.Derived.Coefficients`; `constantComplex Λ (Spec k)` is the monoidal
   unit, in degree zero. Verdict: exact; no boundedness, constructibility,
   perfection or finite Tor dimension is added to K.
4. Ambient dualizing objects: `dualizingComplex (ModuleCat Λ) aY` and the same
   expression at `j ≫ aY`. Read `Etale.Derived.Dualizing` and `UpperShriek`:
   these apply the actual right adjoint of unbounded compact supports to the
   constant unit, not a right adjoint on a constructible subcategory. Read
   `EtaleExceptionalAdjoint` and the recorded ambient-adjoint signature.
   Verdict: the correct ambient objects.
5. D and delta: the existing `Etale.derivedHom (ModuleCat Λ) Y` is the internal
   Hom right adjoint of exactly `Etale.derivedTensor`. Read both upstream
   definitions and their adjunction signature, and the recorded
   `derivedInternalHomOfUniverses` Hom-complex construction. The module-valued
   presentation of constant-ring modules is the same notion as that ringed-site
   construction. `restrictionDualEvaluation` is symmetry followed by the
   counit, in order DK tensor K; `restrictionDualDelta` is its actual
   `homEquiv` transpose, with left tensor DK. The selected symmetry is fixed
   componentwise by the published pairing assertion to the descended Koszul
   symmetry. Verdict: correct canonical map, not an arbitrary natural arrow.
6. Canonical theta: `deltaRestrictionDualizingIso Λ j aY` evaluates the
   `existsUnique_etaleAmbientAdjointLocalityIso` comparison at
   `constantComplex Λ (Spec k)`. Read the complete locality signature and its
   compact-support counit normalization. All Noetherian and compact instances
   in the definition are derived from finite type over k; separated cancellation
   supplies separatedness of j, and Noetherianity supplies quasi-compactness.
   The compactifications are the existing Nagata choices. Verdict: exactly the
   canonical ambient comparison, with no new assumptions or unspecified choice.
7. Natural alpha: `DualDeltaRestriction` existentially quantifies the natural
   isomorphism `H.flip.obj Ω ⋙ r ≅ r.op ⋙ H'.flip.obj Ω'` before quantifying
   K. Its first conjunct fixes every component as the adjunct of the canonical
   tensor comparison followed by restricted evaluation and theta. Read the
   upstream `UpperStarMonoidal` comparison and exact-upper-star descent:
   `deltaRestrictionTensorIso` transports their canonical comparison through
   `L j* ≅ D j*`. Verdict: precisely slice internal-Hom comparison followed
   by theta, with naturality and invertibility, not just objectwise existence.
8. Displayed identity: the second conjunct is
   `r.map δ_K ≫ α_(DK) = δ_(rK) ≫ (H'.map (α_K).op).app Ω'`.
   The `.op` is essential: D_W(alpha_K) goes from D_W D_W(rK) to
   D_W(rD_Y K). This is exactly the node's variance and composition order.
   Verdict: exact.
9. Transported identity: the third conjunct composes alpha_(DK) with the
   inverse of `H'.mapIso (α_K).op`, producing the isomorphism
   rD_YD_Y K to D_WD_W(rK), and equates its composite with r(delta_K)
   to delta_(rK). Verdict: both the stated isomorphism and its stated action
   on the canonical arrow are present.
10. Etale-cover locality: `isIso_delta_iff_etale_cover` has an arbitrary
    `I : Type w`, etale maps `j i : W i ⟶ Y`, all the node's separated
    finite-type conditions over k, and pointwise joint surjectivity
    `∀ y, ∃ i x, (j i).base x = y`. It asserts the iff for exactly the
    dualizing objects and pullbacks of K used above. Verdict: exact.
11. Pro-etale clause: `ProEtale.delta_restriction` takes every specified
    `Ω : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat Λ))`.
    Its Ω_W is literally `upperStar.mapDerivedCategory.obj Ω` and theta is
    `Iso.refl`; the same package asserts all the comparison and delta clauses.
    Read the existing pro-etale tensor, Hom and inverse-image interfaces and
    the recorded `Scheme.proEtaleDerivedCategory`: the latter is the
    constant-ring `SheafOfModules` presentation; the present existing
    `Sheaf ... (ModuleCat Λ)` presentation describes the same ordinary
    constant-coefficient notion and is also the one used by the pairing
    dependency. Neither is the condensed ModuleObject category. Verdict:
    the arbitrary specified dualizing object is retained; specializing to a
    compatible finite realization imposes no exceptional-adjoint hypothesis.

Edge cases: I may be empty; the covering hypothesis then forces Y empty,
and no Nonempty I or Nonempty Y is assumed. W and Y may themselves be empty;
j may be the identity. K may be zero or have unbounded cohomology in both
integer directions. Λ may be zero; exponent 1 then works. Positive
characteristic is allowed precisely under the recorded invertibility
hypothesis. There is no degree n or nonzero-degree restriction. The universe
of the covering index is independent (this is a covering family, not a limit);
the categories retain the established Scheme.{u}/ModuleCat.{u+1} convention.
The generic package permits independent category object and morphism universes.
All variables and universes are explicitly bound with `autoImplicit false`.

Independent searches (2026-10-16), in addition to reading the worker's searches:

- `msearch.py NP lem-weil-delta-restriction leanfinder "An exact restriction
  functor on sheaves preserves the bidual evaluation morphism and internal Hom
  on unbounded derived categories"`: eight hits, including
  `Functor.IsCoverDense.sheafHom_restrict_eq`,
  `Functor.mapDerivedCategoryFactorsh_hom_app`, and condensed internal-Hom
  formulas. These are underived restriction or localization ingredients;
  none states this dualizing comparison and double-dual identity.
- `msearch.py ... loogle '"doubleDual"'`: twelve hits, additive-character
  and normed-space double duals; none is the present categorical theorem.
- `msearch.py ... grep 'biduality|doubleDual|delta_restriction|DualDeltaRestriction'
  CategoryTheory`: zero hits. Direct `rg` in Mathlib, upstream
  `WeilConjectures`, and shared `lean/Sheaf` for bidual/restriction,
  evaluation/restriction and doubleDual/functor combinations found the
  underived presheaf-module bidual and unrelated evaluation lemmas. None is
  an existing version of this statement. Exact-name searches in those trees
  and `dag/lean_names_upstream.json` found no collisions for the new names.

Mismatches found and repaired:

- The worker's bundled `DualityPairing` prerequisite has now been published.
  The current shared node records Q29's module and the live
  `scompile.py --source Sheaf.Paper.DualityPairing` returns it. I read that
  declaration and checked its canonical normalization and all clauses against
  the pairing node and source. Removed the stale sandbox dependency module
  and dependency node copy, so this delivery does not overwrite its landing.
  The earlier Worker report and Dependency modules section describe the
  worker's packet at handoff; this second reading records the final packet.
- The two generic typed braiding projections are helpers of this item's
  restriction construction. Kept them in `DeltaRestriction.lean`, under the
  names `Etale.deltaRestrictionPairingBraiding` and
  `ProEtale.deltaRestrictionPairingBraiding`, with this item's source and
  blueprint docstrings, and listed them in this item's `lean.declarations`.
  They extract the already componentwise determined witnesses of the published
  pairing predicate. No dependency statement or mathematical construction is
  changed. Direct specialization of `Classical.choose` caused excessive
  elaboration, so the projections retain their generic typed interfaces.
- The recorded proof dependency for exact localized module adjunction now
  points to `Sheaf.CategoryTheory.LocalizedModuleExactIndependent`. I read
  that interface and tested its import. It imports the separate finite-coefficient
  pro-etale framework through `RingedProjectionRestriction`, causing a duplicate
  declaration for `AlgebraicGeometry.ProEtale.«term(_)_*[_]»` against this module's
  upstream pro-etale framework. Retained the usable predecessor import
  `Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact`; its small-ringed-site
  theorem applies on the small skeleton used explicitly in the node's proof.
  The newer module is intentionally omitted for this concrete import collision;
  no theorem or assumption is substituted. This framework collision is reported
  here for the maintainer.

There are no new nodes, dependency repairs, or mathematical statement changes
in the final packet. No hollow definitions or proofs inside definitions occur;
the only postponed proofs are the three named theorems, whose docstrings
collectively cover the node's seven proof steps. The node's `lean.statement`
is verbatim the main theorem signature. Final compilation and delivery preflight
are run through the prescribed wrappers after these repairs.

Final validation: `scompile.py NP lem-weil-delta-restriction` compiled the sole
final module cleanly in both sandbox and library contexts (14.8 s and 14.7 s),
with no errors or warnings. The 60 s limit was unchanged. Signature equality,
100-character Lean line width, and exactly three named `sorry` proofs were checked.

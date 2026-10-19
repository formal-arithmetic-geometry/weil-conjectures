## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleCompactSupportBaseChangeQcqs` states
`AlgebraicGeometry.Etale.etale_compactSupport_baseChange_qcqs`, with `sorry` as its
whole proof. No definition is introduced. The source read is
`literature/stacks-project/more-etale.tex`, Tag 0F7L,
`lemma-base-change-shriek`, lines 3428–3469: specifically the first paragraph of
its proof, which fixes a compactification and constructs the two isomorphisms.
The node asks only for that fixed-compactification result, not the subsequent
independence and composition coherence assertions of the full Stacks lemma.

Hypothesis and conclusion correspondence:

- Finite commutative coefficient ring: `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
  Coefficients are `ModuleCat.{u + 1} Λ` throughout, hence constant coefficients
  on the small etale site, not structure-sheaf modules or pro-etale coefficients.
- Schemes: `{X Y Y' : Scheme.{u}}`. For each of these schemes, `[CompactSpace _]`
  expresses quasi-compactness and `[QuasiSeparatedSpace _]` quasi-separatedness.
- Separated finite-type morphism: `(f : X ⟶ Y) [IsSeparated f]
  [LocallyOfFiniteType f] [QuasiCompact f]`. Finite type means locally of finite
  type and quasi-compact, exactly as the conventions node specifies.
- Arbitrary base morphism: `(g : Y' ⟶ Y)`, with no property instance on `g`.
- The general introductory `h:T → B` describes the compactification convention;
  its instance for the morphism in the conclusion is `(c : Compactification f)`.
  This is the source's existing structure, with ambient `c.Z`, open immersion
  `c.i`, proper map `c.g`, and `c.comm : f = c.i ≫ c.g`.
  Although the general structure does not impose quasi-compactness on `c.i`,
  `c.quasiCompact_openImmersion` derives precisely that property from the
  explicit `[QuasiCompact f]`. Thus every `c` quantified here is precisely a
  compactification in the node's sense; no extra dependency module is needed.
- The chosen fibre product `X'` is `pullback f g`, with `g' = pullback.fst f g`
  and `f' = pullback.snd f g`. No separate `X'` or cartesian-square hypothesis
  is necessary. Its qcqs properties follow from the original hypotheses and
  base-change permanence; no extra assumption is placed on the fibre product.
- The pullback compactification is literally `c.baseChange g`, whose type is
  `Compactification (pullback.snd f g)`. Its ambient scheme is `pullback c.g g`,
  proper map is `pullback.snd c.g g`, and open immersion is the canonical lift.
- `Rf_!^c` is `rightDerivedLowerShriekOfCompactificationPlus (ModuleCat Λ) c`.
  Its existing definition is extension by zero applied termwise on the bounded
  below derived category, followed by the bounded below right derived proper
  direct image. The other shriek uses the same definition at `c.baseChange g`.
- Termwise inverse images are `(upperStar (ModuleCat Λ) g).mapDerivedCategoryPlus`
  and the same expression at `pullback.fst f g`. These are the exact functors
  on constant-coefficient module sheaves, applied to complexes and localized.
- The conclusion is `Nonempty (F ≅ G)` for the two displayed composite functors,
  in forward evaluation order: first compact support then `g` inverse image,
  versus first `g'` inverse image then base-changed compact support. A functor
  isomorphism is a natural isomorphism in every `K` and every morphism of
  bounded below complexes; its components are exactly the asserted objectwise
  isomorphisms. This does not replace naturality by merely objectwise existence.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `Scheme.Hom`, full structure signatures and docstrings at lines 36–45, 73–75.
- The conventions node has no declaration of its own and expressly defines no
  notion. Its named Mathlib properties are used as the above instances.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification` and its
  bounded-below counterpart `rightDerivedLowerShriekOfCompactificationPlus`,
  full signatures, docstrings and definitions at lines 83–111. The latter is
  the bounded-below specialization the node needs, not a replacement definition.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `AlgebraicGeometry.Etale.openImmersionLowerShriek`, lines 289–293, and
  `preservesFiniteLimits_openImmersionLowerShriek` for exactness.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`, `upperStar`, and
  `upperStarLowerStarAdjunction`; read full docstrings and signatures. Derived
  direct image is the generic `Functor.rightDerivedFunctorPlus` applied to
  `lowerStar`, as `Derived.UpperLowerStar` documents explicitly. It is used
  inside the existing compactification shriek definition.
- `Sheaf.AlgebraicGeometry.DerivedCategories`: read the full module; the
  recorded mixed record uses the existing `DerivedCategory.Plus` of
  `Sheaf T.smallEtaleTopology (ModuleCat Λ)` for D+; the new torsion predicate
  declared in that module is not needed in the statement.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, and
  `pullback.lift`, signatures and docstrings at lines 94–130.
- `WeilConjectures.Compactification.Defs`: full `Compactification` structure,
  and `quasiCompact_openImmersion` / `quasiCompact_openImmersion_iff`.
  `WeilConjectures.Compactification.BaseChange`: `Compactification.baseChange`,
  full signature, docstring and definition at lines 140–148.

The statement-dependency modules are public imports. Stated proof dependencies
are imported without `public`: Mathlib open immersions, properness, qcqs and
finite-type permanence, exact functors preserving homology,
`Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`,
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper`,
`Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients`, and
`WeilConjectures.SixFunctors.BaseChange.Derived`.
The extension-by-zero exactness dependency is already a public statement import.
`cor-cbc-derived-extension-zero-base-change` has no Lean record on this base,
so there is no recorded proof module to import for it. Its exact role remains
step 4 of the declaration docstring. No imported module substitutes another
coefficient category for the statement's category.

Edge cases checked: empty X, empty Y', and the zero ring are allowed; there is
no nonempty or nontrivial hypothesis. The identity compactification of a proper
f is allowed. There is no characteristic restriction or invertibility
hypothesis; finite coefficients ensure torsion even at residue characteristics.
All degrees and all lower bounds are covered by the full `DerivedCategory.Plus`
functors; no degree, uniform bound, or constructibility restriction is added.
The one scheme universe `u` is arbitrary, and coefficient modules live in
`u + 1`, as required by the existing six-functor encoding. A smaller finite
ring can always be represented in that universe. No auto-implicit variable,
file-local notation, local instance or private helper is used.

Searches actually run:

- `msearch.py ... leanfinder "Etale derived compact support with fixed
  compactification commutes with arbitrary base change"`: eight hits about
  etale morphism permanence and etale ring maps; no derived compact-support result.
- `msearch.py ... loogle '"rightDerivedLowerShriekOfCompactificationPlus"'`:
  zero hits.
- `msearch.py ... grep 'compactSupport.*baseChange|shriek.*baseChange'`:
  zero Mathlib hits.
- `msearch.py ... leansearch "Etale cohomology compact support commutes with
  arbitrary base change"`: unavailable, Internal Server Error; not counted as
  a negative mathematical result.
- `rg` of the upstream `WeilConjectures` tree for the item id and proposed full
  declaration name, and of `dag/lean_names_upstream.json` and `lean/Sheaf` for
  that name: no declaration found. The item's occurrences in the project's
  affine-line constructibility module are prose proof-plan citations only.
- `rg` for `rightDerivedLowerShriekOfCompactificationPlus`, compact-support
  base change, and compactification/base-change names in `lean/Sheaf` and the
  upstream six-functor tree located the existing definitions used above and
  `Derived.LowerShriekBaseChange`. Read that module in full: its exchange map
  is unbounded and its invertibility theorem assumes invertibility of another
  exchange map; it does not state this bounded-below unconditional finite-ring
  theorem. `Derived.LowerShriekFormalism` supplies proper exchange in a generic
  formalism, not this precise statement. The compactification-comparison
  isomorphisms compare compactifications over a fixed base, rather than
  changing the base. None is an exact existing declaration for this node.

No statement correction, new node, dependency replacement, or disputed
statement was needed. The full five-step DAG proof is carried by the theorem's
docstring. Validation: the prescribed `scompile.py` compiled this module cleanly
on the server (3.0 s), along with side-only imported modules in its private
overlay, each under nice 19, two threads and the 60-second per-file limit.

## Second reading by NZ

I read the sandbox node and Lean module independently against Stacks
`more-etale.tex`, Tag 0F7L, `lemma-base-change-shriek`, including the
preceding definition of compact support at lines 3050–3076. The source uses
bounded below torsion cohomology for general coefficients, or arbitrary
complexes for torsion coefficients. A finite coefficient ring annihilates all
its modules by a positive integer, so the node's full D+ is the correct
specialization. The node asks for the construction in the first proof
paragraph with a fixed compactification; it does not ask for the full lemma's
independence or composition compatibility.

Object/hypothesis/conclusion checklist, recorded before comparing the signature:

1. A finite commutative ring Λ. Lean: `(Λ : Type (u + 1)) [CommRing Λ]
   [Finite Λ]`. Verdict: exact; finiteness is of the ring, not just of a
   particular module, and no nontriviality or invertibility assumption occurs.
2. Small etale sites with constant Λ-module sheaves, and their bounded below
   derived categories. Lean: every coefficient category is
   `ModuleCat.{u + 1} Λ`; the domains and codomains of
   `rightDerivedLowerShriekOfCompactificationPlus` and
   `upperStar.mapDerivedCategoryPlus` are `DerivedCategory.Plus` of
   `Sheaf T.smallEtaleTopology (ModuleCat Λ)`. Verdict: exact, using the
   existing dependency encoding, with no pro-etale or structure-sheaf modules.
3. Quasi-compact quasi-separated schemes X and Y. Lean: `{X Y Y' : Scheme.{u}}`
   and `[CompactSpace X] [QuasiSeparatedSpace X]`, likewise for Y. Verdict:
   exact topological qcqs conditions; neither Noetherian nor separated schemes
   are required.
4. A separated finite-type map f : X → Y. Lean: `(f : X ⟶ Y)
   [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]`. Verdict: exact;
   the conventions dependency expressly defines finite type as locally finite
   type plus quasi-compact. No finite-presentation hypothesis is introduced.
5. Arbitrary g : Y' → Y with Y' qcqs. Lean: `(g : Y' ⟶ Y)` and the two
   corresponding space instances on Y'. Verdict: exact, no condition on g.
6. A chosen compactification c = (j,p) of f, j quasi-compact open, p proper,
   and f = pj. Lean: `(c : Compactification f)`. I opened its structure in
   upstream `Compactification/Defs.lean`: `Z`, `i`, `g`, `comm`,
   `isOpenImmersion`, `isProper` are precisely these data. Although the
   structure itself permits a non-qc open immersion, its theorem
   `quasiCompact_openImmersion (hf : QuasiCompact f)` supplies exactly the
   missing property under this statement's hypothesis. Verdict: the binder
   ranges over precisely the node's compactifications. The introductory h:T→B
   describes this construction generally and adds no independent datum.
7. X' = X ×_Y Y', with g' and f' the projections; c' the base change of c.
   Lean: `pullback.fst f g` is g', while `c.baseChange g` has type
   `Compactification (pullback.snd f g)`. I opened both projection signatures
   and `Compactification.baseChange` and its ambient/proper-map formulas.
   Verdict: the chosen fibre product and pulled-back compactification agree
   exactly; no independent compactification is substituted. The qcqs property
   of X' follows from the given hypotheses, so needs no extra binder.
8. Rf_!^c = Rp_*j_!. Lean: the existing bounded below abbreviation
   `rightDerivedLowerShriekOfCompactificationPlus (ModuleCat Λ) c` unfolds
   to `D+(openImmersionLowerShriek _ c.i) ⋙ R+(lowerStar _ c.g)`.
   I opened that abbreviation, its unbounded companion recorded on the
   dependency, `openImmersionLowerShriek`, `lowerStar`, `upperStar`, and the
   project's `DerivedCategories.lean`. Verdict: exactly the dependency notions;
   this is not the right derived functor of the composite underived shriek.
9. For every K in D+, a natural isomorphism
   g⁻¹ Rf_!^c K ≅ Rf'_!^{c'} g'⁻¹ K, inverse image applied termwise.
   Lean: `Nonempty (Rf_!^c ⋙ D+(upperStar _ g) ≅
   D+(upperStar _ (pullback.fst f g)) ⋙ Rf'_!^{c.baseChange g})`, with the
   actual fully spelled expressions in the unchanged signature. Verdict:
   exact forward functor-composition order. An isomorphism of functors is
   natural in all K and all their morphisms, rather than a family of unrelated
   objectwise isomorphisms. `mapDerivedCategoryPlus` is the localization of the
   exact inverse image applied to complexes. No specified exchange morphism,
   independence, or coherence conclusion is imposed by this node.

Edge cases: empty X and empty Y' are allowed; empty Y forces the compatible
empty sources and is allowed. Zero coefficients and zero complexes are
allowed. There is no index family and no n parameter; all integer degrees,
all lower bounds, and in particular complexes concentrated in degree zero
are covered. No characteristic or prime-to-characteristic restriction occurs.
Proper f with its identity compactification is included. The arbitrary scheme
universe u and the existing six-functor coefficient convention u+1 cover the
node's setting; no independent smaller test universe makes a condition vacuous.
All variables and the sole universe are explicitly bound.

Independent H4 searches: ran `msearch.py` LeanFinder with
"Inverse image commutes with exceptional direct image computed by a
compactification on small etale sites" (eight unrelated restriction/open
immersion results), Loogle with `"LowerShriek", "baseChange"` (zero hits), and
grep with `shriek|compactlySupported|compactSupport` (25 unrelated analytic
compact-support results). Also searched Mathlib's algebraic geometry and sites
trees for `shriek|Shriek` (none), upstream and project Lean for compact-support
base-change identifiers, and the exact proposed name in project Lean,
upstream Lean and `dag/lean_names_upstream.json` (none). I opened the actual
upstream `Derived/LowerShriekBaseChange.lean` declarations: its fixed-
compactification map is unbounded and its invertibility theorem assumes
`IsIso (derivedBaseChangeMap ...)`, with additional generic coefficient
structure. Its finite-ring chosen-compactification declaration merely defines
a map. None is this unconditional bounded below natural-isomorphism theorem.
No duplicate definition or exact existing statement was found.

H5/H6/H8/H9: no definition is introduced; the single theorem's entire proof is
`sorry`; source and blueprint tags are present in both docstrings; the five
proof steps track the node, including coefficient forgetting in step 3 and
extension-by-zero exchange in step 4. Imports include the recorded statement
interfaces and available proof interfaces. No private helper, local notation,
local instance, hidden let/show binder, long line, or unbound variable occurs.
The node's `lean.statement` was compared byte-for-byte with the file's theorem
signature and agrees. There are no new nodes, dependency modules, or statement
corrections to audit, and no citer checks are triggered.

No mismatch was found. I changed only this report, leaving the correct Lean
and node untouched. Independent server validation with the prescribed
`scompile.py` passed: the delivered module took 3.1 seconds, with no warnings
or errors; its two side-only overlay dependencies also compiled cleanly.
Every invocation used nice 19, two threads, and the 60-second per-file limit.

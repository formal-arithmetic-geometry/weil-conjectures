## Worker report

States `AlgebraicGeometry.isPerfect_projective_noetherian_derivedDirectImage` with a single
`sorry` proof. The statement and proof plan follow the blueprint node, order 673,
sec-picard-framework/sk-thm-picard-semicon. No node statement was corrected and no new
notion or dependency module was needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Schemes X and S and the named morphism f: `{X S : Scheme.{u}} (f : X ⟶ S)`.
- S locally Noetherian: `[IsLocallyNoetherian S]`, not the stronger `IsNoetherian S`.
- f projective: `[IsProjective f]`, using the recorded H-projective-plus-quasi-compact
  convention, including n = 0 embeddings.
- G an O_X-module: `(G : X.Modules)`, the same carrier as
  `SheafOfModules.{u} (moduleRings X.toRingedSpace)`.
- G coherent: `(hGcoherent : RingedSpace.IsCoherent X.toRingedSpace G)`, the recorded
  finite-type and finite-type-kernel predicate, with no additional quasi-coherence binder.
- G flat over S: `(hGflat : Scheme.Modules.IsFlatOver G f)`, the existing affine-section
  relative flatness predicate equivalent to stalkwise relative flatness. It does not assert
  flatness of f.
- Rf_*G: `(schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
  (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G)`. This is the actual
  unbounded derived direct image applied to G in degree zero.
- The conclusion is exactly `Scheme.IsPerfect S` of that object. The derived-category
  existence instances for X, S and opens of S supply the categorical infrastructure used
  by these recorded definitions, not extra geometric conditions. The source and target
  derived-category universes wX and wS are independent; the opens of S use wS as required
  by `Scheme.IsPerfect`.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`:
  `AlgebraicGeometry.schemeDerivedDirectImage` (and its degree-zero convention).
- `Sheaf.AlgebraicGeometry.PerfectComplex`: `AlgebraicGeometry.Scheme.IsPerfect`;
  also read `IsStrictlyPerfect` and `perfectSubcategory`.
- `Sheaf.AlgebraicGeometry.Coherent`: `AlgebraicGeometry.RingedSpace.IsCoherent`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`:
  `AlgebraicGeometry.IsProjective`, as recorded by def-pc-projective-morphism.
  The corresponding source definition was read in the group clone's
  `lean/Sheaf/AlgebraicGeometry/Morphisms/Projective.lean`; the canonical extracted upstream
  import is available on the server and compiled successfully.
- def-pc-morphism-conventions is explicitly a convention node: it has no declaration or
  module to import. Its named projectivity convention is used above.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`:
  `AlgebraicGeometry.Scheme.Modules.IsFlatOver`, read with its complete docstring/signature.
- Mathlib `AlgebraicGeometry.IsLocallyNoetherian` and `DerivedCategory.singleFunctor`.

Proof-only imports preserve the stated plan: `Sheaf.AlgebraicGeometry.CechResolution`
(`AlgebraicGeometry.cech_resolution_derived_direct_image`),
`WeilConjectures.AlgebraicGeometry.Cohomology.Projective`
(`AlgebraicGeometry.Scheme.Modules.finite_H_of_isClosedImmersion` and
`subsingleton_H_of_isClosedImmersion`), and `Mathlib.RingTheory.Flat.Localization`
(`Module.flat_of_isLocalized_maximal`, `Module.flat_iff_of_isLocalization`, the recorded
Mathlib composite for lem-pc-affine-sections-flat-over-base). The proof dependency
lem-pc-noetherian-flat-complex-perfect has no recorded Lean module and is not imported.
All three steps of the node's proof are transcribed into the theorem docstring.

Edge cases checked: zero G gives the zero, hence perfect, direct image; empty X gives zero
and requires no nonempty cover assumption; empty S forces empty X and the conclusion is
vacuous locally. Projective dimension zero is permitted. A non-quasi-compact locally
Noetherian base is permitted: no compactness or global Noetherian hypothesis was added.
There is no restriction on characteristic or on relative flatness of the morphism itself.
No mathematical fault or STATEMENT-DISPUTED flag was found.

Searches for reuse (2026-10-15):

- msearch leanfinder: "derived direct image of coherent sheaf flat over locally Noetherian
  base projective morphism is perfect": eight unrelated hits on projective resolutions,
  Tor and scheme flatness; no exact match.
- msearch loogle: "AlgebraicGeometry.IsProjective, AlgebraicGeometry.Scheme.IsPerfect":
  zero hits, unknown identifier AlgebraicGeometry.IsProjective.
- msearch grep: "derived.*[Pp]erfect|[Pp]erfect.*direct" in AlgebraicGeometry: zero hits.
- msearch leansearch: "projective morphism coherent relatively flat sheaf derived
  pushforward perfect": unavailable, Internal Server Error.
- rg of the upstream WeilConjectures sources and lean/Sheaf for projective/perfect and the
  exact item id found no theorem stating this item. The upstream names index records
  `isPerfect_Q_cechModuleComplex_of_isClosedImmersion`; its historical RfPerfect source
  module is absent from this checkout. It concerns a Cech module complex, not the recorded
  full derived direct image over an arbitrary locally Noetherian base, so it is not used
  as an existing exact statement. Related `noetherian_perfect_directImage` is a different
  theorem about a perfect object tensored with a bounded complex over a Noetherian base;
  it has different hypotheses and is not an exact duplicate.
- rg found the existing `Scheme.Modules.IsFlatOver` definition in the upstream Basic
  module; no private copy was made. The chosen full theorem name is absent from the
  upstream sources, project Lean and upstream names index.

Validation: scompile.py compiled the delivered module on the server cleanly in 2.3 seconds,
nice 19, two threads, 60-second limit. No local compiler was run. Dry-run result follows
from the required deliver2.py check; the second reader is responsible for delivery.

## Second reading by NJ

I independently read the node JSON, its blueprint source at
sec-picard-framework/sk-thm-picard-semicon/lem-pc-projective-noetherian-rf-perfect.md
(order 673), and the delivered Lean module together. This item's source is the blueprint,
not a Stacks lemma: its statement and three proof paragraphs have no surrounding field,
characteristic, global compactness, or flat-morphism assumption. I also opened all five
statement dependency nodes and the declarations implementing them.

The complete object/hypothesis/conclusion list and correspondence is:

1. Schemes X and S, and a morphism f from X to S: `{X S : Scheme.{u}} (f : X ⟶ S)`.
   Verdict: exact. An arbitrary universe u is bound. The common scheme universe is the
   recorded scheme-morphism convention; schemes of different initial sizes may be placed
   in a common universe.
2. S is locally Noetherian: `[IsLocallyNoetherian S]`. Verdict: exact. I opened Mathlib's
   class: Noetherian rings on affine opens, with no CompactSpace binder. The stronger
   `[IsNoetherian S]` is absent.
3. f is projective: `[IsProjective f]`. Verdict: exact in the blueprint's convention.
   def-pc-projective-morphism records the canonical extracted upstream module. I read the
   source declaration in the group clone's Projective module: `IsHProjective` asks for
   `n : ℕ`, a closed immersion into `ℙ(ULift (Fin (n + 1)); S)`, and its composite equal
   to f; `IsProjective` extends that and `QuasiCompact f`. Stacks morphisms.tex,
   definition-projective (01W8), distinguishes H-projective from its broader unqualified
   projective notion. The node explicitly chooses H-projective plus quasi-compact, and
   the Lean follows that choice. def-pc-morphism-conventions is a convention record, not
   an additional object or declaration.
4. An O_X-module G: `(G : X.Modules)`. Verdict: exact. I opened Mathlib's definition
   `Modules := SheafOfModules.{u} X.ringCatSheaf` and the shared DerivedCategory module;
   the term G is accepted in the shared SheafOfModules category, and no second localization
   on the distinct Modules category instance is introduced.
5. G is coherent: `(hGcoherent : RingedSpace.IsCoherent X.toRingedSpace G)`.
   Verdict: exact. Coherent.lean defines finite type together with finite-type kernels
   of every map from a finite free module on every open U, matching pqf-def-coherent.
   There is no separate finite-presentation, locally-free, or invertibility assumption.
6. G is flat over S: `(hGflat : Scheme.Modules.IsFlatOver G f)`. Verdict: exact here.
   I read the upstream Basic definition: for each affine V of S and affine U of X over V,
   sections of G on U are flat over sections of O_S on V, through `f.appLE`.
   For the coherent (hence quasi-coherent) G in this statement this agrees with the
   source's stalkwise relative flatness: localize to stalks in one direction, and use
   the kernel-localization argument in proof paragraph 2 in the other. Thus this use
   requires no new assumption on G. No `[Flat f]` occurs.
7. The object Rf_*G means G in degree zero followed by the unbounded derived direct image:
   `(schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
   (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G)`.
   Verdict: exact. SchemeDerivedDirectImage specializes the recorded ringed-space
   `derivedModuleDirectImage`, which is the right derived functor of module pushforward;
   its source explicitly identifies computation by K-injective resolutions.
8. The sole conclusion is that this object is perfect on S: `Scheme.IsPerfect S (...)`.
   Verdict: exact. PerfectComplex.lean requires at every point an open neighbourhood
   where restriction is isomorphic to a bounded complex whose terms are retracts of finite
   free modules. This is precisely the recorded definition, not global strict perfectness,
   finite cohomology alone, or a base-change assertion.
9. The three HasDerivedCategory binders provide the chosen localizations for X, S, and
   opens of S required by these recorded definitions. Verdict: categorical infrastructure,
   no additional geometric hypothesis. wX and wS are separately universally bound; open
   restrictions use the target's wS as in IsPerfect. No universe or variable is unbound.

Edge cases: zero G and empty X are included, and give zero direct image; empty S forces
empty X and IsPerfect's pointwise condition is vacuous. No nonempty affine index set is
assumed. The projective embedding allows n = 0 via Fin (n + 1). All characteristics and
non-quasi-compact locally Noetherian bases are included. No global bounded amplitude is
asserted over such a base: perfectness is local. These cases require no signature change.

Independent reuse searches (2026-10-15), with wording different from the worker's:

- msearch LeanFinder, "proper pushforward relatively flat coherent module is a perfect
  complex": eight hits on flat morphisms and tensor exactness; no exact statement.
- msearch Loogle, "IsPerfect, derivedDirectImage": no hits; unknown identifier IsPerfect.
- msearch LeanSearch, "relative flat coherent sheaf projective locally noetherian derived
  image perfect": service unavailable (Internal Server Error); no mathematical verdict
  inferred from this failure.
- rg on Mathlib/AlgebraicGeometry, upstream WeilConjectures, and project lean/Sheaf for
  perfect with pushforward/directImage/direct image, plus IsFlatOver and the proposed
  declaration name. No exact declaration found. I opened the related project signatures:
  noetherian_perfect_directImage assumes globally Noetherian S and concerns a tensor with
  a bounded complex; properSupport_perfect_directImage has different hypotheses and
  includes derived base change; properFlat_single_derivedDirectImage_perfect assumes
  proper finite presentation and finite presentation of F without the locally Noetherian
  base hypothesis. These are related tools, not the same statement to record as existing.
  The upstream names index's isPerfect_Q_cechModuleComplex_of_isClosedImmersion concerns
  a Cech module complex; its historical RfPerfect source is absent from this checkout.

No new node or dependency module is delivered, so H12/H13 introduce no additional files
for this review. All dependency notions used are the recorded shared declarations.
The sole theorem proof is `sorry`; there is no definition, hidden data choice, or proof
added. Module and theorem docstrings identify the blueprint source; the theorem docstring
reproduces all three proof steps with their dependency ids. Statement imports and the
available proof-dependency imports match the plan. The flat-complex-perfect proof node
has no module to import. The node's lean.statement is verbatim the theorem signature.

Mismatches found: none. Changes: appended this independent second reading only; preserved
the correct Lean module and node record without rewriting them. The server scompile.py
check compiled the sole delivered module cleanly in 2.3 seconds, nice 19, two threads,
60 seconds per file. No local compiler or library build was run.

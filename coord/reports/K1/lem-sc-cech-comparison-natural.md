## Worker report

The item is stated in `Sheaf.AlgebraicGeometry.AffineModuleCechComparisonNatural`, as
`AlgebraicGeometry.Scheme.Modules.moduleCechComparison_natural_affine`. Nothing is proved:
all theorem bodies are `by sorry`. The canonical comparison's data are fully defined in
`Sheaf.AlgebraicGeometry.ModuleCechComparison`. A dependency module replaces the unusable
cohomology encoding of `lem-pc-cech-computes` (see below). The item's TeX statement, proof,
proof dependencies, and all maintainer fields are unchanged; its statement dependencies gain
only `def-sc-module-cech-comparison`.

Clause-by-clause reading of the item:

- A scheme X: `(X : Scheme.{u})`, using Mathlib's scheme, not an extra separation,
  noetherianity or finiteness hypothesis.
- A family of opens indexed by I: `{ι : Type u} (U : ι → X.Opens)`.
- The family covers X: `(hcover : iSup U = ⊤)`.
- Every intersection U_{i_0...i_n} is affine:
  `(hU : ∀ (n : ℕ) (y : Fin (n + 1) → ι), IsAffineOpen (⨅ l, U (y l)))`.
  Repetitions are permitted, exactly as in Stacks 01XD. The zero-tuple intersection X
  is not required to be affine; the tuples all have positive length.
- Two quasi-coherent O_X-modules: `(F F' : X.Modules)` and the two separate instances
  `[SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F]` and the corresponding F'.
- A module morphism: `(φ : F ⟶ F')`; it is sectionwise O_X-linear by the category definition.
- Every nonnegative degree: `(p : ℕ)`.
- The two Čech-cohomology objects:
  `((moduleCechFunctor X U).obj F).homology p` and its F' analogue. The functor uses
  the existing Mathlib `CategoryTheory.cechComplexFunctor U`, with section scalars
  restricted along O_X(X) → O_X(V). Its terms are products over the tuples, and its
  differential is Mathlib's alternating restriction differential.
- The two sheaf-cohomology objects:
  `(RingedSpace.moduleCohomology X.toRingedSpace p).obj F` and its F' analogue.
  These are the right derived global-sections functors recorded by pqf-def-cohomology.
- The isomorphisms: the conclusion supplies `e` and `e'` with these sources and targets,
  then requires `e.hom = moduleCechComparison U hcover F p` and the F' version.
  Thus the isomorphisms are the canonical comparisons, rather than arbitrary independent
  choices from `Nonempty`. Their inverses are determined by their forward maps.
- The cochain operation applying φ componentwise is
  `(moduleCechFunctor X U).map φ`. The forget-to-presheaf-module functor maps φ on each
  section module; the existing Čech functor then takes the product of those maps. Taking
  cohomology is `HomologicalComplex.homologyMap ... p`.
- Transport of the induced Čech map to H^p(X,φ):
  `e.inv ≫ HomologicalComplex.homologyMap ((moduleCechFunctor X U).map φ) p ≫ e'.hom =
    (RingedSpace.moduleCohomology X.toRingedSpace p).map φ`.
  Composition is written in Lean's left-to-right convention.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and
  `Scheme.Hom`; a scheme extends a locally ringed space and has affine neighbourhoods;
  its morphisms are morphisms of the underlying locally ringed spaces.
- `lem-pc-cech-computes`: the source import `WeilConjectures.AlgebraicGeometry.Cohomology.Affine`
  reexports `Affine.Leray`; its full `nonempty_cechComplex_linearEquiv_H` signature and
  docstring were read in `Affine/Leray.lean:109`. Its hypotheses are a finite-nonempty-set
  affine-intersection condition, the covering equation, quasi-coherence, and a degree.
  It targets `F.H p`, not the recorded module-derived cohomology. The delivery therefore
  supplies `nonempty_moduleCech_iso_moduleCohomology` in a dependency module, with exactly
  the same mathematical affine-intersection comparison statement and the correct carrier.
- `pqf-def-cohomology`: `Sheaf.Paper.PQFCohomology`,
  `AlgebraicGeometry.sheafCohomologyAndHigherDirectImages`; its signature explicitly
  identifies the cohomological delta-functor degree functors with
  `RingedSpace.moduleCohomology`. The definition and full implementation notes of the
  latter were read in `Sheaf.Topology.RingedSpaceModuleCohomology`; `globalSectionsFunctor`,
  `globalSectionsComplex`, and `globalSectionsFunctor_additive` are reused directly.
- `def-sp-double-complex-total`: the node records Mathlib `HomologicalComplex₂.total`
  and `ιTotal`, reused directly. The existing natural-indexed total-shape signs and finite
  diagonal coproduct instance are imported from
  `WeilConjectures.Mathlib.Algebra.Homology.TotalComplex`; no second total complex is defined.
- `def-sp-injective-resolutions`: Mathlib `InjectiveResolution`, with `cocomplex` and the
  quasi-isomorphism `ι` from the single object in degree zero. Its augmentation and the
  existing `InjectiveResolution.isoRightDerivedObj` are reused directly.
- `def-weil-sheaf-of-modules-category`: Mathlib `Scheme.Modules = SheafOfModules X.ringCatSheaf`.
  The presheaf functor is the existing `SheafOfModules.forget` followed by
  `PresheafOfModules.forgetToPresheafModuleCat`; the source's `Modules.presheafModuleCat`
  is reused to write restriction maps in the zero-cochain construction.
- Enough injectives in the comparison definition is supplied by the already recorded
  `RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace`, not a new instance
  or an extra hypothesis on X. The local `letI` occurs in a definition's implementation,
  never in a theorem signature.

Sources: local Stacks TeX is absent on this machine, so I read the actual source pages
https://stacks.math.columbia.edu/tag/01EQ and https://stacks.math.columbia.edu/tag/01XD.
01EQ constructs alpha and beta into the total complex of the Čech double complex of an
injective module resolution; alpha is a quasi-isomorphism and the map is beta followed
by inverse alpha. 01XD states the affine-intersection isomorphism as global-function
modules. The delivery uses precisely those maps. Our double complex orders resolution
index first, Čech index second; the differential is d_I + (-1)^q d_C, with q the resolution
index. This is the same construction after the standard signed interchange of indices.

Edge cases checked before stating:

- p = 0 gives the usual compatible-sections/global-sections comparison and its naturality.
- Empty I is allowed. The covering equation then forces X to be empty, and no nonempty
  tuple affine hypothesis is imposed. The section and Čech objects on the empty scheme
  are zero, so the asserted isomorphisms and conjugation remain valid.
- No nonempty-index, nonempty-scheme, finite-cover, separatedness, or characteristic
  hypothesis is added. Zero modules and the zero morphism are included.
- Repeated indices, empty intersections (affine empty opens), and disconnected schemes
  are included. Neither the empty finite intersection nor an affine X is required.
- φ = identity gives the identity map by functoriality. A scalar endomorphism gives the
  corresponding scalar cochain operation. Arbitrary choices of unrelated isomorphisms
  would fail this statement; the two forward-map equations exclude exactly that error.
- Universes are explicitly declared inside each namespace; all variables are explicit.
  The scheme, its modules, and the cover index use the shared mathematical universe u,
  as do the source Čech declarations. No test-object hypothesis becomes vacuous through
  an independent lower universe, and no finite or countable restriction is imposed.

Searches performed with the dispatcher search tool (the full transcripts are in
`searches.jsonl`):

- leanfinder, query `Naturality of Cech cohomology comparison isomorphism for quasi coherent
  modules on an affine intersection open cover`: eight results about sheaf gluing,
  equalizers, and restriction naturality; no Čech-to-derived-module comparison.
- loogle, `cechComplexFunctor, NatTrans.naturality`: zero results, unknown identifier
  `cechComplexFunctor` in the service index.
- grep Mathlib CategoryTheory, `cech.*(comparison|natural)|cechComplexFunctor`: two hits
  locating the existing Čech functor, no comparison map.
- leansearch, `canonical Cech comparison map into right derived global sections of a sheaf
  of modules`: unavailable, HTTP Internal Server Error. No successful search is claimed.
- grep Mathlib Algebra/Homology, `cech|Cech`: one local-cohomology comment, no comparison.
- `rg` in the source checkout found `CechComparison.lean` (comparison of two Čech complex
  encodings), `CechCohomology.lean` (existence of an abstract natural iso for an acyclic class
  of abelian sheaves), and `Affine/Leray.lean` (objectwise linear isomorphism with F.H).
  Their signatures and docstrings were read; none defines the 01EQ comparison into the
  recorded module-derived global-sections cohomology.
- `rg` of `lean/Sheaf` found uses of Čech comparison in proof docstrings, including
  `LocallyFreeExtNaturality.lean`, but no canonical module comparison declaration.
- `rg` of the source for this item's blueprint ID and of `dag/lean_names_upstream.json`
  for the proposed names found no existing declaration.
- `python3 tools/blueprint_refs.py search 'Cech comparison'` returned zero blueprint nodes.
  DAG searches located the existing comparison-map *statement* nodes, which have no
  Lean declarations. No definition node provides the concrete canonical comparison;
  the new node names the construction needed in this item's signature.

No STATEMENT-DISPUTED flag or mathematical correction is needed.

## New nodes

`def-sc-module-cech-comparison` records the missing concrete canonical comparison of Stacks
01EQ. Its module defines the Čech coefficient functor using Mathlib, the double complex
using the existing map-on-complexes functor, the restrictions alpha, augmentation beta,
and H(beta) followed by inverse H(alpha) and the existing resolution identification.
All data are explicit. The named proof certificates `moduleCechFunctor_additive`,
`moduleCech_top_restriction`, `moduleCechAlpha_comm`, `moduleCechBeta_comm`, and
`moduleCechAlpha_isIso` have sorry proofs and complete source/proof docstrings; they are
recorded in this construction node's `lean.declarations`. They assert only the facts
needed to type the construction. No naturality or affine-comparison result is built
into the definition. The three search kinds are recorded verbatim by query, with the
actual result counts and unavailable status. The theorem node
`lem-sc-cech-comparison-map-naturality` describes this construction mathematically but
has no Lean declaration; this definition node supplies its data without claiming to
have formalized or proved that separate general naturality statement.

## Dependency modules

`lem-pc-cech-computes`: its original record, `Scheme.Modules.nonempty_cechComplex_linearEquiv_H`,
uses abelian-sheaf Ext cohomology `F.H p`. The item's recorded cohomology dependency instead
uses right-derived global sections on O_X-modules. These carriers are related by a comparison
theorem, not definitional equality. The delivered `AffineModuleCechComputes.lean` states the
node's full isomorphism for every quasi-coherent module on every affine-intersection open
cover, targeting `RingedSpace.moduleCohomology`. Only the dependency node's `lean` is changed;
its note records the unusable old carrier and the replacement statement. The main theorem
then pins down which isomorphisms are meant using the explicitly defined canonical maps.

Validation: all three modules compiled together on the server under the standard limit,
with exit code 0 and no warnings, after removing unused imports. No Lean build ran locally.
The second reading remains for the independently dispatched reader.

## Second reading by K1

I independently opened the item node, all three delivered modules, the new definition
node, and the replacement dependency node. I read the recorded declarations rather than
inferring their meaning from their names. Local Stacks TeX is absent; I obtained the
upstream `cohomology.tex` and `coherent.tex` in this item's scratchpad and read
`lemma-cech-cohomology` (1434–1483, Tag 01EQ) and
`lemma-cech-cohomology-quasi-coherent` (246–264, Tag 01XD), including their proofs.
The rendered source pages were also checked:
https://stacks.math.columbia.edu/tag/01EQ and
https://stacks.math.columbia.edu/tag/01XD.
01EQ assumes a ringed space and an open cover, with no separation or finiteness
hypothesis; 01XD specializes to schemes, quasi-coherent modules and affine intersections.

The item's objects, hypotheses and conclusions, in order, and their Lean renderings:

1. Scheme X [def-pc-scheme]: `(X : Scheme.{u})`. PASS. Mathlib Scheme extends a locally
   ringed space with affine neighbourhoods; the recorded Scheme declaration was opened.
2. An indexed family of opens: `{ι : Type u} (U : ι → X.Opens)`. PASS. No finite,
   ordered or inhabited-index restriction is present.
3. It covers X: `(hcover : iSup U = ⊤)`. PASS. This is equality of opens, hence precisely
   the union condition.
4. Each positive-length tuple intersection is affine:
   `hU : ∀ (n : ℕ) (y : Fin (n + 1) → ι), IsAffineOpen (⨅ l, U (y l))`.
   PASS. This matches all p ≥ 0 and all indices in 01XD, permits repeated indices,
   and does not impose affineness of X as the intersection of an empty tuple.
5. Two quasi-coherent O_X-modules: `(F F' : X.Modules)` and the separate
   `SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf)` instances for F and F'.
   PASS. The recorded Mathlib `Scheme.Modules := SheafOfModules.{u} X.ringCatSheaf`
   and its morphism/category declarations were opened; these are modules over the
   actual structure sheaf, not merely underlying abelian sheaves.
6. A module morphism: `(φ : F ⟶ F')`. PASS. Its section components are linear and
   compatible with restriction. No extra injectivity or surjectivity is assumed.
7. Every degree p ≥ 0: `(p : ℕ)`. PASS, including zero.
8. Čech cohomology for F and F': `((moduleCechFunctor X U).obj F).homology p`
   and the corresponding F' expression. PASS. I opened Mathlib's
   `CategoryTheory.cechComplexFunctor`: terms are products over `Fin (p + 1) → ι`
   and the differential is the alternating coface differential. The delivered functor
   composes this existing functor with the existing module forgetful/scalar restriction
   functors; it does not introduce another Čech differential. The upstream
   `Scheme.Modules.presheafModuleCat` definition was also opened and matches these
   scalar restrictions.
9. Sheaf cohomology for F and F':
   `(RingedSpace.moduleCohomology X.toRingedSpace p).obj F` and its F' analogue.
   PASS. I opened `RingedSpace.globalSectionsFunctor`, `globalSectionsComplex`,
   `moduleCohomology`, and `sheafCohomologyAndHigherDirectImages` of the recorded
   dependencies. This is right-derived module-valued global sections as required by
   pqf-def-cohomology.
10. The two comparison isomorphisms: existential `e` and `e'` with exactly these
    sources and targets, and `e.hom = moduleCechComparison U hcover F p` plus the
    corresponding F' equation. PASS. These equations specify the canonical maps of
    01EQ. They make precise the identifications intended by lem-pc-cech-computes,
    as explicitly confirmed by lem-sc-cech-comparison-map-iso-affine; there is no
    assumption of arbitrary, unrelated choices of isomorphisms.
11. Componentwise application of φ: `(moduleCechFunctor X U).map φ`, followed by
    `HomologicalComplex.homologyMap ... p`. PASS. The composite functor maps φ on
    each section and then on each product factor, exactly the cochain operation in
    the node.
12. Transport to H^p(X,φ):
    `e.inv ≫ HomologicalComplex.homologyMap ((moduleCechFunctor X U).map φ) p ≫ e'.hom =
    (RingedSpace.moduleCohomology X.toRingedSpace p).map φ`.
    PASS. Lean composes left to right, so this is c_F' composed with the Čech map
    and c_F inverse. The quantifiers introduce F, F', φ and p before these
    isomorphisms; the forward-map equations determine them uniquely.

New node and dependency reading (H12/H13):

- `def-sc-module-cech-comparison` is genuinely missing as construction data. I opened
  the existing `lem-sc-cech-comparison-map-naturality`,
  `lem-sc-cech-comparison-map-iso-affine`, and `lem-sc-cech-h1-map-natural`: these are
  statement nodes with no recorded Lean construction, not alternative definition nodes.
  The new node cites the existing scheme, module category, Čech complex, injective
  resolution, total complex and module cohomology notions. Its fields have the required
  definition/split status, empty proof/proof_deps, null mathlib_match, three search kinds
  (including the explicitly unavailable LeanSearch), worker/item/group/date creation,
  correct chapter/unit, ancestor and via, none audits and complete Lean record.
- Its module follows 01EQ's alpha/beta construction literally. I checked the
  `InjectiveResolution` structure and `isoRightDerivedObj` signature and naturality in
  Mathlib: the latter goes from derived cohomology to resolution cohomology, so its
  inverse at the end of `moduleCechComparison` has the correct direction. Alpha inserts
  restrictions into (n,0); beta inserts the augmentation into (0,n). The existing
  natural-indexed total-shape signs give d_I + (-1)^n d_C. This exchanges the two
  source indices by the usual signed interchange and preserves both edge inclusions.
  The enough-injectives certificate was opened and applies to every ringed space.
  All data are explicit; the needed proof certificates are named theorems, documented,
  and recorded in this node's declarations. Their proofs are sorry, not hidden data.
- `lem-pc-cech-computes`: I opened the old
  `nonempty_cechComplex_linearEquiv_H` in `Affine/Leray.lean`, including its full
  signature and implementation notes. It targets F.H, the abelian-sheaf Ext encoding,
  so it is unusable for this item's recorded derived-module carrier without a bridge.
  The replacement module states the same scheme/cover/affine-intersection/quasi-coherence
  hypotheses and all nonnegative degrees, with a module isomorphism into the correct
  cohomology. Its proof docstring follows the dependency node's spectral sequence and
  affine vanishing proof. Its lean.note explains the replacement; no other field changes.
- The existing total-complex and injective-resolution operations are reused. The general
  site Čech node currently has no Lean record, but its required complex construction is
  already Mathlib's functor (also recorded by def-weil-pbc-cech-complex); no missing
  private notion or extra dependency module is needed for this specialization.

Edge cases: PASS for empty index set (hcover forces the empty scheme), empty scheme,
empty intersections, repeated indices, zero modules and zero morphisms, and p = 0.
There is no field/characteristic, no noetherian/separated/finite-cover assumption, and no
nonempty-index assumption. Universe u is explicit and polymorphic; it is the universe
of the scheme, its modules and the cover products, as in the upstream Čech declarations.
There are no test-object quantifiers in a smaller universe and no unbound variables.
Identity morphisms reduce to identity transport by functoriality.

Independent searches used different wording from the first reader:

- `msearch.py ... leanfinder 'Functoriality of the canonical map from an open cover Cech
  complex to derived global sections in modules'`: eight results, about presentations,
  global-section restrictions and gluing; no matching comparison declaration.
- `msearch.py ... loogle 'InjectiveResolution.isoRightDerivedObj'`: service index reports
  unknown identifier, zero hits. I located and read the actual declaration locally.
- `msearch.py ... leansearch 'Cech cohomology comparison map to derived global sections
  natural in sheaves of modules'`: unavailable (Internal Server Error); no successful
  or negative search verdict is claimed.
- Independent rg for `cech.*(compar|deriv|natural)|compar.*cech` in Mathlib's sites,
  upstream Topology/Sheaves, and lean/Sheaf found the upstream CechComparison and
  CechCohomology modules. I opened their naturality and natural-isomorphism signatures:
  the former compares two Čech encodings, and the latter targets abelian-sheaf functorH
  under an acyclic-class condition, not the 01EQ module-derived comparison. Neither
  duplicates this delivery. Project hits are proof comments, not comparison definitions.
- DAG searches for canonical/Čech and the proposed names in the upstream-name index
  found no reusable definition of the canonical module map. Existing comparison
  statement nodes were opened as discussed above.

Mismatch and repair: the multi-declaration construction module lacked the required
main-declarations list in its module docstring. I added `## Main definitions and statements`
with its functor, double complex, alpha/beta, invertibility certificate and comparison map.
No mathematical or signature mismatch was found; no Lean signature, node statement,
statement dependency or node Lean record was rewritten. No statement correction or
STATEMENT-DISPUTED flag is needed. All declaration docstrings carry the source and their
own blueprint id; the main theorem follows both node proof steps. Every delivered theorem
body is sorry, with no proof work added, no hollow definition and no file-local notation.

Validation: the three modules compiled together via scompile.py in dependency order on
2026-10-12, in 4.5 seconds, exit code 0, with no warnings. The signatures remain verbatim
those of their node lean.statement records. Delivery preflight is run after this reading.

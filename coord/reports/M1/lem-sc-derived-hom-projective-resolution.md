## Worker report

The module `lean/Sheaf/Algebra/Homology/DerivedHomProjectiveResolution.lean` states
`CategoryTheory.derivedHom_projectiveResolution`. No theorem is proved.

Hypothesis and clause correspondence:
- The source's commutative ring is `{A : Type uP} [CommRing A]`; modules are
  `F G : ModuleCat.{uP} A` (ordinary modules, equivalently module sheaves on the
  one-point ringed site). All module universes are explicit.
- The complex is `E : CochainComplex (ModuleCat.{uP} A) ℤ`.
- Bounded above means an arbitrary bound `d : ℤ` with `[E.IsStrictlyLE d]`;
  this does not impose a special cutoff or finite length.
- Degreewise projectivity is `[∀ n : ℤ, Projective (E.X n)]`.
- The given resolution is the actual chain map `e : E ⟶ (single ... 0).obj F`
  and `_he : QuasiIso e`; it is not a selected unrelated resolution.
- `HasDerivedCategory.{wP}` is the localization-size infrastructure, with arbitrary
  explicitly bound morphism universe, not a finiteness or projectivity hypothesis.
- Representation is the first `Nonempty` isomorphism, from `Q.obj (moduleHomComplex E G[0])`
  to `moduleDerivedHom F[0] G[0]`. Both are objects of `D(A)`, with their A-module structures.
- The second clause quantifies every `i : ℤ` and compares ordinary complex cohomology
  (`HomologicalComplex.homologyFunctor`) with derived-object cohomology
  (`DerivedCategory.homologyFunctor`). The docstring specifies the canonical zigzag
  and that these cohomology isomorphisms come from this comparison. As in other landed
  comparison statements, isomorphism existence is encoded by `Nonempty`.

Dependency declarations inspected:
- `def-weil-sheaf-of-modules-category`: the usable general-site match is `SheafOfModules`
  in Mathlib.Algebra.Category.ModuleCat.Sheaf; its scheme-only `Scheme.Modules` record
  is not the carrier for ordinary ring modules. Here Mathlib's existing `ModuleCat A`
  is used directly for the one-point specialization.
- `def-pur-derived-internal-hom`: `CategoryTheory.derivedInternalHom` in
  Sheaf.Algebra.Homology.DerivedInternalHom is explicitly on small commutative ringed sites,
  not on `ModuleCat`. Its full signature and replacement construction were read. The
  missing ordinary module object is supplied by the new `def-sc-module-derived-hom`,
  using the same K-injective prescription, without redefining sheaf RHom.
- New definition nodes supply `CochainComplex.moduleHomComplex` and
  `CochainComplex.moduleDerivedHom`, in the modules of the corresponding names.
- Derived category, localization and cohomology are Mathlib's `DerivedCategory`,
  `DerivedCategory.Q`, `DerivedCategory.homologyFunctor`; cochain complexes are
  `CochainComplex`, the recorded declaration of `def-pc-cochain-complex-modules`.
- K-injectivity is Mathlib's `CochainComplex.IsKInjective`; the actual replacement
  is `CochainComplex.kInjectiveResolutionFunctor` in
  WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution. Its full
  definition and natural quasi-isomorphism were inspected. ModuleCat.AB supplies
  Grothendieck abelianness, including for the zero ring.

Edge cases: zero ring and zero modules are allowed; E may be zero when F is zero;
E is allowed to be unbounded below. The bound can be negative, zero or positive.
Every integer cohomological degree is included. Product terms use Mathlib's full
`HomComplex.Cochain` families, not finite-support families. No nonzero ring,
Noetherian or finite generation assumption is inserted. Commutativity is needed for
pointwise A-scalars to preserve A-linear maps; it is made explicit by the correction.

Searches performed during this work (all recorded verbatim as outcomes in the new nodes):
- LeanFinder query `bounded above projective resolution computes derived Hom of modules
  as complex of abelian groups`: 8 hits, all Ext/projective resolution infrastructure;
  no module-valued RHom object or exact statement.
- Loogle query `CochainComplex.HomComplex, CochainComplex.kInjectiveResolutionFunctor`:
  zero hits, unknown second identifier.
- LeanSearch query `derived Hom of modules computed using a K injective resolution`:
  unavailable, Internal Server Error.
- msearch grep `moduleDerivedHom|moduleHomComplex|derivedHom` in Algebra/Homology:
  zero hits. Direct rg in Mathlib, WeilConjectures and lean/Sheaf found the additive
  group HomComplex and the sheaf Hom/RHom, but neither new module-valued notion.
- DAG titles/statements and `tools/blueprint_refs.py search 'derived Hom'` were searched:
  only the existing sheaf notions and this item; no ordinary module-complex definition.
  Upstream was also searched for this item's blueprint id: no hits.

Source texts were opened online because literature/stacks-project is absent locally:
https://stacks.math.columbia.edu/tag/0A8H (product terms and differential),
https://stacks.math.columbia.edu/tag/0A5W (K-injective construction and Lemma 15.75.2),
https://stacks.math.columbia.edu/tag/06XR (projective resolution Ext computation).

## New nodes

`def-sc-module-hom-complex`: the ordinary module-valued Hom complex, with product terms
and signed differential, from Stacks 0A8H. Mathlib's HomComplex is AddCommGrpCat-valued.
The new definition reuses its existing `HomComplex.Cochain` and A-linear `δ_hom`;
only the ModuleCat packaging is added. Structural laws reuse Mathlib's δ_shape and δ_δ.
This is not a second sheaf-Hom definition. Searches above found no existing DAG node
or declaration for this packaging.

`def-sc-module-derived-hom`: the derived object attached to two representative module
complexes is Q Hom(L,I(M)), from Stacks 0A5W. Its data is written in full, using the
existing functorial K-injective replacement and the previous new module Hom complex.
No data is sorry, and no unrelated arbitrary object is bound as RHom. The existing
ringed-site RHom cannot be applied directly to ModuleCat; the searches above found no
module version already carried by a node or declared in the libraries.

## Statement corrected

The original statement is preserved verbatim in `statement_change.old_statement`.
The original first words were “Let A be a ring”. They now read “Let A be a commutative
ring”. This makes the Stacks standing convention explicit: module-valued internal Hom
is not a left A-module under pointwise scalars over an arbitrary noncommutative ring.
For example, for the left regular module A, multiplying an A-linear map by a noncentral
scalar does not preserve left A-linearity. The source 0A8H constructs A-module Hom
terms; 0A5W takes RHom in D(A), with commutative rings understood. The added sentence
names the two required module constructions; the source's conclusion is unchanged.
The statement-dependency additions are recorded with `old_stmt_deps`. No proof,
proof-dependency, target or unit statement was changed.

Every actual citer was found by searching the node id then filtering stmt_deps and
proof_deps (the K-projectivity node mentions the item only in provenance):
- `lem-sc-derived-internal-hom-stalk-localization`: holds; the ring is the commutative
  local ring O_{X,x}.
- `lem-sc-affine-rhom-qcoherent`: holds; the coordinate ring of Spec(A) is commutative.

The caller nodes were read and are not edited. No STATEMENT-DISPUTED flag remains.

## Second reading by M1

I read the corrected node before the Lean, and checked its correction against
Stacks `more-algebra.tex`, `section-hom-complexes` (0A8H), `section-RHom`
(0A5W), and `lemma-RHom-out-of-projective` (Lemma 15.75.2). I also read
`derived.tex`, `lemma-compute-ext-resolutions` (06XR), whose second part is
in an arbitrary abelian category. The local literature checkout is absent;
I fetched those two official Stacks TeX files into the sandbox scratchpad.
The module-valued construction in More on Algebra is over a commutative ring
(the Stacks convention), with no Noetherian, finite generation, bounded-below,
nonzero, or finite-projective-dimension assumption. The correction is justified.

Object, hypothesis, and conclusion checklist, in node order:

- A commutative ring: `{A : Type uP} [CommRing A]`. Exact; no field,
  domain, or nontriviality assumption. `HasDerivedCategory.{wP}` specifies
  the localization universe, as in `def-weil-abstract-derived-category`.
- Two A-modules F and G: `(F G : ModuleCat.{uP} A)`. Exact ordinary
  modules, rather than scheme sheaves or modules over a varying site.
  I opened Mathlib's `ModuleCat` structure and the recorded general-site
  `SheafOfModules` structure. The latter and the scheme-only `Scheme.Modules`
  record are not directly the carrier in this node; no private sheaf category
  or sheaf-Hom copy is introduced.
- A cochain complex E: `E : CochainComplex (ModuleCat.{uP} A) ℤ`.
  Exact integer grading; the generic Mathlib declaration recorded by
  `def-pc-cochain-complex-modules` applies to this category.
- E bounded above: `(d : ℤ) [E.IsStrictlyLE d]`. Exact: terms above d
  are zero objects, with arbitrary d and no lower bound.
- Projective terms: `[∀ n : ℤ, Projective (E.X n)]`. Exact categorical
  projectivity in A-modules; no finite rank or finite generation is imposed.
  I read `isKProjective_of_projective` at KProjective.lean:113, including
  its bound and projectivity binders, rather than relying on its name.
- The given quasi-isomorphism to F[0]: `e : E ⟶ (single ... 0).obj F`
  and `(_he : QuasiIso e)`. Exact. In the repaired conclusion e actually
  specifies precomposition; it cannot be replaced by an unrelated resolution.
- The ordinary Hom complex: `moduleHomComplex E ((single ... 0).obj G)`.
  I read the entire new definition, Mathlib's `HomComplex.Cochain` product
  family and `δ_hom`, and checked the differential against 0A8H. Exact
  full products and pointwise A-linear structure, with the Stacks sign.
- RHom: `moduleDerivedHom F[0] G[0]`. I read its full body and the
  upstream `kInjectiveResolutionFunctor` and `toKInjectiveResolution`,
  including their quasi-isomorphism and K-injectivity guarantees. Its data
  are exactly Q Hom(F[0], I(G[0])), as in 0A5W. I also read the entire
  recorded `derivedInternalHom` declaration and construction: it has a
  ringed-site sheaf carrier and cannot simply be applied to `ModuleCat A`.
- Representation and canonical comparison: repaired. Originally the conclusion
  was only `Nonempty` of an arbitrary object isomorphism, with canonicality
  asserted in prose. It now quantifies the chain maps a and b with their
  exact component formulas: a postcomposes with the fixed K-injective
  resolution map of G[0], and b precomposes with e. Their images under Q
  are isomorphisms. The comparison c is required to satisfy
  `c.hom ≫ Q.map b = Q.map a`. Since b is invertible, this specifies c
  uniquely and is precisely the source's localized comparison zigzag.
  These are descriptions of the construction, not extra hypotheses.
- Every integer cohomological degree, canonically: repaired. `∀ i : ℤ`
  still provides an isomorphism from ordinary complex homology to derived
  homology; now the witness h is required to equal
  `(homologyFunctorFactors ... i).symm.app ... ≪≫
  (homologyFunctor ... i).mapIso c`. Thus every h is the cohomology
  comparison induced by the same c, rather than an unrelated isomorphism.
  The two cohomology functor signatures and factorization direction were read
  in Mathlib's DerivedCategory/HomologySequence.lean.

Edge cases: the zero ring, zero F or G, and zero E when it resolves zero
are admitted. The bound d may be negative, zero, or positive; E may have
infinitely many negative-degree terms. Every i, including zero and negative
integers, is quantified. No characteristic is restricted. The product index
is all integer degree pairs, not finite support; no arbitrary empty-index
family is introduced by this node. Schemes and their emptiness are not
objects in this algebraic statement. All universes (`uP`, `wP`, `uH`,
`uD`, `wD`) are explicitly bound, and the category/localization universes
are those of the dependency infrastructure, not a smallness assumption on F.

Independent searches:

- LeanFinder via msearch: `internal Hom of complexes of modules derived Hom
  bounded projective` returned eight Ext/projective-resolution declarations,
  including `ProjectiveResolution.isoExt` and `extMk`; none is this
  object-level RHom comparison with an arbitrary integer-indexed E.
- Loogle via msearch: `CochainComplex.HomComplex.Cochain` returned twelve
  declarations. I inspected the product cochains, scalar action, composition,
  `δ`, and `δ_hom`; these are reused, not restated as new notions.
- LeanSearch via msearch: `module valued Hom complex with differential and
  derived Hom projective resolution` was unavailable (Internal Server Error).
  No mathematical negative verdict is inferred from that service failure.
- msearch grep `internalHomObj|HomComplex|RHom`, and direct rg with
  `RHom|derivedHom|moduleHomComplex|moduleDerivedHom|internalHom.*[Cc]omplex`
  on Mathlib, WeilConjectures, and the project's Lean. Direct DAG and
  upstream-name searches also included `module-valued Hom`,
  `Hom complex of modules`, and `internalHomObj`.
- The independent grep found upstream `CochainComplex.internalHomObj` and
  `DerivedCategory/Monoidal/Closed.lean`, omitted from the first report.
  I opened their signatures, differential, and construction. The former uses
  differential `(-1)^p (f d_M - d_L f)` on the (p,q) factor, rather than
  the Stacks `d_M f - (-1)^n f d_L`. The latter's ihom also uses that
  convention and a monoidal/K-flat derivability structure; its own docstring
  explicitly leaves the concrete K-injective Hom-complex comparison as future
  API. Neither is the exact concrete complex prescribed here. The new module
  packaging reuses Mathlib's standard-sign cochains and linear differential;
  it does not replicate that differently signed construction.

New-node reading: both new nodes have self-contained statements, definition
kind, split status, null mathlib_match, empty proof/proof_deps, creation data
for this item/group, this item's chapter and unit, ancestor provenance, and
lean_audit none. Their dependencies supply complexes/localization and
K-injectivity; no new unsupported mathematical data are hidden. The module
Hom node says precisely 0A8H's product-and-differential construction. The
module derived-Hom node says precisely 0A5W's fixed K-injective model on
representatives. The definitions contain no sorry data or proofs depending
on a local axiom; the Hom-complex structure laws reuse Mathlib's δ_shape and
δ_δ. No dependency module is included in this delivery.

Correction-citer reading: I opened both actual citers. In
`lem-sc-derived-internal-hom-stalk-localization`, Steps 4 and 5 apply the
result over O_{X,x}, a commutative local ring. In
`lem-sc-affine-rhom-qcoherent`, Step 4 applies it over the commutative
coordinate ring of Spec(A). Both recorded holds:true verdicts remain valid;
neither citer was edited.

Changes: only the item's Lean conclusion, its docstring explanation, and its
verbatim lean.statement record were changed, plus this report. The earlier
Worker report describes the superseded Nonempty-only conclusion. The node's
corrected mathematical statement and both new definitions were retained.
The theorem still has proof `by sorry`; nothing was proved in stage 2.
All three delivery modules compiled together on the server in dependency
order (ModuleHomComplex, ModuleDerivedHom, DerivedHomProjectiveResolution),
exit code 0, in 1.7 seconds, with no warnings. There are no local definitions,
notations, instances, unbound variables, or let/show binders in the signature.

## Reviewer FIX (R-dhp, stage 2)
The two new definition nodes def-sc-module-hom-complex and def-sc-module-derived-hom are
second spellings (H12/H4) of the landed def-pur-hom-complex (`CategoryTheory.homComplex`)
and def-pur-derived-internal-hom (`CategoryTheory.derivedInternalHom`) specialised to the
one-point ringed site, which the citers (lem-sc-derived-internal-hom-stalk-localization)
and STATE (DERIVED INTERNAL HOM) prescribe; they are dropped with their modules
(--drop-nodes/--drop-files). The statement correction only named those nodes and made
the Stacks commutative-ring convention explicit, which derivedInternalHom (a sheaf of
CommRingCat) already imposes; it is reverted (--revert-statement). The Lean is restated on
`CochainComplex.onePointRingSheaf A` (landed, lem-pc-kflat-tensor-quasi-iso): A-modules
are `SheafOfModules` on that site, `Hom^•(E, G[0])` is `homComplex`, R Hom is
`derivedInternalHom ⊥ (onePointRingSheaf A)`; the representation is an isomorphism
`Q Hom^•(E,G[0]) ≅ R Hom(Q F[0], Q G[0])` together with the canonical comparison maps
(postcomposition with η_{G[0]} of every functorial K-injective replacement, precomposition
with e) becoming isomorphisms after Q (form of the landed
isIso_homComplex_resolution_of_isStrictlyPerfect), and the cohomology identification for
every i : ℤ. Compiled with SHEAF_GROUP=L tools/lean_file.sh: 4.0 s, no warnings.

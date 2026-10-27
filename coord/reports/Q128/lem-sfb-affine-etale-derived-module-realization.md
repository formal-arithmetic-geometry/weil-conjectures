## Worker report

Stage 2, Q128, 2026-10-23. The accepted Q65 stage-1 split is preserved.
The inherited ending concerned an unchanged stage-1 delivery, not a defect in
this stage-2 assignment. The current node has no Lean record and is listed
at stage 2 in coord/queue.tsv. There was no preserved Lean module, node copy
or report when this continuation started, and no delivery was in progress.

The module Sheaf.AlgebraicGeometry.AffineEtaleDerivedModuleRealization states
`AlgebraicGeometry.Scheme.Modules.exists_affineEtaleDerivedModuleRealization`.
Its only postponed proof is that named theorem. The three accompanying
helpers construct the associated functor and global sections from existing
canonical functors and write the cohomological full-subcategory predicate.
They are parts of the objects already introduced in the item's statement;
the repair below records the pre-existing canonical site constructions in a new definition node without adding Lean definitions. No data is obtained from a
mere existence theorem or supplied by sorry.

Hypotheses and clause correspondence:

- A commutative ring: `(A : Type u) [CommRing A]`. The affine scheme is
  `Spec (.of A)` throughout; no nonzero, field, Noetherian, finite-type,
  characteristic or boundedness hypothesis is imposed.
- The small étale site and its usual structure sheaf are those of
  `SmallEtaleModules (Spec (.of A))`. This existing abbreviation is
  `SheafOfModules.{u} (smallEtaleModuleRing (Spec (.of A)))`; its ring
  presheaf is the existing regular-functions presheaf. This is the
  scheme small étale site, rather than constant-coefficient étale sheaves
  or a replacement abstract site.
- The associated sheaf a_A is the actual composite
  `tilde.functor (.of A) ⋙ c.extension`, named
  `affineEtaleAssociatedFunctor A c`. The existing extension is the
  canonical ringed-site pullback, constructed by Mathlib's
  `SheafOfModules.pullback` using its specified regular-function map.
  `ZariskiEtaleModuleContext` stores only proofs of continuity and
  existence of its adjoint. The existential `c` therefore supplies
  construction proofs, not an arbitrary functor or comparison.
- The description on affine étale Spec B is implemented through this
  canonical construction. The recorded Zariski/étale comparison identifies
  its sections on every étale V with Gamma(V, V^* tilde(M)), including the
  regular-function scalar action and maps in M. The recorded affine
  pullback-sections lemma identifies this with B tensor_A M. The switch
  from M tensor_A B is the usual tensor symmetry. These are the existing
  associated-sheaf construction and comparison, not a substitute sheaf
  defined only by an abstract equivalence. Restriction sends b tensor m
  to g-sharp(b) tensor m as explained in the proof docstring.
- Exactness is the pair `PreservesFiniteLimits` and
  `PreservesFiniteColimits` of this functor in the ambient module-sheaf
  category; faithfulness is its `Faithful` class. Its additive structure
  is quantified as a conclusion so that the termwise functor can be typed.
- D(A) is `DerivedCategory (ModuleCat.{u} A)`. The target is the full
  subcategory of `DerivedCategory (SmallEtaleModules (Spec (.of A)))`
  cut out by `smallEtaleDerivedQCohProperty`: for every `i : ℤ`, the
  existing `DerivedCategory.homologyFunctor` has an `IsQuasicoherent`
  value. The predicate is Mathlib's local presentation by arbitrary
  coproducts of the ring. No bounded or coherent subcategory is used.
- The displayed derived equivalence is the existential `e : ... ≌ ...`.
  The first natural isomorphism identifies `Q ⋙ e.functor ⋙ inclusion`
  with `a_A.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q`. Thus this
  is the equivalence induced termwise by the specified a_A.
- Ordinary global sections is `affineEtaleGlobalSections A c`, namely
  `c.restriction ⋙ moduleSpecΓFunctor (R := .of A)`. Open restriction
  followed by evaluation on the whole scheme is evaluation on the
  terminal small étale object. The existing `moduleSpecΓFunctor` uses
  the usual Gamma(Spec A) = A scalar identification.
- Derived global sections is `RG`, with transformation `η` from termwise
  sections on the homotopy category to `Qh ⋙ RG`. Bijectivity of
  `β ↦ η ≫ whiskerLeft Qh β` for every target functor is precisely the
  total right-derived universal property. The next clause makes η
  invertible on every K-injective complex. For every complex K the
  following existential supplies a K-injective I and quasi-isomorphism
  f : K → I, together with `RG(Q K) ≅ Q(Gamma(I))`. These clauses state
  both existence of the resolutions and the requested computation.
- `Nonempty (e.inverse ≅ inclusion ⋙ RG)` identifies the quasi-inverse
  with that derived sections functor, rather than an unspecified inverse.
- For every integer i, a natural functor isomorphism identifies
  `e.functor ⋙ inclusion ⋙ H^i_et` with `H^i_A ⋙ a_A`. This includes
  naturality in E, not merely individual isomorphisms of objects.
- The final natural functor isomorphism
  `a_A ⋙ affineEtaleGlobalSections A c ≅ 𝟭 (ModuleCat A)` is the
  claimed Gamma(U_et,a_A(M)) ≅ M, naturally in M.
- The two `HasDerivedCategory` binders retain independently chosen
  localization morphism universes wA and wE. They are the size convention
  of the recorded abstract derived-category definition, and impose no
  equality on the two universes or on the site universes. The additive
  proof witnesses are conclusions, not additional assumptions.

Dependency interfaces read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Spec` and `Spec.map`;
  Mathlib.AlgebraicGeometry.Sites.Etale and Morphisms.Etale:
  `Scheme.smallEtaleTopology` and `Scheme.Etale`.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: read the algebraic-space,
  small-site and regular-functions interfaces of def-trf-algebraic-space.
  The item concerns the scheme Spec A; its scheme site and regular-function
  ring are already furnished by the canonical scheme comparison below.
- Sheaf.CategoryTheory.RingedSiteModules:
  `CategoryTheory.ringedSiteModules`, the transparent abbreviation of
  Mathlib's `SheafOfModules` used by the existing small étale module carrier.
- Mathlib.Algebra.Homology.DerivedCategory.Basic and HomologySequence:
  `DerivedCategory`, `HasDerivedCategory`, `Q`, `Qh`, `homologyFunctor`.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule: read its
  `QCoh` interface and slice obligations; for this scheme specialization
  use the retained exact Mathlib match `SheafOfModules.IsQuasicoherent`
  from Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent. No duplicate
  local-presentation predicate is introduced.
- Mathlib.Algebra.Homology.HomotopyCategory.KInjective:
  `CochainComplex.IsKInjective`; `QuasiIso f` records the resolution map.
- Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence:
  `smallEtaleModuleRing`, `SmallEtaleModules`,
  `ZariskiEtaleModuleContext.extension`, `.restriction`, and the theorem
  `scheme_zariski_etale_quasiCoherent_equivalence`. The canonical definitions are now owned by `def-sfb-scheme-zariski-etale-module-constructions` in stmt_deps. The theorem stays only in proof_deps and proof step 1; no witness is chosen from it.
- The proof-only imports retain the recorded modules for affine
  pullback sections, finite-limit preservation of tilde, the affine
  Zariski derived equivalence, K-injective resolutions, and the total
  derived construction. The two proof dependencies without Lean records
  are not imported as nonexistent modules. They are not needed to type
  the statement, whose whole proof is postponed.

Sources read: spaces-perfect.tex lemma-epsilon-flat and
lemma-derived-quasi-coherent-small-etale-site (08H8 and 071Q), and
perfect.tex lemma-affine-compare-bounded (06Z0). They assert exact
pullback and the unbounded equivalences with the indicated inverse.
The existing associated-sheaf interfaces and their full signatures and
proof docstrings were read in the live source checkout.

Edge cases checked before writing: A = 0 gives the empty spectrum and
zero module categories; no nonemptiness binder excludes it. M = 0 and
zero complexes are included. Every integer cohomological degree,
including negative degrees, is covered by `ℤ`. Arbitrary unbounded
complexes are included. No finiteness condition on modules or rings is
introduced. The module carriers stay in universe u, while the presented
étale site retains its actual object and morphism universes.

Searches performed through msearch.py under this group/item (the local
search log records the actual responses):

- LeanFinder, "The derived category of modules over a ring is equivalent
  to complexes with quasicoherent cohomology on the small etale site of
  its spectrum": eight generic derived-localization and ordinary
  scheme-module-category results, no affine small étale realization.
- Loogle, `DerivedCategory, SheafOfModules`: zero hits.
- Mathlib grep, `[Ee]tale.*[Dd]erived|[Dd]erived.*[Ee]tale`,
  AlgebraicGeometry: zero hits.
- LeanSearch, "Exact functors and derived categories of quasicoherent
  modules on affine etale sites": eight generic exact-functor and Ext
  declarations, none stating this realization.
- rg over lean/WeilConjectures and lean/Sheaf for small étale module,
  affine étale derived equivalence, associated-sheaf and quasi-coherent
  derived-category names located the canonical extension and ordinary
  Zariski affine derived equivalence used here. No declaration states
  this item. Searching the item id in WeilConjectures found no match.

No disputed mathematical assertion was found. The repair adds an explicit definition-node citation to the associated-functor description; its statement_change records this clarification and the complete citer audit. The proof, proof_deps and accepted mathematical split are unchanged. The Lean source has explicit universe/variable binders and no
line over 100 characters. Initial prescribed server compilation passed.
The dry-run preflight and delivery are performed with deliver2.py.

## Repair of returned H2

The initial saved-packet dry run passed at 596752d10bc, but that did not address
the independent return against immutable head eca1a9462a5f. Inspection of the
saved item against the current read clone confirmed that only lean and the
extra theorem dependency differed before repair. The prescribed live-source
read confirmed the same definitions in the server module. The sandbox Lean
module and its lean.statement remain byte-identical. The theorem is retained
in proof_deps and step 1. The item's independent existential context is not
a choice of the theorem's witness.

## New nodes

`def-sfb-scheme-zariski-etale-module-constructions` records, with existing:true on
Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence,
smallEtaleModulePresheaf, smallEtaleModuleRing, SmallEtaleModules,
zariskiEtaleOpenRingMap, zariskiEtaleModuleRestriction,
zariskiEtaleModuleExtension, ZariskiEtaleModuleContext and its extension and
restriction. No declarations are moved, copied or newly defined. Stacks 03DU
gives the regular-function sheaf; 03FH identifies extension as the canonical
ringed-site tensor pullback; the proof of 0GN7 describes restriction along
Zariski opens. The node cites the existing scheme, two sites and module-sheaf
definition nodes. Its statement matches the actual regular-function ring map
and the two proof fields, without asserting existence of a context or any
comparison theorem. All schemes, including the empty scheme, are allowed.
The actual u-small module carrier and the presented site universes are retained.

LeanSearch for canonical Zariski/small-etale module extension and restriction
returned generic restriction-of-scalars and site declarations. Loogle for
SheafOfModules.pullback and SheafOfModules.pushforward returned the generic
ringed-site API. Mathlib grep for the scheme-specific names returned zero hits.
Source rg found the exact definitions in the landed Sheaf module, none in
WeilConjectures; DAG rg found only theorem nodes using them, with no definition
node owning them. blueprint_refs.py search found zero matching blueprint nodes;
ancestor returns None, as for the accepted item's inherited ancestry. Actual
msearch responses are preserved verbatim in the new node's mathlib_searches.

## Statement corrected

The old statement is preserved verbatim in statement_change.old_statement.
Its only change explicitly identifies the associated functor as Zariski tilde
followed by the canonical extension and cites its new definition node. This
repairs the missing definition ownership, rather than changing the mathematical
assertion. Stacks 03FH gives precisely this construction. The complete citer
audit, obtained by examining every stmt_deps and proof_deps reference, is:

- `lem-sfb-affine-etale-derived-hom-realization`: holds; Only the existing canonical construction underlying a_A is now cited through its definition node; the exact functor, equivalence and all comparisons used here are unchanged.
- `lem-sfb-proper-flat-space-derived-duality`: holds; Only the existing canonical construction underlying a_A is now cited through its definition node; the exact functor, equivalence and all comparisons used here are unchanged.
- `lem-sfb-affine-adjoint-unit-properties`: holds; Only the existing canonical construction underlying a_A is now cited through its definition node; the exact functor, equivalence and all comparisons used here are unchanged.
- `lem-sfb-space-coherent-derived-internal-hom`: holds; Only the existing canonical construction underlying a_A is now cited through its definition node; the exact functor, equivalence and all comparisons used here are unchanged.
- `lem-sfb-affine-flat-proper-adjoint-base-change`: holds; Only the existing canonical construction underlying a_A is now cited through its definition node; the exact functor, equivalence and all comparisons used here are unchanged.

- `lem-sfb-space-affine-derived-projection-formula`: holds; uses exactness, the affine derived equivalence, derived sections and the associated-module tensor dictionary, all unchanged. This sixth citer appeared in the refreshed live base during the first repair dry run and was read in full before adding it to the audit.

## Repair self-check

Read the new definition statement against each listed declaration in the
landed module. Its regular-function presheaf, ring sheaf, module carrier, open
ring map, pushforward/restriction, tensor pullback/extension, two proof fields
and accessor definitions agree clause by clause. The comparison theorem is
not an input of these constructions. Read the original item and sandbox Lean
again: all previously verified hypotheses, equivalence clauses, canonical
functors and comparisons are unchanged. Only the definition citation is added.
No other agent was started, as required by the dispatcher; the maintainer's
independent review remains the independent second reading.

The first repair dry run required the live schema's empty import_flags field
on the new node; it is now supplied. The standalone scompile.py check passed
for the unchanged item module. Its signature matches lean.statement verbatim
and there is exactly one sorry, on the main theorem. Proof and proof_deps are
identical to the current base. The final dry run verifies both this module
and every existing declaration listed by the new definition node.

## Second reading by Q128

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

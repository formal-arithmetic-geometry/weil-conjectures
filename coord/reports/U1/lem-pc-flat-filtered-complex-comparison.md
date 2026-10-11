## Worker report

The module `Sheaf.Paper.FlatFilteredComplexComparison` states
`CategoryTheory.flatFilteredComplex_comparison`. It introduces commutative rings `A,B`, a
flat ring map `φ`, bounded filtered cochain complexes `C,D`, a scalar-extension complex
`T`, a filtered comparison map `u`, page objects and maps, and cohomology maps. The
hypothesis `hpage` expresses that every induced second-page map is an isomorphism; the
conclusion says every cohomology map is an isomorphism. The auxiliary `hφ`, finite
filtration witnesses, and category/homology instances render the flatness, boundedness,
and convergence assumptions from the node.

The dependencies used are `RingHom.Flat` (Mathlib), `CochainComplex` (Mathlib),
`CategoryTheory.DecreasingFiltration` and `DecreasingFiltration.IsFinite`
(`Sheaf.CategoryTheory.Filtration`), and the filtered spectral-sequence construction
`CategoryTheory.boundedFilteredComplex_spectralSequence`
(`Sheaf.CategoryTheory.BoundedFilteredComplexSpectralSequence`).

Edge cases checked include arbitrary integer degrees (including negative degrees), empty
or zero graded pieces (allowed by the module-valued page maps), and finite filtrations
with coincident top and bottom steps. The theorem proof is intentionally `sorry` as
required for stage 2.

Searches for an existing declaration: `rg -n "flat.*filtered.*complex|spectral.*comparison"`
on `lean/Sheaf` and the source repository found no matching theorem; Mathlib searches via
LeanFinder/Loogle and grep for filtered spectral-sequence comparison found no declaration.

## Earlier second reading (a previous round; superseded)

Read the node and module signatures clause by clause. `A →+* B` with `hφ : RingHom.Flat φ`
renders the flat ring homomorphism; `C,D` and `FC,FD` render the two filtered cochain
complexes, with `hFC,hFD` rendering finite filtrations. `T` and `u` render
`C ⊗_A B` and its filtered map to `D`; `E₂T,E₂C,E₂D` and `pageMap` render the page
objects and induced maps, while `hpage` is the all-bidegree E₂-isomorphism hypothesis.
`H` and `hmap` render the abutment cohomology maps, and the conclusion quantifies every
integer degree. No hypothesis or conclusion clause was omitted from the formal statement;
the proof remains `sorry`.

## Second reading by U1

This reading supersedes the earlier second reading. I opened the item and each of its
four dependency nodes, their recorded declarations, both shared filtered-complex
modules, and the Stacks TeX on the server (the local checkout lacks the literature
sources). I read homology.tex's filtered-complex construction, the functoriality lemma,
Definition bounded-ss (Tag 0BDU), and the convergence argument; I also read coherent.tex's
entire flat-base-change proof (Tag 02KH), especially the quasi-separated case.
The source gives canonical maps of the actual complexes, not independently supplied
page objects and cohomology maps. No scheme hypotheses belong in this algebraic tool:
quasi-compactness and quasi-separatedness belong to its geometric application.

The node's objects, hypotheses, and conclusions, matched individually:

1. Commutative rings A and B: `(A : Type u) (B : Type v) [CommRing A] [CommRing B]`.
   Correct; independent ring universes, neither a field nor a Noetherian ring assumed.
2. A flat ring map: `φ : A →+* B`, `hφ : φ.Flat`, exactly the dependency's
   `RingHom.Flat` (the flat A-module B via φ.toAlgebra). Correct.
3. Cochain complexes C and D of A- and B-modules: the underlying `C.obj.obj` and
   `D.obj.obj` of `FiniteFilteredComplex (ModuleCat.{max u v w} ...)` are Mathlib
   `CochainComplex`, whose morphisms commute with differentials. Correct. The recorded
   complex dependency is generic Mathlib CochainComplex; its sheaf specialization does
   not prevent using the same constructor for ordinary ring modules here.
4. Bounded below, independently for each complex: `hC` and `hD` explicitly give a
   lower bound below which every term is `IsZero`. Correct; the first draft omitted both.
5. Finite exhaustive decreasing filtrations by subcomplexes: the finite full-subcategory
   property is `DecreasingFiltration.IsFinite`; its steps are subobjects in the abelian
   category of cochain complexes, hence subcomplexes. Its full and zero steps imply
   exhaustivity and separatedness by antitonicity. Correct; no extra assumption needed.
   Mathlib supplies the module and complex Abelian/homology instances, so the redundant
   explicit instance binders of the first draft were removed.
6. Actual termwise tensor complex and induced tensor filtration:
   `ModuleCat.finiteFilteredScalarObject φ C` uses Mathlib extendScalars termwise,
   with each step the image of its tensored inclusion. The conclusion's `s` and its
   inclusion equations identify these images with the actual tensor subcomplexes under
   flatness. Correct. The old arbitrary T had no connection to C or φ.
7. Filtered comparison map: `f : finiteFilteredScalarObject φ C ⟶ D` in the finite
   full subcategory; `f.hom` is the shared `FilteredObject.Hom`, with its stepwise
   factorization condition, and `f.hom.hom` is its underlying cochain map. Correct.
   The old `u : T ⟶ D` did not even preserve a filtration.
8. Convergent filtered spectral sequences: `finiteFilteredSpectralSequence` chooses
   the functor in `boundedFilteredComplex_spectralSequence`, with the first-page
   identifications from that same witness. All its quotient, differential, functoriality,
   and convergence properties remain obtainable from that theorem's choose_spec.
   Correct; the old arbitrary E₂ families were unrelated to any spectral sequence.
9. Canonical flat identification on every page, compatible with differentials:
   `g p` identifies graded *complexes*, and its quotient-projection equation fixes the
   page-zero comparison. For every r >= 1, `e r hr` is an isomorphism of whole page
   complexes, so it intertwines every differential, including the zero off-shape ones.
   The first-page equation normalizes e by canonical graded cohomology base change;
   the following equation fixes compatibility with the next-page homology identification.
   Correct; this whole conclusion was missing from the first draft. The step, quotient,
   and first-page equations characterize the canonical comparison rather than merely
   asserting unrelated isomorphisms between page objects.
10. Induced E₂ tensor map is an isomorphism in every bidegree: the final implication's
    hypothesis is `IsIso ((e 2 _).hom.f (p,q) ≫ ((S_B.map f).hom 2).f (p,q))`.
    Its source is E₂(C) after scalar extension, its target is E₂(D), and the second
    factor is induced by precisely f. Correct. The comparison is produced before this
    implication because its existence is unconditional in the node. This quantifier
    order does not turn the comparison into an extra assumed witness.
11. Every cohomology comparison is an isomorphism: the conclusion quantifies n : ℤ and
    uses `flatFilteredHomologyIso φ hφ C.obj.obj n` followed by
    `HomologicalComplex.homologyMap f.hom.hom n`. This is the inverse of Mathlib's
    exact-functor homology comparison, composed with H^n(f), hence has exactly source
    B tensor H^n(C) and target H^n(D). Correct. The old H/hmap binders were unrelated
    to cohomology of C and the map u.

The original theorem was false, not just underspecified: take A=B=Z with the identity
flat map, C=D=T=0, all supplied pages zero and pageMap their identity; choose H(n)=Z
and hmap(n) the zero map to H^n(D)=0. All its hypotheses hold but its conclusion fails.
The repair changes the Lean to the existing node's valid statement; the node's statement
and proof are unchanged, so no statement_change or unit correction is warranted.

Edge cases: zero complexes and zero rings are admitted; full and zero filtration bounds
can coincide on zero objects. All p,q,n and lower bounds range over Z, including n=0
and negative degrees. Empty/zero graded pieces need no nonempty or nonzero hypothesis.
There is no scheme or external index set in this node, so empty schemes and empty
coverings are not binders of this theorem. Rings have independent universes u,v, with
modules in max u v w and w arbitrary: large modules are not excluded. No restriction
on characteristic, positive degrees, filtration bound order, or tensor faithfulness.

Independent searches: msearch LeanFinder queried exact-functor transport of finite
filtered spectral sequences (returned Ext.mapExactFunctor and tensor exactness, no
comparison theorem); Loogle `SpectralSequence` returned an unknown-identifier response.
LeanSearch queried a canonical finite filtered spectral functor and filtered scalar
extension; both returned Internal Server Error, recorded as unavailable, not no-match.
Additional LeanFinder queries for the finite filtered canonical functor returned
truncations/cm5b, and for tensor filtrations returned IsModuleFiltration and directed
systems of tensors of submodules. None is the required construction. I searched the
DAG, Mathlib, WeilConjectures and lean/Sheaf by the proposed names and by spectral-functor
and filtered-scalar concepts. Existing FilteredPageTwoModel is a parameterized model
starting at page two, not the fixed finite filtered construction with canonical E1;
its module and signature were read. The existing cohomologyBaseChange and
RingTensorCohomology.flatHomologyMap apply to ordinary integer cochain complexes over
same-universe rings (and algebra maps); the page comparison also needs arbitrary
complex shapes and independent universes. The new wrapper reuses the existing generic
ShortComplex.mapHomologyIso, rather than introducing another notion of cohomology.

Repairs: replaced arbitrary T, page families, pageMap, H and hmap; added bounded-below
hypotheses, induced filtration, genuine filtered map, all-page complex isomorphisms,
canonical normalization and page-transition equations; restored the complete three-step
proof docstring, source places and copyright header. Added the two construction nodes
below rather than leaving private or hollow copies. All three modules compiled together
on the server, cleanly in 2.9 seconds, with no warnings. Every universe and variable is
bound, lines are at most 100 characters, and no file-local notation, private definition
or local instance occurs. Every postponed proof is a named theorem with its source and
complete natural-language proof: the item, scalar-filtration finiteness, and flat
scalar exactness; the latter two support the scalar-extension definition node.

## New nodes

`def-pc-finite-filtered-spectral-model` names the full finite filtered category and fixes
one functor and its E1 identifications from thm-sp-spectral-object-yields. Its source is
the actual functorial filtered-complex construction in Stacks Homology, Section 12.24.
The DAG already has the existence theorem and the distinct page-two model; neither
provides this named chosen construction. No new spectral-sequence or filtration notion
is defined. The new module selects real data from the existing theorem and retains its
full specification. Searches and source/signature checks are given above and in its node.

`def-pc-flat-filtered-scalar-extension` gives the termwise tensor construction and its
image filtration using existing extendScalars, mapHomologicalComplex and imageSubobject.
It uses the preceding finite filtered category and the already recorded filtration and
flatness notions. The Stacks Tag 02KH proof explicitly tensors the Cech complex and
commutes tensor with cohomology; Homology's filtered-subcomplex construction supplies
its filtration. Neither the DAG nor the libraries contain this finite filtered scalar
object. Its data are explicit; the finite-bound proof is separately named with a
complete proof docstring. The canonical homology comparison reuses ShortComplex's exact
comparison. Mathlib's preservesFiniteLimits_extendScalars_of_flat (opened in Descent.lean)
only treats rings and modules in the same universe; the separately named general-universe
exactness statement is needed for this construction, has its proof in its docstring,
and is described in this node's statement. No additional exactness instance is assumed
by the item. Additivity and the adjunction instances are obtained from Mathlib's existing
adjunction at explicit universes. Searches are recorded in the node and above.

## Reviewer fix (R-ffc, stage 2)

def-pc-finite-filtered-spectral-model was dropped: `finiteFilteredSpectralSequence` was data by
`Classical.choose` of the sorried `boundedFilteredComplex_spectralSequence`, and the landed
`FilteredPageTwoModel` (def-sp-filtered-page-two-model) already gives the functorial
filtered-complex spectral sequence from page two. The item now quantifies over models
`MA`, `MB` (as FilteredHomotopySpectralSequence does), takes `C, D : FilteredObject` with
`IsFinite` hypotheses, ties every page isomorphism `e r` (r ≥ 2) to the image description
`pageIso` through flat cohomology base change of the quotient complexes `g a b`, and keeps
the E₂ ⇒ Hⁿ implication. FlatFilteredScalarExtension no longer imports the dropped module;
`finiteFilteredScalarObject` removed, `filteredScalarObject_isFinite` takes `IsFinite` as a
hypothesis; the node statement loses the finite-model clause and stmt_dep.

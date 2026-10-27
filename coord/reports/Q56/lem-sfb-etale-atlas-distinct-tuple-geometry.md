## Worker report

The single module `Sheaf.AlgebraicGeometry.EtaleAtlasDistinctTupleGeometry` states
`AlgebraicGeometry.AlgebraicSpace.etaleAtlas_distinctTuple_geometry`. Its only theorem
has proof `sorry`; there are no new definitions, dependency repairs, or statement changes.
The node copy changes only `lean`.

Source read: `literature/stacks-project/decent-spaces.tex`, Tag 0BBN,
`lemma-filter-quasi-compact`, first two proof paragraphs (lines 1554 onward), and Tag 07ST,
`lemma-filter-quasi-compact-quasi-separated`, final proof paragraph (lines 1697 onward);
`spaces-morphisms.tex`, Tag 03KN, `lemma-fibre-product-after-map`, clauses (1) and (4).
The source's surjective atlas and quasi-compact X are used later for the filtration;
neither is needed for this supporting geometry lemma, and neither is imposed here.
Quasi-separatedness of X is the source's condition ensuring quasi-compact finite products.

Hypotheses and clauses, in order:

- The absolute base is `Spec (CommRingCat.of (ULift.{u} ℤ))`. ULift only places the
  integers in the universe of the schemes. All universes and binders are explicit,
  and `set_option autoImplicit false` checks this.
- `X : AlgebraicSpace ...` uses the recorded fppf-sheaf definition. `hqs` is exactly
  quasi-compactness on scheme tests of `prod.lift (𝟙 X.obj.obj) (𝟙 X.obj.obj)`.
  It imposes no quasi-compactness or separatedness on X itself.
- `U : Over ...` and `[IsAffine U.left]` give the affine scheme chart.
  `a : yoneda.obj U ⟶ X.obj.obj` is its map and `ha : IsEtale a` is representable
  étaleness, including representability in the recorded predicate. No surjectivity added.
- `p : ℕ`, `hp : 1 ≤ p` cover all integers p ≥ 1. The ordered index set is `Fin p`.
- `F`, `π`, `b`, and `h` give a scheme over the base, p coordinate projections,
  the structure map to X, and equality of all images in X. The `IsLimit` of their
  `WidePullbackCone` asserts the presheaf universal property of the actual p-fold
  fibre product. This specifies F uniquely up to its unique coordinate-preserving
  isomorphism; it is not an arbitrary scheme or assumed representation. Compatible
  products of fppf sheaves are their presheaf limits. Using this universal property
  avoids choosing a representation from a mere existence theorem in a definition.
- `CompactSpace F.left ∧ F.left.IsSeparated` says precisely quasi-compactness and
  absolute separatedness. Mathlib's latter means the absolute diagonal is closed
  (`Scheme.isSeparated_iff_isClosedImmersion_prod_lift`).
- `Pi.lift π` is the canonical map in the slice category to the product of p copies
  of U. The product in `Over (Spec Z)` is the p-fold product over Spec Z.
  `IsSeparated (Pi.lift π).left` and `(Pi.lift π).left.IsLocallyQuasiFinite` are
  the asserted relative properties; the latter uses the recorded Stacks predicate,
  including local finite type, rather than Mathlib's weaker fibre-only predicate.
- `equalizer.ι (π i).left (π j).left` is the scheme-theoretic equality locus of
  coordinates i and j. The two predicates `IsOpenImmersion` and `IsClosedImmersion`
  for every `i < j` give its clopen scheme structure, not merely topological equality
  of images in U. Equalizers and the pulled-back diagonal give the same subobject.
- `V : F.left.Opens` is specified by equality of its underlying subset with the
  complement of the union of the ranges of these equalizer inclusions. Thus
  `V.toScheme` is W_p with the restricted scheme structure. Its open inclusion
  is the actual `V.ι`, not an unspecified map. `IsClosed (V : Set F.left)` adds
  closedness, and `CompactSpace V.toScheme ∧ V.toScheme.IsSeparated` give exactly
  the two geometric properties required for W_p. For an open subscheme, a closed
  underlying image makes its open inclusion a closed immersion as well.
- `IsEtale (yoneda.map (Over.homMk ... V.ι rfl) ≫ b)` asserts representable
  étaleness of the specified composite W_p → F_p → X. The explicit source of
  `Over.homMk` is `Over.mk (V.ι ≫ F.hom)`; its compatibility proof is definitional.
- `p = 1 → V = ⊤` states W_1 = F_1. The displayed union has no indices i < j
  in Fin 1, so it is empty, as requested.
- Every `Ω : Type u` with `[Field Ω] [IsAlgClosed Ω]`, its structure map `s`,
  and `x : X.obj.obj.obj (op (Over.mk s))` describe an arbitrary geometric point.
  The left subtype of the equivalence is exactly W_p(Ω) over x: maps from
  Spec Ω to W_p whose image under b is x. The right subtype is a tuple of
  U(Ω)-sections with `Function.Injective t` and every `a(t i) = x`. This is
  precisely the set of ordered pairwise distinct tuples in the fibre.
- The final equality `(e w).val i = w.val ≫ ... ≫ π i` fixes every coordinate
  of the equivalence. It therefore fixes the canonical bijection, rather than
  merely asserting equicardinality. Precomposition with a morphism of field spectra
  commutes with these compositions by associativity; restriction to a field extension
  preserves distinctness by faithfully flat descent for maps to a scheme. Thus these
  canonical equivalences have the naturality of the node's fibre description.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map` (read with their definitions/docstrings). The spectrum of the
  universe-lifted integer ring is the absolute base.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `IsRepresentable`, `IsEtale`.
  These use actual Yoneda scheme tests with representing pullback squares.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, `etale_fibreProduct_isScheme`.
  Its existing sheaf fibre-product interpretation is used in the proof plan and the
  finite version is specified directly by Mathlib's `WidePullbackCone` universal property.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`, the
  scheme predicate used inside `IsEtale`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`, used on the equalizers;
  open subscheme data are Mathlib `Scheme.Opens`, `toScheme`, and `ι`.
- `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`:
  `AlgebraicGeometry.Scheme.Hom.IsLocallyQuasiFinite`, using
  `IsQuasiFiniteAtPoint` with finite-type affine neighbourhoods.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; no algebraic closure is
  chosen because the node quantifies over already algebraically closed Ω.
- `def-weil-size-convention` has its existing convention-only record: explicit u
  and the universe-polymorphic scheme/presheaf categories implement it.

All six currently recorded nontrivial proof modules are imported without `public`:
`ChartwiseEtalePermanence`, `SpaceQuasiCompactAffineTests`, `SpaceFibreProductComparison`,
`SeparatedLqfBaseChange` (upstream WeilConjectures), `IsLocallyQuasiFiniteComposition`, and
`SpaceSeparatedEtaleDiagonalComplement`. Existing Mathlib proof matches are supplied by
`AffineScheme` (through the dependencies), `Morphisms.Separated`, `Morphisms.QuasiCompact`,
`Pullbacks`, `Morphisms.QuasiSeparated`, and `Morphisms.ClosedImmersion`.
The proof-only nodes `lem-sfb-space-qcqs-permanence` and
`lem-sfb-space-separated-fp-composition` have no current recorded Lean declaration;
there is no module to import for these two proof dependencies. All statement dependencies
have usable declarations or the size convention. No import cycle is introduced.

Edge cases checked before writing: p = 1 gives a one-member tuple and no equality
pairs; p = 0 is excluded exactly as in the node. Empty U gives empty F_p and W_p for
positive p, all the separation and compactness assertions hold, and both fibre sets
are empty. Empty fibres and p larger than the fibre size give empty distinct-tuple sets.
No nonemptiness, surjectivity, finite fibre degree, fixed characteristic, or quasi-compactness
of X is assumed. The chart may have arbitrarily large discrete geometric fibres.
Equality loci are scheme equalizers, not equality of topological points in U (which would
be a different condition on residue-field maps).

Searches actually run:

- `msearch.py ... leanfinder`: complement of pairwise diagonals in a finite iterated
  étale fibre product of an affine atlas over a quasi-separated algebraic space.
  Eight hits: scheme quasi-separated diagonal and affine-open facts, including
  `QuasiSeparated.diagonalQuasiCompact` and
  `quasiSeparated_eq_diagonal_is_quasiCompact`; no statement of this node.
- `msearch.py ... loogle "widePullback, CategoryTheory.yoneda"`: zero hits;
  service note `unknown identifier 'widePullback'`. Not counted as evidence of absence.
  Mathlib's `CategoryTheory.Limits.Shapes.WidePullbacks` was then read directly.
- `msearch.py ... grep "distinctTuple|distinct_tuple|configurationSpace|AlgebraicSpace"
  AlgebraicGeometry`: zero hits.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for
  `distinctTuple|distinct_tuple|configurationSpace|[Aa]tlas.*[Tt]uple`: no matches;
  separate search for the item id in `lean/WeilConjectures` and upstream name index:
  no matches. Existing algebraic-space separation and fibre-product modules were read.
- `msearch.py ... leansearch`: the complement of pairwise diagonals in finite powers
  of an affine étale chart over a quasi-separated algebraic space is a quasi-compact
  separated scheme: eight hits, all scheme diagonal/quasi-separatedness facts,
  including `QuasiSeparated.quasiCompact_diagonal` and `quasiSeparated_iff`; none
  states the finite-tuple geometry over an algebraic space.

No STATEMENT-DISPUTED issue or node fault was found. The withdrawn CompactObject example
contains no declarations in this checkout; the live modules above supplied the module-mode
header and visibility pattern instead. Every new declaration has source and blueprint
identification and the complete natural-language proof plan.

Validation: the delivered module compiled through the required `scompile.py` wrapper,
including sandbox and library-path compilation, with no errors or warnings. The initial
probe needed an explicit source on `Over.homMk`; that elaboration issue was repaired
without changing any mathematics. The dry run and delivery are recorded below.

## Second reading by Q56

Independent second reading of the delivery at 68daadf7e41e by the maintainer review agent
(the worker's own "second pass by the same worker" is replaced by this section; the Lean
module and node record are unchanged).

Node clauses, with the Lean that renders each, and the verdict:

1. Base Spec Z, schemes, universes: `Spec (CommRingCat.of (ULift.{u} ℤ))`, `Over` of it,
   explicit `universe u`, `autoImplicit false`. Spec of ULift ℤ is terminal in `Scheme.{u}`. OK.
2. X an algebraic space: `X : AlgebraicSpace …` (recorded def-trf-algebraic-space,
   full subcategory of fppf sheaves with `IsAlgebraicSpace`); `X.obj.obj` is the presheaf. OK.
3. X quasi-separated = absolute diagonal quasi-compact on scheme tests:
   `hqs : IsRepresentableWith (fun _ _ q ↦ QuasiCompact q.left) (prod.lift (𝟙 _) (𝟙 _))`;
   `IsRepresentableWith` quantifies over every test `T : Over S` and map `yoneda T → X×X`. OK,
   no quasi-compactness of X (the source's quasi-compact X is used only for the filtration).
4. a : U → X representable étale with U affine: `U : Over S`, `[IsAffine U.left]`,
   `ha : IsEtale a` (= `IsRepresentableWith (Etale ·.left)`). No surjectivity added. OK.
5. p ≥ 1: `p : ℕ`, `hp : 1 ≤ p`, index `Fin p`. OK.
6. F_p = p-fold sheaf fibre product, a scheme: `F : Over S`, `π`, `b`, `h` with
   `IsLimit (WidePullbackCone.mk b (yoneda.map ∘ π) h)` in presheaves (Mathlib
   `WidePullbackCone.mk (b) (π) (h : π i ≫ f i = b)`, read). Sheaf limits are presheaf limits,
   so this pins F_p up to unique coordinate-preserving iso. OK.
7. F_p quasi-compact and separated: `CompactSpace F.left ∧ F.left.IsSeparated` (absolute,
   diagonal closed immersion). OK.
8. Comparison F_p → U ×_Z … ×_Z U separated and lqf (01TD): `Pi.lift π` in `Over S`
   (product in the slice = fibre product over Spec Z); `IsSeparated (Pi.lift π).left`,
   `(Pi.lift π).left.IsLocallyQuasiFinite` (recorded pqf-def-quasifinite declaration, with
   finite type, not Mathlib's fibre-only predicate). OK.
9. Δ_ij open and closed: `equalizer.ι (π i).left (π j).left` is both an open and a closed
   immersion for i < j. The scheme equalizer is the pullback of Δ_{U/Z} along (π_i, π_j);
   since F_p → U×_Z U factors through R = U ×_X U and the node's step-4 square is
   cartesian, it equals F_p ×_{R,Δ_a} U, the node's Δ_ij. OK.
10. W_p: `V : F.left.Opens` with underlying set the complement of the union of the ranges;
    `IsClosed`, `CompactSpace V.toScheme`, `V.toScheme.IsSeparated`; representable étale
    `IsEtale (yoneda.map (Over.homMk V.ι rfl) ≫ b)` for the actual inclusion. OK.
11. p = 1: `p = 1 → V = ⊤`. OK (no i < j in Fin 1).
12. Geometric fibres: for every `Ω : Type u` algebraically closed field, `s`, and
    `x ∈ X(Spec Ω)`, an equivalence between Spec Ω-points of W_p over x and injective
    `Fin p`-tuples of U-points over x, pinned by `(e w).val i = w ≫ ι ≫ π i`. This fixes the
    canonical bijection, and naturality follows from the coordinate formula. A Spec Ω point
    lies in range(equalizer.ι) iff it factors through it (open immersion) iff π_i w = π_j w,
    so the clause is exactly Tag 0BBN's "throw out all diagonals". OK.

Edge cases: p = 0 excluded as in the node; p = 1 gives V = ⊤ and the identity bijection;
U empty gives F_p = W_p = ∅ and both fibre sets empty; empty fibres / p larger than the
fibre give empty tuple sets; non-separated X (e.g. affine line with doubled origin) is
allowed and U → X is still separated (node step 4). No extra instance, Noetherian,
characteristic, surjectivity or universe restriction.

Records: node copy differs from live only in `lean`; `lean.statement` is verbatim the
signature in the file; all statement-dependency declarations (AlgebraicSpace,
IsRepresentableWith, IsEtale, Etale, IsClosedImmersion, IsOpenImmersion,
Scheme.Hom.IsLocallyQuasiFinite, IsAlgClosed) read and used as recorded; proof-dependency
modules imported privately exist on the live tree. No definitions (nothing hollow), proof
`sorry`, module and theorem docstrings carry the source places and
`(blueprint: lem-sfb-etale-atlas-distinct-tuple-geometry)` and the node's proof steps.
Source decent-spaces.tex Tag 0BBN proof read: agrees with the node and the Lean.

Searches: no Mathlib or project declaration of algebraic spaces' distinct-tuple geometry
(worker's logged searches; the node's `mathlib_searches` re-read). No mismatch found;
nothing changed in the Lean.

## Worker report

The module `Sheaf.AlgebraicGeometry.QcqsSpaceMonomorphismQuasiAffine` states
`AlgebraicGeometry.AlgebraicSpace.isRepresentableWith_quasiAffine_of_mono_locallyOfFiniteType`.
Its only proof is `sorry`; it introduces no definitions or additional axioms.
The node's statement, proof and proof dependencies are unchanged. Its statement dependencies
only gain four already landed definition nodes, whose declarations are reused below.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The arbitrary base scheme is `{S : Scheme.{u}}`; `universe u` is explicit and
  `set_option autoImplicit false` excludes auto-bound variables. `A B : AlgebraicSpace S`
  uses the existing full subcategory of fppf sheaves, rather than scheme substitutes.
- The map `f : A ⟶ B` is the natural transformation in that full subcategory;
  its presheaf transformation is `f.hom.hom`.
- Quasi-compactness of A is `hAqc : IsQuasiCompact A.obj`; the existing definition is
  exactly existence of a representable surjective etale atlas from a compact scheme.
  `hBqc : IsQuasiCompact B.obj` supplies the identical condition for B.
- Absolute quasi-separatedness of A and B is `hAqs : IsAbsolutelyQuasiSeparated A`
  and `hBqs : IsAbsolutelyQuasiSeparated B`. This landed definition uses all pairs of
  affine scheme tests and compactness of their fibre product's point space. Its source,
  Stacks 0AHR(3), identifies this with quasi-compactness of the absolute diagonal over
  Spec Z, including for a base S that is not quasi-separated. We impose no condition on S.
- Local finite type is `hft : MapIsLocally (@LocallyOfFiniteType) f`. The existing
  predicate quantifies over all compatible representable etale source and target charts
  and their commuting scheme map. Its scheme property is exactly the recorded Mathlib
  `LocallyOfFiniteType`, not local finite presentation or finite type.
- The stated monomorphism is `hm : ∀ T : Over S,
  Function.Injective (f.hom.hom.app (op T))`: injectivity on sections at every S-scheme,
  without a restriction to fields, affines, or etale tests.
- The conclusion is `IsRepresentableWith (fun _ _ p ↦ IsQuasiAffineHom p.left)
  f.hom.hom`. Unfolding the existing representability predicate gives, for every
  S-scheme T and h_T → B, a scheme U over S, a map p : U → T and an actual Yoneda
  pullback square representing A ×_B h_T. Each p is a quasi-affine scheme morphism.
  For affine T, the preimage of its entire affine open is U, so U is quasi-affine.
  Mathlib's `Scheme.IsQuasiAffine` includes quasi-compactness and implies the canonical
  map to Spec of global sections is an open immersion; thus U is precisely a
  quasi-compact open subscheme of an affine scheme. Conversely the node's condition
  on all affine tests applied to each affine open of an arbitrary T gives
  `IsQuasiAffineHom p.left`. Consequently the conclusion neither strengthens nor
  weakens the affine-test formulation, while retaining representability on all tests.
- The preliminary glossary concerning quasi-compact and quasi-separated morphisms,
  finite type and finite presentation supplies conventions, not additional hypotheses
  or conclusions. No finite-presentation assumption appears in the Lean theorem.
  The existing chart predicate is imported; finite type remains quasi-compactness
  plus the local finite-type chart test. The glossary needs no finite-presentation import.
- Sheaf fibre products and their algebraic-space closure are the existing categorical
  constructions from `AlgebraicSpaceFibreProductsEtaleCovers`, not a new construction.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `IsRepresentable`, `IsEtale`, `IsSurjective`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicSpace.fibreProduct_isAlgebraicSpace` and the existing sheaf pullbacks.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`
  and the imported `QuasiCompact` scheme predicate.
- `def-weil-size-convention` is metatheoretic, with no definition to import; explicit
  universe polymorphism and the recorded `AlgebraicSpace S` implement its convention.
- Added landed node `def-sfb-space-morphism-properties`, module
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `AlgebraicSpace.MapIsLocally`.
- Added landed node `def-sfb-space-absolute-quasi-separated`, module
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `AlgebraicSpace.IsAbsolutelyQuasiSeparated`.
- Added landed node `def-sfb-stack-qcqs-morphism`, module
  `Sheaf.AlgebraicGeometry.StackQcqsMorphism`: `AlgebraicSpace.IsQuasiCompact`.
- Proof-only imports with existing records:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceFiniteAffineSubatlas`
  (`exists_finite_affine_subatlas`, `compactSpace_points_of_surjective`,
  `compactSpace_points_of_scheme_atlas`), and
  `Sheaf.AlgebraicGeometry.SeparatedLocallyQuasiFiniteSpaceRepresentable`
  (`exists_scheme_of_separated_locally_quasi_finite`).
- Added landed node `def-nagata-quasi-affine-morphism` is a statement dependency.
  Its module `WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine` supplies the
  conclusion's
  `AlgebraicGeometry.IsQuasiAffineHom` and the proof dependency
  `IsQuasiAffineHom.of_locallyQuasiFinite`; it is public because its property is in
  the conclusion. The four remaining proof dependencies without Lean records
  (`lem-sfb-space-qcqs-permanence`, `lem-sfb-qc-space-affine-etale-atlas`,
  `lem-sfb-stack-finite-type-calculus`, `lem-sfb-space-lft-monomorphism-separated-lqf`)
  are named in the complete proof docstring, but have no module to import.

Sources read: local `spaces-morphisms.tex`, labels
`lemma-quasi-compact-quasi-separated-permanence` (073B),
`lemma-monomorphism-loc-finite-type-loc-quasi-finite` (0463), and
`lemma-quasi-finite-separated-quasi-affine` (0ABS). These give the permanence,
separated locally quasi-finite reduction and final quasi-affine conclusion. The
module docstring retains the node's four proof steps with every cited DAG input.

Edge cases checked: A empty (its empty atlas and empty scheme pullbacks are allowed);
identity maps; open immersions with quasi-compact source; closed immersions between
qcqs spaces; S empty; non-Noetherian S; S not quasi-separated. No Nonempty binder,
nonzero ring assumption, finite-presentation assumption, or hypothesis on S was added.
Keeping both endpoint qcqs assumptions is intentional even though the proof only needs
A quasi-compact and B quasi-separated. Without source quasi-compactness arbitrary open
immersions need not have quasi-compact affine-test sources.

Searches (2026-10-24):

- `msearch.py ... leanfinder "A locally finite type monomorphism between quasi compact
  quasi separated algebraic spaces is quasi affine"`: scheme quasi-affineness and
  finite-type results, no algebraic-space statement matching this node.
- `msearch.py ... loogle '"Mono", "LocallyOfFiniteType"'`: OK, zero hits.
- `msearch.py ... grep 'AlgebraicSpace|[Mm]ono.*[Qq]uasi[Aa]ffine|[Qq]uasi[Aa]ffine.*[Mm]ono'
  AlgebraicGeometry`: OK, zero hits.
- `msearch.py ... leansearch "A locally finite type monomorphism of quasi compact quasi
  separated algebraic spaces is a quasi affine morphism"`: eight scheme-only hits,
  including `Scheme.IsQuasiAffine.of_isAffineHom` and scheme mono quasi-separatedness;
  none matches the space theorem.
- `rg` searches of `lean/WeilConjectures` and `lean/Sheaf` for quasi-compact,
  quasi-separated, quasi-affine and local finite-type space definitions found the
  three landed predicates above. Searches for `MapIsQuasiAffine`,
  `IsRepresentableWith.*IsQuasiAffine`, and mono/quasi-affine names found no theorem.
- The item-id search in `lean/WeilConjectures` returned no match. The scheme theorem
  `IsQuasiAffineHom.of_locallyQuasiFinite` was read in full and is only a proof input,
  because its objects are schemes and its hypotheses include local quasi-finiteness.

Validation: after the repair, scompile.py compiled this file cleanly as both sandbox
and library module, with no errors or unexpected warnings. The library check took
3.6 seconds; the sandbox check reported 395.9 seconds including server scheduling.
No statement dispute, dependency interface repair, new node, or statement correction.

## Second reading by Q35

I reopened the node copy and the final Lean file for a separate clause-by-clause reading.
This is the worker's second reading; the dispatcher brief prohibits starting other agents
and assigns the independent review to the maintainer.

`S`, `A`, `B`, and `f` have exactly the original types; `hAqc`, `hAqs`, `hBqc`, `hBqs`
retain all four endpoint hypotheses. `hft` tests every compatible etale chart pair;
`hm` quantifies over every S-scheme, with no loss of arbitrary tests. In particular
monomorphism was not replaced by pointwise injectivity on geometric points.
The conclusion's representability quantifies over all schemes, including nonaffine
schemes; the quasi-affine property is equivalent to the node's affine-test condition
by restriction to affine opens, as explained above and in the final proof docstring.
The preliminary finite-presentation glossary does not assert a hypothesis about f,
so none was inserted. The added statement dependencies refer to existing definitions
rather than new copies. No mismatch or change was needed on this reading.


## Repair of returned delivery fe4d53b8a6af

1. H2: added the already landed `def-nagata-quasi-affine-morphism` to `stmt_deps`,
   because its recorded declaration `AlgebraicGeometry.IsQuasiAffineHom` occurs in
   the conclusion. It remains a proof dependency as well. The public import of its
   owning module was already correct and is retained.
2. H9: removed the unused public import
   `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`. Updated the glossary
   and dependency discussion above to reflect the actual final imports.

Compared the retained sandbox with current main: the only node differences before
this repair were the delivered `lean` record and the three added landed statement
dependencies. No other base fields changed. The prescribed delivery wrapper rebases
this repaired packet onto current main. The signature and its mathematical content
are unchanged from the independently reviewed head. Reopened the repaired module
and node for a second reading: the conclusion's owning node is now in `stmt_deps`,
and the unused import is absent. Both returned points are repaired.

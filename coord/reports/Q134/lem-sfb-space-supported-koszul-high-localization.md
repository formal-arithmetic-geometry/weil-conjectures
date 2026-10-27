## Worker report

The new module `Sheaf.AlgebraicGeometry.SpaceSupportedKoszulHighLocalization`
constructs `AlgebraicGeometry.AlgebraicSpace.affineSpaceKoszul` and states
`AlgebraicGeometry.AlgebraicSpace.space_supported_koszul_high_localization`.
The sole postponed proof is the latter theorem, whose entire proof is `sorry`.
The helper has actual data: extend the recorded chain Koszul complex to cohomological
indices, apply the existing canonical affine scalar pullback termwise, and apply Q.
No new definition node, dependency repair, or statement correction is needed.

Source read: `literature/stacks-project/spaces-perfect.tex`, Tag 0GFH,
`proposition-detecting-bounded-above`, especially the paragraphs beginning
“Say V = Spec(A)” and ending with the canonical high-truncation unit comparison;
`perfect.tex`, Tag 0GEJ, `lemma-orthogonal-koszul-first-variant`.
The theorem docstring carries all five proof steps, including the supported excision,
local strict-perfect representatives, topology comparison, and descent of the actual unit.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Size convention: explicit universes `u w`; `S : Scheme.{u}` and all rings and schemes
  in universe u; `[HasDerivedCategory.{w} ...]` on each of the three module categories.
  The standard small affine etale model preserves the original coefficient universe;
  there is no forced equality between the original site object and Hom universes.
- Base and space: `{S : Scheme.{u}}`, `X : AlgebraicSpace S`.
- Quasi-compactness: `hXqc : CompactSpace (Point X.obj.obj)`.
- Absolute quasi-separatedness: `hXqs : IsAbsolutelyQuasiSeparated X`; this is the
  existing affine-test criterion for quasi-compactness of the absolute diagonal,
  not merely the relative diagonal over S.
- The module and derived categories are the existing `X.SmallModules` and
  `X.DerivedModules`, equivalent to modules on the original small etale ringed site.
  `E : X.DerivedQCoh` is the full subcategory of ambient derived objects with
  quasi-coherent cohomology, not the derived category of the abelian category QCoh.
- The open subspace is `U : AlgebraicSpace S`, with inclusion `i : U ⟶ X`.
  `hi` identifies its presheaf with an existing `O : OpenSubspace X` and identifies
  the inclusion itself by `e.hom ≫ O.val.ι = i.hom.hom`.
  `hUqc : CompactSpace (Point U.obj.obj)` is exactly quasi-compactness of U.
- The affine chart is `A : Type u`, `[CommRing A]`, `v : Spec (.of A) ⟶ S`, and
  `p : schemeSpace (Over.mk v) ⟶ X`. Thus its scheme is literally Spec A,
  with arbitrary structure morphism to S. `hp : IsEtale p.hom.hom` includes
  representability by its definition; no surjectivity of p alone is assumed.
- The reduced closed complement is `Z : ClosedSubspace X`,
  `hZred : IsReduced (Z.val : AlgebraicSpace S)`, and
  `hZsupport : pointImage Z.val.arrow.hom.hom = (pointImage i.hom.hom)ᶜ`.
  This quantifies over any representative of the unique reduced closed subspace;
  it does not impose reducedness after base change.
- The distinguished condition is
  `hdist : IsIso (Limits.pullback.snd p.hom Z.val.arrow.hom)`.
  This is the actual sheaf projection V times_X Z to Z.
- The overlap T is rendered without choosing another object: its underlying open
  subset of Spec A is `schemePointMap p.hom.hom ⁻¹' pointImage i.hom.hom`.
- The first conjunct asserts existence of `r : ℕ` and `f : Fin r → A` with that
  subset equal to `⋃ k : Fin r, (PrimeSpectrum.basicOpen (f k) : Set (PrimeSpectrum A))`.
- The second conjunct universally quantifies over every `r` and `f` satisfying
  precisely the same cover equality. No particular chosen cover is substituted.
- Its associated B is the helper `affineSpaceKoszul A v r f`. The recorded
  `ExteriorAlgebra.koszulComplex A r f` has K_n in chain degree n; extension by
  `ComplexShape.embeddingDownNat` gives B^(-n) = associated K_n. The recorded
  `affineScalarPullback` is sheafification of O(W) tensor_A M on actual charts,
  hence is the same associated etale realization as tilde followed by etale
  extension, now expressed directly on the existing equivalent small model.
  Its choice is fixed up to natural isomorphism by the scalar-sections adjunction;
  it is not an arbitrary map, object, or Nonempty choice.
- B_X is literally `(derivedDirectImage p).obj (affineSpaceKoszul A v r f)`.
  Its perfection is the first conclusion for each cover:
  `SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u}
    X.smallStructureSheaf (...)`. This is the recorded etale-local bounded
  finite-free-retract condition, with local bounds and ranks.
- Every E is covered by `∀ E : X.DerivedQCoh`.
- Eventual vanishing is `∃ N : ℤ, ∀ j : ℤ, N ≤ j → Subsingleton (B_X ⟶ E.obj⟦j⟧)`.
  A derived Hom group vanishes exactly when its underlying type is subsingleton.
  An integer lower bound is equivalent to vanishing for sufficiently positive j.
  The shift is on E with positive j, so there is no reversed inequality.
- The final conclusion is `∃ a : ℤ, IsIso
  ((DerivedCategory.TStructure.t.truncGE a).map
    ((spaceDerivedAdjunction i).unit.app E.obj))`.
  Its source and target are the two stated upper truncations. This is invertibility
  of the specified canonical unit, not merely existence of an unrelated isomorphism.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsEtale`,
  `IsRepresentableWith`, `EtaleSite`, `structureSheaf`, and `Modules`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  the transparent specialization of Mathlib `SheafOfModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, and `DerivedCategory.Q`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh`, using
  Mathlib `SheafOfModules.IsQuasicoherent`; the delivered theorem uses the recorded
  cohomological specialization `derivedQCohProperty` and its full subcategory.
- `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`:
  `SheafOfModules.IsPerfectOnRingedSiteOfUniverses`, whose defining local complexes
  and finite-free splittings were read.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace`.
- `Sheaf.AlgebraicGeometry.ReducedClosedSubspaceSupport`:
  `exists_unique_reduced_closed_subspace`; its exact `ClosedSubspace`, `IsReduced`,
  point-support and pullback-projection interface is used in the hypotheses.
- `WeilConjectures.AlgebraicGeometry.KoszulComplex`:
  `ExteriorAlgebra.koszulComplex`, with its exterior-power terms and contraction differential.
- `Sheaf.AlgebraicGeometry.AffineEtaleDerivedModuleRealization`:
  `affineEtaleAssociatedFunctor` and `exists_affineEtaleDerivedModuleRealization`;
  the canonical associated module sheaf is expressed on the affine small model by
  the already landed scalar pullback, rather than introducing a second realization.
- `Sheaf.AlgebraicGeometry.SpaceDerivedEtaleChartCalculus`:
  `spaceEtaleDerivedRestriction`, `space_derived_etale_chart_calculus`,
  `spaceDerivedChart_etale_baseChange` and the normalized composition comparisons.
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`:
  `DerivedCategory.TStructure.t`; `TruncLTGE` supplies its `truncGE` functor.
- Additional existing definition owners are cited in `stmt_deps`:
  `def-sfb-space-absolute-quasi-separated` (`IsAbsolutelyQuasiSeparated`),
  `def-sfb-space-affine-global-sections` (`affineScalarPullback`),
  `def-sfb-space-derived-module-calculus` (`DerivedModules`, `DerivedQCoh`,
  `derivedDirectImage`), `def-trf-scheme-algebraic-space` (`schemeSpace`),
  `def-sfb-space-affine-hom-comparison` (`spaceDerivedAdjunction`), and
  `def-a1-space-point-topology` (`pointImage` and the point topology).
  Each has an existing published Lean record; their definition modules are public imports.

Available proof-only dependencies are plain imports: affine scheme qcqs and principal-open
basis results in Mathlib, `DerivedEtaleZariskiEquivalence`, and
`AffineKoszulUpperLocalization`. The three proof dependencies without a Lean record or
Mathlib match in the read snapshot are `lem-sfb-qcqs-space-fibre-product`,
`lem-sfb-space-supported-etale-excision`, and
`lem-sfb-ringed-site-strict-perfect-local-actual`. Their theorem modules are not imported;
they supply no missing object needed to state this node, and their uses remain explicit
in the proof docstring and unchanged DAG proof dependencies.

Edge cases checked before and after writing: r = 0 gives an empty principal-open union
and K_0 = A; the associated object is O_V in degree zero and T is empty. The zero ring
and empty affine scheme are allowed by `[CommRing A]`; no nontriviality, nonemptiness,
positive rank, or inhabited index assumption was added. Empty U and U = X are allowed.
For U = X, the localization unit is already invertible and the truncated conclusion
still makes sense. Arbitrary negative lower bounds and unbounded E are retained.
No separatedness of S or relative replacement of absolute quasi-separatedness is used.

Searches for an existing statement (2026-10-24):

- LeanFinder via msearch: “In an elementary distinguished square of algebraic spaces,
  the supported Koszul complex is perfect and eventual Hom vanishing makes high
  truncation of the open localization unit an isomorphism”. Eight generic complex
  truncation hits; no supported algebraic-space statement.
- Loogle via msearch: `DerivedCategory, IsPerfectOnRingedSiteOfUniverses, koszulComplex`.
  Zero hits; project predicate unknown to the Mathlib index.
- LeanSearch via msearch: “Koszul complex supported on the complement of an open
  algebraic space and truncation localization”. Eight generic complex truncation hits.
- Mathlib grep via msearch in AlgebraicGeometry:
  `supported.*[Kk]oszul|koszul.*localization|space_supported_koszul`: zero hits.
- `rg` in the source `lean/WeilConjectures` and in `lean/Sheaf` for the item id,
  supported Koszul, and Koszul localization: existing scheme results such as
  `exists_supported_koszul_unit_summand`, and `affine_koszul_upper_localization`.
  None states the distinguished-square algebraic-space result.
- `rg` of `dag/lean_names_upstream.json` and the source for the exact new declaration
  and item id found no existing declaration. Inspection of the scalar-pullback owner
  found the needed associated-sheaf construction, which is reused unchanged.

Validation: prescribed scompile.py passed both sandbox and library-path checks
(2.6 s and 2.8 s) with no errors or warnings. The prescribed deliver2.py --no-push dry run returned OK: preflight and all
final-file compiles passed (dry-run commit d0a2629ea69). No statement dispute was found.

## Second reading by Q134

A separate sequential self-reading compared the complete source node with the helper
and theorem. The cover existence and universal quantifier over all covers are both
present; no claim of reducedness after base change appears. The affine chart is literally
Spec A, and its base morphism is arbitrary. The Koszul degree convention is -n, the Hom
shift is +j, and the map being truncated is the canonical normalized adjunction unit.
The quasi-coherent hypothesis is imposed on every cohomology object through DerivedQCoh.
The perfectness predicate has the exact local bounded finite-free-retract meaning.
The new helper only composes existing constructions. The node's mathematical statement
was not changed. Added dependency edges name already landed definition owners used by
this interface. No mismatch was found. No separate worker was started, as the dispatcher
forbids it; the maintainer supplies the independent review of this delivery.


## Repair of returned delivery bf2dbd079418

H2 repaired: added the four landed definition owners to stmt_deps and their direct
public imports. `def-a1-algebraic-space-point-classes`, module
`Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses`, owns `Point` in hXqc/hUqc
and `schemePointMap` in both cover clauses. `def-sfb-space-closed-subspace`, module
`Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedSubspace`, owns `ClosedSubspace` for Z.
`def-sfb-reduced-algebraic-space`, module
`Sheaf.AlgebraicGeometry.ReducedAlgebraicSpace`, owns `IsReduced` in hZred.
`def-sfb-space-small-ringed-model`, module
`Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel`, owns `smallStructureSheaf`
in the perfectness conclusion and `SmallModules` in the derived-category instances.
The four current dependency records and their statements were read again. No dependency
node is modified. Compared the retained packet with current main: all inherited node
fields outside lean and the authorized added stmt_deps agree, and all current main
statement dependencies are retained. The delivery wrapper rebases the packet on current
main. Both Lean declarations, their docstrings and the verbatim statement field are
unchanged from the returned delivery; only the four direct imports change Lean source.

A sequential repair reading verified each of the four ownership links above against
the signature and direct imports. This resolves the sole returned point. The independent
maintainer review already checked the mathematics clause by clause and found it correct.
Fresh prescribed compile and delivery preflight are run for this repaired packet.


Repair validation: prescribed scompile.py passed the sandbox and library-path compiles
without errors or warnings. Prescribed deliver2.py --no-push returned
`OK (dry run): commit e1932bbc6af passes the preflight and compiles; nothing pushed`.
The final packet contains precisely the item node, its module, and this report.

## Worker report

The module `Sheaf.AlgebraicGeometry.ProperSpaceCurveQcohBound` states
`AlgebraicGeometry.AlgebraicSpace.proper_space_curve_qcoh_bound`, with one `sorry`
and no new definitions. The natural-language item statement is unchanged.

Hypotheses and clauses, read against the node:

- `universe u`, `{S : Scheme.{u}}`, `X : AlgebraicSpace S`, `T : Over S`, and
  `f : X ⟶ schemeSpace T` introduce the source algebraic space, scheme base, and
  morphism. The auxiliary ambient S is the parameter of the existing algebraic-space
  encoding; taking S to be the base includes every family in the node. `T.left` is
  the node's T; `T.hom` merely retains its ambient structure map.
- `hf : IsProperCurveFamily X T f.hom.hom` is exactly the family condition, rather
  than a curve hypothesis on X alone. Reading its definition in ProperCurveModuli:
  its first conjunct is flatness on every representable etale scheme chart; the
  second is closed-immersion representability of the relative diagonal; the third
  and fourth are quasi-compactness and local finite type; the fifth is universal
  closedness; the sixth is quasi-compact diagonal; and the seventh is local finite
  presentation on every etale chart. The final quantified clause tests every
  algebraically closed field in the scheme universe and bounds the topological
  Krull dimension of its actual geometric sheaf fibre product by 1. This point-space
  dimension is the usual etale-chart dimension of an algebraic space. Empty spaces
  have bottom dimension. Thus properness is separated + finite type + universally
  closed and finite presentation is local finite presentation + qc + qs.
- `∀ (F : X.QCoh) (q : ℕ), 1 < q → IsZero ...` is the entire first conclusion:
  every quasi-coherent module and every positive cohomological degree strictly
  greater than one. Its object is
  `((smallModuleDirectImage f).rightDerived q).obj
  (X.smallModuleRestriction.obj F.obj)`.
  Right derivation takes place in all `X.SmallModules`, never in QCoh. The fixed
  `smallModuleEquivalence` is an equivalence with all original module sheaves on
  the small etale ringed site, with unchanged coefficient and section universe.
  It preserves injectives and zero objects. Therefore this is exactly vanishing
  of the sheaf R^q f_* F, expressed on its equivalent small affine model.
- The second conjunct introduces arbitrary `A : Type u`, `[CommRing A]`,
  `V : Over S`, `a : V.left ≅ Spec (.of A)`, and `g : V ⟶ T`.
  The isomorphism a allows every affine scheme presentation. There is no etaleness,
  flatness, dominance, nonemptiness or surjectivity requirement on g.
- The canonical algebraic-space fibre product is `enlargedFibreProduct` of
  the Yoneda arrow of g and f. Its order is V times_T X; the symmetry identifies
  it with X times_T V, and `enlargedFibreProductFst` is its projection to V.
  `G` is bound directly in this product's QCoh category, with no descent or
  pullback-from-X hypothesis. In particular the identity affine base change is
  included, as is the empty affine scheme (the zero ring is allowed).
- Write Z and p here for the displayed `enlargedFibreProduct` and its first
  projection (these are explanatory names, not new definitions or Lean binders).
  `∀ (q : ℕ), 1 < q → IsZero (((affineScalarSections A V a Z p).rightDerived q).obj
  ((smallModuleRestriction Z).obj G.obj))` is the second vanishing assertion.
  It takes the underlying module `G.obj`, restricts it to the equivalent small
  model, and applies the right-derived scalar global-sections functor. In particular it is derived
  sections of module sheaves, not abelian sheaf cohomology substituted without
  comparison and not derivation inside QCoh. `IsZero` is applied to an A-module
  object and to a module sheaf object in the first conjunct, never to a bare Type.
- No binder assumes Noetherian base, coherent module, reducedness, nodality,
  connectedness, Gorensteinness, purity or nonempty fibres.

Recorded dependencies used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
  Read Scheme.lean lines 35--46 and 73--76, including the local-affine definition
  and locally-ringed-space morphism signature/docstring.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsAlgebraicSpace`, `EtaleSite`, `structureSheaf`, `Modules`. Read the full
  signatures/docstrings, including scheme-test representability and the actual
  regular-functions sheaf; no private algebraic-space encoding is introduced.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh`, specializing
  Mathlib `SheafOfModules.IsQuasicoherent`. Read its exact full-subcategory definition
  and Mathlib Quasicoherent.lean lines 249--265 (local arbitrary coproduct presentations).
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `IsProperCurveFamily`, with all its
  constituent definitions and their docstrings read. Its already landed owner
  `def-sfb-proper-curve-moduli` is added to stmt_deps.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel`: `SmallModules`,
  `smallModuleRestriction`, `smallModuleEquivalence`, whose signatures and
  comparison proof docstrings were read. The already landed owner
  `def-sfb-space-small-ringed-model` is added to stmt_deps.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`: `smallModuleDirectImage`
  (the explicitly conjugated canonical module direct image) and its additivity
  instance; the already landed owner `def-sfb-space-derived-module-calculus` is
  added to stmt_deps. `Functor.rightDerived` is Mathlib's injective-resolution
  construction, read in RightDerived.lean lines 60--75 and 110--118.
- `Sheaf.AlgebraicGeometry.SpaceAffineGlobalSections`: `affineScalarSections`
  and `affineScalarSections_additive`; reread the complete construction, which
  is Hom from the structure sheaf with its chart-normalized A-action, and the
  additivity theorem signature/docstring. Its already landed definition owner
  `def-sfb-space-affine-global-sections` is now the statement dependency.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace`,
  `enlargedFibreProduct`, `enlargedFibreProductFst`; reread their actual data and
  source docstrings at lines 68--80 and 227--240. This module is publicly imported.
  `def-trf-scheme-algebraic-space` owns the actual Yoneda sheaf construction;
  `def-sfb-space-sheaf-fibre-product` owns the actual sheaf pullback and projection.
  Both existing definition nodes are now explicit statement dependencies.

Plain proof imports retain the recorded, already stated proof dependencies:
`CurveEtaleSchemeCover.exists_etale_scheme_cover` (using the same family predicate),
`AlgebraicSpaceFlatProperFpLocality.flat_proper_fp_locality`,
`AlgebraicSpaceFibreProductsEtaleCovers.fibreProduct_isAlgebraicSpace` and its
covering statements, and `SiteCoveringAxioms.IsSiteForCoverings`. The affine-base
comparison `SpaceAffineBaseHigherImageSections` remains a plain proof import:
its theorem is used in proof step 4 but no longer in the statement dependency list.
The recorded nodes for proper-flat fibre dimension, scheme etale higher-image
comparison, proper scheme fibre-dimension vanishing, and higher-image etale
restriction have no Lean records in the inspected base, so have no module to
import. They are proof prerequisites only and no substitute is stated here.
A graph traversal found no reverse dependency path from any added stmt_dep to
this item; the extra statement imports introduce no dependency cycle.

Sources read: moduli-curves.tex section-stack-curves, lines 45--59, and
lemma-etale-locally-scheme, lines 253--281 (0E6F); limits.tex
lemma-higher-direct-images-zero-above-dimension-fibre, lines 4807--4855 (0E7D);
spaces-cohomology.tex lemma-quasi-coherence-higher-direct-images-application,
lines 237--265 (08EX). These allow arbitrary bases and arbitrary QCoh modules.
The theorem docstring gives all four recorded proof steps and their dependencies.

Edge checks: empty X and empty fibres obey the same dimension predicate; empty
T and the zero affine ring are not excluded. Zero-dimensional fibres also satisfy
it. Degree zero and degree one are intentionally outside the asserted vanishing;
positive-genus proper curves may have nonzero H^1. Arbitrary non-Noetherian A and
non-finitely-presented G remain quantified. The second assertion is for every G
on the product, with no existence of an antecedent F. Field and ring tests use
universe u, the existing scheme universe, rather than an independent smaller
universe making the tests vacuous. All variables and universes are explicit;
`autoImplicit` is false. No node fault or disputed statement was found.

Searches actually run through msearch.py, 2026-10-24:

- LeanFinder: "Proper flat finitely presented algebraic space curve families have
  no quasi coherent higher direct images or affine base changed cohomology above
  degree one". Eight hits: scheme flatness, flat openness/descent and limit-section
  lemmas; no vanishing theorem.
- Loogle: `"rightDerived", "IsZero"`. One hit:
  `Functor.isZero_rightDerived_obj_injective_succ`; it concerns injective inputs,
  not arbitrary quasi-coherent inputs of proper curve families, so is not a match.
- Mathlib grep: `proper.*curve.*vanish|curve.*qcoh|curve.*cohomological`,
  restricted to AlgebraicGeometry. Zero hits.
- LeanSearch: "For a proper flat family of algebraic space curves higher direct
  images of quasi coherent modules vanish above degree one". Eight hits, all
  scheme-flatness declarations; no match.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  `proper.*curve.*(bound|vanish)|curve.*[Cc]ohomolog`, then the proposed declaration
  name. Existing curve results concern torsion etale cohomology or more restrictive
  curves; no declaration states this arbitrary-base module-cohomology bound.
  The item-id grep found no existing module. Searching `dag/lean_names_upstream.json`
  for cohomological curve bounds found only other curve cohomology nodes.

Validation: the original packet compiled in sandbox and library module mode.
The repaired file is checked afresh using scompile.py, followed by the prescribed
deliver2.py dry run and delivery. No global build or live source edit is performed.

## Repair of returned head 4c77b760eda7

The single H2 return has three requested changes, all implemented:

1. Replaced `lem-sfb-space-affine-base-higher-image-sections` in stmt_deps by
   its required definition owner `def-sfb-space-affine-global-sections`.
   The affine cohomology conclusion now directly applies
   `(affineScalarSections A V a Z p).rightDerived q` to
   `Z.smallModuleRestriction.obj G.obj`. This is definitionally the old
   `affineBaseModuleCohomology` expression, by unfolding that abbreviation's
   functor composition and the QCoh inclusion. The module publicly imports
   `SpaceAffineGlobalSections`; the affine-base theorem's module is a plain
   proof import. Explicit Mathlib right-derived and enough-injectives imports
   supply the API previously exposed through that theorem's module.
2. Added the landed definition owner `def-trf-scheme-algebraic-space` for
   `schemeSpace` to stmt_deps, and publicly imported its recorded module.
3. Added the landed definition owner `def-sfb-space-sheaf-fibre-product` for
   `enlargedFibreProduct` and `enlargedFibreProductFst` to stmt_deps. It shares
   the same publicly imported module. Updated lean.statement verbatim from the
   repaired theorem. No new notion or weaker hypothesis is introduced.

Compared the retained returned node against current main: only stmt_deps and
lean differed, exactly the original packet's additions; preserved current main's
other fields when regenerating the repaired node. The three definition records
were read in full; reverse dependency traversal found no path to this item.
The natural-language statement, family condition, all quantified inputs, both
vanishing clauses, universes, and strict degree bound are unchanged. The first
repair compile exposed a line-broken field-projection parse error; it was repaired
by writing the restriction functor explicitly as `smallModuleRestriction Z`.
The report above now describes the final imports and expanded conclusion.
Independent review remains the maintainer's responsibility, as in this dispatch.

## Second reading by NK

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

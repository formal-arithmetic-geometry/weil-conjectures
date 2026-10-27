## Worker report

Stage 2 statement of lem-sf-native-adic-affine-open-zero-stratification, in
Sheaf.AlgebraicGeometry.NativeAdicAffineOpenZeroStratification, declaration
AlgebraicGeometry.ProEtale.affine_open_zero_stratification. Its only proof is `by sorry`.
No definitions, dependency replacements, new nodes, or statement corrections are needed.
The node copy changes only `lean`. The earlier worker's refusal concerned an already
completed stage-1 split; the present delivery supplies the missing stage-2 declaration.

Clause-by-clause correspondence:

- The prime is `(l : ℕ) [Fact l.Prime]`. The scheme universe `u` is explicit, and U, X,
  all affine charts V, complementary schemes Z and test schemes W are Scheme.{u}.
  There is no finite-field, geometric-fibre, finite-type, Noetherian, separation,
  nonemptiness, or characteristic assumption. The item explicitly applies the framework
  on arbitrary Y itself, which the existing AdicSheaf definitions permit.
- The coefficient category is the existing `AdicSheaf l Y`. In Module.lean:54 this is
  Mod of `adicConstantSheaf l Y` in sheaves of WeilCoefficients l on Scheme.ProEt.topology Y.
  ConstantSheaf.lean:79 defines PadicAlgCl.locallyFiniteFunctions using continuous
  functions whose image locally has finite-dimensional Q_l-span; :321 defines
  adicConstantSheaf by that functions presheaf. These are precisely B_Y and Mod(B_Y).
- All occurrences of pullback use `(adicUpperStar l f).obj`. Module.lean:126 defines
  this through the module left adjoint `modLeft` and adicConstantSheafToLowerStar.
  UpperStar.lean:236 defines that coefficient map by precomposition with the actual
  fibre-product projection. Thus these are the actual coefficient-extension module
  inverse images, not ordinary sheaf inverse image or arbitrary comparison maps.
- The given open immersion is `(j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]`.
  This uses only the quasi-compact clause of def-weil-finite-type-morphism;
  LocallyOfFiniteType is not assumed.
- M and N are `(M : AdicSheaf l U) (N : AdicSheaf l X)`; constructibility of M is hM.
  `IsAdicConstructibleSheaf` is exactly the native local finite lisse stratification
  definition (Constructible.lean:146). `IsAdicLisseSheaf` (:84) permits a rank n
  depending on the covering member, including n = 0.
- The isomorphism j* N ≅ M is the hypothesis e, expressed as Nonempty of the actual
  isomorphism type; it asks for the existence of that isomorphism, with no extra data.
- The hypothesis hzero quantifies over every W and g : W ⟶ X. Disjointness of
  `Set.range g` and `Set.range j` says its image misses j(U). The conclusion of hzero
  is Nonempty of g* N ≅ 0, exactly the stated vanishing up to isomorphism.
- Every affine open immersion is quantified by `∀ (V : Scheme.{u}) (v : V ⟶ X)
  [IsAffine V] [IsOpenImmersion v]`. Affineness is the existing scheme property,
  equivalently an isomorphism to Spec of its global ring, not an extra hypothesis.
- D is the actual `pullback j v`; a is `pullback.snd j v : D ⟶ V`, and b is
  `pullback.fst j v : D ⟶ U`. Thus their fibre-product equation has the required
  orientation. The first chart conclusions are CompactSpace D and
  QuasiSeparatedSpace D on their underlying spaces, exactly qc and qs.
- Constructibility of a(D) is `Topology.IsConstructible (Set.range (pullback.snd j v))`.
- The phrase "let z be the reduced closed subscheme supported on the complement"
  is rendered by quantifying over `(Z : Scheme.{u}) (z : Z ⟶ V)` with
  `[IsClosedImmersion z] [IsReduced Z]` and the equation
  `Set.range z = (Set.range (pullback.snd j v))ᶜ`. These specify precisely that
  reduced induced closed subscheme, independently of its presentation. They are
  not assumptions on X, U, M or N: they bind the complementary subscheme in the
  chart certificate. Existence and uniqueness of this realization are already
  supplied by the imported reduced_induced_closed_subscheme theorem; no choice
  of an arbitrary coefficient map or any replacement of the module category occurs.
- The next conclusions are constructibility of Set.range z and
  `IsCompl (Set.range (pullback.snd j v)) (Set.range z)`. IsCompl states both
  disjointness and covering, and is precisely the two assertions in the node.
- The finite partition of D is an existential S in the recorded dependency's
  `Scheme.FiniteLocallyClosedStratification D`. It contains n, Fin n-indexed locally
  closed subsets, disjointness, covering, schemes and immersions realizing their
  images. `∀ r, Topology.IsConstructible (S.stratum r)` explicitly adds the
  constructibility needed by this item without changing the dependency's notion.
- For each r, the next conjunct states IsAdicLisseSheaf of i_r* b* M using
  S.immersion r and pullback.fst. The following conjunct is Nonempty of exactly
  i_r* a* v* N ≅ i_r* b* M, with all three nested module pullbacks displayed.
- `Nonempty ((adicUpperStar l z).obj ((adicUpperStar l v).obj N) ≅ 0)` is exactly
  z* v* N ≅ 0. It is not weakened to a stalk or underlying-vector-space vanishing.
- The existential T is a finite locally closed stratification of V, with every
  T.stratum constructible and every pullback of v* N along T.immersion lisse.
- `IsAdicConstructibleSheaf N` is the other main conjunct, stating the final local
  constructibility assertion on X. The chart certificates also remain available.

Dependency declarations used:

- def-sf-native-weil-derived-framework: public import
  WeilConjectures.WeilSheaf.LowerShriek, whose native underlying interfaces are
  AlgebraicGeometry.ProEtale.AdicSheaf and adicUpperStar (Adic.Module),
  adicConstantSheaf and PadicAlgCl.locallyFiniteFunctions (Adic.ConstantSheaf),
  IsAdicLisseSheaf and IsAdicConstructibleSheaf (Adic.Constructible).
  This uses the already recorded framework, specialized on the scheme itself as
  explicitly required by the item; none of the Frobenius constructions is restated.
- def-weil-open-immersion: AlgebraicGeometry.IsOpenImmersion,
  Mathlib.AlgebraicGeometry.OpenImmersion (publicly available through the framework).
- def-weil-finite-type-morphism: AlgebraicGeometry.QuasiCompact,
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact; the recorded FiniteType entry
  module is also public-imported for this definition dependency.
- def-weil-affine-spectrum: AlgebraicGeometry.Spec and the existing IsAffine
  characterization, Mathlib.AlgebraicGeometry.Scheme / AffineScheme.
- def-pc-reduced-scheme: AlgebraicGeometry.IsReduced,
  Mathlib.AlgebraicGeometry.Properties.
- def-weil-pbc-quasi-compact-scheme: CompactSpace,
  Mathlib.Topology.Defs.Filter.
- def-weil-quasi-separated-morphism: QuasiSeparatedSpace, identified with the
  scheme's terminal morphism being AlgebraicGeometry.QuasiSeparated by
  Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated.
- def-weil-constructible-subset: Topology.IsConstructible,
  Mathlib.Topology.Constructible (this dependency has a mathlib_match, not lean).
- def-constructible-stratification: AlgebraicGeometry.Scheme.FiniteLocallyClosedStratification,
  Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification, including all its
  topological and immersion fields. Constructibility is deliberately added per stratum.
- def-pc-fibre-product: CategoryTheory.Limits.pullback, pullback.fst, pullback.snd,
  Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback.
- def-weil-closed-immersion: AlgebraicGeometry.IsClosedImmersion,
  Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion.

The remaining public dependencies above are provided transitively by the public
framework and stratification imports. For the proof plan, the module imports
WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme,
WeilConjectures.ConstructibleSheaf.Pullback, and
WeilConjectures.SixFunctors.ProEtale.Adic.ExtensionByZero without `public`.
The latter is the recorded qcqs-stratification dependency module. The affine-qcqs,
open-base-change, affine-cover criterion, constructible-open restriction, retrocompact
open-image and affine-basis Mathlib declarations are already available from the
public imports. lem-sf-native-adic-pullback-exact-lisse has no recorded Lean
attachment in the read snapshot; its proof APIs adicUpperStarComp,
adicUpperStarCompIso and IsAdicLisseSheaf.upperStar are already imported from
native Adic.Module / Adic.Constructible. No duplicate of that node is introduced.

Edge cases checked before writing:

- If D is empty, Fin 0 is permitted for S and the reduced complement is all V;
  the zero-restriction hypothesis gives the only necessary lisse piece.
- If Z is empty, its zero restriction is automatic and the D strata cover V.
- If V or X is empty, all relevant pointwise local conditions are vacuous, and
  zero-stratum finite partitions are permitted by the dependency structures.
- M = 0 and rank-zero lisse restrictions are permitted: no positive-rank condition
  is introduced. The given isomorphism and complement condition are still exactly
  the hypotheses stated by the node.
- j = identity gives D ≅ V and empty complement; j with empty source gives the
  complementary zero case. Neither is excluded by any binder.
- Non-Noetherian affine charts and a non-separated X are included. Quasi-compactness
  of j is essential for qc of D; no extra quasi-compactness of U or X is assumed.
- A finite family is indexed by Fin n with n arbitrary, including 0. This does not
  impose a nonempty family or uniform lisse rank.

Searches (all through the prescribed msearch wrapper, plus direct source rg):

- LeanFinder: "A constructible adic sheaf on a quasi compact open and zero on its
  complement admits finite lisse stratifications on every affine chart". Eight hits,
  including AlgebraicGeometry.compact_open_induction_on and affine-cover results;
  no native sheaf statement matching all these hypotheses and conclusions.
- Loogle: `"IsConstructible", "IsRetrocompact"`. One hit,
  IsRetrocompact.isConstructible, only a topological subset lemma.
- Mathlib grep: `IsAdicConstructible|IsAdicStratifiedLisse|stratification.*[Cc]ompl`.
  Zero hits; native adic notions belong to the project.
- LeanSearch: "A constructible sheaf on a quasi compact open extends constructibly
  if its restriction to the closed complement is zero". Eight hits on constructible
  subsets, including Topology.IsLocallyConstructible.isConstructible and complement
  lemmas; none is a theorem about these module sheaves.
- rg in Mathlib, WeilConjectures and Sheaf for
  `affine_open_zero_stratification|open.*zero.*stratifi|stratifi.*zero.*open`:
  only unrelated prose occurrences in Sheaf, no declaration with this statement.
- rg of the item ID in WeilConjectures and Sheaf: no existing declaration.
- rg on the native IsAdicConstructibleSheaf, IsAdicStratifiedLisseSheaf,
  adicUpperStar, and module pullback compositor definitions located the exact
  existing interfaces reused here. Read Module.lean:54,119-139,300-326;
  Constructible.lean:84-150; ConstantSheaf.lean:79,321; UpperStar.lean:236;
  ExtensionByZero.lean:47-250; and the full finite locally closed stratification module.
  `of_isCompl` assumes globally stratified lisse restrictions, and
  `openImmersionLowerShriek` concerns the specific extension-by-zero object. Neither
  states this item's general-N theorem and its complete affine-chart certificate.

Validation: scompile.py checked the sandbox module and the named library module
against the live published build successfully, with no errors or warnings. The first
probe required opening the standard ZeroObject scope and using the explicit scheme
carrier coercion in CompactSpace and QuasiSeparatedSpace; both are repaired.
No mathematical statement fault or STATEMENT-DISPUTED issue was found.

## Second reading by Q95

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

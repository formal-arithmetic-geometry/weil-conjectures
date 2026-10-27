## Worker report

The module states `AlgebraicGeometry.ProEtale.openScalarRestrictedTransposeExpansion`,
with one sorry, and constructs `openScalarRestrictedTranspose` with real data.
Source read: main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Locality paragraph. The node is unchanged
apart from its Lean attachment and the added landed statement dependency
`sk-def-sp-normalized-towers`, which owns the existing full Dctf category used here.
No new nodes, dependency repair modules, or mathematical statement correction.

Hypotheses and clauses:

- Field k, characteristic p>0, prime ell different from p: `k`, `[Field k]`,
  `[CharP k p]`, `_hp`, `[Fact ℓ.Prime]`, `_hℓ`.
- Finite commutative ell-primary rings and a unital homomorphism: `{A B : Type u}`,
  `[CommRing A] [CommRing B] [Finite A] [Finite B]`, `φ : A →+* B`.
  The common N is `ℓ ^ n`; `_hN`, `_hA`, `_hB` give the stated bound and annihilation.
  In a unital ring `(N : A)=0` is equivalent to N annihilating every element.
- U, X, Y are separated finite type k-schemes: their `Over (Spec (.of k))`
  instances and `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` instances on
  each structure morphism. All maps are k-morphisms via `IsOver`.
- The general separated finite type f is `f`, with its three geometric instances;
  `j` has `IsOpenImmersion` and `QuasiCompact`. No smoothness instance appears.
  Its composite with f is represented in the stipulated composition coordinates.
- The compactification of f is `c : Compactification f`, with the same setting
  imposed on c.Z and both its arrows. A separately chosen compactification of g
  has already been identified with the composite by the node's specified
  adjunction-preserving comparisons; all equations live in those coordinates.
- The category C is `spFiniteConstructibleTorCategory T R`, a full subcategory of
  `Scheme.proEtaleDerivedCategory T R`. Its defining property requires one finite
  cohomology interval, intrinsic constructibility in every degree, and
  `HasFiniteProEtaleTorAmplitude`. The latter tests every degree-zero module sheaf
  with one common finite ordered interval; no perfectness substitute is used.
  The ordinary etale category is background to the given transfer, not an extra
  quantified case in the conclusions, which the node explicitly locates pro-etale.
- F_f is `reductionCompactSupport R c.i c.g`, restricted by `ObjectProperty.lift`.
  `hFA`, `hFB` are membership certificates, and `GA`, `GB`, `adjA`, `adjB`
  are the given right adjoints and their actual finite-Tor adjunctions. These
  quantify over all choices, so also cover the prescribed Brown restrictions.
  Full-subcategory arrows are read by `.hom`, which changes no morphism.
- K is `K : spFiniteConstructibleTorCategory Y A`; M is `(GA.obj K).obj`;
  L is `(proEtaleConstantRingDerivedPullback A j).obj (GA.obj K).obj`.
  The canonical scalar functor is `scalarExtensionFunctor φ T`. The certificate
  `hKB` puts its value on K in C_{Y,B}; this is supplied by scalar preservation.
- `hb` certifies invertibility of exactly the specified b_f component, already
  part of the node's isomorphism data. Its inverse is `@inv ... hb`, never an
  inverse of r. b_f itself is `reductionDirectImageComparison φ c.i c.g`.
- The ringed open-extension coordinates are `openExtension (A := R) j`; their
  right adjoint is exactly `proEtaleConstantRingDerivedPullback R j`.
  `proEtaleRingDerivedOpenAdjunction ...` is the actual localized open adjunction,
  not an independently supplied adjunction or counit. `reductionOpenModel R j`
  is the existing normalized identification from sectionwise extension by zero;
  its definition uses the unit-preserving pullback-coordinate comparison and
  uniqueness of left adjoints. In these coordinates the specified open b_j,
  normalized by its identity proper factor, is `openScalarIso φ j`. Thus the
  statement does not assume an abstract scalar square as a hypothesis.
- The named scalar/restriction map a_j is exactly
  `(directImageScalarPullbackIso φ j).inv`, in the direction T_U U_A -> U_B T_X.
- `r` is an arbitrary ambient morphism from T_X M to G_B T_Y K, with precisely
  the node's `hr` counit equation. Fullness makes this the same finite-Tor arrow.
- The helper constructs d as `a_j.app M ≫ U_B.map r` and applies the inverse
  open Hom equivalence, F_f, and its counit. By `Adjunction.comp_homEquiv` this
  is tau = epsilon_g F_g(d) with the stipulated composition adjunction; there
  is no assumption of the desired expansion in its definition.
- First conjunct: `J_B.map a_j ≫ v_B = b_j.inv.app L ≫ T_X.map v_A`.
  This is the first displayed equality, with Lean's left-to-right composition.
- Second conjunct: tau is `F_B.map (J_B.map a_j ≫ v_B) ≫ F_B.map r ≫ eps_B`.
  This is the first expansion, including the actual open counit.
- Third conjunct: tau is `F_B.map b_j.inv ≫ F_B.map (T_X.map v_A) ≫
  b_f.inv ≫ T_Y.map eps_A`. This is the second expansion. Each endpoint is
  F_f,B J_B T_U L -> T_Y K, which is exactly F_g,B T_U L -> T_Y K under the
  stipulated adjunction-preserving comparison. No clause or invertibility claim
  about r is added.

Dependency declarations read and used (directly or through public reexports):

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `CondensedRing.compactificationOverField`, the standing Nagata setting.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  `Etale.DerivedCategoryModule`, `DerivedCategory.torsionCohomology`.
- `Sheaf.Paper.ProEtaleFixedModuleConstructible`:
  `Scheme.IsConstructibleProEtaleFixedModuleSheaf` and its public intrinsic
  `Scheme.IsConstructibleProEtaleModuleSheaf`, which is the intrinsic category's
  cohomology predicate, not a new constructibility definition.
- `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations`:
  `Scheme.HasFixedCoefficientProEtaleTorAmplitude`; its public imported original
  `Scheme.HasFiniteProEtaleTorAmplitude` is used in the intrinsic category.
- `Sheaf.Paper.EtaleProEtaleAdjunctionTransfer`: `AdjunctionTransfer.proEtaleProperty`,
  `proEtaleLowerShriek`, `brownRestriction`, `etaleProEtaleAdjunctionTransfer`;
  the transfer is background to the given finite-Tor adjunctions.
- `Sheaf.SecSmoothPurity.ScalarExtensionFunctor`: `scalarExtensionFunctor`.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`:
  `ModuleCat.nonempty_ordinaryDerivedChangeOfRings` and the reexported general
  sheaf `DerivedChangeOfRingsCochainModel` interface for the scalar construction.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `WeilConjectures.Compactification.RefinementCategory`:
  `Compactification.Refinement`, `Compactification.category`, and `Compactification`.
- `Sheaf.Paper.FiniteLocalizingExceptionalPreservation`:
  `CondensedRing.localizingExceptionalAdjoint_preserves_finiteConstructible`.
- `Sheaf.Paper.MateOpenRestriction`: `CondensedRing.mateOpenImmersion`.
- `Mathlib.CategoryTheory.Adjunction.Basic`: `Adjunction.comp`, `comp_homEquiv`,
  `comp_counit_app`. The helper uses the two inverse Hom equivalences in succession.
- `Sheaf.Paper.EtaleProEtaleCoefficientCompatibility`:
  `CoefficientCompatibility.etaleProEtaleCoefficientCompatibility_counit` and
  the refinement/composition comparisons justify the chosen coordinates.
- `Sheaf.SecSmoothPurity.ReductionDirectImage`:
  `reductionDirectImage_isIso` and public `reductionDirectImageComparison`,
  `reductionCompactSupport`, `reductionOpenModel`, `openScalarIso`.
- `Sheaf.SecSmoothPurity.DirectImageScalarOperations`:
  `directImageScalarPullbackIso`, the exact named comparison in the dependency.
- Added landed dependency `sk-def-sp-normalized-towers`, module
  `Sheaf.Paper.SmoothPurityNormalizedTowers`: `spFiniteConstructibleTor`,
  `spFiniteConstructibleTorCategory`. Reused to avoid a second definition of Dctf.

The proof dependency `lem-sp-open-proetale-counit-scalar` has no Lean attachment
in the read repository, so there is no module yet to import. The main theorem's
proof docstring records its use in Step 1. It is a proof prerequisite, not a
missing notion needed to type this statement. `Adjunction.comp` is imported.

Edge cases checked before writing: empty U or X, zero K, zero rings, n=0 (then
N=1 and the annihilated rings are zero), the identity open, identity coefficients,
and nonflat maps such as Z/ell^2 -> Z/ell. No nonemptiness, domain, field coefficient,
flatness, or invertibility of r is required. The coefficient universe remains u,
with the existing constant-ring lift and site universes u+1/u; no universe equality
or site size restriction has been imposed. Composition uses no division by scalars.

Searches made:

- msearch.py leansearch: "Composite adjunction counit transpose after open restriction
  and extension of scalars for finite coefficient sheaves". Eight hits on ordinary
  ModuleCat scalar adjunctions and Adjunction.functorialityCounit, no geometric match.
- msearch.py leanfinder: "Expand counit transpose of restricted scalar exceptional
  map using actual open extension by zero counit and scalar pullback comparison".
  Eight hits, led by ModuleCat.ExtendRestrictScalarsAdj.counit_app/counit and
  RestrictionCoextensionAdj.counit'; none states the specified geometric identities.
- msearch.py loogle: "CategoryTheory.Adjunction.comp_counit_app,
  CategoryTheory.Adjunction.counit_naturality". Zero hits for the combined query.
- msearch.py grep, CategoryTheory/Adjunction: "comp_counit|counit_naturality".
  Fourteen hits including Basic.lean comp_counit_app and Mates.lean; read the
  composite-adjunction definitions and signatures. These are abstract tools.
- rg in lean/Sheaf and lean/WeilConjectures for open counit/scalar names and
  restrictedTranspose/restricted_transpose. Found OpenScalarExchange,
  ReductionDirectImageComparison, DirectImageScalarOperations and normalized
  finite-Tor categories; no existing theorem with these three assertions.
- grep of the exact node id in lean/WeilConjectures: no match.
  Existing upstream openImmersionLowerShriekExtendScalarsIso and its mate theorem
  use fixed-module coordinates and do not state the two restricted expansions.

Validation: prescribed scompile.py compiled both the sandbox and library-module
paths without messages (library pass 41.0 seconds). No theorem is proved here.
Prescribed deliver2.py --no-push completed successfully: preflight and compilation
passed for dry-run commit 28ab89b72f6. The search report was then supplemented
with the successful LeanSearch query; the Lean source has not changed. On resumption,
dry-run commit f372ee49d99 also passed. A later delivery compile timed out without
pushing; the prescribed scompile retry passed cleanly in 21.0 seconds (sandbox)
and 20.2 seconds (library), without changing the source or the time limit.

## Second reading by NY

Author's separate second pass, with node and final source open; the dispatcher
explicitly prohibits starting other agents, so this is not claimed as an independent
worker review. The maintainer's independent review remains necessary.

Checked each hypothesis and all three equations against the mappings above. The
important direction check is a_j = directImageScalarPullbackIso.inv; using hom
would reverse the required arrow. The second and third equalities compose in Lean's
reverse printed order relative to the TeX convention, and retain the same source
and target. Tau is defined with the inverse Hom equivalence before expanding it,
so the naturality content has not been made definitional. The open counit and
openScalarIso are fixed existing constructions; no assumed open-scalar equation
or arbitrary replacement map is present. b_f is the specified proper-counit/open
comparison. The only extra Lean binders certify membership and invertibility
already present in the mathematical setup, rather than adding mathematical
hypotheses. Added the landed category-owning dependency instead of duplicating it.
No statement mismatch or disputed mathematical assertion was found.

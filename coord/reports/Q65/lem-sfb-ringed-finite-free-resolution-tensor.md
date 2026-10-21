## Worker report

The module Sheaf.Algebra.Homology.FiniteFreeResolutionTensor states every part of
lem-sfb-ringed-finite-free-resolution-tensor. Its namespace is
SheafOfModules.FiniteFreeResolution. All four theorems have sorry proofs; the four
helper definitions contain real data. No mathematical statement or dependency was
changed, and no dependency repair or new independent notion was necessary.

The source was read in literature/stacks-project/sites-cohomology.tex, labels
lemma-bounded-flat-K-flat, lemma-K-flat-quasi-isomorphism and definition-derived-tor,
and in literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
sk-def-localizing-closure/sk-def-localizing-closure-ctf-equals-bc.proof.md, Local models.
The proof docstrings carry the seven steps of the node, including the finite-coordinate
calculation, bounded-flat argument, signed symmetry, descent and augmentation check.

Clause-by-clause rendering:

- Site and commutative ring sheaf: C : Type u, Category.{v} C,
  J : GrothendieckTopology C, R : Sheaf J CommRingCat.{r}. EssentiallySmall.{r} C
  expresses the site's set-sized smallness in a common containing coefficient universe,
  as the node's proof step 3 specifies. The object, morphism, coefficient and derived
  morphism universes u, v, r, w are separately bound; no equality is imposed.
- Module sheaves: Modules R is the existing KFlatFixedTensor.Modules abbreviation
  for ringedSiteModules, hence exactly Mathlib SheafOfModules over the underlying
  ring sheaf. No module category is constructed afresh.
- Complex and bound: K : CochainComplex (Modules R) ℤ, b : ℤ and
  hbound : ∀ i, b < i → IsZero (K.X i). Zero means categorically zero, not an
  equality with one arbitrary chosen zero object.
- Specified finite ranks and frames: rank : ℤ → ℕ, hrank above b, and
  theta : ∀ i, K.X i ≅ power R (𝟙_ (Modules R)) (rank i).
  The monoidal unit is the existing SheafOfModules.unit of the underlying ring sheaf.
  power is a transparent abbreviation of the categorical finite product indexed by Fin n.
- Termwise flatness and K-flatness: the witnesses hflat and hK are existential proof
  binders for exactly IsFlatOnSite (K.X i) and IsKFlatIndependentCoefficients K.
  They are conclusions; no flatness or K-flatness is assumed.
- Supplied resolution: M : Modules R and epsilon : K ⟶ single R M with
  [QuasiIso epsilon]. single is a transparent abbreviation of Mathlib's single
  cochain complex at integer degree zero.
- Arbitrary second factor: ∀ N : Modules R, without a flatness hypothesis.
- Explicit gamma: gamma i is an isomorphism N ⊗ K.X i ≅ N^(rank i).
  Its hom is N ◁ theta.hom followed by coordinateMap; its inv is coordinateInverse
  followed by N ◁ theta.inv. coordinateMap projects the free factor then uses the
  right unitor, so on pure tensors it is z ⊗ (b_j) ↦ (b_j z).
  coordinateInverse is the finite sum of the N-coordinate projections followed by
  the inverse right unitor and the free-coordinate inclusions, exactly
  (z_j) ↦ Σ_j z_j ⊗ e_j. These are actual categorical maps, not arbitrary witnesses.
- Actual T_N(K): delta and sq supply CochainComplex.of
  (fun i ↦ power R N (rank i)) delta sq. Thus its terms are precisely the finite
  powers, and its differential is gamma.inv ≫ (N ◁ K.d) ≫ gamma.hom.
  sq asserts the differential-square identity.
- Relation with total tensor: tau is an actual cochain isomorphism from
  Tot(N[0] ⊗ K) onto that complex. Its equation on the (0,i) summand fixes its
  degree-i component to gamma after the canonical single-complex identification.
- Ordinary unbounded derived category: DerivedCategory, DerivedCategory.Q and
  HasDerivedCategory.{w} are the recorded Mathlib localization. derivedTensor R
  is the existing curried siteDerivedTensorIndependentCoefficients, with no new choice.
- Canonical comparison: c is a natural isomorphism for the fixed K tensor functor,
  normalized on every flat-term K-flat resolving L by representativeIso. comparison
  has exactly the displayed derived tensor source and Q(T_N(K)) target. Its equality
  specifies the composite of inverse tensor(Q epsilon), c inverse, Q sigma and Q tau.
  Consequently epsilon and the actual total tensor determine the comparison.
- Signed interchange: signedInterchange supplies a cochain isomorphism for every pair
  P,L, with (p,q) summand (-1)^(pq) times the ordinary sheaf braiding, and its
  naturality for arbitrary cochain maps f,g. The sigma used in the main comparison
  satisfies that same summand equation for K and N[0]. This covers the resolving
  complexes and the sign-free (0,i) computation, not merely existence of a symmetry.
- Local matrices: the U : Cᵒᵖ clause quantifies over every site object and every
  coefficient matrix a : Fin(rank(i+1)) → Fin(rank i) → R(U). Its antecedent
  says theta_(i+1) d theta_i^-1 acts by that matrix on sections, tested by the
  categorical coordinate projections. Its conclusion says delta acts on all
  N-power sections by the same Σ_j a_kj • z_j. Because U is arbitrary this
  includes matrices specified only on covering objects; no global matrix is assumed.
- Two-term and degree-zero specializations of the general result: the final clauses
  give zero terms outside {-1,0}, or a specified cochain isomorphism to N^(rank 0)[0]
  whose component at zero is the canonical identity, respectively. The delta formula
  remains part of the same conjunction in both cases.
- Specified short exact presentation: shortExact_finiteFree_augmentation takes
  m,n,M,f,g,hfg and (ShortComplex.mk f g hfg).ShortExact. hfg is the proof datum
  already entailed by short exactness, made explicit to form the ShortComplex.
  It supplies an augmentation of mappingCone(single.map f) onto M[0], whose
  composite with the cone's target inclusion is exactly single.map g, and asserts
  QuasiIso epsilon. This standard cone is the actual complex [B^m → B^n] in
  degrees [-1,0] (with canonical zero direct-sum factors). The accompanying tensor
  formula is Q(mappingCone(single.map (coordinateInverse m ≫ (N ◁ f) ≫
  coordinateMap n))). Thus it uses the given f, not an arbitrary quasi-isomorphic
  complex or an arbitrary differential.
- Specified free isomorphism: finiteFree_iso_augmentation takes the given
  e : B^n ≅ M, asserts QuasiIso(single.map e.hom), and gives the derived tensor
  isomorphism to Q(N^n[0]).
- No existence of points, flatness of N, flatness of cohomology, boundedness below,
  or global bound on the finite ranks occurs in any hypothesis.

Dependency declarations read and used:

- Sheaf.CategoryTheory.SiteCoveringAxioms: Precoverage.IsSiteForCoverings; the site
  topology is its usual GrothendieckTopology encoding, without additional site axioms.
- Sheaf.CategoryTheory.RingedSiteModules: CategoryTheory.ringedSiteModules,
  used through Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated:
  SheafOfModules.KFlatFixedTensor.Modules.
- Mathlib.Algebra.Homology.HomologicalComplex: CochainComplex, with ℤ indices.
- Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite: SheafOfModules.IsFlatOnSite.
- Sheaf.Algebra.Homology.KFlatIndependentCoefficients:
  CochainComplex.IsKFlatIndependentCoefficients.
- Mathlib.Algebra.Homology.QuasiIso: QuasiIso.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: DerivedCategory,
  HasDerivedCategory and DerivedCategory.Q.
- Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients:
  SheafOfModules.siteDerivedTensorIndependentCoefficients, through the existing
  derivedTensor abbreviation and representativeIso in KFlatFixedTensorTriangulated.
- Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses:
  cochainModulesMonoidal, cochainModulesSymmetric, cochainModulesPreadditive,
  and tensor-colimit preservation instances, for the recorded sheaf tensor.
- Mathlib.Algebra.Homology.BifunctorShift: CochainComplex.mapBifunctor and
  ιMapBifunctor, via the recorded totalTensor/ordinaryTensor abbreviations.
- Proof imports retain Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
  (isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite),
  WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed (tensorClosed),
  and Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification (sheafification).
  The fixed-tensor comparison is from the imported
  SheafOfModules.KFlatFixedTensor.kFlat_fixed_tensor_triangulated.

Edge cases checked before and after writing: rank zero uses the empty categorical
product, the empty sum coordinateInverse is zero, and both are zero objects in this
abelian category. N=0 and the zero ring give zero complexes. A negative bound is
permitted. A resolution unbounded below is permitted. For a one-point Z-ringed site,
M=Z/2 with presentation Z --2--> Z and N=Z/2 gives [Z/2 --0--> Z/2], retaining
both degrees and showing why no flatness of N may be imposed. In a degree-zero
presentation the specified e is used in the actual map, not forgotten. All local
matrix quantification includes empty rows or columns. No disputed statement found.

Searches for an existing declaration (the exact tool outputs are in searches.jsonl):

- msearch.py leanfinder: "A bounded above finite free sheaf resolution computes
  derived tensor by the same differential matrices on finite powers of any module
  sheaf". Eight hits: SheafOfModules.relationsOfIsCokernelFree_I,
  relationsOfIsCokernelFree_s, ιFree_mapFree_inv_assoc, Presentation.mapRelations,
  Presentation.mapGenerators, mapFree, PresheafOfModules.Monoidal.tensorObj,
  LightCondensed.instMonoidalLightCondSetLightCondModFree. None states this result.
- msearch.py loogle: "CochainComplex, QuasiIso". Twelve hits on shifts, truncations,
  localization and mapping-cone quasi-isomorphisms; none gives finite-free sheaf
  coordinates, the supplied augmentation and the derived tensor calculation.
- msearch.py grep: "finiteFree|IsKFlat|derivedTensor", Algebra/Homology: zero hits.
- rg in lean/WeilConjectures and lean/Sheaf for finiteFree/tensor, tensor/Pi and
  tensor/biproduct names found MonoidalFree.freeTensorFreeIso (ordinary tensor of two
  free sheaves), flat tensor exactness and K-flat descent. None supplies this theorem.
  ModuleCatFiniteResolution concerns noetherian rings and finite modules rather than
  an arbitrary ringed site with specified sheaf coordinates. Those are not matches.
- rg for the node id in lean/WeilConjectures: no matches. rg for the intended namespace
  and theorem names: no existing full-name collision. The unrelated coordinateMap
  names in other namespaces are not this canonical finite-power contraction.

The finite product and single helpers are transparent aliases of existing notions;
the coordinate maps are the explicit maps belonging to this node's statement under
the authorized owning-node helper rule. They do not introduce independent notions
or require new DAG nodes. Each is listed in lean.declarations with source docstrings.

## Second reading by Q65

A final clause audit was performed with the node and module open. This is the worker's
self-check, not an assertion that another agent reviewed it; the dispatcher brief
prohibits subagents and assigns the independent review to the maintainer.
The audit added signedInterchange for arbitrary complexes and its naturality, beyond
the K,N[0] specialization, and added explicit tensor-cone and single-complex formulas
to the two augmentation theorems. All hypotheses, both coordinate directions, the
local matrix clause and the comparison composite were checked against the node.
No source correction or declaration-interface repair was needed.

## Validation

The prescribed scompile.py compiled the final module cleanly in both sandbox and
final library contexts (42.5 s and 44.8 s). deliver2.py --no-push then printed
OK: preflight and per-file compilation passed. The only changed item-node field
is lean. All four postponed proofs are sorry; no local build or direct repository
edit was used.

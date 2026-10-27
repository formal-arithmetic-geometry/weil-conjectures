## Worker report

The delivery states `AlgebraicGeometry.AlgebraicSpace.supported_etale_excision` in
`lean/Sheaf/AlgebraicGeometry/SupportedEtaleExcision.lean`. It uses the existing unbounded
derived categories on the equivalent small affine model of the small etale ringed topos.
It does not replace the module category by quasi-coherent modules or use abelian-sheaf
cohomology. The only node-field change is `lean`; there are no statement corrections,
new nodes, or dependency repairs. No repair note exists for this item.

The module supplies the transport needed to compose the two recorded interfaces.
`smallEtaleModuleShriek` is literally the inverse of the existing module-basis equivalence,
followed by the recorded `etaleModuleShriek`, followed by target basis restriction.
`smallEtaleModuleShriekAdjunction` transports the recorded adjunction, including the
ordinary multiplication-normalized tensor/restriction comparison.
`smallEtaleModuleShriek_exact` states its exactness and additivity. The three subsequent
instances are projections of that named theorem. `spaceEtaleDerivedShriek` is its
`mapDerivedCategory`, and `spaceEtaleShriekAdjunction` is the actual exact derived
adjunction transported along `spaceEtaleDerivedRestriction_existsUnique`, not an arbitrary
adjunction. `spaceEtalePullbackShift` transports the standard exact-functor shift comparison
along that same representative-normalized isomorphism. Every definition has explicit
data; the two postponed theorems have source and full proof docstrings matching clauses
and proof steps of this node. No independent missing notion is introduced.

Hypotheses and clauses, matched individually:

- The size convention is rendered by explicitly declared universes `u w`, `Scheme.{u}`,
  `AlgebraicSpace S`, their existing small affine model, and
  `[HasDerivedCategory.{w} W.SmallModules]` for `W = X,V,U,T`. This is the dependency's
  chosen derived-localization interface, allowing an arbitrary common localization size.
- The base scheme is `{S : Scheme.{u}}`. The spaces `X,V,U,T : AlgebraicSpace S` have
  exactly their existing etale structure sheaves, module sheaves, and derived categories.
- The open inclusion is `i : U ⟶ X`, with `hi : IsRepresentableWith
  (fun _ _ f ↦ IsOpenImmersion f.left) i.hom.hom`. This is the defining predicate of
  `OpenSubspace` expressed on its inclusion, as in the recorded elementary-shriek node;
  no chosen scheme atlas or scheme representability of X is imposed.
- The representable etale morphism is `p : V ⟶ X` with `hp : IsEtale p.hom.hom`.
  This existing predicate means representability by etale scheme morphisms.
- The reduced closed complement is `Z : ClosedSubspace X`,
  `hZ : IsReduced (Z.val : AlgebraicSpace S)`, and
  `hSupport : pointImage Z.val.arrow.hom.hom = (pointImage i.hom.hom)ᶜ`.
  Existence and uniqueness are already recorded by the reduced-closed-support dependency;
  no redundant uniqueness hypothesis is imposed on the chosen representative.
- The isomorphism over that complement is
  `hIso : IsIso (Limits.pullback.snd p.hom Z.val.arrow.hom)` in fppf sheaves,
  exactly the projection `V ×_X Z → Z`.
- `q : T ⟶ U`, `t : T ⟶ V`, `sq : IsPullback q t i p` present the overlap
  `U ×_X V`. Allowing any pullback presentation is equivalent to using the chosen one.
- `p^*` is the recorded `spaceDerivedPullback p`, canonically identified with exact
  etale restriction by `spaceEtaleDerivedRestriction_existsUnique`. The left adjoint
  is the transported, termwise `spaceEtaleDerivedShriek p hp`; the right adjoint and
  its actual counit are `derivedDirectImage p` and `spaceDerivedAdjunction p`.
- The support condition is the object property
  `fun F : V.DerivedModules ↦ IsZero ((spaceDerivedPullback t).obj F)`.
  Quantification over its full subcategory includes every F satisfying `F|_T=0`.
  `IsZero` means vanishing of the object in the derived category, without any choice
  of complex representative or boundedness requirement.
- `∃ c : inclusion ⋙ spaceEtaleDerivedShriek p hp ≅ inclusion ⋙ derivedDirectImage p`
  gives an actual natural isomorphism on all such F simultaneously. Its component
  `c.hom.app F` is precisely `p_!F → Rp_*F`.
- The first conjunct is `IsIso ((spaceEtaleShriekAdjunction p hp).unit.app F.obj)`,
  exactly invertibility of `F → p^*p_!F`.
- The second conjunct composes that unit with
  `((spaceDerivedAdjunction p).homEquiv _ _).symm (c.hom.app F)` and requires the
  identity of F. The latter term is the transpose of `c_F` under `p^* ⊣ Rp_*`.
  Because the unit is invertible, this equation states exactly that its transpose
  is the inverse unit; it uniquely characterizes each `c_F` and the natural c.
- The third conjunct is `IsIso ((spaceDerivedAdjunction p).counit.app F.obj)`,
  the actual canonical counit `p^*Rp_*F → F`.
- The fourth conjunct is `IsZero ((spaceDerivedPullback i).obj
  ((derivedDirectImage p).obj F.obj))`, namely `i^*Rp_*F=0`.
- The last conjunct quantifies over every `M : X.DerivedModules` and `n : ℤ` and
  asserts `Function.Bijective` of the specified map from `Rp_*F ⟶ M⟦n⟧`.
  It first precomposes with `c.hom.app F`, then applies the actual shriek
  `homEquiv F.obj (M⟦n⟧)`, then postcomposes with
  `(spaceEtalePullbackShift p hp n).hom.app M`. The codomain is therefore exactly
  `F ⟶ ((spaceDerivedPullback p).obj M)⟦n⟧`. The explicit formula ensures naturality
  in M and in supported F: c is natural, the adjunction Hom equivalence is natural,
  and the shift comparison is a natural isomorphism. This states the canonical
  bijection, not only equality of Hom-set cardinalities or an unspecified equivalence.
- There is no quasi-compactness, separation, perfectness, quasi-coherence, flatness,
  or boundedness binder. No such condition is hidden in the full subcategory.

Dependency declarations read and reused (the namespace below is
`AlgebraicGeometry.AlgebraicSpace` except where stated):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsRepresentableWith`,
  `IsEtale`, `Modules`, `pullback`, `structureSheaf`, `etaleMap`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  its underlying category is Mathlib `SheafOfModules` with the existing abelian instance.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and its usual integer shifts.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace` and its exact
  defining scheme-test predicate, used on `i` as in the elementary-shriek signature.
- `Sheaf.AlgebraicGeometry.ReducedClosedSubspaceSupport`:
  `exists_unique_reduced_closed_subspace`; its existing `ClosedSubspace`, `IsReduced`,
  and `pointImage` interface supplies the complement binders.
- `Sheaf.AlgebraicGeometry.ElementaryEtaleShriekExact`: `etaleModuleShriek`,
  `etaleModuleShriekAdjunction`, `elementary_etale_shriek_exact`.
- `Sheaf.AlgebraicGeometry.SpaceDerivedEtaleChartCalculus`:
  `spaceEtaleTensorPullback_exact`, `spaceEtaleDerivedRestriction`,
  `spaceEtaleDerivedRestriction_existsUnique`, `spaceDerivedChart_etale_baseChange`.
  Through its public imports we use the existing `DerivedModules`, `derivedDirectImage`,
  `smallModuleTensorPullback`, `spaceDerivedPullback`, `spaceDerivedAdjunction`,
  `smallModuleEquivalence`, `smallModuleRestriction`, and the section-normalized
  `moduleTensorPullback_etale_restriction`.
- `Sheaf.CategoryTheory.ExactDerivedAdjunction`:
  `CategoryTheory.Adjunction.mapExactDerivedCategory`, the independently universal
  recorded declaration of `def-weil-exact-derived-adjunction`.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `CategoryTheory.Functor.mapDerivedCategory`, `mapDerivedCategoryFactors`, and its
  `CommShift ℤ` instance. This is the `mathlib_match` of
  `lem-weil-pbc-exact-functor-derived-factorization`, not a missing lean record.
- Plain proof imports retain the recorded modules for
  `lem-sfb-space-geometric-points-conservative`,
  `lem-pur-site-restriction-module-adjunction-exact`,
  `def-weil-extension-by-zero-presheaf`, and
  `lem-weil-pbc-module-sheaves-colimits-forgetful`. The currently unstated proof-only
  nodes `lem-sfb-space-derived-hom-mayer-vietoris`,
  `lem-sfb-space-etale-conservative-geometric-points`, and
  `lem-sfb-space-etale-sum-stalks` have no module to import; they are explicitly
  retained in the node's unchanged proof and in the main theorem's proof docstring.

Edge cases checked against the statement and proof:

- F=0 works: both functors preserve zero and the unique transpose is inverse to the
  zero-object identity; both Hom sets are singleton sets.
- U=X makes T=V, so only zero derived objects satisfy the support condition. The
  theorem does not incorrectly assert `p_! ≅ Rp_*` on arbitrary complexes in this case.
- U empty makes the complement all of X (with reduced structure); the etale
  isomorphism over the complement gives the unique geometric lift everywhere.
- Empty spaces cause no excluded nonempty-index or nonzero-ring assumption; the
  full support subcategory and derived categories still make sense.
- p an isomorphism, and the identity in particular, makes both normalized units
  and the comparison the ordinary identity comparisons.
- n=0 and negative n are included by the integer binder and the actual exact-functor
  shift comparison; no cohomological-degree restriction occurs.
- Infinitely many etale lifts over U are allowed because all summands there vanish;
  outside U the fibre is singleton. The morphism need not be quasi-compact or separated.
- Nonreduced X is allowed; no assertion that an arbitrary pullback of Z is reduced
  appears in the signature or proof docstring.

Searches made before adding declarations:

- `msearch.py ... leanfinder "Extension by zero equals derived pushforward for complexes
  supported on an etale neighbourhood of a closed complement"`: eight hits, all about
  shape embeddings of homological complexes (`HomologicalComplex.isZero_extend_X`,
  `IsSupportedOutside`, etc.); none states geometric etale excision.
- `msearch.py ... leansearch "Extension by zero and derived direct image coincide on
  supported complexes in an elementary etale square of algebraic spaces"`: eight hits
  about extending supported functions or complex-shape embeddings, no module-sheaf match.
- `msearch.py ... loogle '"SheafOfModules", "extensionByZero"'`: zero hits. A preceding
  query `Adjunction.homEquiv, Functor.mapDerivedCategory` returned no hits and reported
  the unqualified identifier `Adjunction.homEquiv` unknown; it was not used as evidence
  of a missing generic adjunction API, which was read directly from Mathlib.
- `msearch.py ... grep 'extensionByZero|lowerShriek|supportedEtale'`: zero Mathlib hits.
- `rg -n 'supported.*[Ee]tale|[Ss]upportedEtale|etale.*[Ee]xcision|smallModuleShriek|derivedShriek'
  lean/WeilConjectures lean/Sheaf`: supported-class and coefficient/purity theorems,
  not this structure-sheaf module result on algebraic spaces.
- `rg -n 'lem-sfb-space-supported-etale-excision' lean/WeilConjectures`: no hits.
- `rg -n 'etaleModuleShriek|smallEtaleModuleShriek|spaceEtaleDerivedShriek|spaceEtaleShriekAdjunction'
  lean/Sheaf lean/WeilConjectures`: only the recorded ordinary shriek construction in
  `ElementaryEtaleShriekExact.lean`; reused it instead of introducing another adjoint.
- Searches of the proposed helper names and main theorem in both source roots found
  no existing declarations. `dag/lean_names_upstream.json` contains no new helper match.

The local Stacks source at `spaces-perfect.tex`,
`lemma-pushforward-with-support-in-open` (Tag 08GG), was read through its full statement
and proof, together with `lemma-exact-sequence-lower-shriek` (Tag 08GV). The Lean
statement retains the node's more explicit transpose and Hom naturality formulation.
There is no STATEMENT-DISPUTED finding.

## Second reading by Q29

This is the author's separate second pass with the DAG node and Lean file open;
the dispatcher's explicit instruction forbids starting another agent, so independent
review is left to the maintainer as the brief specifies.

The pass checked each geometric binder against the node: open inclusion, representable
etale p, reduced closed complement with exactly the complementary point image,
isomorphism over it, and an actual overlap pullback square. It checked the coefficient
and derived categories through `SmallModules` and `smallModuleEquivalence`, rather than
assuming the two dependency interfaces used identical presentations. Transport retains
the original adjunction and the multiplication-normalized etale restriction comparison.

The result was read with composition direction in mind. `homEquiv.symm (c.hom.app F)`
has source `p^*p_!F` and target F; the preceding shriek unit has source F, so their
composite being the identity, together with invertibility of the unit, exactly says
the transpose is its inverse. `c` is a natural isomorphism on the entire full support
subcategory. The canonical direct-image counit and U-vanishing are separate conjuncts.
The shifted Hom formula uses precomposition by c, the shriek Hom adjunction, and the
standard shift isomorphism in the correct direction. It includes all M and all integers.

The first compiler pass found an incorrectly broken dotted application, an opaque
abbreviation preventing shift-instance synthesis, and a malformed full-subcategory
type ascription. These were repaired by explicit `Adjunction.ofNatIsoRight`, the
underlying exact functor's shift comparison, and `ObjectProperty.FullSubcategory`.
These repairs change no mathematical statement. The second pass found no additional
hypothesis, missing conclusion, hollow definition, copied module category, or arbitrary
choice of comparison. Every declaration is listed in the lean record, and the node
statement and all its dependencies and proof fields are unchanged.

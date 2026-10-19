## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleBoundedBelowCoproducts` states
`AlgebraicGeometry.Scheme.proEtaleRingDerivedDirectImage_boundedBelow_coproducts`.
The only new declaration is a theorem with proof `sorry`. The node is unchanged outside
`lean`; no new definitions, dependency repairs or statement corrections are needed.

Hypothesis and clause correspondence:

- Schemes and the given morphism: `{T U : Scheme.{u}} (h : T ⟶ U)`.
- Quasi-compactness: `[QuasiCompact h]`, Mathlib's preimages-of-compact-opens condition,
  equivalent on schemes to the affine-open condition in the node.
- Quasi-separatedness: `[QuasiSeparated h]`, exactly quasi-compactness of the diagonal.
- Small pro-etale sites: `ProEt.topology U` and the same site's counterpart for `T`,
  with site object universe `u+1`, morphism universe `u`, and modules in `u+1`.
  The existing operations retain this distinction; no universe equality is imposed.
- Commutative Q-algebra coefficient sheaf: `R : Sheaf (ProEt.topology U)
  CommRingCat.{u+1}` and `[∀ V : U.ProEtᵒᵖ, Algebra ℚ (R.obj.obj V)]`.
  Rational algebra structures are unique: any unital ring homomorphism commutes with
  the rational scalars, since it preserves integers and their inverses. Thus this
  is precisely a sheaf of commutative Q-algebras, including the zero ring; it does
  not require extra compatibility data for restrictions.
- The source coefficient sheaf is literally
  `(proEtaleSheafInverseImage h CommRingCat.{u+1}).obj R`. No independently chosen
  source sheaf or map is assumed. `Iso.refl _` supplies its defining identification
  to the existing operations.
- Every small index set and every common integer bound: `(I : Type (u+1)) (N : ℤ)`;
  small means in the chosen module/derived universe, as specified by the size node.
- The arbitrary family: `K : I → DerivedCategory (proEtaleRingModules T ...)`.
  `proEtaleRingModules` unfolds to the recorded `ringedSiteModules`/`SheafOfModules`.
- The common cohomological bound: `hK : ∀ (i : I) (n : ℤ), n < N →
  IsZero ((DerivedCategory.homologyFunctor _ n).obj (K i))`.
- Ordinary uncompleted derived image: every occurrence is the recorded
  `proEtaleRingDerivedDirectImage`, the K-injective right derived functor on all modules.
- Source coproduct of the family: `∃ s : Cofan K, ∃ _ : IsColimit s`.
- Coproduct of direct images: `∃ t : Cofan (fun i ↦ (...).obj (K i)),
  ∃ ht : IsColimit t`.
- The map and conclusion: `IsIso (ht.desc (Cofan.mk (...obj s.pt)
  (fun i ↦ (...).map (s.inj i))))`. This is precisely the map induced by the
  coproduct inclusions, directed from the coproduct of images to the image of the
  coproduct. Its composites with `t.inj i` are the images of `s.inj i`, by the
  colimit factorization identity. There is no arbitrary map or existential choice
  of an isomorphism in place of the canonical morphism.

Universal coproduct cocones are used instead of assuming `HasCoproducts` on the
unbounded derived categories. Existence of both coproducts is part of the conclusion,
so the formulation is not conditional or vacuous. Coproduct objects, together with
inclusions, are uniquely isomorphic by their universal property; hence this statement
is equivalent to invertibility of the node's comparison for the stipulated sheafified
termwise direct sums. It does not select a different kind of direct sum or assert
that an arbitrary underived direct image preserves sums.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory` documents the original small site
  and coefficient size convention. It is imported transitively by the operations.
  Its constant-coefficient specialization is not used for variable `R`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, used
  through `proEtaleRingModules`; the underlying category is Mathlib `SheafOfModules`.
- `Sheaf.AlgebraicGeometry.ProEtaleOperations`:
  `AlgebraicGeometry.Scheme.proEtaleRingModules`,
  `proEtaleRingModules_hasDerivedCategory`, `proEtaleRingDerivedDirectImage`.
  The latter is the right derived functor of the sectionwise module direct image
  with the adjoint coefficient action. Its exact input signature and docstring
  were read, including the fixed coefficient identification.
- `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`:
  `CategoryTheory.moduleSheaves_colimits_forgetful` gives the stipulated sheafified
  sectionwise colimits and their inclusions, preserved by forgetting the action.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory.standard`; the operations use this same localization.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- Size and scheme conventions are metatheoretic convention records, with no
  declaration to import. Their applicable properties are the Mathlib classes above.

All currently recorded proof-dependency modules are imported (proof-only imports
without `public`), including the hypercover existence/model, K-injective comparison,
sheafification/local sections, derived module sums and cohomology detection modules.
The theorem docstring contains all seven proof steps, with the same affine-basis
qcqs check, finite-support argument, finite-diagonal exchange, exact sheafification,
and canonical-comparison identification as the DAG proof.

Edge cases checked: the empty index set is allowed and gives the map between zero
objects; the zero coefficient sheaf and zero complexes are allowed; the empty schemes
and identity morphisms are allowed; `N` is any integer including zero and negative
values; there is no properness, noetherianity, constructibility, torsion, completeness,
finite cohomological dimension or bounded-above assumption. The family may be infinite,
and its only uniformity requirement is the stated lower bound.

Searches performed:

- `msearch.py leanfinder`, query "Derived direct image on the proetale site commutes
  with coproducts of uniformly bounded below complexes": eight condensed/sheaf
  colimit hits, none the relative derived direct-image statement.
- `msearch.py loogle`, query `PreservesCoproducts, DerivedCategory`: zero hits;
  the service reports unknown identifier `PreservesCoproducts`.
- `msearch.py grep`, query `proetale|ProEtale` under `AlgebraicGeometry/Sites`:
  ten hits in Proetale/ElladicCohomology, none the required theorem.
- `msearch.py leansearch`, query "Derived direct image of proetale module sheaves
  preserves uniformly bounded below direct sums": service unavailable, Internal
  Server Error; other search methods succeeded.
- `rg` on the upstream WeilConjectures source and `lean/Sheaf` for the exact node
  id and pro-etale coproduct names: no existing statement. Broader searches for
  coproducts and bounded-below in the side pro-etale framework found finite-CD
  unbounded continuity discussions and coefficient-compatibility comments, not
  this variable-ring-sheaf, uniformly bounded-below theorem.
- Read Stacks `proetale.tex`, label
  `lemma-quasi-compact-quasi-separated-commutes-direct-sums` (Tag 09A3), its
  full proof and the following remark. The node's relative proof tests this
  absolute hypercover calculation over the specified affine basis.

Validation: the delivered file passed the prescribed `scompile.py ND
lem-weil-pbc-proetale-bounded-below-coproducts <file>` compilation, including
side overlay imports; no errors or warnings. No statements disputed.


## Second reading by ND

Independent second reader, 2026-10-15. Read the node and its seven proof steps,
Stacks proetale.tex Tag 09A3 and its preceding hypercover computation and following
remark, every statement-dependency record, and the actual dependency declarations.
There is no statement_change, no new definition node and no dependency module in
this delivery. No mathematical or Lean mismatch found; the Lean and node record
are retained verbatim. The following is my object/hypothesis/conclusion checklist.

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| Two arbitrary schemes and a specified morphism | `{T U : Scheme.{u}} (h : T ⟶ U)` | Exact. No base field or structure map is added. |
| Inverse images of affine opens quasi-compact | `[QuasiCompact h]` | Exact by Mathlib `quasiCompact_iff_forall_isAffineOpen`. |
| Quasi-compact diagonal | `[QuasiSeparated h]` | Exact: the class field is `QuasiCompact (pullback.diagonal h)`. |
| Small pro-etale sites, stipulated sizes | `ProEt.topology U`, and `T` in `proEtaleRingModules` | Exact. Mathlib uses weakly etale objects and fpqc covers; site objects are in `u+1`, arrows in `u`, modules in `u+1`. |
| A sheaf of commutative rational algebras | `R : Sheaf (ProEt.topology U) CommRingCat.{u+1}` and `[∀ V : U.ProEtᵒᵖ, Algebra ℚ (R.obj.obj V)]` | Exact. Rational scalars have a unique unital map into a ring when such a map exists; restriction homomorphisms therefore automatically respect them. |
| Source coefficients equal the inverse image | `(proEtaleSheafInverseImage h CommRingCat.{u+1}).obj R` | Exact. `Iso.refl _` identifies these very coefficients, without arbitrary replacement data. |
| All module sheaves and ordinary uncompleted derived categories | `DerivedCategory (proEtaleRingModules T ...)` and target counterpart | Exact. Opened `ProEtaleOperations`, `RingedSiteModules`, `ProEtaleDerivedCategory`, and Mathlib derived-category declarations; these are `SheafOfModules` and localization at quasi-isomorphisms. No constructible or completed subcategory is substituted. |
| Every small index set, then every integer bound, then every family | `(I : Type (u+1)) (N : ℤ) (K : I → DerivedCategory ...)` | Exact in the stipulated module universe; no finiteness or nonemptiness. |
| Common lower cohomological bound | `hK : ∀ (i : I) (n : ℤ), n < N → IsZero ((DerivedCategory.homologyFunctor _ n).obj (K i))` | Exact. Opened `homologyFunctor`: for `.up ℤ` this is the node's cohomology. |
| Coproduct of inputs and coproduct of derived images | `∃ s : Cofan K, ∃ _ : IsColimit s, ∃ t : Cofan (fun i ↦ ...obj (K i)), ∃ ht : IsColimit t` | Exact equivalent universal-property formulation. Both coproducts are asserted to exist, with no extra existence hypothesis. |
| Ordinary right derived direct image | Every occurrence of `proEtaleRingDerivedDirectImage h R ... (Iso.refl _)` | Exact. Its actual body is the right derived functor of sectionwise module pushforward with action through the adjoint ring unit. |
| Comparison induced by original coprojections, in the stated direction, is invertible | `IsIso (ht.desc (Cofan.mk (...obj s.pt) (fun i ↦ ...map (s.inj i))))` | Exact. `ht.fac` identifies every composite with `t.inj i` with the image of `s.inj i`; the comparison is canonical, not an existentially chosen map. |
| Sums are sheafified termwise sums | Universal coproduct cocones in these derived module categories | Exact up to the canonical coproduct isomorphism, preserving every inclusion. Opened `moduleSheaves_colimits_forgetful`: its colimit cocone has an isomorphism to sheafification of the sectionwise colimit and the stipulated coprojection formula. Exact sums in the Grothendieck module-sheaf categories give the corresponding derived coproduct. Changing universal cocones conjugates the comparison by these isomorphisms, so its invertibility is independent of their presentation. |

Source check: Tag 09A3 states the absolute qcqs bounded-below result and its proof
explicitly chooses a common bound N and termwise sums. The node requests the relative
rational-module consequence, not the additional homotopy-colimit assertion of that
absolute source. Testing over affine objects factoring through an affine base open
makes the source fibre product qcqs. The node's seven-step relative proof and the
module docstring agree step by step: bounded injective representatives, the affine
basis/qcqs calculation, affine weakly contractible hypercover, finite-support sections,
finite diagonals, exact sheafification, then identification of the actual comparison.
The source imposes no global qcqs assumption on T or U in this relative formulation.
All recorded proof-dependency modules and Mathlib-match files are imported directly
or transitively; in particular QuasiSeparated imports the QuasiCompact results used
for qcqs over an affine base. The generic DerivedModuleDirectSums input is used for
complexes of sections (modules), not incorrectly applied to module sheaves.

Edge cases: `I` may be empty, yielding the comparison between zero objects. Zero
complexes, the zero coefficient ring/sheaf, and empty schemes remain allowed; no
Nontrivial instance is present. A rational-algebra coefficient ring cannot have
positive characteristic unless it is the zero ring, exactly as in the node, while
the underlying schemes have no characteristic restriction. N may be zero or negative;
there is no bounded-above hypothesis. Identities and nonproper qcqs maps are included.
Universe u is explicitly bound; site object and morphism universes remain distinct;
I occupies the chosen larger universe, with smaller index types included by lifting.
No additional instance on the derived functor or its preservation properties is assumed.

Independent searches (with different phrases from the first reader):

- `msearch.py leanfinder`: "Right derived pushforward preserves direct sums with a
  common cohomological lower bound on quasi compact quasi separated pro etale sites".
  Eight results, including ordinary module-sheaf pushforward and sheaf functor
  congruence declarations; none gives this derived preservation statement.
- `msearch.py loogle`: `"coproduct", "Derived"`: zero hits.
- `msearch.py leansearch`: "A quasi compact quasi separated map on pro etale sites has
  right derived direct image preserving uniformly bounded below coproducts of module
  sheaves": service unavailable (Internal Server Error); no negative verdict inferred.
- Independent `rg` for `(coproduct|direct.sum).*(bounded|pro.et|derived)` and the
  reverse order in Mathlib algebraic geometry and derived categories, upstream
  WeilConjectures, side WeilConjectures (the exact 51-module framework) and lean/Sheaf.
  Opened the relevant `ExceptionalAdjoint` and `ModuleObject/Colimit/Compatibility`
  hits: the former assumes uniform finite cohomological dimension for unbounded
  preservation, the latter states proper coefficient-extension compatibility.
  Neither is this arbitrary rational ring-sheaf qcqs common-lower-bound statement.
  The other hits concern ordinary scheme modules, tensor, or existence of coproducts.

H5/H6/H8/H9: the only new declaration is the named theorem, with proof `sorry`;
there are no new definitions, private notions, local instances or local notation.
Source and blueprint tags are present in both docstrings; the proof has all seven
steps. Every binder and universe is explicit. Checked all lines are at most 100
characters and `lean.statement` equals the file signature verbatim.

Changes: appended this independent second-reading audit only; no statement,
dependency, import or Lean-body repair was necessary.

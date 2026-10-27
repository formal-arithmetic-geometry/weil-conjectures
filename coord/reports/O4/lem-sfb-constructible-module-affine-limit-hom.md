## Worker report

States `AlgebraicGeometry.Scheme.constructible_module_affineLimit_hom` in
`Sheaf.AlgebraicGeometry.ConstructibleModuleAffineLimitHom`. Its only theorem proof
is `sorry`; the module introduces no definitions, instances, or additional hypotheses.
The item node changes only in `lean`.

Source read: `literature/stacks-project/etale-cohomology.tex`, lines 12551–12635,
Tag 09YU, `lemma-category-is-colimit`: the Faithful and Fully faithful paragraphs
and the reduction of part (3) to the module-presentation argument. The source assumes
a Noetherian coefficient ring, which every finite commutative ring satisfies. It does
not assume Noetherian schemes. The six-step docstring preserves the node's expanded
presentation/sections proof, including empty families and the final epimorphism
cancellation. This is Hom descent and eventual equality, without any assertion about
essential surjectivity on objects.

Hypothesis and clause correspondence:

- A nonempty directed set I is `{I : Type u} [Preorder I]
  [IsDirected I (· ≤ ·)] [Nonempty I]`. This follows the recorded scheme-limit
  dependency's universe convention; the index lives in the same universe as schemes.
- The inverse system is `D : Iᵒᵖ ⥤ Scheme.{u}`. A transition from j to i, for
  `h : i ≤ j`, is exactly `D.map (homOfLE h).op`.
- Affine transitions are `[∀ {j k : Iᵒᵖ} (f : j ⟶ k), IsAffineHom (D.map f)]`.
- Quasi-compact and quasi-separated stages are respectively
  `[∀ j : Iᵒᵖ, CompactSpace (D.obj j)]` and
  `[∀ j : Iᵒᵖ, QuasiSeparatedSpace (D.obj j)]`. Neither is replaced by a
  Noetherian, affine, or separated condition.
- The specified limit and its projections are `(c : Cone D) (hc : IsLimit c)`;
  `X` is `c.pt`, and `p_i` is `c.π.app (op i)`. No special chosen limit is imposed.
- The coefficient hypothesis is `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
  Modules and small-etale sheaves use the project's coefficient universe u+1.
- The fixed stage is `(i : I)`. The two stage objects are
  `P Q : Sheaf (D.obj (op i)).smallEtaleTopology (ModuleCat.{u + 1} Λ)`.
  Their constructibility hypotheses are `hP` and `hQ`, each using the recorded
  `IsConstructibleEtaleModuleSheaf` definition. That definition uses finite module
  values on a scheme stratification with constructible locally closed strata.
- Module inverse image is the existing `Etale.upperStar (ModuleCat.{u+1} Λ) f`.
  Its objects are the module sheaf inverse images over the fixed constant coefficient
  ring, and its `.map` acts on linear natural transformations. All arrows in both
  clauses lie in this category; no underlying-set morphism is substituted.
- Clause (1) is the first conjunct, universally quantified over
  `a : p_i^* P ⟶ p_i^* Q`. It supplies `∃ (j : I) (h : i ≤ j) (aⱼ : …)`;
  the domain and codomain of `aⱼ` are precisely the pullbacks of P and Q by the
  transition `D.map (homOfLE h).op`.
- The displayed equality is the requested comparison-conjugated inverse image.
  `Etale.upperStarComp … p_j t_ji p_i (c.w …).symm` has direction
  `p_i^* ≅ t_ji^* ⋙ p_j^*`. Its `.hom.app P` therefore goes from the direct
  limit pullback to the iterated pullback. This is followed by `p_j^*.map aⱼ`
  and `.inv.app Q`, and the composite is asserted equal to a. The equality passed
  to the comparison is the cone identity, not an additional assumption or a
  newly chosen comparison.
- Clause (2) is the second conjunct: `∀ a b : P ⟶ Q`, equality of
  `p_i^*.map a` and `p_i^*.map b` implies `∃ (j : I) (h : i ≤ j)` where
  `t_ji^*.map a = t_ji^*.map b`. Both pullbacks share source and target, so no
  conjugation is needed in this clause.
- There is no Noetherian hypothesis on the stages, their limit, or the morphisms.

Dependency declarations read and used (the convention node itself defines nothing):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `AlgebraicGeometry.IsAffineHom`.
- `WeilConjectures.AlgebraicGeometry.LimitAffineTransition`:
  `AlgebraicGeometry.exists_limit_affine_transition`; its diagram, cone and size
  conventions are used with an arbitrary specified limit cone.
- `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`:
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`.
  Read the actual current definition and the underlying `Scheme.Stratification`
  in `WeilConjectures.ConstructibleSheaf.Defs`; its strata are constructible.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`, and
  `Scheme.Etale` in `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
  This is the general ringed-site module category; the statement uses the prescribed
  equivalent constant-coefficient `Sheaf (ModuleCat Λ)` encoding rather than an
  independent definition of that category.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.upperStar`, `upperStarLowerStarAdjunction`,
  `lowerStarComp` and `upperStarComp`. The statement uses the actual composition
  comparison, whose full signature and left-adjoint construction were read.
- `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`:
  `CategoryTheory.ConstantLeftModuleInverseImageData` and
  `constant_left_module_inverse_image`, including their module, underlying-abelian,
  unit and composition comparisons. Imported as the node's fixed-coefficient
  interpretation dependency; no arbitrary inverse-image functor is assumed here.

The stated proof dependencies are imported non-publicly:
`WeilConjectures.AlgebraicGeometry.ConstructibleModuleFinitePresentation`
(`Scheme.exists_affine_free_etale_presentation`),
`WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
(`AlgebraicGeometry.etaleInverseImageModulesExact`),
`Sheaf.Paper.InverseImageFreeEtaleModule`
(`AlgebraicGeometry.inverseImageFreeEtaleModule`), and
`WeilConjectures.AlgebraicGeometry.LimitPullbackSectionsColimit`
(`AlgebraicGeometry.Etale.limit_pullback_sections_colimit`).
The composition dependency is already a public statement import. The elementwise
filtered-colimit node is a Mathlib leaf, with
`CategoryTheory.Limits.Concrete.isColimit_exists_rep`,
`CategoryTheory.Limits.Concrete.isColimit_rep_eq_iff_exists` in
`Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic`, and
`ModuleCat.FilteredColimits.forget_preservesFilteredColimits` in
`Mathlib.Algebra.Category.ModuleCat.FilteredColimits`; both modules are imported.

Edge cases checked before writing:

- A singleton index and identity transitions are permitted. The canonical
  `upperStarComp` handles these without definitional equality assumptions.
- The empty index is excluded exactly by the node's nonempty hypothesis; the index
  need not have a least element, and the witness j may equal i.
- Zero modules, the zero coefficient ring, and empty schemes are permitted. Maps
  between the relevant zero objects are unique, with j=i an allowed stage.
- A nonempty inverse system can have empty limit without any stage being empty;
  neither a nonempty-scheme nor a surjective-transition hypothesis is introduced.
  Eventual equality remains the constructible continuity assertion in that case.
- Empty generating or relation families in the source proof require no extra
  nonemptiness assumption; the docstring explicitly treats them.
- Arbitrary non-Noetherian qcqs schemes and arbitrary affine transitions remain in
  scope, as do all finite ring characteristics.

Searches actually run:

- `msearch.py ... leanfinder`, query “Morphisms of constructible etale module sheaves
  descend along affine inverse limits and equality is detected at a finite stage”:
  eight hits, about affine-limit descent of scheme morphisms and structure-ring
  sections (`exists_hom_comp_eq_comp_of_locallyOfFiniteType`,
  `exists_app_map_eq_map_of_isLimit`, etc.); none states this module-sheaf result.
- `msearch.py ... loogle`, query `IsConstructibleEtaleModuleSheaf, Etale.upperStar`:
  zero hits; service reports unknown identifier `IsConstructibleEtaleModuleSheaf`
  (the project declaration is not in its Mathlib index).
- `msearch.py ... leansearch`, query “Morphisms between constructible module sheaves
  on an inverse limit of schemes descend to a finite stage”: eight hits about
  module-sheaf limits and morphism constructors; no matching theorem.
- `msearch.py ... grep`, query `constructible.*limit|limit.*constructible`,
  Mathlib subdirectory `AlgebraicGeometry`: zero hits.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for the node id and
  `constructible.*affine.*[Hh]om|constructible.*[Hh]om.*limit`: only mentions in
  other proofs and unrelated condensed-sheaf or colimit-factorization results.
  In particular, `FiniteLocalSystemAffineLimitDescent` cites this node in its
  proof docstring but does not state it.
- Exact-name search for `constructible_module_affineLimit_hom` and
  `constructible_module_affine_limit_hom` in both Lean trees and
  `dag/lean_names_upstream.json`: no existing declaration.

Validation: `scompile.py O4 lem-sfb-constructible-module-affine-limit-hom` compiled
both the sandbox and library-path forms successfully (7.1 s and 4.4 s). The source
sets `autoImplicit false`, binds its universe explicitly, has maximum line width
86, and has no `let`, local notation, private helper, or local instance. The
single postponed theorem is matched to this DAG node and carries all six proof
steps in its docstring. No statement correction, missing notion, or unusable
dependency was found.

## Second reading by O4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

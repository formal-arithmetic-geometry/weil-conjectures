## Worker report

The item is stated by
`AlgebraicGeometry.isProper_and_universal_etale_descent_of_isProperHypercover` in
`Sheaf.AlgebraicGeometry.ProperHypercoverEtaleDescent`; its proof is `sorry`.
I read Stacks `spaces-simplicial.tex`, `section-proper-hypercovering-spaces`
(including its explicit scheme specialization and its matching-map conventions),
Tag 0DHL and its proof, and Tags 09WC, 0D70 and 0D99 for the augmentation.
The torsion coefficient restriction and coefficient forgetting follow the node's
nine proof steps. There is no statement correction, disputed statement or dependency repair.

The previous sandbox had no node record/report. Its initial dry run failed for that
reason. Its old helpers did not encode actual matching objects or a covering topology,
and its theorem allowed an unconstrained adjunction and omitted conclusions. They
were replaced with the now-landed proper-hypercover and total-site definitions plus
an explicit canonical augmentation construction. Only the sandbox was edited.

Every hypothesis and clause corresponds as follows:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Scheme X | `{X : Scheme.{u}}` |
| Augmented simplicial scheme | `U : SimplicialObject (Over X)`. Its objects carry the augmentation maps, and its arrows commute with them. Forgetting gives `U ⋙ Over.forget X` with a natural map to the constant X diagram. This equivalent encoding retains all faces and degeneracies. |
| Matching limits of compatible proper faces over X | The imported `IsProperHypercover U` uses `U.properFaceDiagram n`, a cone and its `IsLimit` proof, and the canonical arrow `hc.lift (properHypercoverBoundaryCone U n)`. There is no new private matching diagram or arbitrary matching map. |
| M0=X, M1=U0 times_X U0 | Limits are taken in `Over X`. The degree-zero diagram is empty, with terminal object X/X; degree one has the two vertices. These are consequences of the actual proper-face diagram, not extra hypotheses. |
| Every matching arrow proper surjective | `hU : IsProperHypercover U`, with both predicates in every degree |
| Every term augmentation proper | First conjunct: `∀ n : ℕ, IsProper (U.obj (op (SimplexCategory.mk n))).hom`. This is independent of coefficients. |
| Any base change has proper-surjective matching maps | Second conjunct: `∀ (Y : Scheme.{u}) (f : Y ⟶ X), IsProperHypercover (U ⋙ Over.pullback f)`. Ordinary slice pullback gives U_n times_X Y with its canonical operators. No property of f is assumed. |
| Commutative ring annihilated by m>=1 | Third conjunct quantifies all `Λ : Type (u + 1)`, `[CommRing Λ]`, `m : ℕ`, with `1 ≤ m` and `(m : Λ) = 0`. Vanishing of m times 1 is equivalent to annihilation of the ring: multiply by x, and conversely evaluate at 1. |
| Small etale topoi, constant Lambda-module coefficients | Base `Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)`; total `Sheaf (totalEtaleTopology (U ⋙ Over.forget X)) (ModuleCat.{u + 1} Λ)`. This is the project's fixed-coefficient encoding, equivalent to modules over the sheafification of the constant ring presheaf. It does not require the module sheaf itself to be constant. |
| Total sheaves are families with compatible transitions | The existing `TotalEtaleSite` is the comma full subcategory of etale total objects; its arrows are the specified simplicial operators and commuting scheme maps, equivalently maps to the pullback. Functoriality imposes transition identities/compositions; the generated component coverings impose the component sheaf conditions. |
| Actual augmentation and ordinary unit | `totalEtaleAugmentationAdjunction U Λ` from the added definition node, whose direct image has explicit compatible-section data via right Kan extension. No free geometric morphism, arbitrary unit map, or stronger hypothesis occurs. |
| a* has components a_n* | `totalEtaleAugmentationInverse_component` in the helper module states the natural comparison to the recorded `Etale.upperStar` along the nth augmentation. The direct image includes compatibility under every total-site arrow, so its adjoint is the family with the canonical composition transitions of 0D70. |
| All bounded-below complexes on X | `∀ L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)), ...`; the imported Mathlib bounded-below full subcategory of the recorded derived category |
| L -> Ra_*a*L is an isomorphism | `IsIso ((totalEtaleAugmentationAdjunction U Λ).derivedPlus.unit.app L)`; this is the actual derived unit, not merely an isomorphism between its objects. |
| Ordinary adjunction-unit normalization | `Adjunction.derivedPlus` is characterized on complexes by its `derivedPlus_unit_app_fac`, read in the upstream source. It derives the specified ordinary augmentation adjunction. |
| Every base change, every complex there | Final conjunct quantifies all Y, f and `L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))` and states the same derived-unit assertion for `U ⋙ Over.pullback f`. L need not be pulled back from X. |

Both modules use `set_option autoImplicit false`. All variables and universes are
bound. Sites retain object universe u+1 and morphism universe u; sections and derived
morphisms use the common containing universe u+1. Existing Grothendieck/sheaf instances
supply abelianness, injectives and derived categories: these are not extra hypotheses.
The exact augmentation interface supplies its functor properties.

Dependency declarations used (records, source signatures and docstrings read):

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`,
  `Scheme.Hom`.
- `def-weil-pbc-etale-site`: `Mathlib.AlgebraicGeometry.Sites.Etale`,
  `Scheme.smallEtaleTopology`, `Scheme.ofArrows_mem_smallEtaleTopology_iff`;
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`, `Scheme.Etale`, `Scheme.Etale.forget`.
- `def-weil-sheaf-of-modules-category`: `Sheaf.CategoryTheory.RingedSiteModules`,
  `CategoryTheory.ringedSiteModules`, transparently Mathlib `SheafOfModules`.
  The allowed fixed-coefficient `Sheaf J (ModuleCat Λ)` encoding above is equivalent
  to this variable-ring-sheaf notion specialized to the constant coefficient sheaf.
  No private module-category structure is defined.
- `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic`,
  `DerivedCategory`, `HasDerivedCategory`; bounded-below objects use its `Plus` subcategory.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper` (separated, universally closed, locally finite type;
  the implied quasi-compactness makes this finite type).
- Added landed dependency `def-trf-proper-hypercover`:
  `Sheaf.AlgebraicGeometry.ProperHypercover`, `IsProperHypercover`,
  `properHypercoverBoundaryCone` and their canonical proper-face diagram.
- Added landed dependency `def-trf-total-simplicial-etale-site`:
  `Sheaf.AlgebraicGeometry.TotalSimplicialEtaleSite`, `TotalEtaleSite`,
  `totalEtaleTopology`, `totalEtaleRestriction`, `TotalEtaleAugmentation`.
- Added definition dependency `def-trf-total-etale-augmentation-adjunction`:
  `Sheaf.AlgebraicGeometry.TotalEtaleAugmentationAdjunction`,
  `totalEtaleAugmentationAdjunction` and all its recorded construction declarations.
- Normalized derived adjunction:
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction`,
  `CategoryTheory.Adjunction.derivedPlus`, with its ordinary-unit characterization.

Recorded proof-dependency modules are imported without `public` where not already
public statement dependencies: `PhSchemeSite`, `SiteHypercoverDerivedDescent`,
`Sites.GeometricMorphism`, `RingedSiteModulesGrothendieckOfUniverses`,
`ConstantLeftModuleInverseImage`, upstream `ModuleSheavesColimitsForgetful`.
The remaining ph/etale square, comparison, component, normalization and restriction-counit
nodes have no recorded module. Their exact roles remain in the nine-step proof docstring.
Mathlib geometric leaves and composition adjunctions are already imported by the scheme,
proper, pullback and adjunction modules.

Edge cases checked:

- Degree zero is the empty matching diagram in the slice, degree one is the fibre
  product, and all higher compatibility arrows remain present.
- Constant identity hypercovers and f=id are allowed, with the ordinary unit.
  The original unit is also stated separately from base change.
- Empty schemes/components and empty etale coverings are allowed; there is no
  nonemptiness or finiteness hypothesis. The empty-cover sheaf condition is retained.
- m=1 allows the zero ring; m=0 is excluded exactly by 1<=m. Zero complexes,
  nonconstructible sheaves and complexes unbounded above are included.
- Base change can be empty, nonetale, nonproper or identity; the complex on Y is arbitrary.
  No field, Noetherian, separated-base or dimension assumption is introduced.
- The augmentation helper requires no properness, hypercover or torsion assumption,
  so it does not depend circularly on the descent theorem.

Searches actually made:

1. `msearch.py` LeanFinder: `Proper hypercover of schemes gives universal cohomological
   descent for bounded below torsion etale sheaves`: eight quasi-compact cover,
   component-etale and 0/1-hypercover gluing hits; no exact theorem.
2. Loogle `"Hypercover"`: twelve 0/1-hypercover declarations; no derived proper descent.
3. Mathlib grep `properHypercover|cohomologicalDescent|totalEtale`: zero hits.
4. LeanSearch `The augmentation of a simplicial scheme induces an adjunction between
   the small etale sheaves on the base and the total site`: generic sheaf adjunctions
   and augmented simplicial objects only.
5. LeanFinder `direct image of a simplicial etale site augmentation is compatible
   sections a right Kan extension`: simplicial coskeleton/Kan-extension results only.
6. Mathlib grep `totalEtaleAugmentation|TotalEtaleAugmentation|total.*[Aa]djunction`:
   zero hits. Literal results of the three augmentation searches are in the new node.
7. Direct `rg` of upstream `WeilConjectures` and project `lean/Sheaf` for the matching
   and total-site notions found the two now-landed definitions, which are reused.
   No augmentation adjunction or item theorem was found. Direct upstream item-id search
   and proposed-name search in `dag/lean_names_upstream.json` had no matches.
8. Direct `rg` of `dag/nodes` for augmentation adjunctions; read the total-etale-site
   and `lem-trf-slice-site-simplicial-augmentation` nodes. The latter gives full localized
   sites of a single site, not the varying small-etale subcategories. It does not define
   the required small-etale augmentation adjunction. `tools/blueprint_refs.py search
   'total etale augmentation'` returned zero blueprint nodes; `ancestor` returned
   `lem-trf-local-term-locality`, retained in the new node's provenance.

Validation: both final files compiled in dependency order with `scompile.py`, separately
in sandbox and library mode, without errors or warnings (about four seconds per file).
There was no direct compiler or global build. Lines are at most 100 characters.
The required dry run and delivery use `deliver2.py`.

## New nodes

`def-trf-total-etale-augmentation-adjunction` defines the actual augmentation adjunction
on constant module coefficients, following Stacks 0D70 and its proof, 09WC for the
existing site, and 0D99 for compatibility. `totalEtaleToOver` has explicit object/arrow
data. Its right Kan extension, restricted to etale objects, fixes the direct image on
sections and every compatibility before any adjoint is chosen. The left adjoint is
determined up to the unique adjunction-compatible isomorphism, as allowed by AGENTS.md
section 5 for universal-property constructions. Its ordinary unit is that of this very
adjunction. It is not an unconstrained functor or map, a hollow structure or a choice
of unrelated component isomorphisms.

Four named definition obligations have `sorry` proofs, source and natural-language proofs
in their docstrings, and are listed in this node's `lean.declarations`:
`totalEtaleAugmentationDirect_isSheaf`, `totalEtaleAugmentationDirect_isRightAdjoint`,
`totalEtaleAugmentationInverse_preservesFiniteLimits`, and
`totalEtaleAugmentationInverse_component`. They state precisely the construction
properties in the new node. No definition's data is `sorry`. Other instances forward
these obligations or use existing adjunction/additivity theorems.

The new node preserves the literal three-kind search outputs and direct DAG/upstream/project
and blueprint searches. Generic slice-site augmentation is a different construction.
The existing total-etale-site node supplies the site and augmentation natural-transformation
data, not this adjunction. Both existing definitions are reused; no duplicate definition
or dependency cycle is introduced. The item gains exactly the two landed definition
nodes and this new node as statement dependencies.

## Second reading by NC

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

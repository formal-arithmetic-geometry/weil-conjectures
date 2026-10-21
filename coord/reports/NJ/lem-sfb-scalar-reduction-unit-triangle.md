## Worker report

Item: `lem-sfb-scalar-reduction-unit-triangle`. The delivery states the complete node as
`SheafOfModules.ScalarAdjunctionNormalization.scalarReductionUnitTriangle`, with the
clauses collected in the owning helper structure `ScalarReductionUnitTriangle`.
The only postponed theorem is this named theorem; its proof is `sorry`, and its docstring
contains the nine-step DAG proof and identifies every non-elementary input. There are
no data definitions containing `sorry`, no new independent definition nodes, and no
statement changes.

Sources read: the complete item and each statement dependency; blueprint
`main-20261015/blueprint/sec-six-functors-basics/sk-lem-geo-cartier/sk-lem-geo-cartier.proof.md`,
especially paragraph 4; Stacks `sites-modules.tex`, labels
`lemma-constant-exact` (093J), `lemma-adjoint-pullback-pushforward-modules` (03D7),
`definition-flat` item (3) (03ER); `sites-cohomology.tex`,
`lemma-derived-base-change` (06YY); and `derived.tex`,
`lemma-derived-canonical-delta-functor` (0152). The latter specifies the boundary
as minus the cone projection after the inverse comparison. Mathlib's
`DerivedCategory.triangleOfSESδ` is the recorded implementation of that convention.

Hypotheses and clauses, in statement order:

- The site is `C : Type u`, `[Category.{v} C]`, `J : GrothendieckTopology C`;
  `[HasTerminal C]` occurs on the theorem. `u` and `v` are independent.
  `[EssentiallySmall.{r} C]` and the explicit sheafification/sheaf-composition instances
  are the existing ringed-site and K-flat infrastructure at coefficient size `r`.
  They are size/existence data for a small site, rather than extra geometric assumptions.
  Both derived localization sizes `wZ` and `wR` remain independent. All variables and
  universes are explicitly bound; `autoImplicit` is false.
- `n : ℕ` and `hn : 1 ≤ n` give exactly the positive modulus. The constant integer ring,
  constant residue ring, actual quotient, module categories and restriction are the
  recorded normalization dependency's `integers`, `residues`, `quotient`,
  `IntegerModules`, `ResidueModules` and `restriction`; none is defined again.
- `M : DerivedChangeOfRingsCochainModel (quotient J n)` specifies ordinary tensor `M.E`
  on objects and maps and its universal derived functor `M.T`, with counit `M.ε`.
  This is a model of the functors named in the statement, not an arbitrary map or an
  extra flatness assumption. `N : Normalization J n M` supplies exactly the normalized
  ordinary and derived adjunctions named in the node. The dependency already states
  the existence of N for every M and positive n. The result holds for every such N.
- `coefficient_zero` and `coefficient_exact` state the short exact sequence with first
  map `n • 𝟙 (integerUnit J)` and the actual `coefficientQuotient J n` as last map.
  `ShortComplex.ShortExact` includes both endpoint conditions.
- `residue_killed` states annihilation of all sections of every residue module.
  `torsion_lift` gives an actual residue-module sheaf with its underlying abelian
  sheaf isomorphic to each given n-killed abelian sheaf. `additive_maps` is full
  faithfulness of the underlying-abelian-sheaf functor, giving every additive map its
  unique residue-linear lift. Together these express existence and uniqueness of
  residue structure on a fixed sheaf: transport the lift along its underlying
  isomorphism; the unique lift of the identity between two structures forces the
  scalar actions to agree. `integer_action` explicitly normalizes the action of
  every constant residue section by any integer representative `z : ℤ`.
- `restriction_fullyFaithful` separately states full faithfulness of the restriction
  into integer modules, as the node explicitly requests.
- `quotient_comparison` gives a quotient functor `Q`, a natural transformation `π`
  from the identity to `Q ⋙ restriction`, and for each A the zero composite and
  `Nonempty (IsColimit (CokernelCofork.ofπ ...))`. These universal properties specify
  the sheaf cokernel of n, including its unique residue action, up to its canonical
  isomorphism; they do not mean the sectionwise quotient presheaf. The natural
  isomorphism `e : M.E ≅ Q` is in residue modules. Its unit equation is the quotient
  normalization. Its displayed value on sheafified pure tensors is `a • π(x)` for
  every residue section a, hence for `a = k mod n` it is exactly `k x mod nA`.
  The scalar-first tensor order is that of the existing extension-of-scalars API.
- `all_ordinary_units` quantifies over every functor E with an adjunction
  `a : E ⊣ restriction J n`, without an extra additivity hypothesis on E, and says
  its actual unit on every A is a cokernel of multiplication by n.
- `flat_terms_mono` quantifies over every integer-indexed cochain complex P with
  `∀ i, IsFlatOnSite (R := integers J) (P.X i)` and concludes monicity in every degree.
  There is no boundedness, acyclicity, K-flatness, or degree-zero-cohomology condition
  on this clause.
- `resolution_triangle` quantifies over A, P and the supplied
  `p : P ⟶ (CochainComplex.singleFunctor _ 0).obj A`, assumes exactly
  `IsKFlatResolutionIndependentCoefficients p` and flatness of each term.
  Its actual residue complex is `(M.E.mapHomologicalComplex (.up ℤ)).obj P`.
  Its integral quotient map is the termwise ordinary adjunction unit; the field
  gives the zero composite and its `ShortExact` sequence of complexes, together
  with the cokernel universal property in each degree. Short exactness here is
  equivalently degreewise short exactness in the abelian category of module sheaves.
- The same field supplies `c : M.T.obj (Q.obj A[0]) ≅ Q.obj E(P)` with equation
  `M.T.map (DerivedCategory.Q.map p) ≫ c.hom = M.ε.app P`. Since p is a
  quasi-isomorphism this specifies the canonical resolution comparison, rather
  than a freely chosen isomorphism with the same cohomology.
- `δ` is explicitly `Res(c.hom)`, then the canonical restriction/localization
  identification, then `DerivedCategory.triangleOfSESδ hS`, then `Q(p)[1]`.
  This is exactly the node's `p[1] ∂_P Res(c_A)` in Lean's composition order.
  The triangle with first map n and second map `N.derived.unit` is distinguished.
  The supplied triangle isomorphism has first and second components `Q(p)` and
  third component the canonical localization/restriction comparison followed by
  `Res(c.inv)`, so it is precisely transport by `(p,p,Res(c_A)⁻¹)`.
- `presentations` quantifies over every short exact extension S, epic n on `S.X₁`
  and monic n on `S.X₃`, and gives an actual presentation D with `D.S = S`.
  The recorded presentation has residue H and Q, maps i and p, both zero
  composites, and both required short exact sequences. Its endpoint and middle
  exactness force these objects to be the residue kernel and quotient.

Dependency declarations and modules read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`: `Precoverage.IsSiteForCoverings`, with
  Mathlib `GrothendieckTopology`/`Sheaf` for the associated topology and sheaves.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`, the transparent
  abbreviation of Mathlib `SheafOfModules` with its existing abelian structure.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, and `DerivedCategory.Q`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: the existing
  sheafified tensor infrastructure; the extension is the recorded model's `M.E`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `DerivedChangeOfRingsCochainModel`, `E`, `obj_eq`, `T`, `ε` and `computes`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`: `restrictScalars`.
- `Mathlib.Algebra.Homology.ExactSequence` and its short-complex imports:
  `ShortComplex.ShortExact` and the cokernel universal property.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `IsFlatOnSite`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `IsKFlatResolutionIndependentCoefficients` and `IsKFlatIndependentCoefficients`.
- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`: `triangleOfSESδ`,
  `triangleOfSES`, and the distinguished-triangle convention.
- `Sheaf.Algebra.Homology.ScalarAdjunctionUnitCoefficientNormalization`:
  all constant-coefficient/module/restriction helpers, `Normalization`,
  `Normalization.ordinary`, `Normalization.derived`, and `Normalization.kflat_unit`.
- `Sheaf.Paper.DivisibleExtensionDerivedReduction`:
  `DivisibleReduction.Presentation`. In the current source (also verified with
  `scompile.py --source`), this is literally the abbreviation specializing the
  recorded `CategoryTheory.ScalarReductionPresentation` to these coefficient sheaves.
  The last green build still exposes the identical earlier specialized structure,
  while not yet exposing the newly extracted generic name. I used the surviving
  public specialized name, checking its full compiled signature and fields with
  scompile. This works against both versions and introduces no replacement notion.
- `Sheaf.CategoryTheory.TorsionSheafConstantModule`:
  `existsUnique_constantZModSheafModuleStructure`, `torsionSheaf_hom_linear`,
  `constantZModModuleSheaf_nsmul`, as proof inputs. These are not copied.
- Mathlib `Pretriangulated`/`IsTriangulated`, `distTriang`, and `Triangle` give the
  recorded triangulated-category dependency.
- Proof-only imports include `Mathlib.CategoryTheory.Sites.Sheafification` for exact
  sheafification and `Mathlib.CategoryTheory.Adjunction.Mates` for the unit-compatible
  conjugate isomorphism. Other recorded proof inputs arrive through the public
  imports of the interfaces above. The divisible-reduction module already contains
  this presentation; it must not gain a reverse import of this new theorem, which
  would create an import cycle.

Edge cases checked before writing and rechecked on the final statement:

- n = 1: the residue ring is the zero ring, all residue modules vanish, ordinary
  reduction is the cokernel of the identity, and the triangle is A → A → 0.
  No nontrivial-ring assumption is imposed.
- Zero A or the zero resolution: all displayed quotient and boundary maps are zero,
  and the stipulated triangles and cokernel properties still have their usual meaning.
- A = Z/n is generally not flat. It is covered by a flat-term K-flat resolution;
  the derived tensor may have nonzero cohomology in degree -1. No clause identifies
  derived reduction with an ordinary degree-zero quotient of A.
- Arbitrarily unbounded flat-term complexes are included in `flat_terms_mono`;
  their cohomology is unrestricted. There is no claim that an arbitrary complex is
  K-flat merely because all its terms are flat.
- The extension clause allows every short exact S under exactly the two stated
  multiplication endpoint hypotheses. The middle sheaf is unrestricted.
- Neither coefficient flatness of Z/n over Z nor equality of the site object,
  site morphism, or the two localization universes is imposed.

Searches actually run:

- `msearch.py` leanfinder: "scalar reduction of module sheaves modulo n quotient
  adjunction unit multiplication by n distinguished triangle". Eight results,
  including `ModuleCat.smulShortComplex_g` and generic module/sheafification results;
  no exact public declaration of this multi-clause node.
- `msearch.py` loogle: "SheafOfModules.restrictScalars, CategoryTheory.Limits.IsColimit".
  Successful query, zero hits.
- `msearch.py` grep: "scalarReduction|scalar_reduction|smulShortComplex". Thirteen
  Mathlib hits concerning `ModuleCat.smulShortComplex`; none concerns sheaves or
  the normalized derived-unit triangle of this node.
- `msearch.py` leansearch: "sheaf extension scalars modulo n is cokernel of
  multiplication by n adjunction unit". Eight generic scalar-change, sheafification
  and unit hits; none states the full result.
- `rg` of both `lean/WeilConjectures` and `lean/Sheaf` for scalar reduction, unit
  cokernels and multiplication triangles found the private supporting lemmas in
  `DivisibleExtensionDerivedReduction.lean`, plus unrelated adic-reduction interfaces.
  Their signatures were read. The related public `presentation_exists` covers the
  last clause only. No public declaration states all the item's assertions.
- `grep -rn 'lem-sfb-scalar-reduction-unit-triangle' lean/WeilConjectures`: no hit.
- `rg` of both libraries and `dag/lean_names_upstream.json` for
  `scalarReductionUnitTriangle|ScalarReductionUnitTriangle|ScalarReductionQuotient`:
  no pre-existing declaration with the proposed names.

Validation: `scompile.py NJ lem-sfb-scalar-reduction-unit-triangle <module>` passed
both the isolated sandbox compile (29.5 s) and the real module-name compile (28.2 s),
with no errors or warnings. Initial elaboration issues were repaired: `IsColimit`
is data and is therefore wrapped in `Nonempty` inside propositions; the module
universe of `toSheaf` is now explicitly `r`; and the presentation uses the public
specialized name that exists in the last green build. Temporary `#check`/`#print`
files were removed. No node faults or statement disputes remain.

## Second reading by NJ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

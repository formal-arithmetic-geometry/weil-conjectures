## Worker report

The module `Sheaf.Algebra.Homology.RegularQuotientConeAugmentation` states
`SheafOfModules.RegularQuotientCone.nonempty_augmentation`. Its sole postponed theorem
has proof `sorry`. The auxiliary `Augmentation` structure spells out the simultaneous
conclusions; it has no default values or postponed data. The remaining declarations
are transparent aliases or explicit constructions of the scalar action, the induced
ring-module map, the diagonal cone functor, and its unshifted inclusion. The proofs
inside these definitions are only the structural linearity, naturality and functor
laws required to construct their data; none assumes the augmentation theorem.

No node statement, dependency list, proof, or proof-dependency list is changed. No
new independent notion or dependency module is needed. All helpers belong to the
principal-cone comparison itself and are listed in `lean.declarations`.

Hypotheses and objects, matched to the node:

- The site is `C : Type u`, `[Category.{v} C]`, `J : GrothendieckTopology C`, and
  `[EssentiallySmall.{r} C]`. Ring and module coefficients are in the independent
  universe `r`; the two localization Hom universes `wR`, `wS` are also independent.
  Sheaf composition, sheafification and locally bijective equivalences are the
  standard site infrastructure for the abelian module-sheaf category, not additional
  geometric assumptions or assumptions about points.
- `R S : Sheaf J CommRingCat.{r}` and `φ : R ⟶ S` are the two ring sheaves and map.
  `Modules R` abbreviates the recorded `ringedSiteModules` of the recorded underlying
  ring sheaf. `restriction φ` is literally Mathlib's `SheafOfModules.restrictScalars`.
- The global section is
  `t : (unit (derivedChangeRingIndependentCoefficients J R)).sections`. A unit-module
  section is exactly a compatible family of sections of R. `scalar R t` multiplies
  every module section at U by `t.val U`; it is not a chosen endomorphism.
- `ringMap φ` is `unitHomEquiv.symm` applied to the compatible family `1` in the
  restricted unit S-module. On a local scalar a it sends a to `φ_U(a)`, since its
  linear map sends `1` to `1` and the R-action on S is through φ.
- `ht` is the zero composite of scalar multiplication on the unit with `ringMap φ`.
  Evaluating at the local section `1` gives `φ_U(t_U)=0`, and conversely this identity
  kills the composite on every section by linearity. Thus it is exactly `φ(t)=0`.
- `_hexact` says that the actual `ShortComplex.mk` with those two arrows and zero
  composite is `ShortExact`. This is the asserted exact sequence of module sheaves:
  monicity on the left, exactness in the middle, epimorphicity on the right. It does
  not replace a sheaf epimorphism by surjectivity on all sections.
- `d : DerivedChangeOfRingsCochainModel φ` names the already recorded universal
  ordinary/derived change-of-rings pair. It is arbitrary among such presentations;
  the recorded existence theorem supplies one. It imposes no new mathematical
  assumption. `d.E` has exactly the recorded ordinary tensor objects and maps;
  `d.T` and its universal cochain counit `d.ε` are the specified left derived functor.

Every conclusion clause:

- `complexScalar R t` has degree-n map `(scalar R t).app (P.X n)`.
  `cone R t` has object `mappingCone ((complexScalar R t).app P)` and on h uses
  `mappingCone.map _ _ h h ...`. This is exactly the diagonal formula
  `(y,x) ↦ (h^n(y),h^(n+1)(x))`. Mathlib orders the shifted and unshifted biproduct
  summands differently in its API; `mappingCone.inr` is the unshifted inclusion and
  `mappingCone.snd` the unshifted projection. This represents precisely the stated
  differential `(dy+t x,-dx)`, without changing a sign.
- `Augmentation.ρ` is a natural transformation on all complexes. `ρ_sections`
  fixes each degree and each section to the ordinary coefficient unit followed by
  module sheafification, transported only by `d.obj_eq`. The upstream tensor
  construction is scalar-first, so its formula `1 ⊗ x` represents the node's `x ⊗ 1`.
- `Augmentation.a` is a natural transformation from the strict cone functor to
  termwise extension followed by termwise restriction. `a_components` fixes it to
  `mappingCone.snd ≫ ρ` in every degree. Thus it is exactly `(y,x) ↦ y ⊗ 1`, with
  the shifted component zero. These component equations determine the maps uniquely;
  no unnormalized or arbitrary map is substituted for the canonical augmentation.
- `quasiIso` quantifies over every complex P satisfying the recorded
  `IsKFlatIndependentCoefficients (R := R) P`. No flatness of individual terms or of
  S is required. The natural-transformation type of a gives the displayed naturality
  identity for every chain map, including all maps between K-flat complexes.
- `augmentation_inclusion : inclusion R t ≫ a = ρ` is the strict identity `a_P i_P=ρ_P`.
- `cone_preserves` and `tensor_preserves` are the two quasi-isomorphism preservation
  clauses, both with arbitrary K-flat endpoints and the actual functorial map.
- `V` and `restriction_factor` give the localization of exact restriction on all
  complexes. They are not a different derived restriction: localization determines
  this functor up to the unique isomorphism compatible with that factorization.
  `adjunction : d.T ⊣ V`, together with `unit_normalization`, specifies the actual
  derived scalar-extension unit through the universal K-flat counit and ordinary ρ.
- `D` and `cone_factor` give the localized scalar-cone functor on all complexes.
  `i` and `inclusion_components` give precisely the localized cone inclusions.
- `A : D ≅ d.T ⋙ V` is the requested natural isomorphism on the entire derived
  category. `A_components` states, for every K-flat P, that composing its component
  with restricted `d.ε.app P` and the restriction computation map equals Q(a_P),
  after the cone factorization. These are exactly the canonical computation
  coordinates specified by the node, including arbitrary K-flat P with nonflat terms.
- `unit_identity : i ≫ A.hom = adjunction.unit` is the derived unit compatibility.
- Resolution independence and the three-resolution cocycle are encoded by the
  natural-isomorphism type of A together with `A_components`. For quasi-isomorphisms
  s:P→X and t:P'→X the canonical comparison is Q(s) followed by inverse Q(t), an
  actual derived morphism. A is natural at this morphism. For u:P''→X, composing
  the two comparisons cancels inverse Q(t) with Q(t), so both D and `d.T ⋙ V`
  satisfy the cocycle by their functor laws. No comparison chain map or lifting
  hypothesis is imposed. Naturality also applies to every other derived morphism.
  Separate restatements of the naturality and functor laws would be redundant.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, a
  transparent use of Mathlib `SheafOfModules`, with its existing abelian instance.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`, with its original additive instance.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Q`, and Q's quasi-isomorphism localization.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`, quantifying over all acyclic
  complexes and the recorded total sheaf tensor.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`; it occurs
  through the K-flat predicate and fixes the direct-sum total tensor convention.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel`, its prescribed `E`, `obj_eq`,
  `map_eq`, `T`, universal `ε`, `computes`, and
  `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel`.
- `Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated`:
  `CochainComplex.mappingCone.map`, `map_id`, `map_comp`, and the underlying
  `mappingCone`, `inr`, `snd` constructions and their signatures/docstrings.
- Already stated proof-dependency modules are imported without `public`:
  `HomotopyCategory.ShortExact` (`quasiIso_descShortComplex`), the upstream acyclic
  cone criterion (`quasiIso_iff_acyclic`), `SheafRingDerivedCoefficientAdjunction`,
  `SiteDerivedTensorDescentIndependentCoefficients`,
  `KFlatResolutionIndependentCoefficients`, and Mathlib's localization predicate API
  (`Localization.lift`, `fac`, natural-transformation lift and uniqueness).
  The proof-dependency `lem-weil-pbc-total-tensor-homotopy-cone-signs` currently has
  no recorded declaration/module and therefore supplies no import yet. Its proof
  role remains explicitly in the theorem docstring; no unstated proof node was
  silently taken as an axiom.

Edge cases checked before writing:

- Unbounded complexes and arbitrary integer degrees, including negative and zero
  degrees, are included. P=0 is allowed throughout.
- Empty sites, sites without points, and zero ring sheaves are not excluded.
- If t is invertible then exactness forces S to be zero; the comparison is between
  the contractible scalar cone and the zero extension. No nonzero assumptions arise.
- If t=0 then the monomorphism in `_hexact` forces the unit module, hence R, to
  vanish; exactness also forces restricted S to vanish. No excluded exceptional case.
- Independent site-object, site-morphism, coefficient, and derived Hom universes are
  retained. No smallness condition accidentally quantifies over too small a test class.
- A sheaf quotient need not be a quotient on sections: only categorical ShortExact
  is assumed. The augmentation formula uses sheafification explicitly.
- No flatness of S, termwise flatness of P, boundedness, or existence of points is added.

Searches for an existing statement/construction:

- `msearch.py leanfinder`: "Mapping cone of multiplication by a regular global
  section on a K-flat complex of module sheaves is naturally quasi-isomorphic to
  extension of scalars to the principal quotient". Eight hits: generic mapping-cone
  quasi-isomorphism/comparison and localization declarations; no normalized assertion.
- `msearch.py loogle`: `CochainComplex.mappingCone, QuasiIso`. Two hits:
  `quasiIso_descShortComplex` and `cm5b.instQuasiIsoIntP`; neither is this statement.
- `msearch.py leansearch`: "Canonical mapping cone augmentation for multiplication
  by a regular section on K-flat module sheaves to extension of scalars to the quotient".
  Eight hits, including the cone, `ModuleCat.smulShortComplex_g`, and cone map/lift;
  none gives the sheaf-level K-flat augmentation with normalized derived descent.
- `msearch.py grep`, Mathlib `Algebra/Homology`:
  `scalarCone|mappingCone.*[Aa]ugment|[Aa]ugment.*mappingCone|quotient.*[Cc]one`.
  Four hits in Pretriangulated/Triangulated; no exact theorem.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for scalar/principal/regular
  quotient cones and augmentation names, and the item id. No exact theorem.
  `CategoryTheory.Sheaf.smulNatTrans` is for constant-ring ModuleCat-valued sheaves,
  not variable ring sheaves. `globalSectionMultiplication` in
  `PrincipalKoszulQuotientTowers` acts only on the unit module. The new scalar helper
  supplies the natural action on arbitrary variable-ring module sheaves.
  `DerivedCategory.scalarConeCochainFunctor` in `ScalarConeTensorModel` uses a
  separately installed scalar ring action and assumes a Grothendieck monoidal closed
  framework with functorial flat resolutions and a fixed derived Hom universe.
  It does not provide the present interface on an arbitrary relatively small site;
  the new cone helper directly specializes the same existing Mathlib cone/map API,
  without importing or duplicating a tensor product or derived-category construction.

Sources were read in `literature/stacks-project/sites-cohomology.tex` at
`lemma-K-flat-quasi-isomorphism`, the construction preceding `definition-derived-tor`,
and `lemma-derived-base-change`. The module docstring follows the node's full proof
plan, including extending the normalization from flat-term to arbitrary K-flat models.
No statement dispute or source-based correction was needed.

## Second reading by Q49

A separate source-to-signature reread was performed in this worker session; no
independent agent was started, as the dispatcher brief forbids that. The maintainer's
independent review is still required. This reread checked every field against the
node, especially the distinction between all K-flat complexes and flat-term K-flat
resolutions, the sign/order of the cone coordinates, sheaf epimorphicity rather than
sectionwise surjectivity, and the use of the actual universal counit in A_components.
It also checked that `unit_identity` names an adjunction unit normalized by
`unit_normalization`, and that resolution comparisons may be roofs without any
chosen comparison chain map. All helpers have source/blueprint docstrings and real
data. There is only one `sorry`, the named existence theorem matching this node.

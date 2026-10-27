## Worker report

The module `Sheaf.AlgebraicGeometry.SupportedSectionH1AffineLift` states
`AlgebraicGeometry.Scheme.Modules.exists_supported_section_h1_affine_lift` with
`sorry`. It introduces no new construction or axiom. Source read directly:
`literature/stacks-project/coherent.tex`, Tag 0B5P,
`lemma-quasi-compact-h1-zero-invertible`, lines 426–484, first proof paragraph.
The node extracts the supported-section step with the section and exactness
hypotheses explicit; it does not need closedness of x or quasi-compactness of X.
Those enter the source's construction of q and its later covering argument.

Hypotheses, matched individually:

- Scheme X, affine open U, point x in U: `X : Scheme.{u}`, `U : X.Opens`,
  `hU : IsAffineOpen U`, `x : X`, `hx : x ∈ U`.
- Invertible module: `M : X.Modules` and `[M.IsInvertible]`, the recorded
  `Scheme.Modules.IsInvertible` from
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`.
- Free generator a on U: `a : Γ(M, U)` and bijectivity of `f ↦ f • a`.
  Over the affine U the invertible sheaf is quasi-coherent, so this is exactly
  a rank-one free generator, with unique scalar coordinates, not a choice of
  arbitrary unrelated trivialization.
- I is the reduced boundary vanishing ideal: `hI` identifies I with
  `Scheme.IdealSheafData.vanishingIdeal` of the closed complement of U.
  The recorded `reduced_induced_closed_subscheme` in
  `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme` identifies
  its sections with exactly the pointwise residue-zero condition in the node.
  Its public import supplies `IdealSheafData.toModules` and `toModulesι`.
- J is a quasi-coherent ideal subsheaf of I: J is `X.IdealSheafData`, the
  existing encoding of quasi-coherent ideals; `j : J.toModules ⟶ I.toModules`
  and `hj : j ≫ I.toModulesι = J.toModulesι` fix its inclusion. Since
  `I.toModulesι` is mono, this factorization uniquely determines j. It
  expresses precisely J ⊆ I, without an arbitrary-injection assumption.
- J_x = maximal ideal and I_x = local ring: `hJx` and `hIx`, using the
  localization of each affine ideal along the actual germ map from U.
  Because x belongs to the affine U, these mapped ideals are precisely the
  stalk ideals. They need no new stalk-ideal definition.
- Q = I/J: `cokernel j`, with actual canonical quotient map `cokernel.π j`.
- Short exact tensor sequence: `hseq` asserts that the two canonical tensor
  arrows `j ▷ M` and `cokernel.π j ▷ M` form a short exact complex. The
  existentially bound `hz` is the zero-composite proof field of that
  complex; no zero-preservation instance is assumed. Its three terms are
  J⊗M, I⊗M, (I/J)⊗M.
- The displayed π is canonical: `hπ : π = cokernel.π j ▷ M`.
- Canonical multiplication ι and its injectivity: `hι` identifies ι with
  `(I.toModulesι ▷ M) ≫ (λ_ M).hom`; `[Mono ι]` is injectivity in the
  module-sheaf category. The unitor makes the map locally b⊗m ↦ bm.
- Global quotient section q and nonzero germ: `q : Γ(cokernel j ⊗ M, ⊤)`
  and `hq`, its germ at x is nonzero. The node's canonical identification
  of this stalk with M_x / maximalIdeal·M_x is an isomorphism, and therefore
  preserves and reflects zero. Writing the condition before this
  identification is equivalent, and does not replace the identification
  by an arbitrary isomorphism or require extra comparison data.
- H¹(X,J⊗M)=0: `hH1 : Subsingleton ((RingedSpace.moduleCohomology
  X.toRingedSpace 1).obj (J.toModules ⊗ M))`. This is the right-derived
  cohomology of global sections in O_X-modules, from the recorded
  `WeilConjectures.AlgebraicGeometry.PQFCohomology` interface and its public
  `RingedSpaceModuleCohomology` import.

Conclusion, matched clause by clause:

- `∃ t` with `π.app ⊤ t = q` is the lift of the actual section q.
- `∃ s` with `s = ι.app ⊤ t` names its image in M.
- `x ∈ nonvanishingLocus M s` is nonzero residue at x, using the recorded
  locus from `WeilConjectures.AlgebraicGeometry.Ample`.
- `∀ z, z ∉ U → z ∉ nonvanishingLocus M s` is zero residue at every
  boundary point, literally membership in maximalIdeal·M_z by the locus's
  definition.
- `∃ f` with restriction of s along U≤⊤ equal to `f • a` is s|_U=fa.
- `∃ V : X.Opens`, whose underlying set equals the nonvanishing locus,
  and `V = X.basicOpen f`, names X_s as an actual open and the principal
  basic open of f in U.
- The further set equality
  `(V : Set X) = {y | ∃ hy : y ∈ U, IsUnit (X.presheaf.germ U y hy f)}`
  renders the node's explicit definition of U_f using local-ring units.
- `x ∈ V`, `V ≤ U`, `IsAffineOpen V` render x ∈ X_s=U_f⊆U and affineness.
  The equality with `basicOpen f` is the existing Mathlib encoding of that
  same principal open, not an extra geometric property.

Other dependency interfaces read and imported: `SheafOfModules.IsQuasicoherent`
through `Sheaf.AlgebraicGeometry.CoherentFiniteType` (the recorded
`IsQuasiCoherentFiniteType` conjunction itself is not imposed, since J need
not be finite type); `PresheafOfModules.moduleStalkFunctor` from
`WeilConjectures.Topology.PresheafModuleStalkFunctor`, whose stalk carriers
and germs are Mathlib's; `CategoryTheory.ringedSiteModules` from
`Sheaf.CategoryTheory.RingedSiteModules` is a transparent abbreviation of
`SheafOfModules`, hence the category here is the recorded category;
`SheafOfModules.cochainModulesMonoidal` and its existing tensor interfaces
from `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`.
No new tensor or stalk construction is defined.

Proof-only imports follow every recorded proof dependency:
`moduleSheaves_abelian_enoughInjectives`,
`globalSectionsFunctor_additive_leftExact`,
`Functor.exists_universal_rightDerived_deltaFunctor`, `stalkTensorIso`,
and the Mathlib affine basic-open statements
`Scheme.evaluation_eq_zero_iff_notMem_basicOpen`, `IsAffineOpen.basicOpen`
and `IsAffineOpen.isLocalization_basicOpen`. Their signatures/docstrings
were read from the recorded modules. The six-step proof is reproduced in
the theorem docstring. Statement dependencies which are also proof
dependencies stay public imports.

Edge cases checked: empty X or empty U cannot supply x∈U; no nonempty
assumption on a separate object is added. With U=⊤ the boundary is empty
and its vanishing ideal is the unit ideal; no boundary condition is
lost. The zero section cannot satisfy hq. The chosen x need not be closed:
the given stalk and quotient-section assumptions suffice. No Noetherian,
finite-type, separatedness, quasi-compactness, or characteristic
restriction is inserted. All universes and variables are explicit, with
`set_option autoImplicit false`. No definition contains `sorry`; the
only postponed proof is the named item theorem.

Searches run with msearch.py, group Q76 and this item:

- LeanFinder: “A section of an invertible sheaf lifts from an ideal quotient
  using vanishing H1, with affine nonvanishing locus inside a trivializing
  affine open”: 8 hits, concerning ideal localization, tilde sections,
  fraction representations, and clearing powers. None states the lifting
  and nonvanishing conclusion.
- Loogle: `"rightDerived", "exact"`: 0 hits.
- Mathlib grep: `cohomology|nonvanishingLocus|rightDerived`, restricted to
  AlgebraicGeometry: 6 hits, all cohomology imports/comments in sites.
- LeanSearch: “H1 vanishing lifts quotient sheaf sections and gives affine
  nonvanishing loci for supported invertible sheaf sections”: 8 hits,
  concerning scheme quotient lifts, ideals and affine functions; none is
  this module-sheaf statement.
- Source/project rg: `supported_section_h1|supportedSectionH1|
  supported-section-h1-affine-lift|nonvanishingLocus.*basicOpen` over
  `lean/WeilConjectures` and `lean/Sheaf`: only the tensor-unit basic-open
  comparison in `SectionCohomologyUnitComparisons`, not this theorem.
- Required source grep for the node id: no hits in `lean/WeilConjectures`.
- Further source/project rg for `vanishingIdeal`, `stalkIdeal`,
  `toModules`, tensor multiplication and cokernel projections found the
  existing interfaces used above. No private replacement was introduced.

No statement correction, new node, or dependency repair is needed.

## Second reading by Q76

Author's second reading, not an independent review: reopened the node and
module and checked the above correspondences. Checked in particular that
j is pinned by its inclusion square, π is the cokernel projection tensored
with identity, and ι is inclusion tensored with identity followed by the
left unitor. Thus a supported section cannot be replaced by an arbitrary
injection. Checked that `hq` is equivalent to the stipulated nonzero
residue under the canonical quotient identification, not an assumption
that a lift already exists. Checked that the explicit local unit locus,
nonvanishing locus and affine open all refer to the same s and f, and
that zero residue outside U is present as its own clause. Removed a
`show ... from` term in favor of a typed `le_top` proof. Initial compilation
found a tensor additivity instance hidden by the `X.Modules` alias;
the final statement directly uses the two actual tensor arrows to form
the short exact complex, with its zero-composite proof existentially
bound inside `hseq`. This encodes exactly the assumed short exact
sequence without requiring a functorial mapping instance or adding any
hypothesis. No `MonoidalFree` import or local instance remains.
The maintainer supplies the independent review after delivery.

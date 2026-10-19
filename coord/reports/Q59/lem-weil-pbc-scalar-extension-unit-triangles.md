## Worker report

The module `Sheaf.Algebra.Homology.ScalarExtensionUnitTriangles` states
`SheafOfModules.exists_scalarExtensionUnit_triangles`, with its proof exactly `sorry`.
It also gives two helpers belonging to this node's coefficient-map characterization:
`scalarExtensionCoefficientComplexMap` has real data, using Mathlib's identity,
composition, and termwise natural-transformation comparisons; `ScalarExtensionUnitRoof`
is an explicit proposition, not a chosen map or isomorphism. Neither is a second tensor,
restriction, K-flatness, or derived-category construction. No new independent notion or
DAG node is introduced, and no dependency record or natural statement is changed.

The natural statement and Lean match as follows.

- A site small relative to its module universe is `{C : Type u} [Category.{v} C]`,
  `J : GrothendieckTopology C`, and `[EssentiallySmall.{r} C]`. Its sheafification and
  locally-bijective instances are the existing independent-coefficient infrastructure.
  `u`, `v`, and `r` are independent. The Grothendieck-topology presentation is the sheaf
  presentation of the recorded covering-site notion; no points or pullbacks are assumed.
- The ring morphism is `φ : R ⟶ S` for `R S : Sheaf J CommRingCat.{r}`. Forgetting
  commutativity uses `derivedChangeRingIndependentCoefficients J R` and its S version.
  Module sheaves are exactly the recorded `ringedSiteModules.{r}` abbreviation.
- The unbounded derived categories are Mathlib `DerivedCategory`, with independent
  localization morphism universes `wR` and `wS`. Complexes are all integer cochain
  complexes. `DerivedCategory.Q` is localization from complexes; by
  `DerivedCategory.quotientCompQhIso` it is the stated localization `Qh` composed with
  the homotopy quotient. Using Q therefore renders precisely the same roof.
- `E`, `h`, and `hmap` are a presentation of the stated ordinary scalar extension:
  its objects are exactly `changeOfRings φ M` and its maps exactly `changeOfRingsHom`
  transported by h. This is the existing derived-change-of-rings dependency's interface,
  with `[E.Additive]`. The functor is not arbitrary.
- `F`, `ε`, and `[F.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso ...)]` express
  the given universal derived scalar extension, not an auxiliary map or a new
  resolution. The dependency presents the same universal pair on homotopy categories;
  composing with the homotopy quotient gives the complex presentation used here.
- `[F.CommShift ℤ] [NatTrans.CommShift ε ℤ]` specify the canonical shift of that given
  derived functor: the square is exactly counit compatibility with Q's shift and the
  termwise scalar-extension comparison. This is the node's instruction to give F its
  shift induced from complexes, not an assumption of a new exactness property.
  Mathlib uses `(P[1])^i=P^(i+1)` and differential `-d`. The theorem additionally states
  `F.IsTriangulated` for that very shift. It does not assume a triangulated structure
  with an uncontrolled sign.
- The fixed restriction is exactly `SheafOfModules.restrictScalars` along
  `(sheafCompose J (forget₂ CommRingCat RingCat)).map φ`. Both finite-limit and
  finite-colimit preservation occur as existential conclusions, not hypotheses.
  Under these witnesses, `mapDerivedCategory` is U, with its canonical termwise shift
  and the exact factorization `mapDerivedCategoryFactors`.
- The existential ordinary transformation `ι` is normalized on every section of
  every module: after the object identification h, it is the module tensor adjunction
  unit followed by the presheaf-of-modules sheafification unit. Mathlib puts the
  scalar first, so this is `1 ⊗ x`, precisely the commutative-ring convention for
  the source's `x ⊗ 1`. There is no arbitrary natural transformation substituted.
- The coefficient chain map is `scalarExtensionCoefficientComplexMap E V ι P`.
  Its component in degree n is `ι.app (P.X n)`; naturality supplies the differential
  square through Mathlib's existing termwise natural-transformation construction.
  Its definition uses no proof placeholder or existence choice.
- The conclusion produces `η : 𝟭 D(R) ⟶ F ⋙ U`. For every complex K and every
  `p : P ⟶ K`, `ScalarExtensionUnitRoof` assumes only the recorded
  `IsKFlatIndependentCoefficients P` and `QuasiIso p`. It asserts an isomorphism c
  and the equations `F(Qp) ≫ c.hom = ε.app P` and
  `Qp ≫ η_K ≫ U(c.hom) ≫ restrictionComparison = Q(i_P)`.
  Since Qp is invertible, the first equation specifies c uniquely as
  `F(Qp)⁻¹ ≫ ε_P`. The second is exactly the claimed roof formula after that canonical
  identification. No flatness of P's terms, degreewise epimorphism, or choice of a
  special resolution is required. The `∀ η', ScalarExtensionUnitRoof ... η' → η'=η`
  clause gives uniqueness from the roof characterization alone, hence independence
  of all resolutions. Existence of K-flat resolutions is already a dependency.
- For every derived object X the explicit equation
  `η_(X[1]) ≫ (F ⋙ U).commShiftIso(1).hom.app X = (shiftFunctor _ 1).map (η_X)`
  is exactly `χ_X ∘ η_(X[1]) = η_X[1]` in Mathlib's order of composition.
- For every `T ∈ distTriang _`, its `(F ⋙ U).mapTriangle` image is distinguished,
  and a triangle morphism m has components exactly `η.app T.obj₁`, `η.app T.obj₂`,
  and `η.app T.obj₃`. `TriangleMorphism.comm₁` and `.comm₂` give the first two
  naturality squares. `.comm₃`, together with `mapTriangle`'s last arrow
  `UF(T.mor₃) ≫ χ`, is exactly the connecting square in the node, including the shift
  and its sign. Thus this is the specified morphism, not the unrelated existence of
  a completion of two squares.
- There is no flatness of S, boundedness, constructibility, nonzero-ring assumption,
  or existence-of-points hypothesis anywhere in the signature or helper predicate.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`: `Precoverage.IsSiteForCoverings`, with
  its existing Grothendieck-topology/sheaf presentation retained.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `Q`, `Qh`, their shift and triangulation structures.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`:
  `derivedChangeRingIndependentCoefficients` and
  `derivedChangeOfRingsIndependentCoefficients` (its ordinary functor and universal
  derived-pair presentation, transported through the homotopy quotient).
- `Sheaf.Algebra.Homology.KFlat`: `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`:
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients` (proof import).
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars` and its additive instance.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated` and `.Functor`:
  `Pretriangulated`, `distTriang`, `TriangleMorphism`, `Functor.mapTriangle`,
  and `Functor.IsTriangulated`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`, including its
  public `TensorProduct` interface: `changeOfRings`, `changeOfRingsHom`,
  `changeOfRingsPresheaf`. Rings and modules use the same chosen coefficient size r;
  this does not identify either site universe with r.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategory`, `mapDerivedCategoryFactors`, their canonical
  `CommShift` and `IsTriangulated` instances. This is also the exact Mathlib match
  of `lem-weil-pbc-exact-functor-derived-factorization`.
- `Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent`:
  `SheafOfModules.wf_site_derived_tensor_descent` (proof import).
- `Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`:
  `Functor.leftDerived_from_resolvingClass` (proof import).
- `Mathlib.CategoryTheory.Localization.Predicate`: the recorded localization
  lifting and natural-transformation extension interface (proof import).

The proof-only node `lem-sbc-derived-scalar-extension-counit-shift` presently has
no Lean module to import. It is named in the unchanged proof docstring; the statement
already specifies the canonical shift by its counit compatibility, as that node does.
No undefined construction is used and no missing prerequisite is assumed as an extra
mathematical hypothesis. An independent assertion of existence of the canonical shift
belongs to that existing node, not a new helper notion here.

Edge cases checked by reading the signature and evaluating the mathematical formulas:
identity ring map (the unit is the identity under canonical identifications); zero
complex; zero target ring (the coefficient map is zero); empty site; all integer
shifts; characteristic two (the minus sign becomes plus); and the nonflat map
`ℤ → ℤ/2` on the one-point site, with the two-term resolution `ℤ --2→ ℤ` of `ℤ/2`.
The latter still uses a K-flat complex and no S-flatness hypothesis. Arbitrary K-flat
resolutions, including ones with nonflat terms, are quantified in the roof predicate.
No edge case is excluded, and no statement dispute or correction was found.

Searches for an existing exact statement:

- msearch LeanFinder: “The natural unit from a derived sheaf of modules to
  restriction of its derived extension of scalars commutes with shifts and forms
  morphisms of distinguished triangles”: 8 hits, chiefly underived sheaf pullback
  units and an abstract derived adjunction counit identity; no exact statement.
- msearch Loogle: `CategoryTheory.NatTrans.CommShift`: 12 hits, the abstract
  compatibility class and its structural lemmas; no canonical ringed-site unit.
- msearch LeanSearch: “The canonical derived coefficient map for sheaves of modules
  commutes with shifts and gives morphisms of distinguished triangles”: 8 hits,
  exact-functor derived shifts, mapping cones, and abstract triangle transport;
  no scalar coefficient transformation or K-flat roof characterization.
- msearch grep in Mathlib/CategoryTheory:
  `derived.*[Uu]nit|[Uu]nit.*CommShift|restrictScalars`: 19 hits, abstract total
  derived units/counits and adjunction/shift compatibility, no exact statement.
- `rg` in `WeilConjectures`, `lean/Sheaf`, and the upstream name index for the item
  id and the three proposed declaration names: no declaration already exists.
  Broader scalar-extension, unit, CommShift, and restrictScalars searches found
  the recorded derived-change-of-rings interfaces, pro-etale coefficient specializations,
  and ordinary tensor adjunctions. They lack the complete arbitrary-site roof,
  shift, and triangle assertion. In particular the pro-etale
  `DerivedScalarExtensionRestrictionAdjunction` is a specialization and cannot
  state this node on an arbitrary site.

Validation: the complete module passed `scompile.py` in both its isolated sandbox
and library-module position, with no errors or warnings after line-width repair.
Every variable and universe is explicitly bound. The helpers have no `sorry`; the
only placeholder is the named theorem, with its full six-step proof docstring.
The source, node statement, and file were re-read clause by clause for this report.

## Second reading by Q59

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

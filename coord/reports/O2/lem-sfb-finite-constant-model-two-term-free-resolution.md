## Worker report

The module `Sheaf.Paper.FiniteConstantModelTwoTermFreeResolution` states
`AlgebraicGeometry.ProEtale.finite_constant_model_two_term_free_resolution` with `sorry`.
It contains no other postponed theorem. All helper definitions have real data.
The natural statement, proof plan and proof dependencies of the item are unchanged.
Four already landed statement dependencies are added for the existing interfaces used below.
No new node or dependency-module repair is needed.

Clause-by-clause correspondence:

- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`. The extension is `(E : Type u) [Field E]
  [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]`. This includes all finite
  extensions, without asking for an embedding in an algebraic closure or a chosen metric.
- `IntegralFiniteScalarResolution` uses the recorded `Padic.coefficientExtensionIntegers ℓ E`.
  `RationalFiniteScalarResolution` uses E itself. Both install
  `spectralNorm.normedField (Padic ℓ) E`, the unique topology of this finite extension;
  the integral topology is the induced subring topology. These are definitions, so
  their instance-installing lets are not lets in a theorem statement.
- T is an unrestricted `(T : Scheme.{u})`. Its small site is exactly
  `Scheme.ProEt.topology T`, with object universe u+1 and arrow universe u.
- The usual condensed ring is the existing `Profinite.continuousCoefficientRingObj A`,
  with sections `ULift C(S,A)`. This is the universe-generalized form of
  `Profinite.continuousMapRingObj` recorded for sk-def-sfb-condensed-ring, publicly
  exported by the landed coefficient-category node. The coefficient on T is the
  existing `condensedRingObj ... T`, namely p_T^* of that ring, with its transported
  ring structure. No coefficient is replaced by an arbitrary ring or map.
- `scalarPresheafMap` sends a lifted a to the constant continuous function with value a.
  `pointSectionIso` identifies reconstructed section rings with their original continuous
  function rings by the identity on elements. Its multiplication check uses the existing
  `Sheaf.μ_comp_map_mul`, exactly the section-ring reconstruction normalization.
  `scalarMap` extends that presheaf map by the existing `sheafifyLift`; uniqueness of
  sheafification fixes the canonical map from discrete constant A to the condensed ring.
- The module P is quantified over `ModuleCat.{u+1} (ULift.{u+1} A)`. The universe lift
  is a ring equivalence with A and changes neither modules nor presentations; it fits
  the coefficient universe of the small site. `Module.FinitePresentation ... P` is
  Mathlib's finite-generators/finite-relations condition, equivalent to the finite
  cokernel presentation in the node (`Module.FinitePresentation.exists_fin`).
- `pointModel` is the existing `changeOfRingsOfUniverses (scalarMap A)` applied to
  the existing `commutativeSiteConstantModuleFunctor` on P, transported through the
  existing `sectionModuleEquivalence.inverse`. Its maps `pointModelMap` use the
  existing `changeOfRingsHomOfUniverses`, hence are precisely `1 tensor f`.
  `model` and `modelMap` apply the existing `(upperStarFromPoint T).mapMod`.
  A geometric inverse image preserves constant objects, finite products and colimits,
  hence the constant-module sheafification and the balanced tensor coequalizer.
  Consequently this construction is exactly B_T tensor_{constant A} constant P,
  with its canonical scalar maps on T. It is not a choice of a finite presentation
  or an unspecified module isomorphic to a local model.
- In `HasTwoTermFreeResolution`, the witnesses `a b : ℕ` are finite nonnegative ranks;
  `scalarFree A n` is the actual module `Fin n → ULift A`. The witnesses u and v have
  exactly the scalar source and target of the node. `Function.Injective u`,
  `Function.Exact u v` and `Function.Surjective v` express all three scalar exactness
  conditions, including both endpoint zeros.
- The two `Nonempty` isomorphisms identify the scalar-extended free terms with the
  existing `Mod.finiteFree B_T a` and `Mod.finiteFree B_T b`. These isomorphisms only
  express finite freeness; they do not choose the maps. The sheaf maps are fixed
  separately as `modelMap A T u` and `modelMap A T v`. The following existential h
  records their zero composite and `ShortComplex.ShortExact` asserts their exactness
  and their mono/epi endpoint conditions. After finite-free identification this is
  exactly the displayed short exact sequence of the node.
- K is an actual `CochainComplex` in the ordinary internal B_T-module category.
  `em` and `e0` identify its degree -1 and degree 0 terms with those same extended
  scalar free modules; `IsZero (K.X i)` holds at every other degree. The displayed
  equation on `K.d (-1) 0` fixes its differential as the scalar-extended u.
- ε is an actual map to `(CochainComplex.singleFunctor _ 0).obj (model A T P)`.
  Its degree-zero equation, using `singleObjXSelf`, fixes it as scalar-extended v.
  Every other target term is zero, so no augmentation component is omitted.
  `QuasiIso ε` means the induced map on every cohomology sheaf is an isomorphism.
- The rational flag is false for integral coefficients and true for field coefficients.
  `(rational = true → a = 0)` enforces the specified field-case rank zero.
  The final implication also asserts `Mod.IsFree B_T (model A T P)`, which is the
  existing notion of finite freeness (existence of some finite rank).
- There is no Noetherianity assumption on T, no torsion-freeness assumption on P,
  no completion, and no derived-category size or enhancement assumption.

Dependency declarations used (their full source signatures and docstrings were read):

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, reexporting
  `Padic.coefficientExtensionIntegers` from CoefficientExtension and the DVR interface.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`; and
  `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology`.
  The size-convention node is metatheoretic and is implemented by explicit universe u.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap` and EllAdic:
  `Profinite.continuousMapRingObj` and the usual p-adic specializations. Their
  same construction for A : Type u is `Profinite.continuousCoefficientRingObj` with
  `Profinite.isCommMonObj_continuousCoefficientRingObj`, exported by
  `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing` (added landed dependency
  def-weil-pbc-condensed-e-module-category).
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `upperStarFromPoint`, `coefficientRing`, `condensedRingObj`; and MapMod:
  `CategoryTheory.Functor.mapMod`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`;
  `Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor`:
  `realizationRing`, `commutativeSiteConstantModuleFunctor` (added landed dependency
  def-sfb-site-derived-constant-module-functor).
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `InternalAbelianSheafModule.sectionRingSheaf`, `sectionModuleEquivalence`
  (added landed dependency def-weil-pbc-internal-abelian-sheaf-module-equivalence).
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`, publicly reexporting
  TensorProductOfUniverses: `SheafOfModules.changeOfRingsOfUniverses` and
  `changeOfRingsHomOfUniverses` (added landed dependency def-pur-sheaf-tensor-product).
  These are the existing sheafified balanced scalar tensors; their internal encoding
  uses the existing module equivalence, not a new relative-tensor construction.
- `WeilConjectures.CategoryTheory.ModuleObjects.Monoidal`: the existing internal
  relative tensor `CategoryTheory.Mod.monoidalCategory` and its coequalizer;
  Free: `Mod.finiteFree` and `Mod.IsFree`.
- `Sheaf.Paper.CondensedConstantConstructibility`: the finite constant scalar model
  convention on the point before pullback. No constructibility hypothesis on T or P
  is introduced here: this lemma constructs one chart model itself.
- `Sheaf.CategoryTheory.RingedSiteModules` / Mathlib's `SheafOfModules`: the sectionwise
  module category. The module equivalence above gives its identical internal encoding.
- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex`;
  `Mathlib.Algebra.Homology.QuasiIso`: `QuasiIso`; and ShortComplex.ShortExact.
- The stated proof dependencies are imported, including CompletedConstantSheafReduction,
  ExtensionIntegersDvr (through CoefficientExtensionFinite), FreeModule.PID,
  PrincipalIdealDomain and sheafification. The integral-limit comparison node is still
  unstated, so it has no module to import. It is only a proof dependency and was not
  replaced by any assertion in a definition.

Edge cases checked: P = 0 and zero ranks are included (`Fin 0` is empty);
P with nonzero torsion over O_E is included (only the kernel in a free module is
used as torsion-free in the proof plan); over E the empty basis gives b = 0 for
P = 0; the empty scheme has the zero sheaf category and causes no nonemptiness
hypothesis; no restriction on the characteristic, dimension or Noetherianity of T
is introduced. Universes allow an arbitrary scheme and extension by choosing their
common enclosing universe; the module universe is u+1, with scalar ring ULift A.
No statement fault or disputed clause was found.

Searches (2026-10-18):

- msearch LeanFinder, "Finitely presented module over a finite ell adic extension
  valuation ring has a two term finite free resolution after scalar extension to pro
  etale sheaves": 8 results concerning etale algebras and cotangent complexes;
  none states this scalar-to-condensed-sheaf resolution.
- msearch Loogle, "Module.FinitePresentation, ShortComplex.ShortExact, QuasiIso":
  no hits (ShortComplex.ShortExact not known by the search service). Its actual
  declaration in Mathlib was opened and read directly.
- msearch grep, `(finite.*free.*resolution|resolution.*finite.*free|constant.*[Ee]xact)`
  under Mathlib CategoryTheory: no hits.
- msearch LeanSearch, "constant module sheaf extension of scalars to continuous
  condensed coefficient ring": 8 hits including SheafOfModules.restrictScalars and
  CondensedMod.LocallyConstant.functor; none is this theorem or this full model.
- msearch Loogle, "SheafOfModules.changeOfRingsFunctorOfUniverses": unknown identifier.
  Direct source search instead found the existing object and morphism constructors
  `changeOfRingsOfUniverses` and `changeOfRingsHomOfUniverses`, which are reused.
- rg of WeilConjectures and lean/Sheaf for finite free resolution, scalar extension,
  finiteConstant, constantModel and twoTerm: affine free resolutions, finite-field
  local triviality and ConstantTwoTermResolution were inspected. They concern different
  coefficients, impose extra geometric hypotheses, or treat a specified prime-power
  quotient; none gives this statement. The project's constant model, sheaf tensor and
  module encoding helpers above are reused. The item-id grep of upstream
  WeilConjectures returned no match. No declaration was duplicated.

Sources were opened: Bhatt--Scholze PDF, pp. 60--61, Definition 6.8.10 and
Proposition 6.8.11(3) with its scalar-resolution argument; Stacks sites-modules.tex,
lemma-constant-exact and lemma-completion-flat (Tags 093J/093M); and the current
main-20261015 lem-sfb-dc-hom-preserves.proof.md. No correction to a unit is needed.

Validation: scompile.py compiled the full module both as a sandbox and at its
intended library path, cleanly (3.7/3.9 seconds before the final direct-import change).
The final wrapper compilation and server preflight both passed in deliver2.py --no-push
(commit 62eaf28f1f; OK, nothing pushed). Exact declaration-name searches in
WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json returned no collision.
The node diff contains only lean and the four added landed stmt_deps; all Lean lines
are within 100 columns.

## Second reading by N2

Author's second pass, as this dispatcher brief forbids starting another agent;
the maintainer supplies the independent review. I reopened the original node and
read the final Lean definitions and theorem side by side. The conjunction covers
both scalar rings. Its predicates quantify every finitely presented module over
the lifted original scalar ring; they require injective u, exactness at the middle,
and surjective v, not merely a right-exact presentation. The output uses the actual
scalar-extended maps, and fixes the differential and augmentation by equations.
The free-term isomorphisms do not replace these maps. The target is L[0], the other
source degrees are zero, and QuasiIso is required in all degrees. The field flag
forces a = 0 and explicitly asserts finite freeness. No scheme hypothesis or
completion condition appeared. I checked the real constant-function construction
of scalarMap and the sheafification/tensor/inverse-image definition of model;
no Nonempty choice, unconstrained coefficient map, or data sorry occurs.
The explicit section-ring identification repaired the elaboration of the canonical
constant-function map; no natural-language statement or hypothesis changed.

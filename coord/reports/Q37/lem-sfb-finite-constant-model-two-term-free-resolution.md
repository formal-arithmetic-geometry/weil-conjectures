## Worker report

The module `Sheaf.Paper.FiniteConstantModelResolution` states
`AlgebraicGeometry.ProEtale.FiniteConstantModel.finite_constant_model_two_term_free_resolution`.
All five named theorems have `sorry` proofs. Definitions contain actual data. There are no new
DAG nodes, dependency repairs, or statement changes. The canonical-map and module-action
helpers are part of the local-model construction being stated, as permitted by the brief's
missing-helper authorization; they are all listed in `lean.declarations`.

Hypotheses and clauses, with the node and final source open:

- The prime is `(l : ℕ) [Fact l.Prime]`. A finite extension is `(E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. The valuation ring is exactly the recorded
  `Padic.coefficientExtensionIntegers l E`. Its topology and E's topology come from
  `(Padic.coefficientExtensionAbsoluteValue l E).toNormedField`, inside the coefficient
  definitions. There is no extra choice of absolute value, algebraic-closure embedding,
  topology, or DVR hypothesis.
- `(T : Scheme.{u})` is arbitrary. The coefficient category is the existing internal module
  category `Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u+1}) B`. An internal action on an
  abelian sheaf is the same module sheaf notion of def-weil-sheaf-of-modules-category:
  restrictions respect scalar action, kernels are underlying kernels, and cokernels are
  sheafified underlying cokernels. The framework's `Mod` and abelian structure are used;
  no new category or categorical instance is chosen. `RingedSiteModules` is imported to
  retain the dependency's general ringed-site interface as well.
- The two allowed choices are the two conjuncts. `integralCoefficients` and
  `rationalCoefficients` use the existing `Profinite.continuousCoefficientRingObj`, whose
  sections are lifted continuous functions into the chosen topological ring.
  `condensedRingObj ... T` is exactly the existing monoidal `p_T^*` construction.
- The scalar ring is discrete in the constant sheaf construction, even though the
  coefficient condensed ring has its specified topology. `scalarModules` constructs the
  usual A-action on the additive group of P, using the explicit integer-bilinear scalar
  action. `constantSheaf` sheafifies this constant presheaf. `constantFunctions` sends
  a scalar to its constant continuous function. `scalarToContinuous` is the unique
  morphism induced by that presheaf map through the sheafification adjunction, and its
  ring-map laws are separately named. It is not an arbitrary coefficient morphism.
- `modelFunctor A T` first takes constant modules on the point, then
  `Mod.extendScalars (scalarToContinuous A)`, then `(upperStarFromPoint T).mapMod`.
  Strong monoidal inverse image preserves constants and the balanced coequalizer, so
  this is precisely `B_T ⊗_{constant A} constant P` on T. In particular the scalar
  algebra map on T is the inverse image of constant functions, under the canonical
  identification of the inverse image of constant A with constant A on T. This
  presentation uses the existing relative tensor/coequalizer, and fixes its maps too.
  `integralModel` and `rationalModel` specialize this functor to the two cases.
- The variable P has exactly `[Module.FinitePresentation A P]`, Mathlib's finite
  generators-and-relations notion, equivalent to the finite cokernel presentation
  specified in the node. It is not assumed torsion-free or projective.
- `HasResolution` existentially quantifies `a b : ℕ`, scalar maps
  `f : freeScalars A a ⟶ freeScalars A b`, `g : freeScalars A b ⟶ P`, and asserts
  `Function.Injective f.hom`, `Function.Exact f.hom g.hom`, and
  `Function.Surjective g.hom`. These are the three clauses of the scalar short exact
  sequence. `freeScalars A n` is `Fin n → ULift A`, a universe-lifted A^n; this lift
  has no effect on linear maps or exactness.
- Its sheaf sequence uses precisely `F.map f` and `F.map g`, where F is the specified
  model functor, and asserts `(ShortComplex.mk ... h).ShortExact`. There is no
  existential choice of unrelated sheaf maps. The two `Nonempty` isomorphisms to
  `Mod.finiteFree B a` and `Mod.finiteFree B b` assert that these actual terms are
  the stated finite powers of B. No choice from these isomorphisms defines any object
  or map; the maps remain the functorial scalar extensions before coordinate transport.
- The augmented cochain complex is existentially presented by K, isomorphisms e₁ and e₀
  from its terms in degrees -1 and 0 to those exact sheaf terms, and a chain map ε to
  `(CochainComplex.singleFunctor _ 0).obj (F.obj P)`. All other terms are `IsZero`.
  The equation for `K.d (-1) 0` fixes its differential to the scalar-extended f, and
  the equation for `ε.f 0` fixes its augmentation to the scalar-extended g, using
  Mathlib's `singleObjXSelf`. All other components into the single complex are forced
  by its zero terms. `QuasiIso ε` asserts the quasi-isomorphism of this augmentation.
- The rational case passes `true`; `rational = true → a = 0` gives the requested
  zero negative term, and the additional implication explicitly gives
  `Nonempty (F.obj P ≅ free b)`, so L is finite free. The integral case passes `false`,
  imposing no extra requirement on the rank of the kernel.
- There is no Noetherianity hypothesis on T, no torsion-freeness on P, and no derived
  completion. Only ordinary cochain complexes appear. The site objects retain the
  framework's universe u+1 and morphisms u; values and scalar modules lie in u+1.
  All universe variables and section variables are explicitly bound.

Dependencies read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, importing
  `CoefficientExtension`: `Padic.coefficientExtensionIntegers`,
  `Padic.coefficientExtensionAbsoluteValue`; the recorded finite-level theorem and
  the full DVR theorem signature/docstring were also read.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`;
  `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology`.
  The size-convention node is metatheoretic and supplies no extra Lean declaration.
- The closed upstream audit of sk-def-sfb-condensed-ring supplies
  `Profinite.continuousMapRingSheaf`, `continuousMapRingObj`, `continuousMapRingSheafMap`,
  and its four ell-adic specializations. Their full signatures were read: those
  original continuous-map coefficients are in Type 0. The already published
  `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing` and `ContinuousCoefficientUniverse`
  give `Profinite.continuousCoefficientRingObj` with identical sections and pointwise
  operations for a coefficient carrier in the scheme universe. This existing
  generalization is used, rather than imposing a Type-0 restriction or copying it.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `upperStarFromPoint`, `coefficientRing`, `condensedRingObj`, and their monoidal and
  commutative structures. The exact shared-overlay file and
  `coord/pefw-upstream-framework.md` were read.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf` and its definition
  as constant-presheaf followed by sheafification; `sheafificationAdjunction`;
  `WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal`: `monoidalConstantSheaf`.
- `WeilConjectures.CategoryTheory.ModuleObjects.Monoidal`: `Mod.monoidalCategory`,
  `tensorObj_X`, `tensorObjπ`, `isColimitTensorπ`; `ExtendScalars`:
  `Mod.extendScalars` and `extendScalarsObj_X`; `MapMod`: `Functor.mapMod`.
  The relative tensor uses the balanced coequalizer of the node, with the left action
  through the first factor. `Mod.finiteFree` is the finite biproduct of regular modules.
- `Sheaf.Paper.CondensedConstantConstructibility`: `HasFiniteConstantLocalModel` and
  `IsConstantModelConstructible`. The former gives the same finite scalar matrix
  models pulled back from the point. No constructibility hypothesis is needed here.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex`;
  `Mathlib.Algebra.Homology.QuasiIso`: `QuasiIso`.
- Proof imports retain the available interfaces of
  `lem-weil-pbc-completed-constant-sheaf-reduction`,
  `lem-sc-dvr-fg-torsionfree-free`, `lem-weil-pbc-pid-noetherian-normal`, and the
  exact sheafification/functor category framework. The recorded completed-reduction
  theorem's full signature was read, including its flatness first conjunct.
  `det-prop-sfb-qlbar-colimit-x-integral-limit` has no Lean record/audit declaration yet;
  it is a proof dependency only and its import is consequently omitted. Its A-algebra
  compatibility is retained explicitly in the natural-language proof plan.

Sources: read the local PDF at pages 58, 60--61, including Lemma 6.8.2(1) and the
finite-projective scalar-resolution argument of Proposition 6.8.11(3); read the current
blueprint `lem-sfb-dc-hom-preserves.proof.md`. Also checked the primary Stacks pages
https://stacks.math.columbia.edu/tag/093J and https://stacks.math.columbia.edu/tag/093M.
The Noetherian assumption in 093M is on the scalar ring, not on T.

Edge cases: P=0 allows a=b=0, including the empty products/biproducts. A free P allows
a=0; integral torsion P=O_E/(pi^n) has the usual rank-one presentation and is not excluded.
A finite presentation with no relations is allowed. On an empty scheme all sheaf terms
are zero, without forcing the scalar sequence to be zero. Non-qcqs and non-Noetherian T
are admitted. Field-case P=0 uses the empty basis and a=b=0. The augmentation equations
have the correct direction: transport from K to the specified free terms, apply F(f)
or F(g), then transport back only at the codomain of the differential.

Searches (2026-10-18):

- `msearch.py ... leanfinder "A finitely presented module over a discrete valuation ring
  has a two term finite free resolution that remains exact after extension to continuous
  coefficient sheaves"`: 8 scalar algebra hits, including residue-field tensor criteria,
  localization freeness, and `AdicCompletion.map_exact`; none states the full result.
- `msearch.py ... loogle "Module.FinitePresentation, Module.Free"`: 5 hits, including
  `Module.FinitePresentation.equiv_quotient` and
  `Module.finitePresentation_of_free_of_surjective`; none states the sheaf resolution.
- `msearch.py ... grep "constant.*[Ee]xact|[Ff]ree.*[Rr]esolution"`: no Mathlib hits.
- `msearch.py ... leansearch "Finite free scalar module resolution preserved by extension
  from the discrete constant coefficient sheaf to continuous ell adic coefficients"`:
  8 hits including `SheafOfModules.mapFree`, `pullbackObjFreeIso`, and
  `CondensedMod.isDiscrete_tfae`; no theorem matching the scalar-and-sheaf resolution.
- Searched the named source tree with `rg` for the exact node id and constant resolutions;
  no existing matching declaration. The newer module-object directories are absent
  there and were read in the prescribed shared-overlay tree instead.
- Searched Mathlib homological algebra for finite free/two-term resolutions and the
  shared Sheaf tree for scalar/constant models, continuous ring objects, and two-term
  resolutions. Found the generic tensor, constant sheaf, free module-object and
  constructibility APIs used above, not the full theorem. Searched the final names
  `finite_constant_model_two_term_free_resolution`, `scalarToContinuous`,
  `modelFunctor`, `HasResolution` in Sheaf, upstream source, and the recorded-name index:
  no collisions in the namespace used here.
- Searched DAG definition nodes for constant/scalar models and
  `tools/blueprint_refs.py search 'constant model'` (no blueprint-node match).
  The notion is already part of sk-def-sfb-constructible, so its canonical construction
  helpers stay with this resolution; no independent duplicate definition node is added.

Validation: the complete module passed the prescribed `scompile.py` wrapper, both its
sandbox and library-path checks, with no warnings or errors, within 4 seconds per file.
The final delivery dry run repeats compilation and maintainer preflight.

## Second reading by Q37

This is a separate sequential self-reading with the JSON and complete Lean module open;
the dispatcher explicitly prohibited starting another agent. The maintainer's independent
review remains the independent review of this delivery.

Rechecked every clause against the mapping above. The prime and finite extension are
explicit binders of the main theorem, both ring choices are covered, and T has no geometric
restriction. The scalar maps are actual module morphisms with all three exactness clauses.
The sheaf maps are their functorial images, never independently supplied maps. The free
terms are finite regular-module biproducts up to isomorphism; the actual image sequence
and augmentation remain specified before that coordinate identification. All degrees
except -1 and 0 are zero, and the two component equations identify the differential and
degree-zero augmentation. The rational flag forces a=0. During this reading I added the
explicit rational final-term finite-free clause, and made all finite-extension binders
explicit in the main theorem signature. I also checked that the constant scalar ring
appears before the extension to continuous coefficients, so no discrete/continuous
coefficient conflation occurs. No statement correction, disputed statement, or extra
hypothesis was found.

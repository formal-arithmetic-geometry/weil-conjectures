## Worker report

The module `Sheaf.SixFunctors.SchemeGeometricFrobenius` defines the specified comparison
`WeilConjectures.PurityFiniteSetting.schemeGeometricFrobeniusComparison` as actual
natural-isomorphism data. It also exposes the two square comparisons and states the
factorization, the geometric assertions about both squares, and the exact compatibility
of kappa with the given morphism. Every declaration is listed in `lean.declarations`.
There are no new nodes, dependency repairs, statement corrections, or disputed statements.
The item's JSON changes only in `lean`.

### Hypotheses and clauses

- The global datum and finite coefficients are the single parameter
  `P : PurityFiniteSetting.{u}`. `P.field` has prime `p`, positive `a`, `q = p^a`,
  a finite base field of cardinality `q`, and its fixed algebraic closure. Its
  coefficient datum has prime ell different from p, a finite subextension of the fixed
  coefficient closure, and a positive level. The coefficient ring throughout is exactly
  `P.Ring = Padic.coefficientExtensionRing ... P.level`, the recorded quotient A_E,n.
- The models are `X₀ Y₀ : Over (Spec (CommRingCat.of P.field.k₀))`; the model map
  is `f₀ : X₀ ⟶ Y₀`. The square and compatibility theorems retain
  `[LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left] [IsSeparated f₀.left]` and
  `[SmoothOfRelativeDimension d (P.frobeniusMap f₀)]`, with `d : ℕ`. These are finite
  type and separatedness of f0 and smoothness of relative dimension d of its base change.
  No assumption on either structure morphism is added. The component constructions and
  factorization are defined for arbitrary models, as the node explicitly requests.
- `P.frobeniusFiber T₀` abbreviates the object part of the recorded `Over.pullback`
  functor at `Spec.map (algebraMap k₀ k)`. Its underlying scheme is exactly
  `T₀ ×_{k₀} k`, with its second projection as structure map. `frobeniusMap f₀`
  abbreviates the underlying morphism of that functor's image of f0.
- Gamma is the existing `FiniteField.geometricFrobeniusAlgEquivOfAlgebraic` at the
  fixed closure; its inverse is arithmetic Frobenius sigma. The `Fintype.ofFinite`
  parameter enumerates the already finite base field without restricting the datum.
  `frobeniusGaloisMap` and `frobeniusArithmeticMap` abbreviate the dependency's actual
  unrestricted `galoisMap` at these two automorphisms. They are therefore exactly
  id times Spec(gamma) and id times Spec(sigma), with the existing projection and
  inverse equations, including semilinearity. These abbreviations introduce no new
  version of geometric Frobenius.
- `frobeniusSchemeMap` is the image under the same `Over.pullback` functor of
  `Over.homMk (T₀.left.iterateFrobenius ... P.field.a) (model_frobenius_over ...)`.
  This is the actual base change of absolute q-power Frobenius, without an
  absolute finite-type assumption. It expands to the recorded relative Frobenius
  definition when that definition's more restrictive model hypotheses hold.
- `frobeniusAbsoluteMap` is `Scheme.iterateFrobenius` on the base-changed scheme,
  with exponent a and characteristic obtained through its first projection to the
  model. It is the absolute map F_T^(q), rather than the k-linear Phi_T.
- `schemeGeometricFrobenius_factorization` states BOTH arithmetic factorizations
  `F = g_sigma ≫ Phi` and `F = Phi ≫ g_sigma`. Its final equality
  `Phi = F ≫ g_gamma` supplies the domain identification in the comparison definition.
  This is Lean composition order; the last equality says Phi = g_gamma composed with F.
- `schemeGeometricFrobenius_squares` states that both geometric-Galois maps are
  isomorphisms, that their square is `IsPullback gX f f gY`, and that
  `gX ≫ f = f ≫ gY` and `PhiX ≫ f = f ≫ PhiY`. It asserts no Cartesian property
  for the second square. Its remaining clauses give universal homeomorphism of each
  ABSOLUTE map and `F.Etale.IsEquivalence`, the recorded small-etale-site invariance.
  The final two clauses assert that the canonical `Scheme.etaleSetPullback`
  functors are equivalences of the small etale topoi. The covering consequence is
  supplied by the imported recorded
  `Etale.universalHomeomorphism_invariance`; it is not used to select pro-etale data.
- `frobeniusOrdinaryComposition` selects the composition family of the recorded
  arbitrary-pullback Frobenius theorem. The theorem fixes its conjugate direct-image
  comparison on EVERY section to the fibre-product-pasting map, and uses the actual
  normalized module adjunctions. Thus it determines the ordinary comparison uniquely,
  rather than merely asserting Nonempty. `frobeniusDerivedComposition` is exactly its
  `proEtaleFrobeniusDerivedComp` descent. By the dependency's section/adjunction
  normalization and the K-flat normalization, this is the composition comparison of
  `lem-weil-pbc-proetale-derived-pullback-composition` specialized to constant rings.
- `frobeniusAbsoluteTrivialization` selects tau from that SAME dependency theorem
  and applies `proEtaleFrobeniusDerivedIso`. The relative-Frobenius projection equation
  determines r: its other projection is fixed because it is an arrow over T. This
  determines r and its inverse uniquely by the fibre-product universal property.
  The section-unit equation then uniquely determines the ordinary module tau through
  the fixed adjunction; exact descent determines the derived tau. Consequently choosing
  these fully normalized witnesses satisfies the project's prohibition on arbitrary
  isomorphism choices. Its characteristic pair is built from the existing prime and
  restriction-of-global-characteristic theorems, without a new axiom or assumption.
  Finiteness of A_E,n is supplied by `Padic.finite_coefficientExtensionRing`, not by an
  additional binder on P.
- The main definition `schemeGeometricFrobeniusComparison T₀` is precisely
  `eqToIso (congrArg Lpullback factorization)`, followed by the canonical composition
  comparison for `(F_T, g_T,gamma)`, then `isoWhiskerLeft Lg* tau`, then `rightUnitor`.
  Its type is `L Phi_T* ≅ L g_T,gamma*`. This fixes both kappa_X and kappa_Y explicitly.
- `frobeniusGaloisSquareComparison` and `frobeniusSchemeSquareComparison` define c_g
  and c_Phi from the inverse composition comparison, the respective commutativity
  equality, and the forward composition comparison. Neither is an arbitrary iso.
- `schemeGeometricFrobenius_naturality` states the exact equality
  `whiskerRight kappa_Y.hom Lf* ≫ c_g.hom =
   c_Phi.hom ≫ whiskerLeft Lf* kappa_X.hom`.
  Both sides have source `L Phi_Y* ⋙ Lf*` and target `Lf* ⋙ Lg_X*`.
  Reading functor composition in mathematical order, this is precisely the last
  displayed natural-transformation equality in the node, including both identifications.

### Dependencies read and used

The full statements and Lean records of all fifteen statement dependencies were read,
as were the recorded signatures and docstrings. The convention-only morphism-properties
node introduces no declaration. The following interfaces supply the actual objects:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`, `.Ring`.
- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`: `FiniteFieldDatum.galoisMap`,
  `galoisMap_inverse`, and its projection equations, plus the existing field Frobenius.
- Its imported `RelativeFrobeniusGeometricFiber`: `model_characteristic`,
  `model_frobenius_over`; `WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius`:
  `Scheme.iterateFrobenius`, `natCast_eq_zero_of_natCast_top_eq_zero`.
- Mathlib `AlgebraicGeometry.Over` and `CategoryTheory.Over.pullback`: schemes over
  the base, chosen scheme fibre products, and base change of their morphisms.
  The base-change dependency's record expressly directs scheme-base-change consumers
  to these constructions, rather than its primary declaration for module base change.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `SmoothOfRelativeDimension`.
  The finite-type and separated classes are Mathlib's recorded scheme properties.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: `proEtaleDerivedCategory`;
  `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`:
  `proEtaleConstantRingPullback`, `proEtaleConstantRingDerivedPullback`, and the
  normalized adjunction used in the dependency's canonicality characterization.
- `Sheaf.AlgebraicGeometry.FrobeniusTrivializationPullback`:
  `absoluteFrobenius_proEtale_trivialization_pullback`; its imported
  `AbsoluteFrobeniusSite`: `proEtaleFrobeniusDerivedIso`, `proEtaleFrobeniusDerivedComp`.
- The stated proof imports are the recorded modules `FrobeniusSquareCartesian`,
  `AbsoluteFrobeniusUniversalHomeomorphism`, `UniversalHomeomorphismInvariance`, and
  `ProEtaleCanonicalPullbackComposition`. The affine-spectra proof dependency is a
  Mathlib leaf, `AlgebraicGeometry.pullbackSpecIso`, already available through the
  imported geometric-fibre modules. No nonexistent project module is assumed for it.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` supplies the already recorded
  coefficient-extension notion's finite-quotient theorem at the positive level.

The small pro-etale site retains objects in u+1 and morphisms in u; module values are
in u+1 and coefficients are the canonical ULift of P.Ring. No universe equality is added.
There are three postponed theorems, all embedded assertions of this same definition node:
`schemeGeometricFrobenius_factorization`, `schemeGeometricFrobenius_squares`, and
`schemeGeometricFrobenius_naturality`. Each has `sorry` only, the source/blueprint tag,
and a full proof plan in its docstring. No definition has sorry data.

### Edge cases and searches

Empty schemes are retained, including the zero section ring: characteristic is obtained
by restriction rather than a nontriviality instance. The identity of an infinite disjoint
union of Spec(k₀) tests the absence of any absolute finite-type hypothesis. For Spec(k₀),
Phi is identity while g_gamma is generally nontrivial; the definition compares their
pullbacks through tau instead of equating the scheme maps. Nonreduced models such as
Spec(k₀[epsilon]/epsilon^2) test that absolute Frobenius need only be a universal
homeomorphism. For affine space over Spec(k), the scheme-Frobenius square is generally
not Cartesian, and no such clause occurs. Relative dimension zero and empty fibres are
allowed. The node has a>=1 and n>=1 through P; no illicit a=0 or n=0 hypothesis is added.

Authentic searches are in sandbox `searches.jsonl`. LeanFinder query `scheme and
geometric Frobenius of a purity datum` returned arithmetic Frobenius/perfection and
Witt-vector declarations, with no exact match. Loogle query `geometricFrobenius,
iterateFrobenius, IsPullback` returned unknown identifier geometricFrobenius, and thus
supplied no positive match. Mathlib and source grep queries
`geometricFrobenius|SchemeGeometricFrobenius` returned no exact package. LeanSearch
query `The base change of scheme Frobenius and geometric Galois Frobenius have a
canonical natural comparison of derived pro etale pullback functors` returned
`pullbackComparison`, finite field Frobenius, and ordinary scheme-module pullback
comparisons; those are not this constant-coefficient pro-etale statement.
Direct rg over upstream WeilConjectures, side Sheaf, and dag/lean_names_upstream.json
for the node id and the proposed main/naturality declaration names returned no hits.
The earlier broad Frobenius source inspection found the existing geometric-Galois
construction, whose docstring explicitly leaves the scheme/Galois comparison as TODO,
and trace-formula relative-Frobenius maps, which do not supply this comparison/naturality.
The delivered helper abbreviations use those existing constructions without introducing
private versions of their notions.

Validation: the complete delivered module passed scompile.py both as a sandbox file and
at its final module path, without errors or warnings (5.1 s and 5.6 s). No global build,
proof completion, live source edit, or delivery push was performed. Required dry-run
validation is performed after this report is written; its terminal result accompanies
this worker's one-line response. The independent second reader writes their own reading.

Process note: early discovery included read-only Git commands in the shared clone and
searches outside the directories authorized in the brief. That was a mistake; it caused
no shared file edits. Subsequent source work used the specified read-only paths, all
writes stayed in this item's sandbox, and all compilation used scompile.py.

## Second reading by Q102

I read the item node, its current `main-20261015` source place, the Stacks Frobenius
lemmas used there, and the complete Lean module. The node's step-1 list and the Lean
rendering are as follows.

- The fixed global datum is the single `P : PurityFiniteSetting.{u}`. Its `field`
  supplies `(p,a,q,k₀,k)`, and its coefficient datum supplies `ell`, `E`, and `n`;
  the coefficient ring is exactly `P.Ring`. This is rendered by
  `PurityFiniteSetting`, `PurityFiniteSetting.Ring`, and the corresponding fields
  used by `schemeGeometricFrobeniusComparison`. Verdict: exact.
- `X₀` and `Y₀` are objects of `Over (Spec (CommRingCat.of P.field.k₀))`,
  `f₀ : X₀ ⟶ Y₀`, and the scalar extensions and map are `frobeniusFiber` and
  `frobeniusMap`. The square theorem adds `[LocallyOfFiniteType f₀.left]`,
  `[QuasiCompact f₀.left]`, `[IsSeparated f₀.left]`, and
  `[SmoothOfRelativeDimension d (P.frobeniusMap f₀)]`, exactly expressing
  finite-type separated `f₀` and smooth base change of relative dimension `d`.
  No structure-map finiteness is added. Verdict: exact.
- `g_{T,γ}` and its inverse are `frobeniusGaloisMap` and
  `frobeniusArithmeticMap`, using the existing geometric Frobenius algebra
  equivalence and its inverse. Verdict: exact object and convention.
- `Φ_T` is `frobeniusSchemeMap`, the base change of the model's `q`-power
  `iterateFrobenius`; `frobeniusAbsoluteMap` is the absolute `q`-power map on the
  scalar extension. Verdict: exact distinction and construction.
- The first square is rendered by `IsPullback` together with both `IsIso` clauses
  and the commutativity equality in `schemeGeometricFrobenius_squares`. The second
  square is rendered only by its commutativity equality; no Cartesian assertion is
  present. Verdict: exact.
- `schemeGeometricFrobenius_factorization` states both arithmetic factorizations
  `F = g_σ ≫ Φ` and `F = Φ ≫ g_σ`, plus `Φ = F ≫ g_γ`; these are the affine
  factorization and the geometric comparison required by the node. Verdict: exact.
- The two absolute maps have `IsUniversalHomeomorphism`, their `Etale` maps and
  canonical `Scheme.etaleSetPullback` maps have `IsEquivalence`, as required by the
  universal-homeomorphism/étale-site paragraph. Verdict: exact, with no
  finite-type assumption on the structure maps.
- For finite coefficients, all derived pullbacks are
  `proEtaleConstantRingDerivedPullback P.Ring`. `frobeniusOrdinaryComposition`
  uses the normalized absolute-Frobenius comparison family, and
  `frobeniusDerivedComposition` and `frobeniusAbsoluteTrivialization` descend
  those normalized comparisons. `schemeGeometricFrobeniusComparison` is the
  explicit composite `eqToIso` (factorization), composition comparison, τ, and
  right unitor. Verdict: exact canonical κ construction; no arbitrary map is
  introduced.
- `frobeniusGaloisSquareComparison` and `frobeniusSchemeSquareComparison` are the
  two square identifications, and `schemeGeometricFrobenius_naturality` states
  `whiskerRight κ_Y ≫ c_g = c_Φ ≫ whiskerLeft κ_X`, which is precisely the
  node's `Lf* κ_Y = κ_X Lf*` after the two pullback-composition identifications.
  Verdict: exact order and domains.

The Stacks source checks impose only characteristic `p` for absolute Frobenius being
a universal homeomorphism and give commutation of relative Frobenius with arbitrary
scheme maps. The aligned blueprint source supplies the finite-type separated and
smooth-base-change hypotheses used by this node. Empty schemes and zero rings are
covered by the characteristic and Frobenius declarations; no nonemptiness is assumed.
The cases `a = 1`, relative dimension `0`, empty fibres, identity morphisms, and
nonreduced schemes remain included. An infinite disjoint union of affine models shows
that no absolute finite-type assumption on `X₀` or `Y₀` was added. The `Spec(k₀)`
case keeps `Φ` and `g_γ` distinct and is handled by κ.

I reran the required searches. LeanSearch for a scheme/geometric Frobenius comparison
returned only generic Frobenius and category-theory declarations; Loogle returned no
`IsPullback` match for the query; grep for `geometricFrobenius|SchemeGeometricFrobenius`
returned no match in Mathlib. Direct `rg` over the project source and upstream-name
index likewise found no existing declaration. Thus this is not a duplicate notion.

No mismatch was found and no source, node, or Lean repair was necessary. The node's
`lean.statement` is verbatim the main definition signature. The module has no hollow
definition, all postponed assertions use `sorry`, every declaration carries the source
and `(blueprint: def-pur-scheme-geometric-frobenius)` documentation, and no variable or
universe is implicit. The module compiled cleanly with `scompile.py` before this second
reading; I recompile it below and then run the delivery preflight.

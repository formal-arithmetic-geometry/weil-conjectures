## Worker report

`Sheaf.AlgebraicGeometry.LisseLatticeFiniteEtaleDescent` states
`AlgebraicGeometry.ProEtale.exists_lisse_lattice_finite_etale_descent` with `sorry`.
Its docstring gives all six steps of the node's proof, including the inverse-image
slice identification, finite sum of sheet lattices, pointwise DVR calculation,
permutation independence on overlaps, and module sheaf gluing. No new definition
or additional postponed theorem is introduced. The natural-language statement is
unchanged. The already landed node `lem-weil-pbc-lisse-lattice-etale-local` is added
to `stmt_deps` to cite the existing continuous coefficient sheaves and slice maps.

Clause-by-clause reading:

- The prime is `(l : ℕ) [Fact l.Prime]`. The finite extension is `(E : Type)
  [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. This is precisely the
  existing continuous-coefficient API's coefficient universe; the scheme universe
  `u` remains arbitrary. The canonical spectral norm defines the topology in
  `lisseFieldSheaf` and `lisseIntegerSheaf`. The latter uses
  `Padic.coefficientExtensionIntegers l E`, with its induced topology. A uniformizer
  is already provided by `Padic.coefficientExtensionUniformizer`; no choice of it
  occurs in this assertion, so the assertion is independent of that choice.
- `(X : Scheme.{u})` supplies the scheme. Its small pro-etale site is
  `Scheme.ProEt.topology X` on `X.ProEt`, with object universe `u+1` and Hom
  universe `u`. Modules and coefficient rings use universe `u+1` throughout.
  The coefficient sheaves are the existing `lisseFieldSheaf l E X` and
  `lisseIntegerSheaf l E X`: sections are `ULift C(|V|, E)` and
  `ULift C(|V|, A)`, with pointwise operations and restriction by composition.
  The ULift changes only size. Forgetting commutativity uses `sheafCompose`.
- `[TopologicalSpace.NoetherianSpace X]` is exactly noetherianity of the underlying
  space. In particular it does not require locally noetherian local rings.
- `L : ringedSiteModules ... (lisseFieldSheaf ...)` gives the E_X-module sheaf;
  `hL : L.IsFiniteLocallyFree` uses the existing general-site local-generators
  definition. Its finite generator set is allowed to depend on the covering
  member, and is allowed to be empty. It therefore gives precisely the stated
  finite locally free condition, without a fixed positive rank.
- `{Y : Scheme.{u}} (p : Y ⟶ X) [IsFinite p] [Etale p] [Surjective p]` expresses
  a finite etale surjection. These are the exact morphism properties used in
  `(@IsFinite ⊓ @Etale).Over ⊤ X`, the category in the dependency's Mathlib match.
- `hM : ∃ M : ringedSiteModules ... (lisseIntegerSheaf l E Y), ...` is existence
  of the integral module on Y. Its first conjunct is `M.IsFiniteLocallyFree`.
  Its second is `Nonempty ((SheafOfModules.changeOfRings ... M).val ≅ ...)`.
  Here the map is `lisseIntegerToField`, the coefficient inclusion on continuous
  functions; `changeOfRings` is sheafification of E_Y tensor over A_Y with M.
- The right side of that isomorphism is
  `(PresheafOfModules.pushforward (lisseEtaleCoefficientIdentification l E p)).obj
  L.val`. Despite the generic API name `pushforward`, its underlying site functor
  is `lisseEtaleSiteInclusion p : Y.ProEt ⥤ X.ProEt`, so this is restriction
  along the inclusion of the slice, not geometric direct image along p. The
  coefficient identification is identity on continuous functions. For etale p,
  this is the canonical slice presentation of the actual inverse image. The
  representative/graph verification is explained in the theorem's proof plan.
  It uses the dependency's construction rather than choosing an arbitrary map.
- The conclusion is existence of `M₀` in A_X-module sheaves, with
  `M₀.IsFiniteLocallyFree` and
  `Nonempty ((SheafOfModules.changeOfRings (lisseIntegerToField l E X) M₀).val
  ≅ L.val)`. An isomorphism of underlying module presheaves gives exactly an
  isomorphism of module sheaves, since the forgetful functor is fully faithful.
  There is no descent datum on M and no assertion that the pullback of M₀ is M.

Dependency declarations used:

- `Sheaf.AlgebraicGeometry.LisseLatticeEtaleLocal`:
  `AlgebraicGeometry.ProEtale.lisseFieldSheaf`, `lisseIntegerSheaf`,
  `lisseIntegerToField`, `lisseEtaleSiteInclusion`, and
  `lisseEtaleCoefficientIdentification`. These are reused unchanged.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` (and its public import
  `CoefficientExtension`): `Padic.finite_coefficientExtensionRing`,
  `coefficientExtensionIntegers`, `coefficientExtensionUniformizer` and the
  spectral-norm topology used in the continuous sheaf construction.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory` and
  `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and its topology.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  the abbreviation for Mathlib's `SheafOfModules`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`, publicly
  importing `TensorProduct`: `SheafOfModules.changeOfRings`. Universe arguments
  are specified explicitly, as are those of `PresheafOfModules.pushforward`.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFree` and its local-generators interpretation.
- Mathlib's `AlgebraicGeometry.Scheme`, `IsFinite`, `Etale`, `Surjective`;
  `CategoryTheory.MorphismProperty.Over` gives the finite-etale category match.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: the repaired general
  `Scheme.proEtaleSheafInverseImage`, its index category, adjunction, and
  `proEtaleModuleInverseImage`. See the dependency repair below.

The stated proof dependencies are imported: finite-etale etale-local splitting,
site comparison, site covering axioms, the DVR theorem, module sheaf gluing, and
Mathlib's finite torsion-free modules over a PID. Statement dependencies already
publicly import the module and inverse-image interfaces needed by the proof.
The restriction-injectives node has no recorded Lean module, is not used in the
signature, and therefore has no import yet.

Edge cases checked: zero modules and rank zero use the existing finite local
freeness predicate (empty generator set); ranks may vary between covering
members; no connectedness, normality, or nonemptiness is assumed. On the empty
scheme the empty covering is permitted. A finite etale surjection over a nonempty
split chart has a positive number of sheets, without assuming a global constant
sheet number. The conclusion asks only for some lattice. Topological
noetherianity is not strengthened to `IsNoetherian X`. No `STATEMENT-DISPUTED`
issue or source-statement correction was found.

Searches performed before writing:

- `msearch.py ... leanfinder "Finite etale descent of existence of lisse integral
  lattice for continuous p-adic coefficient module sheaves"`: eight unrelated
  results, including BDeRham constructions, solid condensed modules and
  `CondensedMod.ofSheafProfinite`; none states this assertion.
- `msearch.py ... loogle '"Sheaf", "lattice"'`: five lattice-order constructions
  for sheaves/submodules, not integral lattices.
- `msearch.py ... leansearch "A locally free sheaf over continuous p-adic
  coefficients has an integral lattice if it does after finite etale surjective
  pullback"`: service returned Internal Server Error; not used as evidence of
  absence.
- `msearch.py ... grep 'invariant.*lattice|lattice.*invariant|LocallyFree.*[Ee]tale'`:
  eight hits about invariant submodule lattices, elliptic invariants and root
  systems, none about the present assertion.
- Direct `rg` in both upstream `WeilConjectures/` and project `lean/Sheaf/`, for
  `lisse|Lisse|locally free|locallyFree`, coefficient pullback, and
  `lattice-finite-etale|Lisse.*Integral|Integral.*Lisse|isLisse.*lattice`:
  found the existing continuous sheaves in `LisseLatticeEtaleLocal`, general
  finite-local-freeness, and adic-system lisse sheaves with a different notion.
  No existing finite-etale lattice descent theorem was found. Searching the
  exact node id in upstream sources likewise found no existing declaration.
- Read the local Bhatt--Scholze PDF, Definition 6.8.1, Definition 6.8.3,
  Proposition 6.8.4 and the first paragraph of Lemma 6.8.13, together with
  the node's six-step refinement. The definitions and assertion agree.

Validation: the two delivered modules were compiled individually, in dependency
order, by `scompile.py` against the side-project overlay. Both compile cleanly;
only the intended main theorem proof is postponed. No global build was run.

## Dependency modules

`def-weil-proetale-inverse-image`: its latest primary record exposes a
constant-coefficient module pullback, which cannot itself supply inverse image
of a continuous-function coefficient sheaf. The existing general construction
in `Sheaf.AlgebraicGeometry.ProEtaleInverseImage` does supply it. However, that
file imported `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`,
while the continuous-function framework imports the general upstream version.
Combining them produced duplicate declarations, including
`AlgebraicGeometry.ProEtale.lowerStarComp`. This delivery preserves every
construction in the general inverse-image file and replaces only its
finite-coefficient framework import by
`WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs`; it also explicitly
sets `autoImplicit false`. The repaired file compiles with the existing unmodified
continuous coefficient module. The node's only changed field is `lean`, with a
note and all declarations of this owning module listed. The separate
larger-universe constant-coefficient module and its declarations remain unchanged
and available. This repair adds no axiom, no arbitrary comparison map and no
new sorry. It retains the small site's object universe `u+1` and Hom universe `u`.

## Second reading by NY

I read the item's node and Lean module independently, all nine statement-dependency
records and their defining declarations, and the delivered inverse-image dependency
module. I also read Bhatt--Scholze Definition 6.8.1, Definition 6.8.3,
Proposition 6.8.4 and Lemma 6.8.13 in the obtained PDF. Section 6.8 starts with an
arbitrary scheme; the additional hypothesis in Lemma 6.8.13 is topological
noetherianity. Its first paragraph passes to a finite etale cover of a stratum
before obtaining a lisse lattice. This item isolates that intermediate assertion,
not the final constructible lattice assertion. The node's explicit sum-of-sheet
proof avoids adding the connectedness chosen in the paper's representation
argument. I read Stacks `etale.tex`, lemma-finite-etale-etale-local (04HN),
`sites.tex`, lemma-glue-sheaves (04TR), and `proetale.tex`, section-morphism
(09A5), together with the presheaf inverse-image indexing construction in
`sites.tex`, section-functoriality-PSh. None adds a noetherian-local-ring,
separatedness or characteristic assumption to this assertion.

The object/hypothesis/conclusion checklist is as follows; each verdict is a match.

1. A prime ell: `(l : ℕ) [Fact l.Prime]`. The finite field extension is
   `(E : Type) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`.
   The last hypothesis is vector-space finiteness, not a finite-type ring
   hypothesis. I opened `CoefficientExtension` and `ExtensionIntegersDvr`:
   `coefficientExtensionAbsoluteValue` is the spectral absolute value, and
   `coefficientExtensionIntegers` is the subring characterized by absolute value
   at most one in the DVR theorem. That characterization determines the subring;
   it is not a hollow choice of arbitrary data. A uniformizer is available from
   the same dependency but unused in this assertion, so no uniformizer condition
   is lost by omitting it from the binders.
2. The scheme and its small pro-etale site: `(X : Scheme.{u})`,
   `Scheme.ProEt.topology X`. I opened Mathlib's `Scheme`, `Scheme.ProEt`,
   its `precoverage` and `topology`, and `ProEtaleDerivedCategory`.
   Objects are weakly etale schemes over X with all X-morphisms; the topology
   is the pro-etale topology, not the small etale topology. The continuous
   coefficient sheaves here are not that dependency's constant ring sheaves.
3. The coefficient rings A_X(V) = C(|V|, A) and E_X(V) = C(|V|, E):
   `lisseIntegerSheaf l E X` and `lisseFieldSheaf l E X` from the landed
   `LisseLatticeEtaleLocal` module. I opened all six helper definitions there
   and the upstream `continuousMapRingPresheaf`/map construction in the
   group's framework. Sections are ULifts of precisely these continuous maps;
   ring operations are pointwise and restrictions are precomposition.
   The spectral-norm instance supplies the canonical field topology, and A has
   the subspace topology. Forgetting commutativity by `sheafCompose` preserves
   those section rings. No second coefficient construction is introduced.
4. Topological noetherianity: `[TopologicalSpace.NoetherianSpace X]`.
   Mathlib defines this as `WellFoundedGT (Opens X)`, exactly the ascending
   chain condition in the node. There is no assumption on the local rings.
5. The E_X-module L: the displayed `ringedSiteModules` binder, with
   `(hL : L.IsFiniteLocallyFree)`. `ringedSiteModules` is transparently
   `SheafOfModules`. I opened the upstream finite-local-freeness class and
   Mathlib's `LocalGeneratorsData`, `IsLocallyFreeData` and `IsFiniteType`:
   they assert a cover of the final object with invertible maps from free
   modules on finite generator sets. Finiteness is per covering member, so
   the rank may vary and may be zero, exactly as the node specifies.
6. The cover: `{Y : Scheme.{u}} (p : Y ⟶ X) [IsFinite p] [Etale p]
   [Surjective p]`. These are the finite/etale properties in the finite-etale
   category's recorded Mathlib specialization. `Surjective` is surjectivity
   on underlying points. There is no Galois, constant-degree or connectedness
   assumption.
7. The premise lattice: `hM : ∃ M : ringedSiteModules ...,
   M.IsFiniteLocallyFree ∧ Nonempty (...)`. Its coefficient sheaf is A_Y.
   `SheafOfModules.changeOfRings (lisseIntegerToField l E Y) M` is
   sheafification of sectionwise scalar extension E_Y tensor over A_Y with M.
   I opened `changeOfRingsPresheaf` and `changeOfRings` rather than inferring
   their meanings from the names. This is the sheaf tensor of Stacks 03EK.
8. The premise isomorphism to p-inverse L: its right side is
   `(PresheafOfModules.pushforward
   (lisseEtaleCoefficientIdentification l E p)).obj L.val`.
   I opened Mathlib's `pushforward₀` and `pushforward`: this is
   precomposition with `lisseEtaleSiteInclusion p`, followed by restriction
   of scalars through the identity on continuous functions. On V over Y it
   is L evaluated on the same V regarded over X, with the identical E-section
   action. For etale p this is the slice presentation of inverse image.
   The node and theorem docstring give the actual comparison with the
   inverse-image colimit: restrict a representative along V to Z, and use
   Z = V with its graph for the inverse. Their composite is identified by
   the indexing-category restriction. Thus no arbitrary comparison or map is
   assumed. Module operations commute with these section restrictions.
   The isomorphism is linear over E_Y, not just an isomorphism of sets.
9. The conclusion is `∃ M₀ : ringedSiteModules ...,
   M₀.IsFiniteLocallyFree ∧ Nonempty (...)`, now over A_X, with
   `changeOfRings (lisseIntegerToField l E X) M₀` isomorphic to L.
   Both sides are underlying module presheaves of sheaves; the fully faithful
   forgetful functor identifies this with an isomorphism of module sheaves.
   The existential conclusion has no reference to the specified M and adds
   no compatibility with M after pullback. The order of the independent L
   and p binders has no mathematical effect; hM precedes the existential M₀.

Edge cases: finite generator sets may be empty, so the zero module and rank zero
are included. There is no nonempty covering-index or positive-degree binder.
The empty scheme admits the empty cover; a surjection from the empty scheme to
a nonempty X is correctly excluded by `Surjective p`. Cover degree and ranks may
vary. Every prime is allowed, with no condition relating ell to the residue
characteristics of X. The scheme universe u is arbitrary. The small site has
objects in u+1 and morphisms in u; both delivered modules retain this difference,
and the module/ring sections lie in u+1. E uses the existing framework's small
coefficient convention (`Type`); finite extensions of the small field Q_l have
small models by a finite basis, so this does not restrict the finite extensions
under discussion. No equality of site universes or connectedness instance is
added.

For H13 I read the whole delivered `ProEtaleInverseImage` module against
`def-weil-proetale-inverse-image` and its Stacks source. Its base change is
`MorphismProperty.Over.pullback @WeaklyEtale ⊤ f`; its direct image is
precomposition with this base change. Its inverse image is the constructed
left Kan extension followed by sheafification, and its index is
`StructuredArrow U (proEtaleBaseChange f)` (the colimit uses the opposite).
The unit/counit and constant-section maps give the specified adjunction and
coefficient structure map. Module inverse image uses this unit on the AsSmall
model and transports back; this only enlarges Hom types, keeping every site
object. Constant-coefficient pullback subsequently applies the stated sheaf
change of rings. Each definition has real data. Comparing against the recorded
source file confirms that the worker changed only the finite-coefficient
framework import to the general framework import and added `autoImplicit false`.
That import repair is needed because the continuous-function framework already
uses the general framework and the alternative imports duplicate names. The
latest coefficient-sized constant-pullback module is still present and is not
rewritten. The dependency's mathematical statement is unchanged. No new
independent notion or new node is needed.

Independent searches, with different wording from the worker:

- LeanFinder: "A finite locally free sheaf of continuous p-adic modules admits an
  integral form if its restriction to a finite covering does". Eight results
  concern finite local generators or finite presentations; none states this
  integral-lattice assertion.
- Loogle: `"SheafOfModules", "LocallyFree"`. Eleven results give the existing
  local-freeness and local-generator interfaces; these are correctly reused.
- LeanSearch: "Existence of integral lattices in locally free sheaves descends
  along finite etale covers". The service returned Internal Server Error;
  this is not evidence of absence.
- Wrapper grep: `stable.*lattice|lattice.*stable|integral.*form|finite.etale.*descent`.
  Results concern ordinary integrals, root systems and algebraic integral
  closure, not the asserted theorem. Direct rg in Mathlib, upstream
  WeilConjectures and project Sheaf, also using `lisse.*descent`,
  `lattice.*descent`, `integralForm` and `lattice`, found the existing etale-local
  lattice helpers, representation-lattice results, and
  `isLisseEtaleSheafOfSets_of_etale_surjective_pullback`. I opened that last
  theorem: it is about finite set sheaves on the etale site and says nothing
  about integral structures over continuous coefficient rings. It is not a
  match. There is no existing exact theorem to attach instead.

No mathematical mismatch was found, so I preserved both Lean files and both node
records. The main node's `lean.statement` is verbatim its theorem signature.
The dependency record gives its exact abbreviation signature and lists the
owning module's declarations. No statement correction or citer audit is required.
All six natural-language proof steps are present in the theorem docstring,
including injection into L, local constancy of the sheet lattices, the DVR
finite-free calculation, permutation independence, gluing and rationalization.
Every declaration in the delivery has its source/blueprint docstring, all binders
and universes are bound, and the only postponed proof is the main theorem.

I compiled both sibling files separately through `scompile.py`, in dependency
order. The wrapper checked both the sandbox and library presentations cleanly,
with no errors or other warnings. No global build or direct live-source edit was
performed. The second reading changes only this review report.

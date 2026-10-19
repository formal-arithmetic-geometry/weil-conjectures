## Worker report

The delivery states `AlgebraicGeometry.ProEtale.CondensedRing.integralProperProjectionFormula`
in `Sheaf.Paper.IntegralProperProjectionFormula`. The item statement, proof and existing
statement dependencies are unchanged; one definition dependency is added to expose the
canonical module-object map that the item names. The item theorem proof is `sorry`; the helper contains only a concrete definition.
The definitions contain actual terms. No assertion is marked STATEMENT-DISPUTED.
The resolved stage-1 repair note was read: it concerns the already completed split of
proof step 7, not a withdrawn stage-2 interface. That nine-step DAG proof is preserved.

Hypotheses and clauses:

- The prime ell is `(ℓ : ℕ) [Fact ℓ.Prime]`. The finite extension inside the chosen algebraic
  closure is `(E : PadicAlgCl.FiniteIntermediateField ℓ)`. Its coefficient object is exactly
  `Profinite.padicIntegersRingObj ℓ E.val`, the condensed valuation ring, not a discrete ring.
- The base is `(k : Type u) [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]`. Prime characteristic states precisely positive characteristic
  for a field; it includes characteristic 2 when ell differs from 2.
- `X` and `Y` are arbitrary `Scheme.{u}`, with `Over (Spec (.of k))`. Each structure map has
  `LocallyOfFiniteType`, `QuasiCompact` and `IsSeparated`, rendering separated finite type.
  The scheme morphism is `(p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]`.
- The ambient types are `DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T)
  Ab.{u + 1}) (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) T))`.
  Thus they are the small pro-etale site, pulled-back coefficients and ordinary
  unbounded derived categories of internal modules, with no completeness hypothesis.
- The first conjunct quantifies over all such K on X and L on Y. Its two hypotheses are
  `constantModelBoundedConstructible ... X K` and the corresponding predicate on Y.
  Its conclusion `IsIso (moduleObjectProjectionMap ... p K L)` is clause (1).
- The middle conjunct quantifies over EVERY standing `T`, with its own scheme-over-k,
  separatedness and finite-type instances, and every pair K,L in its ambient derived
  category. The two membership hypotheses and conclusion use
  `CategoryTheory.localizingClosure (constantModelBoundedConstructible ... T)`.
  The output object is `((derivedTensor ... T).obj K).obj L`. This is exactly tensor
  closure in clause (2), independently of the chosen proper map's source and target.
- The last conjunct quantifies over arbitrary ambient K,L with membership in the two
  corresponding closures, and concludes invertibility of precisely the SAME
  `moduleObjectProjectionMap` as the first conjunct. No bound, finite Tor condition,
  derived completeness, or extra witness is imposed on these K,L.
- The map is the existing `Adjunction.rightAdjointProjectionMap` for
  `derivedUpperStarLowerStarAdjunction`, `derivedTensor` and the generic
  `CondensedRing.leftDerivedUpperStarTensor`. Its transpose is the
  comparison followed by counit tensor identity, in exactly the order in the node.
  The helper uses the published `leftDerivedUpperStarTensor`, characterized by its
  derived counits and the signed total of the ordinary tensorator.

Dependency declarations read and used:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField`. This encodes the
  standing over-field convention; the theorem spells the setting out with binders.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.coefficientRing`, `condensedRingObj` and its commutativity.
  `coefficientRing` is actual monoidal inverse image from the point.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`:
  `CondensedRing.derivedUpperStarLowerStarAdjunction` and the generic total derived
  functors of the actual underived module-object composites.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `AlgebraicGeometry.ProEtale.constantModelBoundedConstructible`. This is the recorded
  sk-def-sfb-constructible notion. The upstream `boundedConstructible` uses a different
  arbitrary-matrix constructibility predicate; the theorem does NOT substitute it.
- `Sheaf.Paper.LocalizingClosure`: `CategoryTheory.localizingClosure` and
  `IsLocalizingSubcategory`. The generic closure applies directly to Dbc, as required.
  `localizingClosureProEtale` specializes instead to Dctf and is therefore not used.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom` and its tensor import:
  `CondensedRing.derivedTensor`, the K-flat relative monoidal tensor and its internal Hom.
- `Sheaf.Paper.ProjectionMateExact`: `SheafOfModules.ringedProjectionMateExact` and the
  canonical `derivedProjectionFormulaMate` built from `rightAdjointProjectionMap`.
  The ringed result is a proof import/interface, not a replacement coefficient category.
- The helper imports the LIVE `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal`,
  read through scompile.py --source. Its `leftDerivedUpperStarTensor` is the actual
  two-variable derived lift, with `leftDerivedUpperStarTensor_fac` and its representative
  description; `leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison` identifies it
  with the generic derived comparison. No monoidal construction is repeated.

The recorded proof modules that are stated are imported, including IntegralTensorInverseImage,
RingedProjectionFirstShift, KFlat and the relevant Mathlib shift/triangulated/geometry modules.
The following proof prerequisites have no usable recorded Lean statement on this base and
are not imported merely by inventing module names: det-def-localizing-closure-ctf-equals-bc,
det-def-localizing-closure-existence, det-thm-sfb-proper-base-change-integral,
det-proper-base-change-unbounded-pullback, det-proper-image-localizing-proper,
lem-pd-module-ringed-topos-derived-comparison. They are proof-only prerequisites, and the
statement needs no theorem from them. The docstring retains every proof step and citation.

Edge cases checked mathematically before writing: K=0 or L=0 gives a zero-to-zero map;
p=id yields the identity after the canonical comparisons; the empty scheme gives its
zero module category; E=Q_ell is allowed; no restriction on ell=2 beyond differing base
characteristic; unbounded objects, negative shifts, zero objects and empty ambient sums
are retained in the second clause. The middle conjunct really ranges over every T, not
only X,Y. All universes are bound and `autoImplicit false` is set. The inherited fixed
size convention is used without equating the site's object and morphism universes.

Searches for the item's statement: msearch LeanFinder query “Proper projection formula
for bounded constructible integral adic module objects and their localizing closure”
returned 8 unrelated adic-completion/local-cohomology declarations; Loogle
`DerivedCategory, "projection"` returned 0; Mathlib grep
`projectionFormula|ProjectionFormula|boundedConstructible` in AlgebraicGeometry/Sites
returned 0. LeanSearch “proper projection formula integral constructible pro etale derived
tensor” returned 8 unrelated ordinary scheme-pullback/properness declarations.
`rg` of the source WeilConjectures tree and shared Sheaf tree found finite constant-ring
projection theorems and abstract geometric-operation packages, not this internal-module
integral assertion; the exact node-id search in the source tree returned no declaration.
The current blueprint statement and proof and the local Stacks 03EL and 0943 texts were read.

## New nodes

`def-sfb-module-object-projection-map` supplies `Sheaf.Paper.ModuleObjectProjectionMap`.
It gives a name to the specified canonical derived adjoint-transpose map, using the
EXISTING live `CondensedRing.leftDerivedUpperStarTensor` and
`derivedUpperStarLowerStarAdjunction`, with `Adjunction.rightAdjointProjectionMap`.
There is one definition, no structure chosen, and no helper theorem or new sorry.
Sources: Stacks 03EL and 0943 and the current blueprint's canonical-map convention.

The new-node searches are recorded in its mathlib_searches: LeanSearch on canonical
strong monoidality of internal-module pullback returned ordinary module monoidal/free
functors and cartesian over-category results; LeanFinder on preservation of flat objects
returned ordinary ModuleCat flat tensor/extension statements; Mathlib grep for
`mapMod.*Monoidal|upperStar.*Monoidal|upperStar.*PreservesFlat` returned 0. Direct source and
Sheaf searches initially found no internal-module comparison in the stale local overlay.
Checking the LIVE source with scompile.py --source exposed
ModuleObject.Derived.Monoidal, so the drafted comparison/flatness helpers were REMOVED.
Its canonical `leftDerivedUpperStarTensor` is reused. The source accessor confirmed
there is no ModuleObject.Derived.LowerStarProjection or .ProjectionFormula module.
DAG/blueprint search found no existing definition of this map. The existing
lem-pd-module-ringed-topos-derived-comparison theorem mentions the implicit canonical map
but has no Lean interface defining it. This helper does not restate that full comparison
theorem. It only applies the existing generic adjunction mate to the existing comparison.

## Second reading by Q98

Author self-reading for direct delivery; the maintainer supplies independent review.
I reopened the DAG statement, all three conclusions in the module and the helper's
specification. Prime characteristic, unequal ell, finite extension, standing geometry,
k-linearity and properness appear as the binders listed above. The first and third
conclusions use identical canonical maps. The closure is of the recorded Dbc predicate,
not of the different upstream constructibility predicate or Dctf. Every T is quantified
in the tensor-closure clause. The tensors are the recorded ordinary relative tensors.
The helper was checked against the LIVE source of ModuleObject.Derived.Monoidal.
The comparison has direction Lf*(M tensor N) to Lf*M tensor Lf*N. The existing
right-adjoint projection map follows it by counit tensor identity before taking
the adjoint transpose, as stated in the item. A first draft duplicated an ordinary
monoidal interface absent locally; source-accessor inspection found its live
implementation and that duplicate was removed before delivery. No arbitrary map,
monoidal structure or flatness hypothesis remains. There is no statement correction
and no dependency record is replaced.

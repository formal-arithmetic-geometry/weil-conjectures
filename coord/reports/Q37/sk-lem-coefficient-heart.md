## Worker report

The module `Sheaf.Paper.CoefficientHeart` states `AlgebraicGeometry.ProEtale.coefficientHeart`.
Its four transparent assertion predicates spell out this one node's introduction,
three numbered conclusions, and curve specialization. They are logical conjunctions
and quantifiers with real bodies, not additional mathematical notions or unconstructed
objects. The only postponed proof is the named theorem `coefficientHeart`, with all
ten DAG proof steps and their dependencies in its docstring. No statement correction,
new node, dependency repair, or disputed assertion is needed.

I read the current blueprint unit `_section.md`, the complete node and proof, its
statement dependencies and their records, the available dependency source modules,
and `coord/pefw-upstream-framework.md`. The repair note is a resolved stage-1
re-splitting instruction; its requirement to preserve this unit's statement is respected.
The unit is its own blueprint unit. Its mathematical statement is unchanged.

Hypotheses and clauses:

- `ℓ : ℕ` with `[Fact ℓ.Prime]` is the fixed prime. `hL` is precisely the alternative
  that `L` is `padicSubfieldCondensedRing ℓ E` for a finite-dimensional intermediate
  field `E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)`, or is
  `padicAlgClCondensedRing ℓ`. In particular the algebraic-closure coefficient is the
  existing finite-subextension-valued sheaf, not all continuous maps into Qbar_l.
  `[IsCommMonObj (coefficientHeartRingObj L)]` records its commutative ring-object
  structure, with the existing canonical underlying monoid structure.
- `k : Type u`, `[Field k]`, `p : ℕ`, `[Fact p.Prime]`, `[CharP k p]`, and
  `hpℓ : p ≠ ℓ` render the standing positive-characteristic field and invertible
  coefficient prime. Positive characteristic of a field is prime, so this prime
  structure does not exclude a standing field.
- `[X.Over (Spec (.of k))]` is the standing scheme over k. The three structure-morphism
  instances are `LocallyOfFiniteType`, `QuasiCompact` (together finite type), and
  `IsSeparated`. There is no smoothness, reducedness, irreducibility, connectedness,
  properness, or extra Noetherian hypothesis.
- The theorem's explicit `IsNoetherian` structure uses exactly
  `LocallyOfFiniteType.isLocallyNoetherian` and
  `QuasiCompact.compactSpace_of_compactSpace` applied to the structure morphism.
  This is the recorded finite-type-over-Noetherian Mathlib interface. It provides
  the Noetherian instance needed by the closure construction without restricting X.
- Every sheaf is an internal `Mod` over `condensedRingObj Λ X`, where
  `Λ = coefficientHeartRingObj L`; all pullbacks and direct images are the recorded
  `CondensedRing.upperStar` and `CondensedRing.lowerStar`.
- The introductory equality Dctf = Dbc is equality of the actual ambient object
  predicates: `constantModelBoundedConstructible Λ X ⊓
  DerivedCategory.finiteTorAmplitude _ = constantModelBoundedConstructible Λ X`.
  The full subcategories are determined by exactly these predicates in the
  constructibility dependency. Stability under both standard truncations is
  explicitly quantified over every derived object and integer using the standard
  `DerivedCategory.TStructure.t.truncLE` and `.truncGE`.
- Constructible iff lisse on finite strata is the third conjunct of
  `CoefficientHeartAssertions`: `IsConstantModelConstructible Λ X F ↔ ∃ R :
  X.FiniteLocallyClosedStratification, ∀ a, IsLisseCoefficientModule Λ
  ((CondensedRing.upperStar Λ (R.immersion a)).obj F)`. This uses the dependency's
  notion of scheme stratification with its specified scheme immersions, and the
  existing lisse predicate, whose `Mod.IsFree` means finite free rank. Constructibility
  of locally closed strata is automatic on the Noetherian X. No scheme factorization
  is inferred from inclusion of underlying point sets.
- `CoefficientHeartExtensionAssertions` uses the existing
  `coefficientHeartLocallyClosedExtension Λ a ha`, whose real definition is
  `openImmersionLowerShriek Λ a.toImage ⋙ lowerStar Λ a.imageι`. Thus the closure is
  the scheme-theoretic image, the first map is open and the second closed, as required.
  The defining instance-bound terms merely supply immersion and Noetherian-space
  structures from the given immersion, as in the existing construction; no proof
  data are postponed there. The predicate explicitly asserts preservation of finite
  limits and colimits for each factor and for their composite. Its concluded additive
  structure permits the termwise complex functor. It then concludes existence of a
  functor D on the unbounded derived categories with the natural isomorphism
  `DerivedCategory.Q ⋙ D ≅ a_!.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q`.
  This localization square characterizes the induced functor up to unique natural
  isomorphism. It is descent of the actual termwise extension, without a resolution;
  no arbitrary functor is accepted without this defining comparison.
- Clause (1), kernels and cokernels: quantify over `F G : ConstantModelConstructible Λ X`
  and every ambient arrow `f : F.obj ⟶ G.obj`, and assert constructibility of
  `kernel f` and `cokernel f` in that ambient module category.
- Clause (1), extensions: quantify over an arbitrary ambient middle object M and
  arrows `f : F.obj ⟶ M`, `g : M ⟶ G.obj`. `Mono f`, `Epi g`, and
  `(ComposableArrows.mk₂ f g).Exact` express the whole short exact sequence; the
  conclusion is `IsConstantModelConstructible Λ X M`.
- Clause (1), abelian category and exact inclusion: `Nonempty (Abelian
  (ConstantModelConstructible Λ X))` asserts the abelian structure on the actual
  full subcategory, with its existing category and preadditive structure. The next
  conjuncts assert `PreservesFiniteLimits` and `PreservesFiniteColimits` of the
  canonical inclusion `ObjectProperty.ι (IsConstantModelConstructible Λ X)`.
- Clause (2): `EssentiallySmall.{u + 1} (ConstantModelConstructible Λ X)` uses the
  same fixed universe as `coefficientHeart_essentiallySmall`; ambient sheaf objects
  can have universe u+2, and no equality of the site universes is imposed.
- Clause (3): `CoefficientHeartFiltrationAssertions` quantifies over each actual
  constructible F and supplies `m : ℕ` and `T : Fin (m+1) → Subobject F.obj`.
  `T 0 = ⊥` and `T (Fin.last m) = ⊤` are exactly its endpoints. The witnesses
  `h a : T a.castSucc ≤ T a.succ` give subsheaf inclusions. Each quotient is the
  ambient `cokernel (Subobject.ofLE ... (h a))`, isomorphic to the actual locally
  closed extension of an `IsLisseCoefficientModule Λ L` on a scheme S via the
  specified immersion `j : S ⟶ X`. These are ordinary subsheaf inclusions, not
  strict inclusions; the node's proof explicitly makes this convention.
- Curve specialization: `CoefficientHeartCurveAssertions` is conditional on
  `topologicalKrullDim X ≤ 1`, allowing reducible and nonreduced curves, as well as
  the zero-dimensional and empty boundary cases covered by the proof. For each F
  it supplies a `Dense` open U on which `upperStar Λ U.ι` of F is lisse, a closed
  immersion `i : Z ⟶ X` with `Set.range i = Uᶜ`, and finiteness and closedness of
  the points of Uᶜ. Here L is literally u*F. The left term is literally u!u*F and
  the right term is literally i*i*F (with the first i* denoting direct image).
  `Mono` of the actual open adjunction counit, `Epi` of the actual closed
  adjunction unit, and `ComposableArrows.mk₂ ... .Exact` give the claimed short
  exact sequence. The final `IsZero` assertion for open restriction of the closed
  term expresses that its support lies in that finite closed complement. These
  arrows are fixed by the recorded adjunctions, not arbitrary arrows between
  isomorphic terms. The chosen G is exactly i*F.

Dependency declarations used:

- `Sheaf.Paper.CondensedConstantConstructibility`:
  `HasFiniteConstantLocalModel`, `IsConstantModelConstructible`,
  `ConstantModelConstructible`, `constantModelBoundedConstructible` and the
  full subcategories Dbc and Dctf. The broader upstream
  `IsConstructibleModuleObject` is deliberately not substituted.
- `Sheaf.Paper.CoefficientHeartCommonStratification`:
  `coefficientHeartRingObj`, `IsLisseCoefficientModule`, and the common
  stratification proof interface `coefficientHeart_commonStratification`.
- `Sheaf.Paper.CoefficientHeartFiltration`:
  `coefficientHeartLocallyClosedExtension`, with its exact canonical closure
  construction, and `coefficientHeart_filtration` as a proof dependency.
  The two existing nodes owning these interfaces are added to stmt_deps; they
  were already proof_deps and have usable Lean records. No prerequisite is restated.
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `Scheme.FiniteLocallyClosedStratification`, its scheme domains and immersions.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `condensedRingObj`, `isCommMonObj_condensedRingObj`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:
  `CondensedRing.upperStar`, `.lowerStar`, `.upperStarLowerStarAdjunction`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`:
  `CondensedRing.openImmersionLowerShriek` and its adjunction, exactness and
  additivity instances.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `Profinite.padicSubfieldCondensedRing` and `.padicAlgClCondensedRing`.
  The latter closed upstream audit is usable without a separate lean record.
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing` exports the recorded
  commutative continuous coefficient interface; its canonical definitions are read.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `ModObj`, `Mod`, `Mod.forget`,
  `Mod.regular`, the closed upstream module-object dependency.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  the recorded `CondensedRing.compactificationOverField` setting interface.
  `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions` is imported for
  the recorded derived-category dependency; the ambient `DerivedCategory`, Q and
  termwise exact-functor comparison are Mathlib's existing constructions.
- `WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude`:
  `DerivedCategory.finiteTorAmplitude`; Mathlib supplies standard truncation,
  subobjects, cokernels, essentially-small categories and exact composable arrows.
- All recorded, stated proof-dependency modules are imported, including the existing
  smallness, condensed-coefficient comparison, closure, image-restriction, universal
  homeomorphism, closed-cover refinement, reduced closed subscheme, and finite
  zero-dimensional complement interfaces. The unrecorded detailed closure and
  Tor-amplitude nodes are proof inputs only, not missing statement constructors.

Edge cases checked before writing:

1. For F = 0 the filtration may have equal terms, or m = 0. No strictness or
   nonempty strata is imposed. Rank zero is included in `Mod.IsFree`.
2. For X empty, the empty stratification and m = 0 are possible, U = X is dense,
   Z is empty, the closed set is finite and the counit/unit sequence is zero.
3. The curve need not be reduced or irreducible. Its dimension is topological;
   neither an integral-curve class nor a factorization from point-set containment
   is imposed. The dense open can have empty complement.
4. Identity and empty locally closed immersions use the same canonical
   scheme-image/open-extension construction. Filtration quotients remain ordinary
   subobject quotients in all endpoint cases.
5. Both coefficient alternatives are the actual condensed fields; finite E of
   degree one is allowed. The base field is any standing field, not just finite or
   algebraically closed. The site stays at its existing object/morphism universes.

Searches for an exact existing statement:

- `msearch.py ... leansearch "Constructible sheaves form an abelian category and
  have finite filtrations by extensions by zero of locally free sheaves"`:
  eight hits about abelian sheaf/module categories, not this coefficient-heart
  statement or its curve and filtration clauses.
- `msearch.py ... leanfinder "Constructible pro-etale sheaves over an l-adic field
  form an essentially small abelian category and admit a finite filtration by
  locally closed extensions of lisse sheaves"`: eight condensed-module/sheaf
  Grothendieck-abelian and constructor hits, no matching theorem.
- `msearch.py ... loogle "EssentiallySmall, Abelian, FullSubcategory"`:
  no hits; the endpoint reports unknown identifier EssentiallySmall. The actual
  Mathlib declarations were then read locally.
- `msearch.py ... grep "[Cc]onstructible|[Ll]isse" CategoryTheory`: no hits.
- `rg` of the upstream project for this node id has no match. Its pro-etale
  `IsConstructible` concerns discrete ModuleCat sheaves and finite coefficients;
  its module-object `IsConstructibleModuleObject` admits arbitrary local matrices.
  Neither states this finite-constant-model coefficient heart.
- `rg` of `lean/Sheaf` for coefficientHeart/coefficient-heart and lisse identifies
  the actual common-stratification, smallness, and filtration modules used above.
  No complete statement of this unit exists. Searches of the upstream project,
  `lean/Sheaf`, and `dag/lean_names_upstream.json` for the new full declaration
  names have no matches. The assertion predicates only organize this node and
  do not redefine constructibility, lisseness, stratification, or extension by zero.

Validation: per-file compilation uses the prescribed `scompile.py` wrapper only.
The initial elaboration identified the need to bind the concluded additive
structure in the extension descent clause and to qualify `ObjectProperty.ι`.
Both were repaired. The implicitly used additive binder is named `_hadd` to
satisfy the unused-variable linter. Final `scompile.py` passed cleanly in both sandbox and library modes
(14.7 s and 14.6 s), with no warnings. `deliver2.py --no-push` then
printed `OK (dry run)` for commit `1193633d7f`, passing preflight and
compilation. Only the report, item node, and new module were staged.

## Second reading by Q37

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Worker report

The module `Sheaf.AlgebraicGeometry.QuasiFiniteFlatWeightedTrace` states
`AlgebraicGeometry.Etale.quasiFiniteFlatWeightedTrace`, with proof `sorry`.
Its ten helper definitions contain real data or explicit propositions, with no
postponed data and no additional theorem. They belong to this node's weighted-trace
notion and are recorded in `lean.declarations`. No other DAG node is stated.

The previous worker's unchanged-node preflight was a stale stage-1 delivery, not a
stage-2 statement: the preserved sandbox had only brief markers, the shared node had
no `lean` field, and its existing review concerned splitting its ten-step proof.
This delivery adds a Lean statement and changes only the item's `lean` record.

The source read was SGA 4 Exposé XVII, the local reedition PDF, §§6.1.2–6.1.4,
6.2.1–6.2.5 and 6.2.7–6.2.11. In particular 6.2.3, Var 2 and Var 3 specify the
base-change and composition equations, and Var 4 specifies the etale sum counit.
The length weights retain the nonreduced structure of the actual fibre scheme.

Hypothesis and clause correspondence:

| Natural statement | Lean rendering |
| --- | --- |
| Schemes X and Y | `{X Y : Scheme.{u}}` |
| Both Noetherian, in the finite affine Noetherian-cover sense | `[IsNoetherian X] [IsNoetherian Y]`; Mathlib `isNoetherian_iff_of_finite_affine_openCover` identifies this with the stated convention |
| Morphism u:X→Y | `(f : X ⟶ Y)` |
| Separated | `[IsSeparated f]`, the closed-diagonal condition |
| Quasi-finite | `(hq : f.IsQuasiFinite)`, the exact recorded Stacks predicate, including finite type and isolation in the fibre |
| Flat | `[Flat f]`, equivalent to flat stalk maps by `Flat.iff_flat_stalkMap` |
| Finite presentation | `[LocallyOfFinitePresentation f] [QuasiCompact f]` together with separatedness, which supplies quasi-separatedness; this is precisely the comparison clause in the finite-presentation dependency |
| Finite commutative coefficient ring B | `(B : Type (u + 1)) [CommRing B] [Finite B]` |
| Arbitrary B-module sheaf F on Y_et | `Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)`; no constructibility, local constancy or torsion-order invertibility is imposed |
| The sheaf compact-support functor u_! | Existing `lowerShriek (ModuleCat B) f`, extension by zero followed by proper direct image for the chosen compactification; `lowerShriekToLowerStar` is its actual inclusion into direct image |
| u_! is exact | First two conjuncts, `PreservesFiniteLimits` and `PreservesFiniteColimits` |
| Agrees with Ru_! on degree-zero sheaves | Natural isomorphism `DerivedCategory.singleFunctor _ 0 ⋙ rightDerivedLowerShriek _ f ≅ lowerShriek _ f ⋙ DerivedCategory.singleFunctor _ 0`, on the ordinary unbounded categories; this also gives the asserted bounded-below degree-zero comparison |
| Natural B-linear map u_!u^*F→F | `∃! τ : upperStar (ModuleCat B) f ⋙ lowerShriek (ModuleCat B) f ⟶ 𝟭 _`; its components are morphisms of B-module sheaves, hence B-linear, and naturality is part of the natural transformation |
| Geometric point Spec Ω→Y with Ω algebraically closed | Every stalk quantifier is `(Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)` |
| Actual scheme X_y and its finite points | `pullback f y : Scheme`, `IsFinite (pullback.snd f y)`, and `Finite (pullback f y : Scheme)` |
| Index by points of this scheme, rather than arbitrary chosen stalk identifications | `weightedTraceFibrePoint` takes an Ω-lift to its point in the actual pullback by `pullback.lift`; its bijectivity is an explicit conjunct |
| Local rings Artinian with residue Ω | For every actual fibre point x, `IsArtinianRing ((pullback f y).presheaf.stalk x)` and `IsIso ((pullback.snd f y).residueFieldMap x)`; the latter is the structural residue-field isomorphism from the residue field of Spec Ω, canonically Ω |
| Length means finite composition length over the local ring itself | `IsFiniteLength R R` for each local fibre ring R; `weightedTraceMultiplicity` is `(Module.length R R).toNat` |
| Stalk u_!u^*F is the direct sum of copies of F_y | The canonical `weightedTraceCoordinate` map to the product indexed by `f.GeometricFiber y` is bijective; the index is finite by its explicit bijection with the finite point set, so this product is the direct sum |
| Coordinates are the canonical germs | `weightedTraceCoordinate` is the stalk of `lowerShriekToLowerStar`, then `stalkRestrict`, then `upperStarCompSheafFiberIso`, then transport along the defining equality of the Ω-lift; no arbitrary isomorphism was chosen |
| Weighted sum formula | `IsQuasiFiniteFlatWeightedTrace B f τ`: `(stalk.map (τ.app F)) a = ∑ᶠ t, weightedTraceMultiplicity f y t • weightedTraceCoordinate B f F y t a` |
| Formula determines the map uniquely | `∃! τ, IsQuasiFiniteFlatWeightedTrace B f τ`; naturality does not weaken objectwise uniqueness because canonical coordinates exist for every F |
| Arbitrary change of Noetherian base | `WeightedTraceBaseChange`: all Cartesian squares and arbitrary b:Y'→Y between the stated Noetherian schemes; the support comparison e is specified by its inclusion square with the actual adjunction `baseChangeMap`, and the trace square uses the actual `squareUpperStarIso` |
| Composition of such morphisms | `WeightedTraceComposition`: g has exactly the separated, flat, finite-presentation, quasi-finite hypotheses; the comparison c is specified inside ordinary composite direct image, and the equation is τ_fg = τ_g after g_!(τ_f) and the canonical pullback compositor |
| Change of coefficient ring | `WeightedTraceCoefficientChange`: every homomorphism φ:B→B' of finite commutative rings, without flatness; k is fixed inside direct image and compares traces after restriction. For sheaf scalar extension E with `adj : E ⊣ Sheaf.restrictScalars _ φ`, `weightedTraceScalarComparison φ f k E adj F` is the actual adjoint of the unit-induced map, and is asserted invertible with `comparison ≫ τ'.app (E.obj F) = E.map (τ.app F)` |
| Etale u gives the sum-of-sheets counit | `WeightedTraceEtaleNormalization`: for every `[Etale f]`, e identifies etale sum extension with compact supports, its inclusion is the actual graph-extension `etaleLowerShriekToLowerStar`, and `e.hom ≫ τ` is the counit of `etaleLowerShriekUpperStarAdjunction` |
| Finite locally free constant rank r | `WeightedTraceRank`: every r and `[f.IsFiniteLocallyFreeOfDegree r]`; the direct-image trace t is specified by `lowerShriekToLowerStar ≫ t = τ`, and the ordinary adjunction unit followed by t equals `r • 𝟙 F` |

The auxiliary `HasCompactification` binders in compatibility predicates only make
existing functors typecheck; for the morphisms in the theorem and their composites
and Noetherian base changes they follow from the standing hypotheses by the existing
Nagata instance. No compactification is supplied as extra data in the main theorem.
The base-change predicate imposes no flatness or smoothness condition on b.


Scalar extension uses the same universal-property encoding as the recorded
`lem-pod-etale-stalk-tensor-scalar`: E with its adjunction to restriction of scalars
is B'⊗_B- on sheaves, uniquely up to the unit-compatible isomorphism. This is
nonvacuous: the existing `Sheaf.restrictScalars` has an `IsRightAdjoint` instance,
constructed by scalar extension and sheafification. The comparison is not an
existentially chosen arrow. Its definition applies `adj.homEquiv.symm` to
u_!u^* of the scalar-extension unit, then the actual inverse-image coefficient
comparison, then k inverse. This is exactly the map of proof step 9. Its
invertibility and the equation with traces are explicit conclusions. No flatness
of φ, exactness of E, or derived scalar extension is assumed.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`: `Scheme.Hom.IsQuasiFinite`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat` and `Flat.iff_flat_stalkMap`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`, with `IsSeparated` and `UniversallyClosed` from their owning Mathlib modules.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`, `Scheme.Etale`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback` and its projections/lift, used for def-weil-geometric-fibre.
- `Mathlib.CategoryTheory.Sites.Point.Basic`: `GrothendieckTopology.Point.sheafFiber`.
- `Mathlib.AlgebraicGeometry.Sites.EtalePoint`: `Scheme.pointSmallEtale`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`; `Mathlib.AlgebraicGeometry.Noetherian`: `IsNoetherian` and the finite-cover equivalence.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`: the shared module's sheaf categories/conventions; the current source was read in `lean/WeilConjectures`, since this newer module is absent from the older source checkout.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `upperStar`, `upperStarLowerStarAdjunction`, `lowerStarComp`, `upperStarComp`.
- `Sheaf.AlgebraicGeometry.DerivedCategories`: the recorded ordinary module-valued derived-category convention; `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`: `DerivedCategoryModule`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`: `rightDerivedLowerShriekOfCompactification` and `rightDerivedLowerShriek`, exactly the recorded candidate of def-amb-etale-compact-support.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`: `Scheme.Hom.IsFiniteLocallyFree`, `Scheme.Hom.IsFiniteLocallyFreeOfDegree`.
- `Mathlib.RingTheory.Length`: `Module.length`, with `IsFiniteLength`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison`: `lowerShriekToLowerStar`.
- `WeilConjectures.SixFunctors.Finite.Stalk`: `stalkRestrict` (its declaration does not require finiteness of f).
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk`: `upperStarCompSheafFiberIso`.
- `WeilConjectures.SixFunctors.BaseChange.Square`: `baseChangeMap`, `squareUpperStarIso`.
- `Sheaf.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons`: `lowerStarRestrictScalarsIso`, `upperStarRestrictScalarsIsoSheaf`; scalar restriction itself is the existing `Sheaf.restrictScalars`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtale`: `etaleLowerShriekToLowerStar`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`: `etaleLowerShriek`, `etaleLowerShriekUpperStarAdjunction`.

Imports include the recorded statement dependencies and every already-stated proof
dependency (Mathlib matches included where the record gives an owning module).
`lem-pur-quasifinite-finite-parts-presentation` has no Lean statement yet; it is
only a proof dependency, so it is listed here and not restated or imported. The
actual trace is not chosen from this unstated presentation: this delivery states
existence and uniqueness using the canonical stalk coordinates already available.
Its full ten-step natural-language proof is preserved in the theorem docstring,
including construction by the future finite-parts generators, rather than claiming
that arbitrary stalkwise formulas automatically glue.

Edge cases checked:

- Empty X or empty geometric fibre: the coordinate product is the zero module and
  the finsum is empty, giving the zero trace. No `Nonempty` index is imposed.
- Empty Y: the assertion is the unique map between zero sheaves; constant ranks
  are vacuous but multiplication maps on zero sheaves agree.
- Rank zero and rank one: the finite locally free clause gives zero and identity.
- Zero coefficient ring: all module sheaves are zero; `[Finite B]` permits it.
- Ramified/nonreduced fibre, e.g. Ω[ε]/(ε²): one geometric lift has local length
  two, so the formula is twice the identity, not a finite-etale-only trace.
- Characteristic dividing a weight, and φ:B→B' nonflat: integer scalar
  multiplication remains well-defined; no weight is inverted and no scalar
  extension is assumed exact.
- Finite length is asserted before `.toNat` is used mathematically, so the
  convention sending infinite length to zero cannot hide a missing hypothesis.
- Scheme and point universes are the same u, and coefficient modules use the
  existing u+1 convention; no independent smaller test-object universe or
  equality between distinct site universes is introduced.

Searches made (the actual wrapper log is preserved in `searches.jsonl`):

- LeanFinder: “For a separated quasi-finite flat morphism of schemes the trace on
  etale sheaves is the sum weighted by geometric fibre local ring lengths”. Eight
  hits, all algebra/field trace or localization lemmas, none the sheaf trace.
- Loogle: `AlgebraicGeometry.Etale, trace`. Zero hits; it reports unknown identifier
  `trace`, so this query alone gives no completeness evidence.
- Mathlib grep via msearch: `trace.*[Qq]uasi|[Ww]eighted.*[Tt]race|[Tt]race.*[Ff]lat`
  in `AlgebraicGeometry`. Zero hits.
- LeanSearch: “A separated quasi-finite flat morphism has a trace on etale sheaves
  weighted by the lengths of the local rings of geometric fibres”. Eight hits,
  giving quasi-finiteness and separatedness definitions, not a trace statement.
- Direct rg of the source repository and `lean/Sheaf` for weighted traces,
  quasi-finite flat traces, and the blueprint id: no existing trace declaration.
  Finite-etale trace modules were read and rejected as matches because their
  nonreduced local multiplicities are all one.
- Direct rg in the upstream-name index, Mathlib, source and `lean/Sheaf` for all
  eleven proposed declaration names: no collision.

No statement correction, new node, dependency replacement, or mathematical dispute
was needed. The only postponed proof is the named theorem for this DAG node.

Validation: the complete module, including proof-plan imports, compiled cleanly
through `scompile.py`, in separate sandbox and library-name checks; no warning was
reported. The required `deliver2.py --no-push` result is recorded below after it runs.

Dry-run result: `deliver2.py NJ lem-pur-quasifinite-flat-weighted-trace --no-push`
printed `OK (dry run): commit 930faa75ac compiles and passes the preflight except
for the second reading, which the second reader writes; nothing pushed.`
The final dry run is repeated after this report update. No second-reading section
was fabricated, and no delivery was pushed.

The subsequent coefficient-clause audit added the canonical ordinary
scalar-extension comparison and its invertibility and trace equation. The updated
module again compiled cleanly through `scompile.py`; the final dry run below
validates this complete version, superseding the earlier intermediate commits.


## Second reading by NJ

I independently read the node and its entire ten-step proof, then the Lean module,
all sixteen statement-dependency records, and the signatures and constructions
listed below. The primary source is the local SGA 4 Exposé XVII reedition PDF,
read in §§6.1.2–6.1.4 and 6.2.1–6.2.5, 6.2.7–6.2.11. This item has an SGA source,
not a Stacks trace source; the finite-etale-only trace is insufficient. The
source's 6.2.3 assumes separated, flat, finitely presented, quasi-finite morphisms
and arbitrary abelian sheaves. The node specializes to Noetherian schemes and
finite commutative coefficient rings. These restrictions are stated explicitly
in Lean. No additional reducedness, coefficient-characteristic, constructibility,
or flat-base-change restriction is inherited from the surrounding source.

Here is my object, hypothesis, and conclusion list, matched against the file.
Every row has verdict **matches**; the explanations address the encodings that
could otherwise change the statement.

| Node object, hypothesis, or clause | Lean rendering and verdict |
| --- | --- |
| Schemes X and Y, and their morphism u | `{X Y : Scheme.{u}} (f : X ⟶ Y)` uses the recorded scheme category. Matches. |
| Noetherian X and Y in the finite affine-cover sense | `[IsNoetherian X] [IsNoetherian Y]`. I read Mathlib's class (locally Noetherian plus compact) and `isNoetherian_iff_of_finite_affine_openCover`; this is the node's convention, not a globally affine restriction. Matches. |
| Separated u | `[IsSeparated f]`, the recorded closed-diagonal condition from the proper-morphism node. Matches. |
| Quasi-finite u | `(hq : f.IsQuasiFinite)`. I opened `QuasiFiniteMorphism.lean`: this is locally finite type, quasi-compact, and each `f.asFiber x` isolated in the actual fibre. It is not Mathlib's weaker local-quasi-finite predicate. Matches. |
| Flat u | `[Flat f]`. I checked the dependency and Mathlib's `Flat.iff_flat_stalkMap`, so this is flatness of all local-ring maps. Matches. |
| Finite presentation | `[LocallyOfFinitePresentation f] [QuasiCompact f]`, with quasi-separatedness supplied by separatedness. The finite-presentation dependency expressly defines finite presentation this way. Quasi-compactness also occurs inside `hq`; the instance makes the functors available without adding a mathematical condition. Matches. |
| Finite commutative coefficient ring B | `(B : Type (u + 1)) [CommRing B] [Finite B]`. Matches the recorded six-functor size convention and permits the zero ring. |
| Arbitrary B-module sheaf F on Y_et | `Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)`, quantified in the characterization and comparisons. This is the recorded six-functor encoding; F has no finiteness or local-constancy assumption. Matches. |
| Compact-support sheaf functor u_! | Existing `lowerShriek (ModuleCat B) f`. I read its body: extension by zero along the chosen compactification followed by proper direct image. Matches. |
| Exactness of u_! | `PreservesFiniteLimits` and `PreservesFiniteColimits` are the first two conjuncts. For this additive functor between abelian sheaf categories these express exactness. Matches. |
| Agreement with Ru_! on degree-zero sheaves | The displayed natural isomorphism between `singleFunctor _ 0 ⋙ rightDerivedLowerShriek _ f` and `lowerShriek _ f ⋙ singleFunctor _ 0`. I read the derived functor's body: `Dj_! ⋙ Rr_*` on unbounded ordinary derived categories. The assertion concerns only degree-zero inputs, so it also applies to the source's bounded-below inputs. Matches. |
| Geometric point with algebraically closed Ω | `(Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)`, universally quantified. Matches. |
| Actual geometric fibre X_y | `pullback f y`, with its structure morphism `pullback.snd f y`. I checked the fibre-product dependency; this retains nonreduced scheme structure. Matches. |
| X_y finite over Ω, with finitely many points | `IsFinite (pullback.snd f y)` and `Finite (pullback f y : Scheme)`. Matches. |
| Actual fibre points index the formula | `weightedTraceFibrePoint f y` sends an Ω-lift to the point obtained by `pullback.lift`, and its bijectivity is a conclusion. I opened the existing `GeometricFiber`: it is exactly the subtype of maps whose composite is y. Thus indexing by those lifts is explicitly identified with the actual point set. Matches. |
| Artinian local rings of X_y | `∀ x, IsArtinianRing ((pullback f y).presheaf.stalk x)`. Matches. |
| Residue field canonically Ω | `IsIso ((pullback.snd f y).residueFieldMap x)`. Its source is the residue field of Spec Ω at the image of x, canonically Ω; it is the structural residue-field map. Matches. |
| Finite self-composition length | `IsFiniteLength R R`, and `weightedTraceMultiplicity` is `(Module.length R R).toNat` for that actual fibre local ring. I read `Module.length` and `length_ne_top_iff`; no dimension or residue-field degree is substituted. Matches. |
| Stalk of u_!u^*F is the direct sum of F_y | Bijectivity of the tuple of `weightedTraceCoordinate` maps. Its target is a product over the lift set, which is finite by the preceding finite-point and bijection conclusions; this is exactly the finite direct sum. Matches. |
| Canonical, rather than arbitrary, stalk coordinates | `weightedTraceCoordinate` first takes the stalk of `lowerShriekToLowerStar`, then the existing `stalkRestrict`, then `upperStarCompSheafFiberIso`, and transports along the defining equality of the lift. I read these constructions; `stalkRestrict` imposes no finiteness hypothesis in its actual signature. Matches. |
| Natural B-linear map u_!u^*F → F | The existential natural transformation has type `upperStar _ f ⋙ lowerShriek _ f ⟶ 𝟭 _`. Its components are module-sheaf morphisms, hence B-linear. Functor composition has the required order. Matches. |
| Displayed weighted sum at every geometric stalk | `IsQuasiFiniteFlatWeightedTrace` says the stalk map is `∑ᶠ t, weightedTraceMultiplicity f y t • weightedTraceCoordinate ... t a`. Its finite index makes this the stated finite sum; natural-number scalar multiplication works in every coefficient characteristic. Matches. |
| Formula determines the trace uniquely | `∃! τ, IsQuasiFiniteFlatWeightedTrace B f τ`. This is uniqueness of the natural sheaf map; objectwise uniqueness follows from the same canonical stalk formulas and geometric-stalk conservativity. Matches. |
| Arbitrary change of Noetherian base | `WeightedTraceBaseChange`: all Cartesian squares with Noetherian X' and Y', arbitrary b, and the trace satisfying the fibre formula. The existence theorem applies to f' since the class is stable under base change; X' is automatically Noetherian from finite presentation over Y'. The comparison is fixed by its square with the actual adjunction base-change map into ordinary direct image, and the trace equation uses `squareUpperStarIso`. Matches. |
| Composition of such morphisms | `WeightedTraceComposition`: arbitrary g:Y→Z in the same class and the two characterized traces. The comparison is fixed by its inclusion in ordinary direct image and `lowerStarComp`; the equality uses `upperStarComp`, then g_! of τ_f, then τ_g. This is the source's order for f followed by g. Matches. |
| Change of coefficient ring | `WeightedTraceCoefficientChange`: every ring homomorphism to every finite commutative B', the canonical restriction-of-scalars comparisons, and ordinary sheaf scalar extension specified by its adjunction. `weightedTraceScalarComparison` is the actual adjoint of the unit-induced map, not a chosen arrow; invertibility and the trace equation are explicit conclusions. The existing restriction-of-scalars functor has a left adjoint, so the quantifier over adjunctions is nonvacuous. Matches. |
| Etale morphism gives the sum-of-sheets counit | `WeightedTraceEtaleNormalization`: `[Etale f]`, an isomorphism from the existing etale lower shriek whose inclusion is graph extension, and the equality with `etaleLowerShriekUpperStarAdjunction.counit`. Matches. |
| Finite locally free constant rank r | `WeightedTraceRank`: every `r : ℕ` and `[f.IsFiniteLocallyFreeOfDegree r]`. I opened `FiberDegree.lean`: this extends finite, flat and locally finitely presented, with every residue-fibre degree equal to r. The map t on ordinary direct image restricts to τ and its composite with the actual ordinary adjunction unit is `r • 𝟙 F`. Matches. |

The `HasCompactification` instances in the compatibility definitions do not add
compactification data to the theorem: the Nagata instance supplies them from its
standing hypotheses, also for the composable maps and base changes. All quantified
traces in compatibility clauses exist by the main existence statement applied to
those morphisms. The comparisons e, c, and k are characterized inside direct image;
they cannot be adjusted arbitrarily to make the trace equations hold. The coefficient
scalar-extension comparison uses the inverse of that same k and the displayed
adjunction unit, so changing the chosen left adjoint merely transports the equation.

Edge cases checked independently:

- Empty X and empty geometric fibres: there is no nonempty-index hypothesis, and
  the tuple target and finsum are respectively the zero module and zero sum.
- Empty Y: its sheaf category is the zero category; rank hypotheses over it are
  vacuous and the asserted endomorphism equality still holds.
- Zero F and the zero coefficient ring: neither is excluded by the binders.
- Rank r=0, identity/rank one, and disconnected bases: all ranks in ℕ are allowed;
  constant degree is required only in the rank clause, not for the main trace.
- A nonreduced local fibre Ω[ε]/(ε²): the weight is two because the length uses the
  fibre local ring itself. An unweighted finite-etale trace would fail this check.
- Characteristic dividing a multiplicity, purely inseparable finite flat maps,
  and nonflat coefficient homomorphisms: no integer is inverted, etaleness is not
  a main hypothesis, and scalar extension is not assumed exact.
- Universes: one arbitrary u for schemes and geometric points, the established
  u+1 convention for coefficients and module values, no independent smaller
  test-object universe, and `autoImplicit false` with every binder accounted for.

Independent searches used different wording from the first worker. The msearch log
records LeanFinder for “Trace map on étale module sheaves for a flat quasi-finite
scheme morphism with ramification multiplicities” (eight unrelated algebra-trace,
localization, or etale-definition hits); LeanSearch for “Trace on sheaves for a flat
quasi-finite morphism is multiplication by the lengths of the geometric local fibre
rings” (eight algebra-trace and flatness hits); Loogle for the upperStar/lowerShriek
pair (no hits; unknown identifier, hence no completeness evidence from that query);
and grep for `weightedTrace|quasiFiniteFlatWeightedTrace|quasiFinite.*[Tt]race`
(no hits). Direct rg of Mathlib's algebraic geometry, the source WeilConjectures tree,
and the project's lean/Sheaf used `trace`, `ramif`, `multiplicit`, and `weighted`,
then quasi-finite/trace and quasi-finite/counit in both orders. No existing declaration
states this node. Existing finite-etale trace/adjunction constructions are its
normalization, not a match for ramified flat maps. No module can be dropped.

No new node or dependency module is part of this delivery, so H12/H13 introduce
no extra records to review. The length dependency's `mathlib_match` is sufficient
although it has no `lean` field. The imported dependency declarations are usable
at the stated universes. I also checked the recorded etale-site, geometric-stalk,
finite-locally-free, inverse-image, sheaf category, and derived-category signatures;
there is no private copy of those notions in the module.

Mismatches found and repairs: only the helper source citations were inaccurate.
The two docstrings called the project server a weighted-sum formula, but it is the disjoint-union
lemma. They now cite the actual construction on p. 425 and §§6.2.4–6.2.5. The etale
normalization citation now points explicitly to Proposition 6.2.11 instead of calling
it Variance 4; the rank helper identifies Variance 4 (and 4' of 6.2.5) explicitly.
The coefficient helper now describes 6.2.3's functoriality and integral construction,
rather than suggesting Variance 1 separately states coefficient changes. The
previous Worker report's source summary should be read with these corrections.
No mathematical signature or helper data changed, and no statement_change is needed.

All ten helper definitions contain real constructions or propositions, with no
sorry or arbitrary existence choice. The only theorem has proof `by sorry` and
its docstring reproduces all ten proof steps and their dependencies. Every
declaration has a source/blueprint docstring; there are no file-local instances,
notations, private declarations, or unbound variables. All lines are at most 100
characters. I checked byte-for-byte that the node's `lean.statement` equals the
module's theorem signature. The required scompile wrapper compiled both the
sandbox name and library name cleanly before the citation changes; the final
compile and delivery dry run are recorded below.

Final second-reader validation: scompile.py compiled the final module cleanly
under both names (6.3 s sandbox, 10.6 s library). The required dry run printed
`OK (dry run): commit 8ab346d6e1 passes the preflight and compiles; nothing pushed`.
Only this report, the item node record, and its owning Lean module are staged.

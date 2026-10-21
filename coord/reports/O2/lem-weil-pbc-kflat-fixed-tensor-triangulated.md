## Worker report

Item: `lem-weil-pbc-kflat-fixed-tensor-triangulated`.
Module: `Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated`.
Main declaration: `SheafOfModules.KFlatFixedTensor.kFlat_fixed_tensor_triangulated`.
The theorem has the sole `sorry` in this delivery; its docstring gives the node's nine-step
proof, including the signed cone calculations, connecting arrow, localization, resolving
normalization, and arbitrary derived-map compatibility. No proof is supplied at stage 2.

The four abbreviations `Modules`, `ordinaryTensor`, `totalTensor`, and `derivedTensor`
only specialize existing declarations. In particular, `derivedTensor` is the curry of
`siteDerivedTensorIndependentCoefficients`, not another derived tensor. `representativeIso`
exposes the actual comparison of that chosen descent theorem: it applies the inverse
localized homotopy tensor comparison and then the resolving comparison. Its data are
explicit composites of the dependency's isomorphisms, with no new existence axiom or
unconstrained choice. The helper's lets occur only in its construction, never in a
statement. There are no new nodes, dependency repairs, or statement corrections.

The following table matches every hypothesis and clause with the statement. Names in the
table are in `SheafOfModules.KFlatFixedTensor` unless qualified.

| Node text | Lean rendering |
| --- | --- |
| Small site | `{C : Type u} [Category.{v} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}`; independent object, morphism and coefficient universes. Essential smallness expresses exactly smallness relative to the modules and supplies sheafification and the abelian structure. |
| Sheaf of commutative rings R | `(R : Sheaf J CommRingCat.{r})`. |
| Its abelian module-sheaf category | `Modules R` abbreviates recorded `CategoryTheory.ringedSiteModules` applied to the underlying ring sheaf, at module universe r. |
| Unbounded derived category and localization | `[HasDerivedCategory.{w} (Modules R)]`, `DerivedCategory (Modules R)` and `DerivedCategory.Q`. The localization morphism universe w is independent. |
| Direct-sum total tensor | `totalTensor R = (ordinaryTensor R).map₂CochainComplex`, where the ordinary tensor is recorded `SheafOfModules.monoidalCategory R` and `curriedTensor`. This is the direct-sum total with differential d_A tensor 1 + (-1)^p 1 tensor d_B. |
| K-flat derived tensor from the cited descent | `derivedTensor R` is precisely `Functor.curry.obj (siteDerivedTensorIndependentCoefficients J R)`. |
| Every K-flat complex A with flat terms | `∀ (A : CochainComplex (Modules R) ℤ) (hA : CochainComplex.IsKFlatIndependentCoefficients A) (hAf : ∀ n : ℤ, IsFlatOnSite (A.X n)), ...`. |
| Both orders preserve every quasi-isomorphism | The first conjunct quantifies over arbitrary `B B'` and `f : B ⟶ B'` and concludes `QuasiIso (((totalTensor R).obj A).map f)` and `QuasiIso (((totalTensor R).flip.obj A).map f)` from `QuasiIso f`. There is no resolving hypothesis on B or B'. |
| Descend to functors D(R) to D(R), canonically identified with QA tensor-derived - and - tensor-derived QA | The descended functors are the actual `(derivedTensor R).obj (Q.obj A)` and its flip, with natural isomorphisms `cL : totalTensor.obj A ⋙ Q ≅ Q ⋙ derivedTensor.obj (Q.obj A)` and `cR` for the flip. They are normalized, not arbitrary: `cL.app B = representativeIso R A B hA hB hAf hBf` and `cR.app B = representativeIso R B A hB hA hBf hAf` for every flat-term K-flat B. These equations use the dependency's selected comparison; localization makes this the canonical descent. |
| Exact descended functors | The pair of `IsTriangulated` conclusions for those two fixed derived functors, using the shifts selected by the single existential s. Mathlib's `IsTriangulated` implies additivity and preserves all distinguished triangles. |
| Coherent integer-shift comparisons localize the signed total-complex maps | `∃ s : (derivedTensor R).CommShift₂Int, ...`, and `NatTrans.CommShift cL.hom ℤ` / `NatTrans.CommShift cR.hom ℤ`. The source structures of these transformations are the standard `map₂CochainComplex` structures and the standard localization Q. Thus the commuting squares identify the derived comparisons with localized `mapBifunctorShift₂Iso` / `mapBifunctorShift₁Iso`, not arbitrary coherent shifts. Their representatives are respectively signed (-1)^(np) and unsigned. |
| Cone triangles go to distinguished triangles including the connecting map | The last conjunct asserts membership in `distTriang` for both fixed functors' `mapTriangle.obj (Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f))`, for every chain map f. `mappingCone.triangle` has third arrow induced by `-fst`; `mapTriangle` maps that arrow and composes with the selected commShiftIso 1, so the third arrow is included explicitly. The cL/cR shift compatibility identifies these with the localized tensor images of the cone triangles. |
| Shifts preserve K-flatness and flat terms | Second conjunct: for every `n : ℤ`, `IsKFlatIndependentCoefficients (A⟦n⟧)` and every term of `A⟦n⟧` satisfies `IsFlatOnSite`. |
| Chain maps between resolving fixed arguments induce transformations commuting with varying shifts | `s.commShift_map` and `s.commShift_flip_map` assert this for all derived maps, hence in particular `Q.map a` for every such chain map a. The cL/cR normalizations identify these with the localized ordinary tensor transformations on resolving representatives. |
| All maps obtained by localization have the same compatibility | Those fields of `CommShift₂Int` quantify over every derived morphism, including inverses and composites in the localization, not only images of chain maps. |
| Both shift-extraction orders retain signed compatibility | `s.comm` is exactly Mathlib's mixed identity with `CommShift₂Setup.int.ε a b = (-1)^(ab)`, after canonical identification of the total shifts. Each `s.commShiftObj` and `s.commShiftFlipObj` is a `Functor.CommShift ℤ` with zero and addition laws. |
| No boundedness or flatness of cohomology | All complexes are unrestricted `CochainComplex ... ℤ`. No bound, cohomological-flatness, or additional exactness hypothesis is present. |

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, transparently
  the recorded Mathlib `SheafOfModules` category.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`, `DerivedCategory`,
  `DerivedCategory.Q`, `Qh`, their coherent shifts, triangulated localization, and
  `quotientCompQhIso` (the latter comparison explains the definitionally matching objects).
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`,
  `Functor.map₂CochainComplex`, `mapBifunctorShift₁Iso`, `mapBifunctorShift₂Iso`, their
  summand formulas, fixed-argument `NatTrans.CommShift` instances, and mixed-sign identity.
  The node's Mathlib match is the `map₂CochainComplex.CommShift₂Int` instance in this file.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`:
  `site_derived_tensor_descent_independentCoefficients` and
  `siteDerivedTensorIndependentCoefficients`. `representativeIso` composes its selected
  homotopy comparison and resolving comparison using its membership equivalence.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients` (tensor acyclicity against every acyclic
  test complex), and inherited independent-coefficient small-site/sheafification interfaces.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`,
  exactness of the actual sheafified sectionwise right tensor.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` (the proof dependency
  `def-pur-sheaf-tensor-product`): canonical independent-universe module tensor,
  `cochainModulesMonoidal`, `cochainModulesPreadditive`, and tensor colimit instances.
  These provide the canonical additivity/totalization interfaces without a local instance
  or new mathematical assumption.
- Proof imports: `Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients`
  (`tensorLeft_preservesColimits_independentCoefficients`);
  `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
  (`CochainComplex.exists_isKFlatResolutionIndependentCoefficients`);
  `WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone`
  (`CochainComplex.mapBifunctorMappingCone₂Iso`);
  `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`
  (`CochainComplex.mappingCone.quasiIso_iff_acyclic`);
  `Mathlib.CategoryTheory.Localization.Predicate` (`Localization.lift`, `fac`,
  `liftNatTrans`, `liftNatIso`, `natTrans_ext`);
  `Mathlib.Algebra.Homology.HomotopyCategory.Triangulated` (its triangulated instance);
  `Mathlib.CategoryTheory.Triangulated.Pretriangulated` (the recorded TR1--TR3 notion).
  These last two are explicit proof-dependency imports, even though they are also
  transitively available through derived-category and functor imports.
- `Mathlib.CategoryTheory.Triangulated.Functor`: `Functor.IsTriangulated` and
  `Functor.mapTriangle`, with its third-arrow definition read; the latter maps the original
  connecting arrow and composes it with commShiftIso 1.

Source and edge-case check:

Read Stacks sites-cohomology.tex `lemma-derived-tor-exact`, `definition-K-flat`,
`lemma-K-flat-quasi-isomorphism`, the construction preceding `definition-derived-tor`,
and the definition itself. These cover arbitrary unbounded complexes on a ringed site.
Read more-algebra.tex `item-shift-tensor` and `item-flip-tensor-product`, as well as the
Mathlib summand formulas and the negative projection in `mappingCone.triangle`.

Checked zero complexes, zero ring and empty site (none is excluded), n = 0 and all negative
integer shifts (CommShift ℤ includes all), the identity and zero maps, and characteristic 2
(the sign maps specialize to identity without changing the statement). The quasi-isomorphism
clause permits arbitrary non-K-flat endpoints. Site object and morphism sizes may differ,
and coefficient and localization sizes remain independent. No false or ambiguous clause was
found; no STATEMENT-DISPUTED flag or statement change is needed.

Searches performed (the exact wrapper outputs are retained in the sandbox searches.jsonl):

- `msearch.py leanfinder`, query "Tensoring with fixed K flat complex of sheaves preserves
  quasi isomorphisms and descends to exact functor of derived categories with signed integer
  shifts": eight hits, including `CategoryTheory.Tor`, `Tor'`, and
  `CategoryTheory.Functor.mapDerivedCategory` with its shift instances. They concern
  projective Tor or exact functors on coefficient abelian categories, not the whole statement
  with this published unbounded site tensor and its normalized resolving comparison.
- `msearch.py loogle`, query `Functor.CommShift₂Int,Functor.IsTriangulated`: the service
  reports an unknown unqualified identifier, so this is not negative search evidence.
  The exact fully qualified declarations were instead read in local Mathlib source.
- Follow-up `msearch.py loogle`, query `"IsTriangulated"`: twelve hits, including
  `CategoryTheory.Functor.IsTriangulated`, its additive instance and transport lemmas.
  These give the right general predicate, not the site-specific result.
- `msearch.py grep`, query `KFlat|kFlat|kflat` in `Algebra/Homology`: zero Mathlib hits.
- Direct `rg` on both `lean/WeilConjectures` and `lean/Sheaf` for
  `kflat.fixed.tensor|KFlat.*[Tt]riangulated|kFlat.*[Tt]riangulated`, plus upstream grep for
  this item id: no existing statement with the item's binding. The upstream derived
  monoidal shift module has triangulated tensor and normalization results for its own
  general K-flat monoidal construction; it does not state the resolving normalization for
  the site's separately published descent functor used by this node. We reuse the generic
  shift interfaces instead of declaring another monoidal or tensor structure.
- `rg` for `siteDerivedTensor` found the actual dependency implementation, the total-model
  consumer, and shifted-morphism-calculus consumers. Read those to verify how to expose
  the dependency's chosen representative comparison. Their total-model and morphism
  statements do not assert the fixed-functor exactness and both comparisons in this item.
- Direct `rg` for `KFlatFixedTensor|kFlat_fixed_tensor_triangulated` in Mathlib and both
  source roots found no conflicting declaration.

Validation: prescribed `scompile.py` succeeded cleanly for both the sandbox module
(24.8 seconds) and final library module name (30.0 seconds). No warning other than the
allowed postponed-proof warning, and no errors. An initial parser error from a line break
before an explicit universe suffix was corrected before that successful compile.

## Second reading by O2

No independent second worker was started: the dispatcher explicitly requires direct delivery
and forbids starting other agents. The maintainer performs the independent delivery review.
A second pass by this worker checked the table against the node and file, particularly the
actual selected tensor (rather than a free tensor parameter), both comparison orientations,
normalization on all resolving complexes, all derived fixed-argument maps, and the cone's
negative connecting arrow. The single existential `CommShift₂Int` occurs before the
quantification over A, so every fixed argument shares one coherent bifunctor structure.
The compiler accepts its local instance as the one used by `IsTriangulated`,
`NatTrans.CommShift`, and `mapTriangle`. No mathematical mismatch was found.

The first prescribed delivery dry run passed preflight and compilation. Before final
delivery, two explicit proof-dependency imports were added (homotopy triangulation and
pretriangulation); the final packet is rechecked by the prescribed delivery wrapper.

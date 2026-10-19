## Worker report

The module `lean/Sheaf/AlgebraicGeometry/GlobalGeneratedStalkwise.lean` states
`AlgebraicGeometry.Scheme.isGloballyGeneratedEtaleSheaf_iff_geometricStalk_surjective`.
It gives exactly the equivalence in `lem-kun-global-generated-stalkwise`: global generation
is `IsGloballyGeneratedEtaleSheaf F`, namely the epimorphism of the evaluation morphism
from `def-kun-global-generated`; the second clause quantifies every field `Ω : Type u`
with `[Field Ω] [IsAlgClosed Ω]`, every geometric point
`t : Spec (.of Ω) ⟶ T`, and requires `Function.Surjective` for the induced map on the
`ModuleCat` geometric stalk
`((pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} Λ)).map
(etaleGlobalSectionsEvaluation F)`. No hypotheses or conclusion clauses were added.
The proof is postponed as the named theorem's `sorry`; its source route is the cokernel
criterion, exactness after forgetting coefficients, exact stalks, and conservativity of
geometric stalks (Tags 03DA, 03PT, 03PU).

Dependencies used:

- `def-kun-global-generated`: `Sheaf.AlgebraicGeometry.EtaleGloballyGenerated`,
  declarations `AlgebraicGeometry.Scheme.etaleGlobalSectionsEvaluation` and
  `AlgebraicGeometry.Scheme.IsGloballyGeneratedEtaleSheaf`.
- `def-kun-constant-sheaf`: its constant-sheaf construction is used by the recorded
  evaluation declaration above (the node's recorded generic complex declaration is
  not needed directly in this theorem).
- `def-weil-pbc-geometric-stalks`: Mathlib
  `CategoryTheory.GrothendieckTopology.Point.sheafFiber`, specialized through
  `AlgebraicGeometry.Scheme.pointSmallEtale`.

Edge cases checked: the empty scheme and zero sheaf satisfy both sides vacuously; an
empty global-section index is represented by the free module on an empty type; no
connectedness, finiteness, or nonzero coefficient assumptions occur; `Ω` has the same
universe as `T` as required by `pointSmallEtale`; and `IsAlgClosed` supplies the geometric
point condition used by the small étale point construction.

Searches made:

- `msearch.py ... leanfinder "epi sheaf morphism iff geometric stalk maps surjective
  etale module sheaf"`: related generic sheaf local-surjectivity and presheaf epi
  declarations, but no exact evaluation criterion.
- `msearch.py ... grep "IsGloballyGeneratedEtaleSheaf|etaleGlobalSectionsEvaluation"
  AlgebraicGeometry`: no source-library match; the only project matches are the
  dependency node/module.
- `rg -n "Function.Surjective.*pointSmallEtale|..." lean/Sheaf dag/nodes`: found
  existing stalk-surjectivity usages such as `FinitePushforwardCoefficientControl`,
  but no declaration of this equivalence.
- `rg -n "IsGloballyGeneratedEtaleSheaf|etaleGlobalSectionsEvaluation"` over the
  project and `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`: no pre-existing
  statement of this item.

No new nodes, statement correction, or `STATEMENT-DISPUTED` flag is required.

## Second reading by Q05

I independently read the sandbox node and Lean file, all three statement-dependency
nodes and their actual declarations, and the four additional proof-dependency nodes.
The blueprint text is absent from this read-only clone's literature directory; I read
the exact item and evaluation-definition source files in the launcher's literature
mirror, `/home/ubuntu/weil-launcher-nt/literature/blueprint/master/blueprint/`.
For the Stacks sources I read the local TeX copies in `/home/ubuntu/c1-stacks-review/`:
`etale-cohomology.tex`, definition-geometric-point, lemma-stalk-exact (03PT), and
theorem-exactness-stalks (03PU); `sites-modules.tex`, lemma-abelian (03DA); and
`homology.tex`, definition-injective-surjective (010B) and
lemma-characterize-injective (010C). These assume an arbitrary scheme and a geometric
point with algebraically closed residue field, and impose no Noetherian, finiteness,
connectedness, or characteristic condition. The source and node agree.

The complete object/hypothesis/conclusion checklist is:

1. Arbitrary scheme T: `{T : Scheme.{u}}`. Verdict: exact; no extra scheme instance.
2. Arbitrary commutative coefficient ring Lambda: `{Λ : Type (u + 1)} [CommRing Λ]`.
   Verdict: exact under the established module-valued etale-sheaf size convention;
   neither a field nor a nonzero/finite/torsion coefficient ring is required.
3. A sheaf of constant-Lambda modules on the small etale site:
   `(F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))`. Verdict: exact. The
   category uses fixed Lambda-linear restriction maps and is the coefficient-module
   sheaf category of the recorded definition, with no constructibility assumption.
4. The evaluation map indexed by every global section, sending its basis vector to
   that section: `etaleGlobalSectionsEvaluation F`. Verdict: exact. I read its real
   definition in `Sheaf.AlgebraicGeometry.EtaleGloballyGenerated` and confirmed the
   current source through `scompile.py --source`. Its free module is
   `((F.obj.obj (op (Etale.mk (𝟙 T)))) →₀ Λ)` (inside `ModuleCat.of Λ`),
   i.e. finite linear combinations of all sections over the terminal etale object.
   Its constant sheaf is the displayed coproduct because `constantSheaf` is a left
   adjoint; the adjunction applied to `Finsupp.linearCombination Λ id` gives exactly
   the evaluation map. No chosen generators or arbitrary replacement map occur.
5. Clause (1), evaluation is epi: `IsGloballyGeneratedEtaleSheaf F`. Verdict: exact;
   the dependency defines this literally as `Epi (etaleGlobalSectionsEvaluation F)`.
6. Clause (2), every geometric point: `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
   (t : Spec (.of Ω) ⟶ T), ...`. Verdict: exact. In particular algebraic closedness
   matches the Stacks definition, although Mathlib's point construction works more
   generally for separably closed fields.
7. Clause (2), surjectivity of this same evaluation map on the geometric stalk:
   `Function.Surjective (((pointSmallEtale t).sheafFiber
   (A := ModuleCat.{u + 1} Λ)).map (etaleGlobalSectionsEvaluation F))`.
   Verdict: exact. I read `pointSmallEtale` in Mathlib's `Sites/EtalePoint.lean`:
   its fibre consists of lifts of t to etale objects. I read `presheafFiber` and
   `sheafFiber` in `Sites/Point/Basic.lean`: the stalk is the colimit over the
   opposite category of these pointed neighbourhoods, precisely the dependency's
   definition. The map is a module homomorphism coerced to its underlying function.
8. Equivalence of (1) and (2): `↔`, followed by the universal geometric-point
   quantifiers. Verdict: exact, both directions, with T, Lambda and F fixed first.

Dependency check: `def-kun-constant-sheaf` records the generic termwise-complex
construction `Functor.mapHomologicalComplex`; its note explicitly specializes the
functor to `constantSheaf`. I opened both actual definitions. This theorem uses only
the degree-zero constant sheaf already present in the evaluation declaration, so a
complex-specific import or replacement definition is unnecessary. For the proof I
also opened `moduleSheaves_colimits_forgetful`,
`Preadditive.epi_iff_isZero_cokernel'`, the finite-limit and left-adjoint stalk
instances, `ShortComplex.ShortExact.map_of_exact`, and
`Scheme.isIso_of_isIso_sheafFiber_map`. These are the recorded proof interfaces;
the forgetful theorem concerns ring-sheaf modules, whose application here is through
the standard identification with sheaves valued in the fixed coefficient category.
There are no dependency modules or new definition nodes in this delivery.

Universe check: schemes and the algebraically closed fields of their geometric
points live in u; the small etale site's objects live in u+1 and its morphisms in u.
Coefficient modules live in u+1 as in the recorded global-generation definition.
The stalk colimits exist at these sizes. I additionally opened
`GrothendieckTopology.Point.uliftSheafFiberIso` in upstream
`WeilConjectures/Mathlib/CategoryTheory/Sites/Point/Basic.lean`: the recorded
conservativity theorem uses lifted site points for coefficients in u+1, and this
natural isomorphism identifies their fibres with the unlifted fibres in this
statement. Thus no equality of site object and morphism universes, or restriction
to coefficient modules in u, has been introduced. Every scheme point has the
geometric point supplied by the algebraic closure of its residue field in u.

Edge cases: on the empty scheme there are no geometric points and every module
sheaf is zero, so both sides hold. The zero sheaf and the zero coefficient ring
are covered; their evaluation stalk maps are surjective. Arbitrary characteristic
is covered. There is no degree n or positive-rank hypothesis. The worker report's
empty-index comment needs qualification: the actual global-section type always
contains zero, so it cannot be empty for this F. The free-module construction itself
also supports an empty index, and the theorem imposes no separate nonemptiness
requirement. No mathematical case is lost.

Independent searches (all run again for this second reading):

- LeanFinder via `msearch.py`: "A sheaf of modules on a scheme is generated by its
  global sections if and only if the evaluation from the free constant sheaf is
  onto at all geometric fibers". Eight hits were variants of
  `SheafOfModules.GeneratingSections` and `LocalGeneratorsData`. I opened
  `Mathlib/Algebra/Category/ModuleCat/Sheaf/Generators.lean`; these are generating
  family data for ring-sheaf modules, not this stalkwise equivalence.
- Loogle via `msearch.py`:
  `CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.jointlyReflectEpimorphisms`.
  One generic result. I opened its actual signature in `Point/Conservative.lean`;
  it needs a conservative family and the appropriate concrete coefficient universe,
  and does not state the evaluation criterion or supply its etale specialization.
- LeanSearch via `msearch.py`: "An etale sheaf of modules is globally generated
  exactly when its evaluation map is surjective on geometric stalks". The service
  returned Internal Server Error; recorded as unavailable, without a match verdict.
- `rg` over Mathlib's `CategoryTheory/Sites` and `AlgebraicGeometry`, upstream
  `WeilConjectures/`, and this project's `lean/Sheaf/`, using
  `globally.?generated`, `global.?sections.?evaluation`, `epi_iff.*(stalk|fiber)`,
  and `surjective.*geometric.?stalk`. Only the existing evaluation dependency and
  unrelated line-bundle results appeared. Upstream `WeilSheaf.surjective_stalkMap`
  is one direction for a different coefficient/sheaf setup; I inspected its
  signature. The item id and proposed declaration name also have no upstream-name
  table match. No exact existing declaration replaces this module.

Mismatches repaired: the initial file omitted non-public imports for recorded proof
dependencies, and its docstring compressed the proof enough to omit the zero-object
criterion and explicit compatibility of module and abelian stalks. I added proof
imports for `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`,
`Mathlib.CategoryTheory.Preadditive.Basic`,
`Mathlib.CategoryTheory.Sites.Point.Skyscraper`,
`Mathlib.Algebra.Homology.ShortComplex.ShortExact`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`. The docstring now follows
the node's three steps and notes the existing universe transport. The theorem
signature and natural-language node statement are unchanged; no statement correction
or citer audit is needed. The only theorem proof is still `by sorry`, and no new
definition, local notation, local instance, hidden hypothesis, or proof was added.

Validation: `scompile.py Q05 lem-kun-global-generated-stalkwise` compiled the delivered
file as a sandbox file and at its real library module path, in 4.6 and 4.8 seconds,
with no errors or warnings. The signature printed by `tools/stage2_delivery.py
signature` is verbatim equal to `lean.statement`; all universes and variables are
explicitly bound, every Lean line is at most 100 characters, and comparison with the
read-only base node shows that only its `lean` field differs.

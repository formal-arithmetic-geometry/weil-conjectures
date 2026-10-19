## Worker report

Repair of returned immutable head `040617da6c1d07ae1978afb74496ba42d4a9a92f`.
The retained module, main theorem, elementary generator constructions, and mathematical
node statement are preserved. The module is
`Sheaf.CategoryTheory.ProjectiveCochainMonoidalModel`; the theorem is
`HomotopicalAlgebra.projectiveCochainMonoidalModel`. Its sole postponed proof is `sorry`.
It asserts `Nonempty (ProjectiveCochainMonoidalModel R)`.

The returned review was opened in full. All five numbered findings are repaired:

1. `combinatorial` now has `CombinatorialModelCategory.{u + 1, u, u}`. The small-index
   universe is the module/Hom universe `u`, not the object universe `u+1`.
2. The arbitrary `monoidal` field is removed. Every tensor, unit and pushout product
   uses the fixed Mathlib `HomologicalComplex.monoidalCategory`, whose tensor is
   `HomologicalComplex.tensorObj`. `symmetricBraiding` identifies the symmetric
   structure's braiding with the existing upstream
   `CochainComplex.Monoidal.braidedCategory`; its formula is the Koszul formula proved
   by `CochainComplex.Monoidal.ι_braiding_hom`. The standard product Hom is reused
   from `CochainComplex.moduleHomComplex`, with `closedInternalHom` identifying the
   closed right adjoint's object with precisely that complex. `closedEvaluation`
   specifies its counit on homogeneous pure tensors, so the actual adjunction is
   constrained as well. The only added statement dependency is the already landed
   owning definition node `def-sc-module-total-hom-complex`. No duplicate Hom
   construction or arbitrary replacement map remains in the delivered module.
3. The substantive second reading below replaces the missing/placeholder reading.
4. Every declaration now has its source and blueprint annotation, including
   `cochainZero` and the two generating-class definitions. The main theorem's
   docstring contains all thirteen retained DAG proof steps and their dependency
   references, including the retract, Hom-defect and shifted-sign arguments.
5. Statement interfaces are public imports, including the recorded
   `Sheaf.CategoryTheory.CombinatorialLocalizationPresentability`. Every available
   proof dependency is imported as a proof-only import; the full list is below.

The statement, clause by clause, is rendered as follows:

| Node object, hypothesis or conclusion | Lean rendering |
| --- | --- |
| Every commutative ring, without nonzero, field, Noetherian or characteristic assumptions | `(R : Type u) [CommRing R]`, explicitly bound everywhere |
| All unbounded cochain complexes, differential of degree +1 | `CochainComplex (ModuleCat.{u} R) ℤ`, with `ComplexShape.up ℤ` |
| A complete and cocomplete model structure | Structure fields `model : ModelCategory ...`, `hasLimits : HasLimits ...`, `hasColimits : HasColimits ...` |
| Combinatorial in the dependency's sense | `combinatorial : @CombinatorialModelCategory.{u + 1, u, u} ... model`, including local presentability, set-generated weak factorization systems and functorial factorizations |
| Weak equivalences exactly the quasi-isomorphisms | Equality of the model's weak equivalences with `HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)` |
| Fibrations exactly termwise surjections | `fibrations` equates the model property with `ProjectiveFibration R`, which is `TermwiseSurjective f := ∀ n : ℤ, Function.Surjective (f.f n).hom` |
| Termwise split injection means degreewise R-linear retractions | `TermwiseSplitInjection f := ∀ n, ∃ r : B.X n ⟶ A.X n, f.f n ≫ r = 𝟙 _`; no retraction of complexes is demanded |
| Acyclic means zero cohomology in every degree | Mathlib `N.Acyclic`, characterized by `CochainComplex.acyclic_iff_isZero_homology` |
| dg-projective means projective terms and acyclic Hom into every acyclic complex | `DgProjective R P := (∀ n, Module.Projective R (P.X n).carrier) ∧ ∀ N, N.Acyclic → (P.HomComplex N).Acyclic`; forgetting only the R-module structure in this last test does not change cohomology vanishing |
| Cofibrations exactly split injections with dg-projective cokernel | `ProjectiveCochainCofibration R f := TermwiseSplitInjection f ∧ DgProjective R (cokernel f)`; field `cofibrations` equates it with the model class |
| Direct-sum total tensor with Koszul differential | Fixed `HomologicalComplex.monoidalCategory`; its `tensorObj` is the coproduct total tensor in `Mathlib.Algebra.Homology.Monoidal`; upstream `CochainComplex.ιTensorObj_d` gives `d_P ⊗ 1 + (-1)^i 1 ⊗ d_Q` on the `(i,j)` summand |
| Koszul symmetric structure | `symmetric` and `symmetricBraiding`, identifying its braided structure with the upstream Koszul construction, whose summand formula is `(-1)^(i*j)` times the module braiding |
| Product total module internal Hom | `closedInternalHom P Q` equates the right adjoint's object with `CochainComplex.moduleHomComplex P Q`; this has terms `HomComplex.Cochain P Q n` and `δ_hom R P Q n m`, i.e. the product of R-linear maps with differential `d_Q u - (-1)^n u d_P` |
| The tensor-Hom adjunction for those constructions | `closed : MonoidalClosed ...` supplies the adjunction; `closedEvaluation` fixes its evaluation on `x ⊗ φ` to `(-1)^(i*j) φ_i(x)`, as required with `P` first and the stated normalized Hom differential |
| Unit R[0], cofibrant | The fixed Mathlib monoidal unit is definitionally `HomologicalComplex.tensorUnit (ModuleCat.{u} R) (ComplexShape.up ℤ)`, the single complex on R in degree zero. `unitCofibrant` says its initial map is `ProjectiveCochainCofibration R`. The old unit equality became redundant after fixing the monoidal structure and was removed |
| Pushout product cofibrant, trivial if either input is trivial | `pushoutProduct` quantifies both arrows, assumes the two projective cofibration predicates, and concludes that the fixed tensor's pushout product is a projective cofibration and is a quasi-isomorphism if either arrow is one |
| S^n is R in degree n | `cochainSphere R n` is `HomologicalComplex.single ... n` applied to `ModuleCat.of R R` |
| D^n is R in degrees n,n+1, with differential +1 | `cochainDisk R n` is the mapping cone of the identity on `cochainSphere R (n + 1)`; Mathlib's positive cone off-diagonal is the required identity |
| Generator S^(n+1) → D^n, upper-degree identity | `cochainSphereDisk R n` is the cone inclusion `CochainComplex.mappingCone.inr` |
| Generator 0 → D^n, all integers | `cochainZeroDisk R n` is the unique initial map; all generator definitions quantify `n : ℤ` |
| These families generate the two cofibration classes | `projectiveGeneratingCofibrations` and `projectiveGeneratingTrivialCofibrations` are the left lifting classes of the right lifting classes of these generators. The corresponding structure fields identify them with cofibrations and with cofibrations intersect weak equivalences |

Statement dependencies read and used:

- `def-weil-abstract-derived-category`: public import
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, declarations `DerivedCategory`
  and `HasDerivedCategory`; cochain and quasi-isomorphism definitions are Mathlib's.
- `lem-coef-combinatorial-localization-presentability`: public import
  `Sheaf.CategoryTheory.CombinatorialLocalizationPresentability`, declaration
  `HomotopicalAlgebra.ModelLocalization.combinatorialLocalizationPresentability`.
  Its public shared interface is `HomotopicalAlgebra.CombinatorialModelCategory`
  in `Sheaf.CategoryTheory.ModelColimitLocalizationComparison`.
- `def-weil-pbc-projective-module`: public import
  `Mathlib.Algebra.Module.Projective`, declaration `Module.Projective` and its
  direct-summand/lifting interpretation.
- Added landed owner `def-sc-module-total-hom-complex`: public import
  `Sheaf.Algebra.Homology.ModuleHomComplex`, declaration
  `CochainComplex.moduleHomComplex`. Its full definition and two real property
  proofs were read. The node, whose record points to the published library,
  already specifies precisely the normalized module-valued Hom needed here.

Proof-only dependency imports, read against the nodes' recorded interfaces:

- `def-sp-grothendieck-abelian`: `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`,
  `CategoryTheory.IsGrothendieckAbelian`.
- `lem-coef-complexes-grothendieck`: `Mathlib.Algebra.Homology.GrothendieckAbelian`,
  `HomologicalComplex.isGrothendieckAbelian`.
- `lem-coef-grothendieck-locally-presentable`:
  `WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu`,
  `CategoryTheory.IsGrothendieckAbelian.isLocallyPresentable`.
- `lem-weil-pbc-complex-ses-homology-long-exact`: `Mathlib.Algebra.Homology.HomologySequence`,
  `CategoryTheory.ShortComplex.ShortExact.homology_exact₁`, `homology_exact₂`,
  `homology_exact₃` and the connecting morphism `δ`.
- `lem-coef-presentable-small-object-factorization`:
  `Sheaf.CategoryTheory.PresentableSmallObjectFactorization`,
  `CategoryTheory.MorphismProperty.hasFunctorialFactorization_of_isLocallyPresentable`.
- `lem-coef-presentable-cellular-factorization`:
  `Sheaf.CategoryTheory.PresentableCellularFactorization`,
  `CategoryTheory.SmallObject.exists_cellular_factorization_of_isLocallyPresentable`.
- `lem-coef-lifting-class-closure`: `Mathlib.CategoryTheory.MorphismProperty.LiftingProperty`,
  its `llp` and `rlp` stability under retracts, cobase change and composition.
- The two proof dependencies that are also statement dependencies are already public imports.

The module also reuses
`WeilConjectures.Mathlib.Algebra.Homology.Monoidal` for its actual Koszul braiding.
The upstream `CochainComplex.internalHomObj` was also opened; it uses a different
isomorphic sign convention, with component differential `(-1)^p(d_Q u - u d_P)`.
It cannot silently be substituted for the normalized `d_Q u - (-1)^n u d_P`
complex in this node. The already published `moduleHomComplex` is the exact
normalized construction, so no new definition is needed.

Edge cases checked: zero and nonzero rings of every characteristic; all positive,
zero and negative degrees; zero complexes and zero acyclic targets; no boundedness
or finite-support restriction on Hom cochains; tensor degrees use coproducts but
Hom degrees use products; either or both trivial factors in the pushout product.
All indexing universes are `u` where needed; no `u+1`-small coproduct is demanded.
The equality and evaluation fields include zero degree and all negative signs.

The node's recorded LeanSearch query (2026-10-16),
“The projective model structure on unbounded cochain complexes of modules over a
commutative ring is combinatorial symmetric monoidal with cofibrant unit”, returned
module monoidal instances, K-projectivity and generic model classes, not the theorem.
Its second LeanSearch query, “Cofibrations of complexes are degreewise split
monomorphisms with dg projective cokernel and tensor has the pushout product axiom”,
returned generic cofibration/lifting classes and the simplicial-set model.
These are retained historical searches, not claimed as new calls.

Fresh repair searches on 2026-10-17:

- `msearch.py ... leanfinder "product total internal Hom module cochain complexes closed tensor Koszul symmetry"`:
  eight hits, including `HomologicalComplex.tensorObj`, `ιTensorObj`,
  `CochainComplex.HomComplex`, the module structure on cochains and module evaluation.
- `msearch.py ... loogle "CochainComplex.HomComplex.δ_hom"`: two hits, the exact
  linear differential and its application lemma.
- `msearch.py ... grep "MonoidalClosed|productTotalInternalHom|projectiveCochainMonoidalModel" Algebra/Homology`:
  no Mathlib match for a closed complex instance or this model structure.
- Focused `rg` in upstream `WeilConjectures` and project `lean/Sheaf` for
  `HomComplex.Cochain`, `HomComplex.δ_hom`, `def.*[Hh]om[Cc]omplex` and
  `def.*[Ii]nternalHom` found the upstream differently signed internal Hom and
  the landed normalized `ModuleHomComplex` module. Those exact definitions were
  opened, and the latter is reused instead of the repair's temporary construction.
- Searches for `projectiveCochainMonoidalModel`, dg-projective/projective model
  language, and the item tag found no complete existing theorem. The bounded-below
  injective model and K-projectivity alone do not state this theorem.

The mathematical node is unchanged, so no statement correction or citer audit is
needed. Only `lean` and the allowed addition of the landed definition owner to
`stmt_deps` change in the JSON. No new node or dependency replacement module is delivered.

## Second reading by NA

This is a fresh repair reading of the previous worker's saved packet against the
item JSON, its thirteen proof steps, all recorded statement interfaces, the existing
module Hom construction, and the returned independent review. The node's source was
opened: Hovey's Model Categories, Definition 2.3.3, Propositions 2.3.4–2.3.5,
Lemmas 2.3.6 and 2.3.8, Proposition 2.3.9, Theorem 2.3.11 (printed pp. 41–44),
and Proposition 4.2.13 (printed pp. 111–112). The chain-to-cochain conversion sends
the lower chain sphere inclusion to the upper cochain sphere inclusion. I also
read the current blueprint ancestor paragraph 2; the coefficient adjunction route
is retained. Source: https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/hovey-model-cats.pdf.

The table in the worker report is the complete object/hypothesis/conclusion
checklist used for this reading. I rechecked each entry against the final file:

1. Ring and category binders match the arbitrary commutative ring and all
   integer-indexed complexes. There is no characteristic, nonzero or boundedness
   assumption. Projectivity uses the dependency's `Module.Projective`.
2. The weak-equivalence, fibration and cofibration equalities identify exactly
   the classes claimed, in both directions. The degreewise split condition is
   correctly weaker than a split mono in the category of complexes. The
   categorical cokernel is the usual degreewise quotient complex.
3. The returned universe defect is repaired: `.{u+1,u,u}` asks for local
   presentability at the Hom universe. I elaborated the actual partial application
   `@ModelLocalization.combinatorialLocalizationPresentability.{u+1,u,u}
   (CochainComplex (ModuleCat.{u} R) ℤ) inferInstance S.model S.hasLimits
   S.hasColimits S.combinatorial` for an arbitrary `S`.
   `scompile.py` accepted it and printed the localization conclusion with
   `IsPresentable.{u,u+1}`. The temporary `#check` was then removed.
4. The returned tensor/Hom under-specification is repaired. There is no arbitrary
   monoidal field: all uses resolve the imported total tensor instance. The
   symmetric structure has exactly the existing upstream Koszul braided
   structure. Internal Hom objects are the exact published normalized product
   total Hom complexes. The counit equation fixes the evaluation adjunction;
   its sign is necessary because `tensorLeft P` puts the argument `P` first.
   For `|x|=i`, `|φ|=j`, evaluation is `(-1)^(ij)φ_i(x)`; applying the two
   differentials cancels the two `φ(d_P x)` contributions and leaves
   `(-1)^(ij)d_Q(φ_i(x))`. Thus no wrong ungraded evaluation has been imposed.
5. The fixed unit is the single complex on R in degree zero, and its initial
   arrow is a projective cofibration. The pushout-product field is for the same
   fixed total tensor; its implication includes both trivial factors.
6. Sphere and disk definitions are unchanged. The cone of the identity on the
   sphere in degree `n+1` places its domain component in degree `n` and the
   codomain in `n+1`; the off-diagonal identity is positive. `mappingCone.inr`
   is the inclusion in degree `n+1`. The two lifting-class equalities express
   generation, not just membership of individual generators.
7. I checked the source/blueprint annotation of every helper, the main theorem's
   complete thirteen-step proof docstring, all fifteen listed declarations, the
   public statement imports and ordinary proof imports, the verbatim signature
   in `lean.statement`, explicit binding of `universe u`, both auto-implicit
   options, the single terminal `sorry`, and the 100-character line limit.

The fresh searches and edge cases are recorded above. They led to an additional
repair: reuse the already landed `CochainComplex.moduleHomComplex` and upstream
Koszul braiding instead of defining either again. No mathematical dispute remains.
Compilation of the final module and the required delivery dry run are the release
checks. This report records an actual reading and repairs, not a substitute claim
that the earlier external review had already approved the defective packet.


## Returned collision repair: immutable head 091771049a88

The retained packet was inspected first and `deliver2.py NA
lem-coef-projective-cochain-monoidal-model --no-push` was run before edits.
It failed while compiling the automatically loaded overlay
`Sheaf.CategoryTheory.SpaceValuedStraightening`, at line 64: its computable
`Diagrams` abbreviation depends on the noncomputable `smallSpaces`. This occurs
before the delivered file is compiled. The subsequent direct `scompile.py`
call reproduced the same diagnostic.

The returned collision was then checked against both the shared source and the
current server source obtained with `scompile.py --source
Sheaf.CategoryTheory.SiftedGoodDiagramCalculus`. Its existing declaration is:

```lean
def ProjectiveCofibration {M : Type u} [Category.{v} M] [ModelCategory M]
    {I : Type v} [SmallCategory I] {X Y : I ⥤ M} (f : X ⟶ Y) : Prop :=
  ∀ (E F : I ⥤ M) (p : E ⟶ F),
    (∀ i : I, Fibration (p.app i) ∧ WeakEquivalence (p.app i)) →
      HasLiftingProperty f p
```

This is the projective **diagram** cofibration predicate for an already supplied
model category. The delivered helper instead takes a commutative ring and a map
of unbounded module cochain complexes, without a model-category assumption, and
means the explicit conjunction of termwise splitting and dg-projectivity of its
cokernel. Its argument is a complex map rather than a natural transformation of
`I`-indexed diagrams. Substituting the existing declaration would require an
unprovided model structure and would change the condition that this theorem is
supposed to characterize. These are different notions and different signatures,
so the return's express exception for different declarations applies.

The specialized helper is now named
`HomotopicalAlgebra.ProjectiveCochainCofibration`. All five occurrence sites in
the model structure's cofibration equality, unit, and pushout-product fields are
updated; the node's `lean.declarations` is updated too. No declaration named
`HomotopicalAlgebra.ProjectiveCofibration` is introduced. There is no new proof,
no new definition body, no additional hypothesis, and no mathematical statement
change. The existing generic diagram predicate is left with its original owner;
importing its whole theorem module is unnecessary for the specialized condition.

### Repair self-check

I reread the node and complete delivered module. The clause-by-clause table and
second reading above continue to apply with the specialized predicate's new
name. The complex category, arbitrary commutative ring, the small-index universe
`u`, quasi-isomorphisms, surjective fibrations, termwise splitting, dg-projective
cokernels, fixed total tensor and Koszul symmetry, normalized product total Hom
and evaluation, cofibrant unit, pushout-product condition, and both generating
families are unchanged. The zero ring, zero complexes, negative degrees and
unbounded complexes therefore retain exactly their previous encodings.

Focused declaration searches in the shared `lean/Sheaf` and upstream
`WeilConjectures` found this single collision and no existing declaration with
the new specialized name. I checked the source dependency interfaces and current
node records, the one-terminal-`sorry` theorem, explicit universe and variable
binding, 100-character line lengths, and the verbatim recorded theorem signature.
Comparison with the shared base changes only `lean` and the already authorized
addition of the landed Hom-complex owner to `stmt_deps`; the delivery wrapper
performs the required rebase. The saved earlier repair is retained in full.


### Final release checks: blocked by automatic server overlay

The repaired module was sent again through the prescribed `scompile.py`; it
failed before reaching the delivered file. The final `deliver2.py --no-push`
also exited 1 with exactly the same failure and reported nothing pushed:

```text
Compiling overlay Sheaf.CategoryTheory.SpaceValuedStraightening
SpaceValuedStraightening.lean:64:7: error(lean.dependsOnNoncomputable):
failed to compile definition, consider marking it as 'noncomputable'
because it depends on 'smallSpaces', which is 'noncomputable'
```

The prescribed compiler implementation was read in the shared
`tools/nt_srv_compile.py`: `run` compiles every explicit source override from
`source-overrides.json` before inspecting the delivery's imports. This is an
automatically loaded server-overlay failure, not a diagnostic in this packet.
The source override and server/live source files are read-only to this worker;
changing them or the compiler is outside the authorized item/dependency packet.
The saved collision repair, node record, and self-check are ready for the next
wrapper retry after that overlay is repaired. No delivery was pushed, and no
compile or preflight success is claimed.

### Successful retry after the server overlay repair (2026-10-17)

This retry began by reading the retained report and running the required
`deliver2.py NA lem-coef-projective-cochain-monoidal-model --no-push` before
editing. That run reproduced the historical `SpaceValuedStraightening` overlay
failure. A direct `scompile.py` call also reproduced it in its immutable snapshot.
During validation the server source was repaired: `scompile.py --source
Sheaf.CategoryTheory.SpaceValuedStraightening` now reports
`noncomputable abbrev Diagrams`. No live source or compiler was edited by this
worker. The subsequent delivery dry run completed successfully: it compiled both
the sandbox and library versions of this packet's module and printed
`OK (dry run): commit 0ec51daff9 passes the preflight and compiles; nothing pushed`.
Thus the blocker described in the preceding historical section is resolved.

I retained the saved mathematical work and rechecked the return against the
current shared source. `SiftedGoodDiagramCalculus.ProjectiveCofibration` (in the
`HomotopicalAlgebra` namespace) is a lifting predicate on natural transformations
of diagrams in an already given model category. The present
`HomotopicalAlgebra.ProjectiveCochainCofibration` is the explicit split-injection
and dg-projective-cokernel predicate on module-complex maps before a model
structure is supplied. Their distinct signatures and meanings justify the
return's exception permitting renaming different declarations. The module
introduces no `HomotopicalAlgebra.ProjectiveCofibration` declaration.

The final self-check found no lines over 100 characters, explicit universe and
auto-implicit controls, one postponed theorem proof, and a verbatim match of the
theorem signature with `lean.statement`. Compared with the current shared node,
only `lean` and the authorized addition of the landed module-Hom owner to
`stmt_deps` differ. The clause and edge-case readings above remain applicable;
this retry changes only this report and retains the saved collision repair.
The delivery wrapper rebases and validates the packet against current main.

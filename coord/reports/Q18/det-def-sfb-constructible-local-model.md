## Worker report

Item: `det-def-sfb-constructible-local-model` (Q18, stage 2).
Source read: the item's complete node, every statement dependency and its recorded
Lean declaration or closed upstream audit, and blueprint main-20261015
`sec-proetale-coefficients/sk-def-sfb-constructible/` local-model statement and proof.
The resolved stage-1 repair note was read: it preserves the statement and the
reviewed counterexample route. No natural statement or dependency record is changed.

The module is `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`. It reuses the
already landed `AlgebraicGeometry.ProEtale.HasFiniteConstantLocalModel` from
`Sheaf.Paper.CondensedConstantConstructibility`, rather than defining it again.
That predicate uses finitely presented internal modules on the condensed point.
The new `finiteConstantLocalModel_iff_exists_cover` states its equivalence with the
source's ordinary scalar-module formulation. The remaining theorems give the
same-cover matrix equivalence, local finite presentation and failure of the converse.
All theorems have `sorry` proofs; every definition and instance with data is an
actual construction from existing functors, adjunctions, biproducts and scalar extension.

Hypothesis and clause correspondence:

- An arbitrary commutative condensed ring is
  `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}` with `[MonObj Λ]` and
  `[IsCommMonObj Λ]`. The site is the category of profinite sets with its coherent
  topology; the coefficient category is precisely the framework's abelian groups.
- The scalar ring Λ(*) is `scalarRingObj Λ`. Its underlying abelian group is
  evaluation of Λ at `op (Profinite.of PUnit.{u + 1})`. The monoid structure is
  transported through evaluation with the lax monoidal structure right adjoint to
  the monoidal constant-sheaf functor; `scalarRingObj_comm` records commutativity.
  An internal module `Mod Ab (scalarRingObj Λ)` is an ordinary Λ(*)-module,
  with its bilinear action encoded by the tensor universal property. Its
  `Mod.IsFinitelyPresented` is the finite-free-cokernel definition, including torsion.
- `scalarConstant X` first sheafifies the constant presheaf on the profinite site
  and then applies `upperStarFromPoint X`. It only applies inverse image to
  constant sheaves. `scalarConstant_iso_constantSheaf` explicitly states its
  monoidal natural identification with `constantSheaf (ProEt.topology X) Ab`.
  Thus the construction is the source's sheafified constant R_X and P_X,
  rather than the pullback of an arbitrary condensed module being called constant.
- The canonical map R_X → Λ_X is `scalarCoefficientHom Λ X`: apply `p_X^*`
  to the constant-sheaf adjunction's counit at Λ. On sections it pulls a scalar
  back from the point. No scalar map, section, isomorphism or action is supplied
  as an additional assumption. `scalarCoefficientHom_isMonHom` states that this
  actual map preserves the ring structure.
- `finiteConstantScalarExtension Λ X` is `mapMod` for that constant construction followed by
  `Mod.extendScalars (scalarCoefficientHom Λ X)`. Its value on P is literally
  the relative tensor construction Λ_X ⊗_{R_X} P_X of the dependency interface.
- The arbitrary scheme is `X : Scheme.{u}`. A module M has type
  `Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)`.
  No qcqs, Noetherian, nonempty, flat, torsion-free or characteristic assumption
  is imposed.
- A pro-etale cover is
  `𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X`, the existing covering
  interface with fpqc covering condition. Restriction to its i-th member is
  `(CondensedRing.upperStar Λ (𝒰.f i)).obj M`, the existing ringed-topos pullback
  including extension of scalars along the canonical coefficient comparison.
- Clause (1) on a specified cover is `HasFiniteConstantLocalModelOnCover Λ M 𝒰`:
  for every i, existential P with `Mod.IsFinitelyPresented (scalarRingObj Λ) P`
  and an isomorphism to `(finiteConstantScalarExtension Λ (𝒰.X i)).obj P`.
  The initial definition existentially quantifies exactly this cover in
  `finiteConstantLocalModel_iff_exists_cover`; the left side reuses the existing
  predicate and the right side spells out this scalar-module description.
- A scalar a is encoded by an additive map from the integer tensor unit to
  `scalarRingObj Λ`; its value at 1 is the actual element of Λ(*), with no
  restriction on that element. `scalarSection` includes the monoidal unit
  comparison and the canonical scalar map. `scalarMatrix` uses
  `Mod.regularLift` and `biproduct.matrix` to act between the finite free
  Λ_X-modules of ranks m and n. The first matrix index is the source column,
  the second the target row. This is precisely an arbitrary finite scalar matrix.
- Clause (2) is `HasScalarMatrixPresentationOnCover`: for every i there are
  m, n and the scalar matrix A, with the restricted M isomorphic to its cokernel
  in the coefficient module category. There is no arbitrary sheaf-matrix entry.
- The stated equivalence on the same given cover is
  `finiteConstantLocalModelOnCover_iff_scalarMatrix`. No refinement or cover
  replacement is hidden in either side.
- The consequence is `HasFiniteConstantLocalModel.isLocallyFinitelyPresented`,
  with exactly `IsLocallyFinitelyPresented (condensedRingObj Λ X) M` as conclusion.
- The final failure of the converse is
  `not_locallyFinitelyPresented_implies_finiteConstantLocalModel`: the universal
  implication, quantified over every commutative condensed ring, scheme and
  module, is false. This says that some coefficient ring, scheme and locally
  finitely presented module have no finite constant local model; it does not
  falsely assert that the converse fails for each fixed coefficient ring.
  Its proof docstring reproduces the reviewed seven-step counterexample route.

Dependencies read and used:

- `sk-def-sfb-condensed-ring`: the published
  `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing` and its
  `Profinite.isCommMonObj_continuousCoefficientRingObj` (with its public
  continuous-section constructors), together with the general condensed-sheaf
  encoding in the framework. Imported for the continuous ℚ_ℓ counterexample.
- `sk-def-sfb-pulled-back-coefficients`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`,
  `coefficientRing`, `condensedRingObj` and preservation of commutativity.
- `sk-def-sfb-module-objects`: Mathlib `CategoryTheory.Monoidal.Mod`,
  `ModObj`, `Mod`, `Mod.forget`, `Mod.regular` (closed upstream audit).
- `def-weil-pbc-proetale-site`: Mathlib `AlgebraicGeometry.Sites.Proetale`,
  `Scheme.ProEt`, `ProEt.topology`, `Scheme.proetalePrecoverage` and `Scheme.Cover`.
- `def-weil-pbc-constant-sheaf`: Mathlib `CategoryTheory.Sites.ConstantSheaf`,
  `constantSheaf`, `constantSheafAdj`, including the actual adjunction counit.
  `WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal` supplies its
  monoidal structure; the proof dependency on sheafification is inherited here.
- `def-sfb-modobj-extension`:
  `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`,
  `CategoryTheory.Mod.extendScalars` (closed upstream audit), including the
  coequalizer construction and extension/restriction adjunction.
- `def-sfb-finitely-presented-module`:
  `WeilConjectures.CategoryTheory.ModuleObjects.Free`,
  `Mod.finiteFree`, `Mod.IsFinitelyPresented` (closed upstream audit).
- `def-sfb-locally-finitely-presented`:
  `WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def`,
  `AlgebraicGeometry.ProEtale.IsLocallyFinitelyPresented`.
- `sk-def-sfb-module-pushforward-pullback`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`,
  `CondensedRing.upperStar`, defined as `mapMod` followed by actual extension
  along `condensedPullbackHom`, with its adjunction and composition structure.

Additional proof imports are the recorded point pullback, sheaf tensor,
ringed-site modules and locally constant prime spectrum modules, and the Mathlib
algebraic closure, residue field, affine coproduct, Spec/colimit and quasi-separated
modules. `det-pe-condensed-point-coefficients` and
`lem-sfb-coefficient-sections-localization` have no recorded declaration and no
closed upstream audit; there is therefore no stated module for them to import.
Their use remains in the counterexample proof docstring for stage 3.

The existing local-model predicate belongs to the constructibility module, whose
DAG node already has this item in both its statement and proof dependencies.
Importing that existing module is necessary to avoid H4, but adding its node as
this item's dependency would create a DAG cycle. No such reverse edge is added.
The maintainer must omit insertion of the reverse import of this module into
`CondensedConstantConstructibility`; the stage-2 import-cycle exception applies.
There is no Lean import cycle in the delivered module.

Edge cases checked before drafting and again against the final signatures:
zero ring and zero scalar module; zero free ranks m or n; empty matrices;
zero and identity matrix; the empty scheme and empty cover; varying P_i and ranks
on different covering members; disconnected schemes; torsion scalar modules;
all coefficient characteristics; arbitrary scheme universe u and coefficient
universe u+1. In particular no flatness is required for the cokernel calculation,
no uniform bound on the presentation ranks is introduced, and the converse
failure is existential in the coefficient ring. The ℓ-adic example uses a field
so each scalar model has finite rank, whereas its geometric fibre rank jumps at
∞; the finite affine covering condition rules out any constant-model cover.

Searches (all invoked through the prescribed search wrapper where applicable):

- LeanFinder: `finite constant local model module sheaf condensed ring scalar
  finite presentation`: 8 hits, including `Condensed.finFree` and the general
  `SheafOfModules` finite-presentation API; none gives this statement.
- Loogle: `CategoryTheory.Mod.extendScalars, CategoryTheory.constantSheaf`:
  0 hits, unknown upstream identifier `CategoryTheory.Mod.extendScalars`.
  The actual upstream declaration was then read in the shared framework.
- Mathlib grep: `constantSheaf|[Cc]onstant.*[Mm]odel|[Ss]calar.*[Mm]atrix`
  in CategoryTheory: 21 hits on constant sheaves and global sections; no match.
- LeanSearch: `finite constant local model sheaf of modules scalar matrix
  cokernel`: 8 hits on module cokernels and general sheaf presentations;
  none states the scalar local-model equivalence or counterexample.
- Project source rg: `finiteConstant|FiniteConstant|constant.*[Mm]odel|scalarRing|
  scalar.*[Mm]atrix`, and exact node-id grep: upstream has no exact local-model
  statement. The overlay's constructibility definition gives arbitrary local
  finite presentation, which is different from the scalar-entry condition.
- Shared `lean/Sheaf` rg with those terms and the subsequent exact
  `HasFiniteConstantLocalModel` name search located
  `Sheaf.Paper.CondensedConstantConstructibility` and its consumers. Its full
  declaration/docstring and owning DAG node were read. That definition is reused.
- Names checked against the upstream declaration index and project sources;
  the only other `scalarConstant` is in `WeilConjectures.IntegralOnSlice`,
  a different namespace and a different notion.

No new independent notion or node is needed: the helper declarations are the
scalar map, relative tensor and matrix already explicitly introduced by this
item. There is no statement correction and no STATEMENT-DISPUTED finding.

Validation: all compilation is via the prescribed `scompile.py`; the final
compile and delivery preflight results are recorded below after they complete.

Final `scompile.py` result: clean sandbox compilation (41.2 s) and clean
library-path server confirmation (9.5 s); no errors or warnings. The final
signature record was compared verbatim with the module, all 19 own declarations
are recorded, all 8 theorem proofs are `sorry`, the longest line has 99 characters,
and the natural statement is unchanged.


## Repair of return L (2026-10-18)

The saved packet was inspected and submitted to the prescribed initial dry run.
The returned head c0e06dc5d196 declares
`AlgebraicGeometry.ProEtale.scalarExtension`, also declared by
`Sheaf.SecSmoothPurity.OpenScalarExchange`. I read the latter module in the
shared checkout and confirmed its current source with `scompile.py --source`.
These declarations have different signatures and mathematical meanings:

- The existing `scalarExtension φ T` takes a homomorphism `φ : A →+* B`
  of ordinary constant coefficient rings and acts between the derived categories
  of sheaves over the constant ring sheaves `A_T` and `B_T`. It is derived
  extension along `Scheme.proEtaleConstantRingMap φ`.
- This item's helper takes a condensed ring Λ and a scheme X. Its domain is
  `Mod Ab (scalarRingObj Λ)`, the ordinary Λ(*)-module category; its codomain is
  `Mod (Sheaf (ProEt.topology X) Ab) (condensedRingObj Λ X)`, the ordinary
  module-sheaf category for the possibly nonconstant coefficient sheaf Λ_X.
  It sheafifies a scalar module and then uses the already existing
  `CategoryTheory.Mod.extendScalars` along the canonical scalar map.

Consequently the existing derived constant-ring functor cannot render the
relative tensor in this node. The return explicitly permits renaming when the
constructions differ. This helper is now `finiteConstantScalarExtension`;
its use in `HasFiniteConstantLocalModelOnCover` and its `lean.declarations`
entry are updated. An exact-name search in the upstream project and shared
`lean/Sheaf` found no existing `finiteConstantScalarExtension`.
The natural-language statement, main Lean signature, underlying construction,
and all other declarations are retained from the saved packet.

Repair self-check: the definition still has real functor data and reuses
`Mod.extendScalars`; the cover predicate still permits every finitely presented
scalar module, every cover member and all zero-rank/empty cases. The same-cover
matrix equivalence, local-finite-presentation consequence and universal converse
failure keep their signatures. All theorem proofs remain `sorry`.

Repair validation: the initial dry run printed OK (commit cce1c31a1e; nothing
pushed). The repaired module then compiled cleanly with the required
`scompile.py`: sandbox 19.6 s and library-path confirmation 4.9 s, with no
compiler errors or warnings. The final self-check confirmed the verbatim main
signature, all 19 declaration records, all 8 sorry-only theorem statements,
line lengths at most 100, and that only `lean` differs from the current DAG node.

## Second reading by Q18

Independent maintainer second reading, 2026-10-18, of immutable delivery
5bec8b98d315a8f1e8c263db4aaf69eb70fd147d. This reading was performed after the
worker delivery; the reviewer did not author or previously second-read it.

I read the item, all nine statement-dependency records, the blueprint local-model
statement and proof, all delivered Lean declarations and their docstrings, and
the exact dependency implementations in the Q18 side framework and Mathlib.
The source statement is rendered correctly:

- General commutative condensed coefficients are the sheaf Λ with MonObj and
  IsCommMonObj; X and M have exactly the dependency's scheme and internal-module
  types. No Noetherian, qcqs, flatness, nonemptiness or characteristic assumption
  is added. Profinite.{u}, Scheme.{u}, the small ProEt site and Ab.{u+1} follow
  the existing framework without equating distinct site universes.
- scalarSections is evaluation at the final profinite singleton. scalarRingObj
  receives its actual ring structure from the constant-sheaf/evaluation adjunction.
  Mod Ab (scalarRingObj Λ) is the ordinary scalar-module category, and the reused
  Mod.IsFinitelyPresented is a finite-free cokernel condition, including torsion.
- scalarConstant is constant sheafification followed by inverse image, and
  scalarConstant_iso_constantSheaf identifies it monoidally with constant
  sheafification on X. This applies inverse image only to constant sheaves.
- scalarCoefficientHom is the inverse image of the actual adjunction counit.
  Its ring-hom property is separately stated. It is the source's canonical
  scalar map, with no arbitrary map or extra scalar-identification hypothesis.
- finiteConstantScalarExtension is mapMod followed by the existing coequalizer
  extension of scalars. Its domain and codomain differ from the derived
  scalarExtension in OpenScalarExchange, so the repair's rename is appropriate.
- HasFiniteConstantLocalModelOnCover quantifies separately over every member of
  the specified pro-etale cover, then over a finitely presented scalar module
  and an isomorphism with its extension. finiteConstantLocalModel_iff_exists_cover
  existentially quantifies that cover and connects the formula to the existing
  HasFiniteConstantLocalModel. Reading the latter definition shows it uses
  finite-free presentations on the condensed point; their arrows are exactly
  scalar matrices. Thus the bridge does not identify arbitrary condensed modules
  with constant sheaves, and avoids a duplicate definition.
- scalarSection includes the monoidal unit comparison. scalarMatrix uses
  regularLift and biproduct.matrix; its first index is the source column, its
  second the target row. Every scalar is allowed, via a map from the integer
  tensor unit. HasScalarMatrixPresentationOnCover has the required cokernel
  in the coefficient module category, on the same cover.
- finiteConstantLocalModelOnCover_iff_scalarMatrix states both implications on
  that fixed cover. The adjunction/cokernel proof plan preserves actual matrix
  entries and requires no flatness. HasFiniteConstantLocalModel.isLocallyFinitelyPresented
  has precisely the recorded local-finite-presentation predicate as conclusion;
  transport along the canonical coefficient isomorphism explains the different
  presentation categories in the two definitions.
- not_locallyFinitelyPresented_implies_finiteConstantLocalModel negates the
  universal implication over all coefficients, schemes and modules. It therefore
  says the converse fails in general, rather than for every coefficient ring.
  Its docstring retains the node's seven-step argument: the function tending
  to zero on the profinite convergent sequence, the one-by-one cokernel,
  unit/zero geometric fibres, finite scalar ranks, and the finite-affine-cover
  compactness contradiction. The quotient module is locally finitely presented;
  zero-rank covering members cannot cover the nonclosed finite-point locus by
  finitely many compact images. No unstated statement prerequisite is needed to
  formulate these declarations. The as-yet unstated coefficient-evaluation and
  localization proof lemmas remain proof dependencies, not arbitrary input maps.

I checked zero rings, zero scalar modules, m=0, n=0, empty matrices, zero and
identity matrices, empty schemes and covers, disconnected schemes, varying local
ranks and presentations, torsion, all characteristics, and the framework's
universe binders. The universal counterexample does not claim failure on an empty
scheme or for the zero ring. There is no uniform rank bound.

One-definition searches with local-model, scalar-matrix and exact declaration
names in Mathlib, upstream WeilConjectures and lean/Sheaf located the existing
HasFiniteConstantLocalModel, which is reused. Other scalarSections/scalarConstant
hits have different namespaces and types. I read Mod.regularLift, Mod.finiteFree,
Mod.IsFinitelyPresented, Mod.extendScalars, constantSheaf/constantSheafAdj,
upperStarFromPoint, condensedRingObj, CondensedRing.upperStar and
IsLocallyFinitelyPresented, rather than relying on their names. The module-object
abbreviations of the recorded dependency reduce to the same Mathlib Mod used here.
The report retains the worker's LeanSearch, LeanFinder/Loogle and grep records.

All 19 own declarations are recorded; all eight theorem bodies are only sorry.
Definitions and data instances are actual constructions, with required proof
obligations separated into named theorems. Source/blueprint docstrings and proof
plans are present. The primary lean.statement matches the file verbatim; maximum
line length is 99. No source-based statement correction or citer audit is needed.
The existing defining module is imported without adding a reverse DAG edge; its
parent must not acquire a reverse proof import that creates an import cycle.

The current dropped-node list has no intersection with the item's stmt_deps or
proof_deps. The repair note's by field is L (human decision), not route pivot;
its resolved note concerns splitting the old counterexample proof. This module
introduces no infinity/dg/model-category machinery and no replacement site.

Reproduction used exactly:
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q18
  det-def-sfb-constructible-local-model
  snapshot/lean/Sheaf/AlgebraicGeometry/FiniteConstantLocalModel.lean
(on one command line). Exit status was 0, with no errors or warnings. The wrapper
reported sandbox compilation 8.8 s and library-path confirmation 66.2 s. These
are the wrapper's reported elapsed times; its own compiler-limit and overlay
handling were left unchanged. The currently installed wrapper dispatches to the
server side overlay; no direct ssh or alternative compiler was invoked.
No global build, live Lean write, delivery, merge or repository mutation occurred.

Finding and correction: H1/H11, the delivered second-reading section was only a
statement that no second reading occurred. It did not satisfy the explicit
maintainer-review requirement for a real reading. This complete section replaces
that placeholder. The mathematics, Lean module and node record need no change.

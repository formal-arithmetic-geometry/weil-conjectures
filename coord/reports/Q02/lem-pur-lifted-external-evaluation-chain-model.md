## Worker report

Item: `lem-pur-lifted-external-evaluation-chain-model`, Q02, stage 2.
Module: `Sheaf.Paper.LiftedExternalEvaluationChainModel`.

Six named theorem statements, each with `sorry`, render the clauses of this single
node. No definition is introduced and no mathematical theorem is proved. The
natural-language statement, dependencies, proof and all other node fields are
unchanged; only `lean` is recorded. There is no statement dispute or correction.

### Hypotheses and objects

- Commutative A: `A : Type (u + 1)` and `[CommRing A]`. Schemes and the two arbitrary
  morphisms: `{X Y P : Scheme.{u}}`, `a : P ⟶ X`, `b : P ⟶ Y`.
  This is the recorded six-functor common-module-universe convention. Site object
  and arrow universes are not identified: the small etale site still has its native
  object/morphism universe levels, while modules and rings live in `u + 1`.
- Ordinary module cochain complexes: `Complexes A X` and `Complexes A Y`, the existing
  aliases for `CochainComplex (Sheaf smallEtaleTopology (ModuleCat A)) ℤ`.
- Bounded flat E and H: `hE : IsBoundedFlat A E` and `hH : IsBoundedFlat A H`.
  This existing predicate says there exist finite lower and upper term bounds,
  and every term is flat using `SheafOfModules.IsFlatOnSite` after the canonical
  existing scalar realization. No uniform bound is chosen or assumed.
- K-injective representatives: `[I.IsKInjective]`, `[I'.IsKInjective]`.
  K and L are their localized objects `(siteQ A X).obj I` and
  `(siteQ A Y).obj I'`; `hK`, `hL` assert `IsPlus` of these objects. Using the
  representatives as the names of K,L loses no object: an arbitrary specified
  representative isomorphism transports the normalized comparisons functorially.
- The bounded-below external target is precisely `hF : IsPlus A (external A a b
  ((siteQ A X).obj I) ((siteQ A Y).obj I'))`, with the recorded derived inverse
  images and derived tensor, not ordinary tensor of I and I'.
- All U,V, alpha,gamma, evaluations, lifts, homotopies and final resolutions are
  universally quantified by the existing `HasChainNormalization A a b E H I I'`.
  Its `f,g` are alpha,gamma with `[QuasiIso f]`, `[QuasiIso g]`. Its two independent
  `IsKFlatIndependentCoefficients` hypotheses on `pointComplex` and its two
  degreewise `IsFlatOnSite` hypotheses are exactly flat-term K-flat U,V. These use
  the already existing one-point realization, not a new definition of K-flatness.
- In that predicate `t,t'` have type `chainEvaluationSource ... ⟶ I` (respectively
  I'), and `IsChainEvaluation ... f t` is the componentwise evaluation formula.
  It then quantifies over N,M,u,v,c,c', with quasi-isomorphism instances on c,c',
  K-flatness of `ringedComplex N/M`, flatness of every term under `ringedRealization`,
  and `Nonempty (Homotopy (u ≫ c) t)`, `Nonempty (Homotopy (v ≫ c') t')`.
  Thus neither equality of chain maps nor strict factorization replaces homotopy.
- Its final quantifiers are over every J and `i : externalComplex ... N M ⟶ J`
  with `[QuasiIso i]`, `[J.IsKInjective]`. There is no choice or existence-only
  replacement of the given homotopy lifts or of i.

### Conclusions and formulas

1. `lifted_external_evaluation_chain_evaluation` says that the unsigned formula
   `t(w ⊗ e) = alpha(w)(e)` defines a chain map. Its conclusion is `∃ t,
   IsChainEvaluation A E I U α t`. The existing predicate evaluates every degree,
   every local section and every cochain through the direct-sum tensor inclusion
   and constant-sheaf unit. Apply it on X and on Y.
2. `lifted_external_evaluation_chain_model` supplies the normalized `HomModel`
   isomorphisms on X and Y, together with `HasChainNormalization` for every lift.
   That predicate produces a chain map `κ : U ⊗ V ⟶ homComplex A G J` and fixes it
   by `IsChainEvaluation` against `chainPairEvaluation ... u v i`.
   Here `externalComplex A a b E H` is exactly G and
   `externalComplex A a b N M` is exactly T. `chainPairEvaluation` is the existing
   actual composite: constant/pullback comparisons, the total-complex `tensorμ`
   interchanging the V and E factors, pulled-back u and v, followed by i.
   Its braiding contributes `(-1)^(s*q)`, with s the V degree and q the E degree.
   The construction uses the canonical sheafification maps on local pure tensors.
   Thus the predicate encodes the displayed local formula, rather than an
   arbitrary map with an unspecified Koszul normalization.
3. The equation in `HasChainNormalization` is the full localization identity:
   tensor the normalized Q(f),Q(g) comparisons; apply the canonical `pairing`;
   map the target by `targetModel`; the result equals the ordinary tensor
   localization comparison followed by Q(κ), the normalized target Hom model,
   and contravariant transport through `externalModel`. `pairing` is defined by
   the canonical constant/sections and internal tensor/Hom adjunctions and the
   two pulled derived evaluations. No derived evaluation or transpose is assumed
   as an extra hypothesis.
4. The remainder of the main statement explicitly asserts `IsIso (targetModel
   ... (externalComplex ... N M) c c' (𝟙 _))`. Its source is F and target is QT,
   so T represents F before choosing any resolution. For every i,J it also
   asserts `IsIso (targetModel ... J c c' i)` and `Nonempty (HomModel A G J)`.
   This supplies the canonical target identification needed in the preceding
   normalization equation, rather than presupposing it. The two source Hom
   models and Q(f),Q(g), with K-flat U,V, give the stated source identification.
   Universal quantification over all choices makes every resulting localized map
   the same `pairing`; no chosen resolution is declared canonical on its own.
5. `lifted_external_evaluation_hom_shift` is for any complex B and K-injective I,
   with no boundedness hypothesis. It supplies the actual chain isomorphism θ.
   Its component is `f.leftUnshift (n + -1) ...`; the existing Mathlib
   `CochainComplex.HomComplex.Cochain.leftUnshift_v`, specialized to a=1,
   gives exactly `(-1)^n f^(p-1)` with the required index identifications.
6. `lifted_external_evaluation_shifted_lift` supplies θ with the same component
   normalization and η as a chain isomorphism from the shifted evaluation source
   to the original one. Its explicit local-section equality is multiplication
   by `r.negOnePow`, after `shiftFunctorObjXIso` identifies w with its degree
   r-1 value and e with its degree q+1 value. This is the node's η, including
   the sign of the shifted U degree, not its unshifted degree.
7. The shifted quasi-isomorphism is explicitly `α⟦(-1 : ℤ)⟧' ≫ θ.inv`. Its
   evaluation is `η.hom ≫ t`, and the shifted factorization is `η.hom ≫ u`
   with the unchanged c and N. `Nonempty (Homotopy ((η.hom ≫ u) ≫ c)
   (η.hom ≫ t))` asserts the required homotopy. The same statement also explicitly
   preserves U's K-flatness, all its flat terms, and E's bounded flatness under
   the prescribed shifts. Applying this theorem separately on X and Y allows
   either or both inputs to shift. Neither N nor M changes, so the definition
   of T is literally the same term and each original J,i remains available.
8. `lifted_external_evaluation_derived_hom_shift` supplies the derived Hom shift
   structures and `HasSignedHomShift`. Unfolding that existing predicate gives
   target naturality and the equality between localized θ and the derived
   first-variable shift through every evaluation-normalized Hom model. Its
   cochain component is the same `leftUnshift` formula. An additional universal
   clause supplies normalized models m,m' and the full localization equality
   for arbitrary B and arbitrary K-injective I, without any IsPlus condition.
   The explicit `@negativeHomShiftIsoOf` application supplies the selected S
   instance without a let binder. Thus the realization assertion retains all
   unbounded targets as well as those needed in the external evaluation.

The source identification is additionally explicit in
`lifted_external_evaluation_source_model`: for the same point-realized K-flat and
flat-term U,V hypotheses, the actual localization tensor constraint
`Functor.LaxMonoidal.μ (moduleQ A) U V` is an isomorphism. Thus the normalization
identity uses proved-to-be-invertible comparisons on both ends, rather than leaving
the source identification only implicit in the K-flat hypotheses.

### Dependency declarations read and used

- `def-pc-scheme`: Mathlib.AlgebraicGeometry.Scheme,
  `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `def-weil-size-convention`: metatheoretic convention, no declaration; explicit
  universe u and coefficient/module universe u+1 as above.
- `def-weil-pbc-derived-categories`: WeilConjectures.AlgebraicGeometry.DerivedCategories
  and its public import of SixFunctors.Etale.Derived.Coefficients,
  `AlgebraicGeometry.Etale.DerivedCategoryModule`; Mathlib `DerivedCategory.IsGE`
  through the existing `IsPlus` predicate.
- `def-weil-pbc-inverse-image`: WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs,
  `AlgebraicGeometry.Etale.upperStar`, through `pullComplex` and `pull`.
- `def-pc-tensor-complex-sheaves`: Mathlib.Algebra.Homology.BifunctorShift,
  `CochainComplex.mapBifunctor` and the native `HomologicalComplex.tensorObj`.
- `def-pc-cochain-complex-modules`: Mathlib.Algebra.Homology.HomologicalComplex,
  `CochainComplex`.
- `def-pc-flat-sheaf-modules`: Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite,
  `SheafOfModules.IsFlatOnSite`, through the canonical existing realization.
- `def-pur-kinjective-complex`: its Mathlib match
  Mathlib.Algebra.Homology.HomotopyCategory.KInjective,
  `CochainComplex.IsKInjective`, and Mathlib `Homotopy`.
- `def-kun-derived-tensor`: WeilConjectures.SixFunctors.Etale.Derived.Tensor,
  `AlgebraicGeometry.Etale.derivedTensor`, the fixed derived monoidal tensor.
- `def-kun-constant-sheaf`: Mathlib.Algebra.Homology.Additive,
  `Functor.mapHomologicalComplex` on `constantSheaf`, through `constantComplex`.
- `def-pur-derived-internal-hom`: Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
  publicly exposes the recorded ordinary-etale `Etale.derivedHom` and its
  `derivedTensorHomAdjunction`; `globalHom`, `transpose` and `evaluation` use
  precisely that existing closed structure and right-derived sections.
- `def-kun-constant-projection-morphism`:
  Sheaf.AlgebraicGeometry.EtaleConstantProjectionMap,
  `derivedConstantGlobalSectionsAdjunction`, normalized constant-sheaf monoidal
  constraints, and the existing canonical left-derived tensor comparison.
- `def-pc-kflat-complex`: Sheaf.Algebra.Homology.KFlatIndependentCoefficients,
  `CochainComplex.IsKFlatIndependentCoefficients`, on the existing ringed and
  point realizations, without replacing the defining acyclic-tensor test.
- `def-pc-quasi-iso-modules`: Mathlib.Algebra.Homology.QuasiIso, `QuasiIso`.
- `def-pur-hom-complex`: WeilConjectures.Algebra.Homology.HomComplex,
  `CategoryTheory.homComplex`. The global version used here is the existing
  `ExternalRHom.homComplex`, built from Mathlib's global linear cochains with
  `δ_hom`, not another product-Hom construction. Its signature and body and
  the recorded internal-Hom signature/docstring were read.
- `def-weil-abstract-derived-category`:
  Mathlib.Algebra.Homology.DerivedCategory.Basic, `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q`, and the native signed cochain shift.

The already stated proof dependencies are imported by their recorded modules:
`Sheaf.Algebra.Homology.KFlatTotalTensorModel`,
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`,
`Sheaf.Algebra.Homology.KInjectiveHomComplex`, and
`Sheaf.SixFunctors.ResolvingDerivedAdjunction`. The proof-only nodes
`lem-pur-global-hom-evaluation-flat-lift`, `lem-pur-external-evaluation-transpose-natural`
and `lem-sfb-hom-kflat-chain-transpose` have no recorded module in this checkout;
no nonexistent import is fabricated. They are not missing notions required by the
statement: all evaluation and adjunction constructions are already present.

Existing helper definitions are reused from `Sheaf.Paper.ExternalRHomConePairing`.
Its downstream theorem `external_rhom_cone_pairing` is neither invoked nor assumed.
Import-cycle notice for the maintainer: do not add a reverse proof-only import of
this module to ExternalRHomConePairing; stage 2 rule 7 explicitly omits such imports
when they close a cycle. This delivery makes no edits outside its sandbox.

### Edge cases and source check

Read sites-cohomology.tex, sections hom-complexes and internal-hom, including
lemma-compose (0A90), and the node's nine explicit proof steps. Checked zero
complexes, the zero coefficient ring, empty schemes/sites, identity morphisms,
negative cochain degrees, unbounded B in the Hom-shift clause, and independent
choices of N,M,J,i. No nonempty scheme, nontrivial ring, lower degree bound on B,
finite-rank condition, torsion condition or characteristic restriction is imposed.
For η the four differential contributions reduce to
`(-1)^r dw ⊗ e - w ⊗ de`, agreeing on both sides. For θ the sign is that of n,
not n-1; in characteristic 2 the same unit-scalar formulas still make sense.
No product is replaced by a direct sum in Hom. T uses the flat replacements,
never the ordinary tensor of the K-injective representatives.

### Searches

Search outputs are also retained in sandbox searches.jsonl.

- msearch LeanFinder: "Chain representative of external derived Hom evaluation
  from K-flat lifts and Koszul interchange, compatible with first-variable shift".
  Eight general Ext/derived-fraction results; no exact theorem.
- msearch Loogle: "HomologicalComplex.homComplex,
  CochainComplex.shiftFunctorObjXIso, CochainComplex.tensorObj".
  No hits; first expected identifier was unknown. Replaced the guessed names by
  signatures actually read in the local source and confirmed with server #check.
- msearch grep: `globalHom|homComplex|tensorObj`, Mathlib/Algebra/Homology.
  Found existing HomComplex cochains, shift formulas, and direct-sum tensor API.
- msearch LeanSearch: "External evaluation of derived global Hom computed using
  K-flat lifted evaluations with Koszul sign and simultaneous shifts".
  Found `Cochain.leftUnshift`, `leftUnshift_v`, shiftEval, and generic Ext results;
  no theorem giving this combined node.
- rg over lean/Sheaf and lean/WeilConjectures for external evaluation, global Hom
  and Hom shifts found ExternalRHomConePairing's helper definitions and generic
  HomComplexShiftLeft. Those are reused; the former's combined cone theorem does
  not state the present node's common shifted homotopy lift.
- rg for the exact item id in lean/WeilConjectures found no declaration. The DAG
  search found this node and its parent citer only; no duplicate node was created.
- The suggested CompactObject example has been withdrawn to an empty module in
  this checkout; the format follows the actual live ExternalRHom modules and
  the full written stage-2 convention instead.

### Validation

All checks use the prescribed scompile.py server wrapper, one file at a time,
within the unmodified 60-second limit. An initial guessed proof import path was
corrected to the dependency's recorded Algebra.Homology path. The opposite-category
shift interface needed `open CategoryTheory.Pretriangulated.Opposite`, as in its
owning module. Expected `sorry` declarations are the only postponed proofs.
The final dry-run and delivery output record the final compile and preflight.

## Second reading by Q02

This is a separate self-audit pass by the dispatched worker, not a claim of an
independent agent review. The brief forbids starting other agents and assigns the
independent delivery review to the maintainer.

With the node and final module open, traced the hypotheses through
HasChainNormalization: both alpha maps are quasi-isomorphisms, both U,V and N,M
have separately stated K-flat and term-flat conditions, both factorizations use
homotopies, and every K-injective i,J is quantified. The target is the same
externalComplex N M before and after η. Traced the localization equality through
pairing, targetModel and externalModel; it uses the actual canonical comparisons,
not arbitrary representative isomorphisms. Traced the local formula through
tensorμ and IsChainEvaluation, which gives the prescribed s*q sign.

The first audit found that preserving shifted flatness and K-flatness was only
explained in prose, and that the derived interpretation of θ needed a visible
normalization conclusion. These were added explicitly to shifted_lift and the
separate derived_hom_shift statement. It also made the existence of the unsigned
chain evaluation explicit rather than only using its predicate as a hypothesis.
Checked α[-1] then θ inverse is the composition order in Lean, η's sign is r,
and the shifted homotopy uses exactly the original c,N. Checked the standalone
Hom-shift theorem has arbitrary B and no IsPlus condition. The final source-model audit also made invertibility of the source tensor
constraint an explicit theorem conclusion. The final derived-shift clause was
also extended to state the normalized equality for arbitrary K-injective I,
without an IsPlus hypothesis. No natural-language
node correction, added notion, dependency-interface replacement, or unresolved
statement dispute remains.

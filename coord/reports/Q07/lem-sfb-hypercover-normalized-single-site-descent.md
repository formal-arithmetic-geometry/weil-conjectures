## Worker report

Item: `lem-sfb-hypercover-normalized-single-site-descent`.
Group: Q07. Date: 2026-10-22 (UTC).
Module: `Sheaf.AlgebraicGeometry.ProEtaleNormalizedHypercoverDescent`.
Namespace below: `AlgebraicGeometry.Scheme.ProEt.NormalizedDescent`.

This delivery states the unchanged node, with `descent` as the primary declaration
and the other recorded declarations supplying its explicit formula, naturality,
signed homotopy, refinement identities, and degree-zero coefficient identification.
All 17 theorem proofs are `sorry`. Definitions contain actual data. There are no
new DAG nodes, dependency repairs, statement corrections, or disputed statements.
The item JSON differs only in `lean`.

The preserved sandbox contained only launcher brief markers, not the previous
worker's claimed report or Lean files. The live stage-1 review passes and there is
no released repair note. This is a stage-2 delivery; it does not reopen or alter
that split. The prescribed stage-2 compile wrapper accepts the work.

### Hypothesis-by-hypothesis and clause-by-clause correspondence

| Node text | Lean rendering |
| --- | --- |
| A scheme X and its small pro-etale site | `X : Scheme.{u}`, `X.ProEt`, `topology X`, from the recorded Mathlib definitions. |
| Compatible site and coefficient sizes | The site has object universe `u+1`, morphism universe `u`; `R : Sheaf (topology X) CommRingCat.{u+1}`, and `Modules X R` uses module universe `u+1`. The two explicit `HasDerivedCategory.{v}` / `.{w}` parameters choose the localizations required by the recorded size convention. They impose no equality between site universes, and such localizations exist (e.g. the standard construction). |
| A sheaf of commutative rings, and its module sheaves | `R` as above; `Modules X R` is a transparent abbreviation of the recorded `ringedSiteModules` after the standard forgetful functor from commutative rings to rings. No alternate category is defined. |
| An arbitrary site object W | `W : X.ProEt`; no terminal-object, affineness, or quasi-compactness restriction. |
| An augmented simplicial object U over W | `U : SimplicialObject (Over W)`; the slice supplies the augmentation and its compatibility with all operators. |
| Finite proper-face matching objects exist and matching arrows cover | `IsHypercover X W U` is exactly `∀ n, ∃ M μ, IsProperFaceMatchingArrow U n M μ ∧ Sieve.generate (Presieve.singleton μ.left) ∈ topology X M.left`. Existence is explicit, so the covering condition cannot be vacuous. This helper only bundles this node's displayed hypotheses. |
| Degree-zero matching object is W | The recorded proper-face predicate in degree zero says `M` is terminal in `Over W`. This is the identity object of W, up to the unique terminal isomorphism. Degree one is the fibre product over W; higher degrees use the recorded limiting boundary diagram. |
| Every U_p is weakly contractible | `hweak : ∀ p : ℕ, (topology X).IsWeaklyContractible.{u+1} (U _⦋p⦌).left`. The recorded definition uses locally surjective set-sheaf maps, equivalent to epimorphisms by `Sheaf.isLocallySurjective_iff_epi`. |
| Integer-indexed strictly bounded-below E, F, I | `CochainComplex (Modules X R) ℤ`, integer bounds `NE`, `NF`, `NI`, and the corresponding `IsStrictlyGE` instances. Bounds may be negative, distinct, or zero. |
| Signed coproduct total T_U with delta+(-1)^p d | `total` composes the recorded `hypercoverTotal X R W U` with termwise forgetting of scalars. It does not reconstruct a total or alter its sign/order. The published total first flips the coefficient/section bicomplex so p is the first index. |
| Restriction augmentation alpha_E into (0,q) | `augmentation` is `Functor.whiskerRight (hypercoverAugmentation X R W U)` by the same forgetful functor on complexes. It uses the existing actual restriction augmentation. |
| All conclusions after forgetting scalars, in D(Ab) | `evaluation`, `total`, and `augmentation` take values in `AddCommGrpCat.{u+1}` or its complexes; every displayed `DerivedCategory.Q` on these values is the abelian-group localization. |
| Evaluation of module sheaves at each U_p is exact, without affineness | `evaluation_exact` states `∀ p, (evaluation X R (U _⦋p⦌).left).PreservesHomology`, the exact-functor formulation for additive functors of abelian categories. There is no `IsAffine` binder. |
| Evaluation preserves every coefficient quasi-isomorphism | `evaluation_quasiIso` applies to arbitrary integer-indexed complexes and `[QuasiIso f]`, with no boundedness needed for evaluation itself. |
| T_U sends bounded-below quasi-isomorphisms to quasi-isomorphisms | `total_quasiIso`, with independent lower bounds for E and F. |
| alpha_I is a quasi-isomorphism for every bounded-below termwise-injective I | `augmentation_quasiIso` uses `I.IsStrictlyGE N` and `[∀ n : ℤ, Injective (I.X n)]`. Injectivity is in module sheaves, not an assumption about underlying abelian sheaves. |
| Every resolution i:E to I has both quasi-isomorphisms | The universal resolution clause of `descent` states both `QuasiIso ((total ...).map i)` and `QuasiIso ((augmentation ...).app I)` for every I, NI, and i with the stated properties. No monomorphism of i is assumed. |
| Actual right derived evaluation R Gamma(W,-) | `derivedEvaluation` is the recorded `evaluation.rightDerivedFunctorOfQuasiIsoResolutions (coefficient_resolutions X R)`. Its unit is the universal unit from that API. `coefficient_resolutions` records the existence used to instantiate this definition, obtained from the existing general ringed-site resolution node. |
| Canonical rho_i on any bounded-below injective resolution | `resolutionComputation` uses `isKInjective_of_injective I N` and the recorded `rightDerivedFunctorOfQuasiIsoResolutionsObjIso`. This is RF(Qi) followed by the inverse universal unit and canonical Q/quotient identifications, not a freely chosen isomorphism. |
| A_U,E=(QT_U(i))^-1 Q alpha_I rho_i | `comparison_formula` states equality with `resolutionComputation ... ≪≫ injectiveAugmentationIso ... ≪≫ (resolutionTotalIso ...).symm`. The latter two helpers are `asIso` of the actual localized arrows, justified by named quasi-isomorphism theorems. |
| Independence of resolution | `descent` gives `∃! A` satisfying the normalization for every resolution; `comparison` chooses this uniquely characterized A. `comparison_formula` holds for every i, so every displayed formula equals the same comparison. The theorem determines the chosen object up to equality. |
| Every-resolution normalization | `comparison_normalization` states `comparison.hom ≫ QT(i) = rho_i.hom ≫ Q(alpha_I)`, i.e. exactly the node's equation in Lean's diagrammatic composition order. |
| Naturality for all coefficient chain maps | `comparison_naturality` takes an arbitrary `f : E ⟶ F` between bounded-below complexes, and states `A_E ≫ QT(f) = RGamma(Qf) ≫ A_F`. No strict lift of f to resolutions is assumed. |
| Signed coefficient homotopy | `signed_homotopy` states existence of an actual `Homotopy` between the total maps. On each total injection (p,q), its component is exactly `(-1 : ℤˣ)^p` times the section-row map of `s.hom q q'`, followed by the (p,q') injection, where q'+1=q. The homotopy type itself requires zero components off degree -1 and the chain-homotopy equation. The formula uses arbitrary integer p, so negative zero rows are included. |
| Homotopy-commuting resolution comparison k | `resolution_comparison` takes `s : Homotopy (i ≫ k) i'` and states both `QT(i) ≫ QT(k)=QT(i')` and `rho_i.hom ≫ QGamma(k)=rho_i'.hom`. This is the exact orientation of the node after converting composition notation. |
| Refinement r:U' to U over W and its actual section restrictions | `rowRefinement` uses `r.rightOp`, ordinary presheaf/module restriction on `Over W`, the alternating coface map, and extension by zero. `refinement` applies that natural transformation termwise and then the same flip, total, and forgetting functors. No map or nonempty existence choice is supplied as a hypothesis. |
| r_I alpha_I=alpha'_I | First conjunct of `refinement_squares`. |
| r_I T_U(i)=T_U'(i) r_E | Second conjunct of `refinement_squares`. It is stated already for coefficient chain maps, hence applies to every resolution. |
| Qr_E A_U,E=A_U',E for another hypercover satisfying the same assumptions | `comparison_refinement` with the independent matching-cover and weak-contractibility hypotheses for V=U'. |
| Refinement maps commute with coefficient maps, identities, and composites | The three clauses of `refinement_functoriality`. `r : V ⟶ U`, `s : Z ⟶ V` give `refinement (s ≫ r) = refinement r ≫ refinement s`, as restriction is contravariant. |
| M in degree zero gives the alternating section complex | `single_sheaf` provides the chain isomorphism from the published alternating section row (after forgetting scalars) to the total of `M[0]`. Its forward arrow is characterized degreewise by the actual (n,0) total injection after `singleObjXSelf.inv`. Its image under Q is the derived identification. The source row definition has degree p term M(U_p), zero negative terms, and alternating face differential. |

The helpers `Modules`, `evaluation`, `total`, `augmentation`, and `IsHypercover`
only expose the precise specializations and bundled hypotheses of this node.
They do not introduce an independent site, sheaf category, totalization, or
augmentation. The older downstream module
`Sheaf.Paper.AcyclicHypercoverPullbackNormalization` contains similar convenience
composites, but its descent is sheaf-in-degree-zero/terminal-base material and
cannot state this node for arbitrary W and bounded-below coefficient complexes.
That parent now lists this item as a proof dependency; importing it would create
a dependency cycle. This module therefore uses the owning total and augmentation
declarations directly and does not import the downstream theorem.

### Recorded dependencies used

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its category.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Mathlib.AlgebraicTopology.SimplicialObject.Basic`: `SimplicialObject`, its slice encoding and simplicial operators.
- `Sheaf.CategoryTheory.SiteHypercoverDisjointUnion`: `SimplicialObject.IsProperFaceMatchingArrow`, including all three degree cases.
- `WeilConjectures.CategoryTheory.Sites.WeaklyContractible`: `GrothendieckTopology.IsWeaklyContractible`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`, transparently Mathlib's `SheafOfModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.AlgebraicGeometry.ProEtaleHypercoverTotal`: `hypercoverSections`, `hypercoverSectionRows`, `hypercoverTotal`, with their published additive instances.
- `Sheaf.AlgebraicGeometry.ProEtaleHypercoverAugmentation`: `hypercoverAugmentation`.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`: `Functor.rightDerivedFunctorOfQuasiIsoResolutions`, its actual universal unit, and `rightDerivedFunctorOfQuasiIsoResolutionsObjIso`.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`: `Injective`; resolutions of general complexes are rendered by their actual quasi-isomorphism to bounded-below injective complexes. The object-only `InjectiveResolution` is not substituted for a general coefficient resolution.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`: `Homotopy`, `CochainComplex.IsKInjective`, `isKInjective_of_injective`.

Proof-plan imports also retain the recorded exact-evaluation, column comparison,
ringed injective hypercover-row, injective-complex augmentation, general-universe
ringed-site K-injective existence, enough-injectives, bounded-below injective
resolution existence, and K-injective comparison modules. The node's source and
all statement-dependency declaration signatures and docstrings were read.

### Edge cases checked

- W is arbitrary, including an empty site object. The augmentation and slice
  terminal matching object still have the stated meaning.
- The zero complex and zero coefficient sheaf give zero rows and totals, and the
  unique normalized comparison. Nothing assumes a nonzero ring or nonempty set
  of sections.
- Lower bounds are arbitrary integers, including negative N. E and F may have
  different lower bounds; their minimum gives finite effective diagonals.
- Degree zero and one of matching are the slice terminal object and fibre
  product, respectively. Matching existence is asserted, not inferred from a
  universally quantified covering condition with no witness.
- Negative simplicial rows are zero. The signed homotopy formula covers them
  as well as p=0 and p=1; in those two degrees its signs are +1 and -1, and the
  mixed horizontal terms have opposite signs.
- Coefficient quasi-isomorphisms need not be monomorphisms. Resolution comparison
  triangles need commute only up to the given actual homotopy.
- Identity and composite refinements are included as chain-map equalities,
  before localization. V and U have separate hypercover assumptions only where
  descent comparisons for both are used.
- A constant hypercover, when its terms are weakly contractible, gives ordinary
  evaluation up to the alternating-row contraction; the normalization fixes the
  same comparison. For M[0], only coefficient degree zero contributes.

### Searches for existing statements and notions

All wrapper searches used `batch2/msearch.py Q07` with this item:

1. LeanFinder: `Weakly contractible hypercover total sections descent with canonical injective resolution augmentation normalization`.
   Result: 8 matches, headed by `GrothendieckTopology.HOneHypercover`, its quotient
   functor, and one-hypercover amalgamation/gluing. These are truncated hypercover
   notions, not this signed derived comparison and normalization statement.
2. Loogle: `"hypercoverTotal", "QuasiIso"`.
   Result: 0 matches.
3. Mathlib grep: `(hypercover|Hypercover).*(normalized|Normalized|refinement|Refinement)`.
   Result: 4 matches in `CategoryTheory/Sites/Hypercover/Homotopy.lean`, `Zero.lean`,
   and `One.lean`, all truncated refinements or their homotopies.
4. LeanSearch: `A weakly contractible hypercover computes derived evaluation by a signed total with augmentation normalization natural in coefficient complexes and refinements`.
   Result: 8 matches, chiefly `HomologicalComplex` evaluation limit/colimit
   preservation, `forgetEval`, and shift evaluation. None states the node.
5. Source searches with `rg` in both `lean/WeilConjectures` and `lean/Sheaf`:
   `(hypercover.*[Rr]efin|[Rr]efin.*hypercover|hypercoverTotal.*[Hh]omotopy|normalizedSingleSite)`
   and the exact item id. No existing exact statement. The older downstream
   augmentation-normalization module is restricted to sheaves in degree zero
   over the terminal base and supplies no arbitrary-coefficient/W statement.
6. Direct source/name searches for `IsHypercover`, `isHypercover`,
   `IsProEtaleHypercover` in the project and Mathlib site directory found no
   competing full simplicial matching predicate. The helper used here simply
   bundles the item's explicit existential matching-cover hypothesis.
7. The existing `hypercoverTotal_map_quasiIso_of_weaklyContractible` covers only
   the total quasi-isomorphism clause; it does not state the normalized derived
   isomorphism, every-resolution equations, signed homotopy, or refinement
   identities. Its source was read. The existing exact evaluation and injective
   augmentation clauses remain the proof dependencies of this larger statement.

### Validation

The prescribed `scompile.py` compiled the final module in module mode on the
server against the live published library, without errors or warnings other
than permitted sorry diagnostics. Every variable and universe is explicit, with
`set_option autoImplicit false`; no local notation, private declaration, or local
instance is used. The module has no diagnostic commands and all lines have at
most 100 characters. All theorem proofs remain `sorry`; definitions use real
constructions or the comparison uniquely specified by `descent`.

The prescribed `deliver2.py --no-push` printed `OK (dry run)` for commit
`43ffd83b87c`: server preflight and compilation both passed. The delivery wrapper
repeats those checks on the final packet before pushing. No second worker was
started, as the dispatcher brief forbids other agents; independent maintainer
review follows delivery.

## Second reading by Q07

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

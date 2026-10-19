## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteConstructiblePushforwardVanishing` states
`AlgebraicGeometry.Etale.constructible_lowerStar_and_higherDirectImage_vanishing_of_finite`.
Its only theorem has proof `sorry`. The item node changes only in `lean`; no new notion,
dependency module, or statement correction is needed.

Hypothesis and conclusion correspondence:

- A field `k`: `(k : Type u) [Field k]`.
- Schemes `X` and `Y` over `k`: `{X Y : Scheme.{u}}` with
  `[X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]`. The node does not require `f` to
  commute with those structure morphisms, so no `IsOver` hypothesis is added.
- Finite type over `k`: `LocallyOfFiniteType` and `QuasiCompact` for each structure
  morphism `X ↘ Spec (.of k)` and `Y ↘ Spec (.of k)`.
- The finite morphism: `(f : X ⟶ Y) [IsFinite f]`.
- Finite presentation: `[LocallyOfFinitePresentation f] [QuasiCompact f]
  [QuasiSeparated f]`, precisely the conjunction specified by
  `def-weil-pbc-scheme-conventions`. The latter two are also consequences of finiteness;
  they spell out finite presentation without strengthening the statement.
- Coefficients: `(N : ℕ) (Λ : Type (u + 1)) [CommRing Λ]` and
  `hcoeff : IsSmoothBaseChangeCoefficients N Λ (Spec (.of k))`. By the recorded
  definition this means `0 < N`, `Finite Λ`, `(N : Λ) = 0`, and
  `IsUnit (N : Γ(Spec (.of k), ⊤))`. The canonical global-sections identification for
  `Spec k` identifies the last condition with invertibility in `k`. This is exactly
  the finite commutative ring killed by a positive invertible integer in the coefficient
  convention. Its finiteness proof `hcoeff.2.1` is passed explicitly to constructibility;
  there is no additional choice of finiteness data or extra coefficient assumption.
- The module sheaf: `F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)`, the recorded
  module-sheaf encoding, with constructibility
  `hF : @Scheme.IsConstructibleEtaleModuleSheaf X Λ _ hcoeff.2.1 F`.
- Ordinary direct-image constructibility is the first conjunct, the same recorded
  predicate applied to `((lowerStar (ModuleCat.{u + 1} Λ) f).obj F)` on `Y`.
- Positive higher-direct-image vanishing is the second conjunct,
  `∀ q : ℤ, 0 < q → IsZero (higherDirectImage Λ f q F)`.
  The imported `higherDirectImage` is defined as degree-`q` homology of the recorded
  right-derived direct image on the sheaf in degree zero, so this uses exactly `R^qf_*F`.

Dependency interfaces read and used:

- `Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients`:
  `AlgebraicGeometry.Etale.IsSmoothBaseChangeCoefficients`, with its full definition
  and documentation. Imposing it on the base gives precisely invertibility on `k`;
  invertibility on `X` and `Y` follows by the structure maps.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`: the recorded
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible` and
  `BoundedConstructibleDerivedCategory` were inspected. The present item uses only
  their sheaf constructibility component, imported from
  `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`, namely
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`. Its full definition was
  read: finite locally closed constructible partition, with finite constant module
  trivializations on an etale cover of each stratum.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`, whose sectionwise definition is evaluation on
  the base change of each etale object. The recorded
  `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus` is in the imported upstream
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`; its full signature
  and definition as `rightDerivedFunctorPlus` were inspected. The helper
  `AlgebraicGeometry.Etale.higherDirectImage` in upstream
  `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs` packages its homology on `F[0]`.
- `def-weil-pbc-scheme-conventions` is a convention-only record. Its finite-type,
  finite-presentation, and finite-morphism meanings are expressed by Mathlib's
  `LocallyOfFiniteType`, `QuasiCompact`, `LocallyOfFinitePresentation`,
  `QuasiSeparated`, and `IsFinite`. Their respective morphology modules are imported.
- The proof dependency `sbc-def-coefficient-conventions` is publicly imported, as is
  `def-weil-pbc-direct-image`. The proof-only
  `fin4-thm-finite-morphisms-constructible` has no Lean record in the inspected DAG;
  there is consequently no recorded module to import. It supplies no missing notion
  needed to type this statement. The complete two-step DAG proof is in the theorem
  docstring for stage 3, including the degree-zero identification.

Edge cases checked before writing: empty source (zero direct images), empty schemes
(vacuous stratifications), identity finite morphism (the original sheaf in degree zero),
zero sheaf, and the zero coefficient ring (allowed). No nonempty-scheme or nonzero-ring
hypothesis was introduced. `N = 1` is allowed, and `N = 0` is excluded exactly by the
positive-annihilator convention. In positive characteristic the unit condition excludes
annihilators divisible by the characteristic. The integer quantifier covers every positive
degree and asserts nothing about degree zero vanishing. The site and module universes
follow the existing `Scheme.{u}` / `ModuleCat.{u + 1}` convention.

Sources: read the item's complete source markdown on the project server because the local
literature checkout is absent. Also read Stacks https://stacks.math.columbia.edu/tag/095R
(finite finitely presented pushforward constructibility) and
https://stacks.math.columbia.edu/tag/03QP (positive higher-direct-image vanishing).
The source agrees with the DAG statement. No disputed statement or node fault was found.

Searches for an existing statement:

- `msearch.py` LeanSearch query: "finite morphism constructible etale module sheaf direct
  image higher direct images vanish". Service returned Internal Server Error; recorded
  as unavailable.
- `msearch.py` LeanFinder query: "finite morphism pushforward constructible etale module
  sheaf higher direct images vanish". Eight hits, including constructible-set image
  theorems and module pushforward definitions, none the item.
- `msearch.py` Loogle query: "IsConstructibleEtaleModuleSheaf, rightDerived". No hits;
  unknown identifier for the project-specific constructibility predicate.
- `msearch.py` Mathlib grep query:
  `constructible.*(lowerStar|higherDirectImage)|finite.*higherDirectImage`. No hits.
- Source `rg` for the item id, finite direct image, and finite pushforward
  constructibility found the finite exactness and constructible embedding APIs but no
  declaration with this full statement. Source `Etale.higherDirectImage` was inspected
  and reused.
- Side-library `rg` found
  `Scheme.isConstructibleEtaleModuleSheaf_lowerStar_of_finite_finitePresentation` in
  `Sheaf.AlgebraicGeometry.FiniteFinitePresentationPushforwardConstructible`, which
  lacks the vanishing conclusion, and
  `Etale.finite_directImage_constructible_and_higher_vanishing` in
  `Sheaf.AlgebraicGeometry.FiniteConstructibleDirectImage`, whose full signature was
  read. The latter is a stronger general result: it assumes only finite-type target,
  no finite presentation or field structure on the source, and invertibility on the
  target rather than on `k`. It is not the exact item statement, so no `existing: true`
  attachment is claimed. No notion is redefined in the new module.

Validation: the prescribed `scompile.py` file-only compilation passed with no warnings or
errors. `deliver2.py NJ lem-kun-095r --no-push` printed `OK (dry run)` at commit
`62de8537d8`: compilation and preflight passed except for the independent second reading,
which the second reader supplies. Nothing was pushed.


## Second reading by NJ

I independently opened the item node, its original blueprint markdown at
`/home/ubuntu/weil-launcher-nt/literature/blueprint/master/blueprint/sec-smooth-purity/`
`sk-prop-sf-kunneth-ordinary/lem-kun-095r.md`, and the delivered Lean module.
I read Stacks `etale-cohomology.tex`, `lemma-finite-pushforward-constructible`
(Tag 095R, lines 12527–12555) and `proposition-finite-higher-direct-image-zero`
(Tag 03QP, lines 8244–8289), including their surrounding hypotheses and proofs.
095R assumes finite and finitely presented f and a Noetherian coefficient ring;
a finite commutative ring is Noetherian. 03QP assumes only finiteness and proves
abelian-sheaf vanishing; the DAG's cited finite-morphism theorem explicitly supplies
the module-sheaf conclusion, so no unrecorded abelian/module comparison is asserted.
The field, finite-type and coefficient invertibility restrictions are the blueprint's.

My object/hypothesis/conclusion checklist, with the file open:

- Field k: `(k : Type u) [Field k]`. Exact.
- Schemes X and Y over k: `{X Y : Scheme.{u}}`,
  `[X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]`. Exact. The node does not say
  that f is a k-morphism; the Lean correctly imposes no `IsOver` condition.
- Each scheme has finite type over k: `LocallyOfFiniteType` and `QuasiCompact`
  instances for each structure map. This is exactly the recorded scheme convention.
- Morphism f: `(f : X ⟶ Y) [IsFinite f]`. Exact, with no smoothness, surjectivity,
  nonemptiness, separatedness over k, or Noetherian hypothesis added.
- Finite presentation of f: `[LocallyOfFinitePresentation f] [QuasiCompact f]
  `[QuasiSeparated f]`. Exact Stacks 01TP convention. The last two properties also
  follow from finiteness, so they exclude no finite morphism in the node.
- Coefficients: `(N : ℕ) (Λ : Type (u + 1)) [CommRing Λ]` and
  `hcoeff : IsSmoothBaseChangeCoefficients N Λ (Spec (.of k))`. I opened that
  definition: `0 < N ∧ Finite Λ ∧ (N : Λ) = 0 ∧ IsUnit (N : Γ(T, ⊤))`.
  These are precisely the positive annihilator, finite commutative ring and
  invertibility on k of `sbc-def-coefficient-conventions`; global sections of
  Spec k canonically identify with k. Naming N before Λ does not change the
  universal quantification or the mathematical assertion.
- Sheaf F: `Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)`. Exact module-sheaf
  encoding of the coefficient convention, not an O_X-module sheaf.
- Constructibility hypothesis: `hF : @Scheme.IsConstructibleEtaleModuleSheaf
  X Λ _ hcoeff.2.1 F`. I opened the definition: finite locally closed constructible
  stratification and etale constant finite module trivializations on its strata.
  This is the recorded constructibility notion, with finiteness supplied by hcoeff.
- First conclusion: the identical predicate on Y for
  `((lowerStar (ModuleCat.{u + 1} Λ) f).obj F)`. I read `lowerStar` and its
  sectionwise formula in the recorded upstream module: evaluation on the base
  change W ×_Y X. This is exactly f_*F, not restriction or extension by zero.
- Second conclusion: `∀ q : ℤ, 0 < q → IsZero (higherDirectImage Λ f q F)`.
  I read `higherDirectImage` in upstream SmoothBaseChange/Defs and
  `rightDerivedLowerStarPlus` in Derived/UpperLowerStarCoherence. They are the
  homology of the bounded-below right-derived lowerStar applied to F in degree
  zero. Thus this is exactly R^q f_*F = 0 for every positive q, with no degree-zero
  vanishing and no bounded range substituted.

Dependency review: opened all four statement dependency nodes and their recorded
interfaces. `BoundedConstructibleComplexes` publicly imports the exact constructible
module-sheaf predicate used here; no private copy or alternate upstream
`IsConstructibleSheaf` is used. The direct image and derived direct image are the
recorded upstream constructions. The scheme convention is a convention-only node,
rendered by the Mathlib morphism properties above. No missing notion, new definition
node, dependency repair, hollow definition, or statement correction is required.
The proof-only `fin4-thm-finite-morphisms-constructible` currently has no Lean record
in the shared DAG, hence no recorded module is missing from the proof imports.

Edge cases: empty X gives zero module direct images; if Y is empty then X is empty.
Zero F and the zero coefficient ring are allowed. N = 1 is allowed (forcing Λ zero),
N = 0 is excluded exactly by the coefficient convention. The q = 0 boundary is
constructibility of ordinary f_*F; all positive integers occur in the ℤ quantifier.
In characteristic p the unit condition excludes p-divisible annihilators exactly as
the source does. No index set or nonempty hypothesis occurs. The single arbitrary
universe u for schemes/field and the u+1 site-valued modules follow the dependency
interfaces; finite coefficients can be lifted to this universe without excluding
any finite ring. There is no free variable or unbound universe in the signature.

Independent searches used words different from the worker's queries:

- LeanFinder via `msearch.py`: "Exact direct image on etale module sheaves under
  finite scheme morphism preserves constructibility". Eight hits: Chevalley image
  statements, etale cancellation and related scheme morphism facts; no exact theorem.
- Loogle via `msearch.py`: `IsConstructibleEtaleModuleSheaf higherDirectImage
  lowerStar`. No hits; the project-specific predicate is unknown to the service.
- Direct rg of Mathlib for `constructible.*(lowerStar|higherDirectImage)` and
  `finite.*higherDirectImage`: no matching theorem. Direct rg of upstream and
  project Lean by the node id, declaration names and these concepts found no exact
  duplicate. I opened both neighboring project declarations: finite/finitely
  presented pushforward constructibility lacks vanishing; the NU finite direct
  image theorem has only a finite-type target, no finite presentation or k-structure
  on X, and coefficient invertibility on the target. The latter is a stronger
  general theorem, not verbatim this node's hypotheses. Both reuse the same notions;
  neither is an exact existing attachment for this item.

H5/H6/H8/H9: the module introduces only one theorem, with sole proof `sorry` and no
new data definitions. Its module and declaration docstrings cite the source and
`(blueprint: lem-kun-095r)`; the declaration gives both DAG proof steps, including
invertibility via structure maps, the degree-zero kernel identification and positive
module-sheaf vanishing. No file-local notation/instance or unbound auto-implicit
occurs. I mechanically compared the signature with `lean.statement`: verbatim equal.

Mismatches found: none. Changes: appended this independent second reading; retained
the correct module and node record. The Worker report remains intact.

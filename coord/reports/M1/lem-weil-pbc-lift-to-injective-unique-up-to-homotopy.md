## Worker report

The module `Sheaf.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy` states
`CochainComplex.homotopy_of_comp_quasiIso_of_injective`, with its sole proof `sorry`.
No definition, dependency module, or new node is needed; the node changes only in `lean`.

Hypothesis and clause correspondence:
- Abelian category A: `{C : Type u} [Category.{v} C] [Abelian C]`, with independent,
  explicitly declared object and morphism universes.
- The three Z-indexed cochain complexes: `{K L I : CochainComplex C ℤ}`.
- I bounded below: `hI : ∃ a : ℤ, ∀ n : ℤ, n < a → IsZero (I.X n)`.
  Vanishing means being a zero object, rather than literal equality to a chosen zero.
- Each term of I injective: `[∀ n : ℤ, Injective (I.X n)]`.
- Alpha a complex morphism and quasi-isomorphism: `(α : K ⟶ L)` and
  `[QuasiIso α]`; in an abelian category homology exists and this
  says that every induced cohomology map is an isomorphism.
- Two complex morphisms beta_i: `(β₁ β₂ : L ⟶ I)`.
- Their composites with alpha chain-homotopic: `h : Nonempty (Homotopy (α ≫ β₁) (α ≫ β₂))`.
  Lean composition proceeds left to right, so these are beta_i composed with alpha.
  The parenthetical equal case is included by `Homotopy.ofEq`.
- Conclusion chain-homotopic, with the specified components and equation:
  `Nonempty (Homotopy β₁ β₂)`. For a witness H put k^n = `H.hom n (n - 1)`.
  The shape condition permits exactly these degree-minus-one components. `H.comm n`
  reads beta_1^n = dNext n H.hom + prevD n H.hom + beta_2^n,
  equivalent to beta_1^n - beta_2^n =
  `L.d n (n + 1) ≫ H.hom (n + 1) n + H.hom n (n - 1) ≫ I.d (n - 1) n`.
  Commutativity of addition gives precisely d_I k + k d_L as in the node.
  Conversely the displayed family gives a Mathlib Homotopy by extending it by zero
  outside the permitted degrees, so the conclusion neither strengthens nor weakens it.

Dependencies read and used:
- `def-sp-abelian`: `CategoryTheory.Abelian` in `Mathlib.CategoryTheory.Abelian.Basic`.
  Its class fields and docstring were read; it supplies preadditivity and homology.
- `def-weil-abstract-derived-category`: its mathlib_match is `DerivedCategory` in
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`; the definition, localization Q,
  and docstring were read. This item uses only the complex/quasi-isomorphism clauses
  of that node, directly as `CochainComplex` in
  `Mathlib.Algebra.Homology.HomologicalComplex` and `QuasiIso` in
  `Mathlib.Algebra.Homology.QuasiIso`. No derived category object is needed, so its
  localization module and a HasDerivedCategory hypothesis would be unused here.
- `def-sp-injective-resolutions`: its recorded `CategoryTheory.InjectiveResolution`
  in `Mathlib.CategoryTheory.Preadditive.Injective.Resolution` and docstring were
  read. Its mathlib_match.how explicitly identifies the injective-object clause
  with `CategoryTheory.Injective` in `Mathlib.CategoryTheory.Preadditive.Injective.Basic`;
  that class's extension field was read and is used. I is not assumed to resolve an
  object, and enough injectives is not assumed.
- `Homotopy` in `Mathlib.Algebra.Homology.Homotopy`, imported through QuasiIso,
  was read in full, including hom, zero, comm, dNext and prevD.

Edge cases checked before writing: the zero target complex satisfies both target
hypotheses and admits the zero homotopy; equal maps and alpha the identity are
included; any negative lower bound is allowed, with no restriction to degree zero;
K and L may be unbounded in both directions, and I need not have concentrated
cohomology. A category without enough injectives is allowed. There is no excluded
object/hom universe or finite/empty indexing assumption.

Source checked: the local `literature/stacks-project/derived.tex` is absent on this
machine, so the full statement and direct proof were read at
https://stacks.math.columbia.edu/tag/013S (Lemma 13.18.7). Its common-gamma formulation
is equivalent to the node: compose homotopies through gamma, or take gamma to be
alpha followed by beta_1. The seven-step proof in the module follows the node's
mapping-cylinder reduction, acyclic quotient and correction/nullhomotopy argument.
No statement fault or correction was found.

Searches for an existing declaration (actual msearch calls recorded in searches.jsonl):
- leanfinder: "two maps into a bounded below complex of injective objects whose
  composites with a quasi-isomorphism are homotopic are homotopic". Eight hits:
  K-injective homotopyZero and nonempty_homotopy_zero, InjectiveResolution.descHomotopy,
  homotopyEquiv, descHomotopyZero, and localization ingredients; no exact statement.
- loogle: "CochainComplex.IsKInjective, Homotopy". Four hits, all nullhomotopy or
  K-injective constructor declarations, not this uniqueness theorem.
- grep: "homotopy.*(quasiIso|injective)|homotopy_of|boundedBelow" in Algebra/Homology.
  Twenty-five hits on K-injective, localization and homotopy-category machinery;
  none states this implication for arbitrary K and L.
- leansearch: "two chain maps into a bounded below injective complex are homotopic
  if their compositions with a quasi-isomorphism are homotopic". Service unavailable
  (Internal Server Error), recorded as unavailable, with no mathematical verdict.
- rg over WeilConjectures and lean/Sheaf with
  `homotopy.*(quasiIso|injective)|lift_to_injective|unique.*homotopy`: related
  K-injective and comparison modules only, not an existing declaration.
- grep -rn of the exact node id over WeilConjectures: no hit.
- rg for the proposed full-name suffix `homotopy_of_comp_quasiIso_of_injective`
  over the source and project Lean: no collision.
- Read Mathlib HomotopyCategory/KInjective: `isKInjective_of_injective` establishes
  K-injectivity, but does not itself state uniqueness along a quasi-isomorphism.

Validation: server single-file compilation and deliver2.py --no-push dry run;
see their final result accompanying this delivery. No independent second-reading
section is supplied by this worker; the second reader performs that review.

## Second reading by M1

I independently read the sandbox node, all seven proof steps, the module, the three
statement-dependency nodes and their Mathlib declarations. I also fetched the actual
Stacks `derived.tex` into this item's scratchpad and read lines 6205--6230 (section
context) and 6480--6537 (the source lemma and direct proof), checking Tag 013S at
https://stacks.math.columbia.edu/tag/013S. The section discusses existence under enough
injectives, but this lemma starts afresh with an arbitrary abelian category and already
given injective terms; it does not assume enough injectives. Its common map gamma is
equivalent to the node's hypothesis: transitivity and symmetry combine the two
homotopies, and conversely take gamma = beta_1 composed with alpha. No statement
correction or citer recheck is needed.

My object/hypothesis/conclusion checklist, in the node's order:

1. An arbitrary abelian category A: `{C : Type u} [Category.{v} C] [Abelian C]`.
   PASS. `CategoryTheory.Abelian` (Basic.lean:112) supplies preadditivity, normal
   monos/epis, finite products, kernels and cokernels, hence zero objects and finite
   biproducts. Object and morphism universes are independent and explicitly bound.
2. Cochain complexes K, L, I in A, indexed by all integers:
   `{K L I : CochainComplex C ℤ}`. PASS. I read HomologicalComplex.lean:59--65,
   150--158 and 217--226: the differential has square zero, the up shape gives
   degree +1, and morphisms commute with differentials. These are exactly the
   complex clauses of `def-weil-abstract-derived-category`, not a module-sheaf
   specialization or a derived object requiring `HasDerivedCategory`.
3. I bounded below: `(hI : ∃ a : ℤ, ∀ n : ℤ, n < a → IsZero (I.X n))`.
   PASS. This says zero object in every sufficiently negative degree, with arbitrary
   integer bound; it neither requires a chosen literal zero nor fixes the bound at 0.
4. Every term of I injective: `[∀ n : ℤ, Injective (I.X n)]`. PASS.
   Basic.lean:32 defines injectivity by extension of every map along every mono,
   exactly the injective-object clause of `def-sp-injective-resolutions` and its
   `mathlib_match.how`. Resolution.lean:43--55 defines an injective resolution;
   that stronger structure and enough injectives are correctly absent here.
5. A complex morphism alpha from K to L, quasi-isomorphic:
   `(α : K ⟶ L) [QuasiIso α]`. PASS. QuasiIso.lean:139 requires a quasi-isomorphism
   in every degree, equivalent to all induced cohomology maps being isomorphisms.
   Abelian categories supply the needed homology instances without extra binders.
6. Two complex morphisms beta_1 and beta_2 from L to I: `(β₁ β₂ : L ⟶ I)`.
   PASS. They are universally quantified after alpha, with no augmentation,
   resolution, monomorphism or boundedness assumption on K or L.
7. Their composites with alpha are homotopic:
   `(h : Nonempty (Homotopy (α ≫ β₁) (α ≫ β₂)))`. PASS. Composition is left-to-right,
   so these are the required beta_i composed with alpha. `Nonempty` records existence
   without selecting extra homotopy data. Equal composites are included by
   `Homotopy.ofEq`; no additional equality is assumed.
8. Conclusion: beta_1 and beta_2 are homotopic, with degree-minus-one maps and the
   displayed differential equation: `Nonempty (Homotopy β₁ β₂)`. PASS.
   I read Homotopy.lean:35,70,126--129: for a witness H, set k^n = H.hom n (n-1).
   The zero field permits exactly the degree-minus-one components. The comm field is
   beta_1^n = (d_L^n followed by k^{n+1}) +
   (k^n followed by d_I^{n-1}) + beta_2^n. Subtraction and commutativity of addition
   give precisely the node's beta_1^n - beta_2^n = d_I^{n-1} k^n + k^{n+1} d_L^n.
   Conversely any such family extends by zero in the other bidegrees to H; those
   extra components impose no stronger condition. The quantifiers match throughout.

Edge cases: the zero complex I has zero/injective terms and is included; zero K or L,
equal maps, and identity alpha are included. At n=0 the degree -1 component is retained;
negative and positive lower bounds are both allowed. K and L can be unbounded in either
direction, and I need not resolve an object or have cohomology concentrated in degree 0.
A category without enough injectives is allowed. There is no varying index set, scheme,
ring or characteristic in this statement, so empty index sets, empty schemes and
characteristic restrictions introduce no missing cases. An empty category cannot satisfy
Abelian because a zero object is required by both source and Lean. No universe restriction
or unbound variable occurs.

Independent duplicate searches (recorded by msearch in searches.jsonl):
- LeanFinder: "precomposition with a quasi-isomorphism is injective on homotopy classes
  of maps to a bounded below injective cochain complex". Eight results: K-injective
  nullhomotopy, orthogonality, Qh_map_bijective and injective-resolution ingredients;
  no exact statement.
- Loogle: `Homotopy, QuasiIso`. Zero hits.
- Grep: `comp.*(injective|homotopy)|homotopy.*comp|map_bijective`, restricted to
  Algebra/Homology. Hits concern homotopy operations, K-injectivity and localization;
  no exact uniqueness theorem. I independently opened the KInjective declarations
  `isKInjective_of_injective`, `Qh_map_bijective` and `quasiIso_iff`.
- LeanSearch: "uniqueness of maps of complexes into injectives up to chain homotopy
  after precomposition by a quasi-isomorphism". Service unavailable (Internal Server
  Error), recorded as unavailable; no mathematical verdict inferred.
- Local rg over the project's lean/Sheaf and upstream WeilConjectures with
  `homotopy.*(quasi|injective)|quasi.*homotopy|homotopy_of_comp|lift.*injective.*unique`.
  I opened the related project modules KInjectiveComparisonPrinciple.lean and
  KInjectiveComputes.lean. The former states bijectivity on homotopy-category morphisms
  for a K-injective target with a derived-category binder, and the latter concerns
  chosen resolutions and functors between Grothendieck categories. Neither states
  this theorem with these objects, hypotheses and conclusion. Deriving this theorem
  from comparison requires proving bounded-below termwise-injective implies K-injective,
  interpreting quotient equality, and applying injectivity; it is not a duplicate.

No mismatch found; no Lean or node changes were needed. No new nodes or dependency
modules were delivered. The three imports supply the category, injectivity and
quasi-isomorphism/Homotopy notions used. There is one named theorem with proof `sorry`,
no definitions and no proved results. The header, namespace and lines follow conventions;
both docstrings name Stacks 013S and the blueprint item. The declaration docstring
faithfully carries all seven node proof steps, including the quotient, acyclicity,
extended homotopy correction and return along s. The source's displayed correction
contains a misplaced parenthesis (and its h_1-h_2 line has the reversed subtraction
sign); the node and Lean docstring use the correctly oriented given homotopy and the
well-typed d h + h d, without changing the statement.

Validation by the second reader: scompile.py compiled the only module in 1.2 seconds,
exit code 0, with no errors or warnings. A literal signature comparison against
`lean.statement` passed, and every Lean line is at most 100 characters. The independent
`deliver2.py --no-push` run printed OK: preflight passed and the module compiled.

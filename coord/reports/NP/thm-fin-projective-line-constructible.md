## Worker report

The module `Sheaf.AlgebraicGeometry.ProjectiveLineConstructible` states
`AlgebraicGeometry.Etale.isConstructibleEtaleModuleSheaf_higherDirectImage_projectiveLine`.
Its only proof is `sorry`; no definitions or auxiliary theorems are introduced.
The node statement and all other original node fields are unchanged except `lean`.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- “k a field”: `(k : Type u) [Field k]`.
- “S of finite type over k”: `(S : Scheme.{u}) [S.Over (Spec (.of k))]`,
  `[LocallyOfFiniteType (S ↘ Spec (.of k))]`, and
  `[QuasiCompact (S ↘ Spec (.of k))]`. These two morphism classes together are
  finite type; no separatedness hypothesis on S over k is imposed.
- “the finite commutative ring Λ killed by a positive integer invertible in k”:
  `(N : ℕ) (Λ : Type (u + 1)) [CommRing Λ]` and
  `(hcoeff : IsSmoothBaseChangeCoefficients N Λ (Spec (.of k)))`.
  The recorded predicate is exactly `0 < N ∧ Finite Λ ∧ (N : Λ) = 0 ∧
  IsUnit (N : Γ(Spec (.of k), ⊤))`. Global sections of Spec k identify with k,
  so this is the stated invertibility in k. Annihilating the unit is equivalent
  to annihilating the whole ring. `hcoeff.2.1` supplies the finite instance to
  both occurrences of the recorded constructibility predicate; it is not an
  additional coefficient hypothesis.
- “F a Λ-sheaf on P¹_S”: the binder `F : Sheaf
  (ProjectiveSpace (ULift.{u} (Fin 2)) S).smallEtaleTopology (ModuleCat.{u + 1} Λ)`.
  The lifted two-element type indexes homogeneous coordinates, so this is the
  projective line, not a projective plane.
- “constructible F”: `hF : @Scheme.IsConstructibleEtaleModuleSheaf
  (ProjectiveSpace (ULift.{u} (Fin 2)) S) Λ _ hcoeff.2.1 F`.
  This is precisely the project's finite-module local-model notion with a finite
  partition by locally closed constructible subschemes.
- “π : P¹_S → S”: `(ProjectiveSpace (ULift.{u} (Fin 2)) S ↘ S)`, the recorded
  canonical structure morphism, which is the first pullback projection.
- “every higher direct image R^q π_* F”: `(q : ℤ)` and the expression
  `DerivedCategory.Plus.homologyFunctor ... q` applied to
  `rightDerivedLowerStarPlus (ModuleCat Λ) π` applied to
  `DerivedCategory.Plus.singleFunctor ... 0` on F. This follows the integer-degree
  convention of def-weil-pbc-direct-image and includes all nonnegative degrees.
- “is constructible”: the conclusion applies that same
  `Scheme.IsConstructibleEtaleModuleSheaf` to the resulting sheaf on S.

Dependency declarations read and reused:

- `Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients`:
  `AlgebraicGeometry.Etale.IsSmoothBaseChangeCoefficients`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`; the derived declaration is actually defined
  in `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`:
  `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus`. Both modules are public imports.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`:
  `AlgebraicGeometry.ProjectiveSpace`, `AlgebraicGeometry.ProjectiveSpace.over`.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible` describes complexes,
  and publicly imports `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`,
  whose `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf` is the sheaf clause
  of this dependency used here. No boundedness assumption on F or its images is added.
- `def-weil-pbc-scheme-conventions` is a convention node, with no module of its own.
  Its finite-type meaning uses Mathlib's `LocallyOfFiniteType` and `QuasiCompact`
  from `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.

Every available recorded proof-dependency module is imported without `public`, except
those already public because used by the statement. The declaration docstring contains
all ten node proof steps, including finite-type/Noetherian reductions, finite-pushforward
resolution, finite-over-projective and fibre-dimension arguments, finite-sum compatibility,
finite-group coefficient comparison, Cartan–Eilenberg spectral sequence, Serre closure,
scalar-action refinement, and gluing from finitely many affine opens. Proof dependencies
without a recorded module do not add imports. No import cycle was intentionally omitted.

Edge cases checked: S can be empty (the empty stratification works); Λ may be the zero
ring, and N may be 1 (all module sheaves are zero); no Nontrivial Λ is assumed. The
zero sheaf is included. In positive characteristic the annihilator must be invertible,
exactly as stated; no characteristic-zero assumption is added. Negative q are included
and their higher images vanish by the nonnegative injective-resolution argument in the
node. Degree zero is included. S may be nonseparated. `ULift.{u} (Fin 2)` places the two
homogeneous coordinates in the scheme universe without restricting the field universe.
There is no fixed bound on the degree q in this statement.

Searches (2026-10-15):

- msearch LeanFinder, “Higher direct images of constructible finite torsion etale
  sheaves under the projective line projection are constructible”: eight results,
  all about constructible subsets or affine-transition limits; no matching theorem.
- msearch Loogle, `AlgebraicGeometry.Etale.lowerStar,
  AlgebraicGeometry.Scheme.IsConstructibleSheaf`: zero results; unknown identifier
  lowerStar in Mathlib-only search. Its upstream source was therefore read directly.
- msearch grep, `constructible.*(directImage|lowerStar)|projective.*constructible`:
  zero Mathlib hits.
- msearch LeanSearch, “Higher direct images of constructible torsion etale sheaves
  under projective space projection”: service unavailable (Internal Server Error).
- rg in the upstream WeilConjectures and project lean/Sheaf trees,
  `projective.*constructible|constructible.*projective|thm-fin-projective-line-constructible`
  case-insensitively: upstream only comments about pro-etale perfect modules;
  project results include projective coherent ranks, the finite-constant-group curve
  theorem, and projective constructibility conditional on the projective-line case.
  None states this theorem for arbitrary constructible Λ-sheaves.
- rg in dag/lean_names_upstream.json for ProjectiveLineConstructible and the node id:
  no declaration match. Exact proposed declaration name checked against both source
  trees as well.

No STATEMENT-DISPUTED issue, statement correction, new node, or dependency repair.
Validation: server single-file compilation and deliver2 dry run are recorded below.

## Second reading by NP

I independently read the item JSON, the blueprint statement and proof at order 1618,
the coefficient convention source, all five statement-dependency records, and the
actual dependency declarations. No statement correction, new node, or dependency
module is needed. The Lean module and the node's signature are unchanged.

Object/hypothesis/conclusion checklist (the node's statement, in order):

1. A field k: `(k : Type u) [Field k]`. Exact; k is not assumed algebraically
   closed or of characteristic zero.
2. A scheme S of finite type over k: `(S : Scheme.{u})`,
   `[S.Over (Spec (.of k))]`, `[LocallyOfFiniteType (S ↘ Spec (.of k))]`,
   `[QuasiCompact (S ↘ Spec (.of k))]`. Exact finite-type convention, with
   no added separatedness or explicit Noetherian assumption.
3. Finite commutative coefficients annihilated by a positive invertible integer:
   `(N : ℕ) (Λ : Type (u + 1)) [CommRing Λ]` and
   `hcoeff : IsSmoothBaseChangeCoefficients N Λ (Spec (.of k))`.
   I opened SmoothBaseChangeCoefficients.lean: its body is precisely
   `0 < N ∧ Finite Λ ∧ (N : Λ) = 0 ∧ IsUnit (N : Γ(T, ⊤))`.
   On Spec k the last clause is invertibility in k. Exact; the same N is used
   in all coefficient clauses, and the finite instance is hcoeff.2.1.
4. The projective line over S and its canonical projection π: the scheme is
   `ProjectiveSpace (ULift.{u} (Fin 2)) S` and π is its `↘ S` morphism.
   I opened upstream ProjectiveSpace.lean, lines 124–142: homogeneous coordinates
   are indexed by the supplied type, and `ProjectiveSpace.over` sets `hom` to
   `pullback.fst`. Two coordinates therefore give exactly P¹, not P². Exact.
5. A constructible Λ-sheaf F on that line: `F : Sheaf ...smallEtaleTopology
   (ModuleCat.{u + 1} Λ)` and `hF : @Scheme.IsConstructibleEtaleModuleSheaf
   ... Λ _ hcoeff.2.1 F`. I opened BoundedConstructibleComplexes.lean and its
   public dependency IsConstructibleEtaleModuleSheaf.lean: the predicate uses a
   finite locally closed partition, constructible parts, canonical pullback to
   strata, and etale local trivializations with finite constant module values.
   This is exactly the dependency's sheaf clause; the theorem does not assume
   the input or output to be a bounded complex.
6. Every higher direct image R^q π_*F: `(q : ℤ)` follows F and hF, and the term is
   `Plus.homologyFunctor ... q` of `rightDerivedLowerStarPlus ... π` applied to
   `Plus.singleFunctor ... 0` on F. I opened upstream UpperLowerStar/Defs.lean:
   lowerStar is the sheaf pushforward by the base-change functor, objectwise
   F(V ×_S P). I opened Derived/UpperLowerStarCoherence.lean: the Plus functor
   is its rightDerivedFunctorPlus. These are precisely the recorded dependency's
   module-valued higher images. Exact, including degree zero.
7. The conclusion is constructibility of that resulting sheaf on S, over the
   same Λ: `@Scheme.IsConstructibleEtaleModuleSheaf S Λ _ hcoeff.2.1 (...)`.
   Exact; no boundedness, vanishing bound, or extra conclusion is inserted.

Source and proof check: the item's primary source is a blueprint node, not a
Stacks theorem asserting this entire result. The coefficient source fixes N > 0,
finite commutative Λ and invertibility; it supplies no extra hypotheses on k or S.
I also read derived.tex at lemma-cartan-eilenberg and
lemma-two-ss-complex-functor (015I/015J), and sites-cohomology.tex at
lemma-restrict-direct-image-open (0D6G). These assume the stated abelian/enough
injectives/left exact setup or a morphism of ringed sites, respectively; they do
not impose an unmentioned separatedness or characteristic assumption. The module
contains the node's ten proof steps, including the affine-local reduction and
finite gluing, the scalar-action refinement, and negative-degree vanishing.
I checked all recorded proof-dependency modules against the import list.

Edge cases: empty S and its empty stratification are admitted; no nonempty
scheme hypothesis occurs. The zero sheaf and zero coefficient ring are admitted.
N = 0 is correctly excluded by the source's positivity convention; N = 1 is
allowed (and forces the zero coefficient ring). Positive characteristic is
restricted exactly by invertibility of N. Every integer q is admitted, including
q = 0 and negative q, whose vanishing is addressed by proof step 8. There is no
variable projective dimension here: P¹ uses two coordinates even at u = 0.
The coordinate ULift preserves the two-element index set and raises it to the
scheme universe. The scheme/field universe u is arbitrary; the coefficient and
module universe u+1 follows the recorded small-etale convention, rather than
adding an equality between site object and morphism universes. There is no
index-family nonemptiness restriction.

Independent searches, with queries different from the first reading:

- msearch LeanFinder: `etale cohomology of projective line preserves constructible
  module sheaves`; eight hits about condensed locally constant module functors,
  with no matching theorem.
- msearch Loogle: `"constructible"`; twelve hits about constructible subsets of
  topological spaces, with no matching sheaf theorem.
- msearch LeanSearch: `Constructibility of higher direct image along projective
  line over a field`; unavailable (Internal Server Error).
- msearch grep: `(higherDirectImage|rightDerivedLowerStar).*([Cc]onstructible|
  projectiveLine)`; zero hits.
- rg in Mathlib, upstream WeilConjectures and project lean/Sheaf for projective
  line/P¹ and constructibility in both orders found only an upstream warning
  about integral coefficients and ProjectiveConstructibilityFromLine. The latter
  assumes the projective-line case to deduce the projective case; it is not this
  theorem. No duplicate was found.

H5/H6/H8/H9: there are no definitions or helper declarations in this delivery;
the sole theorem has `by sorry`. Both docstrings name the source and blueprint id.
The declaration has no private notation or local instance; autoImplicit is false,
u is explicitly bound, and all object and instance binders are accounted for.
No line exceeds 100 characters. A textual comparison confirms lean.statement is
verbatim the theorem signature before `:= by`.

Mismatches and changes: none in the statement, dependency use, module or node.
Added this independent review only. The first compile invocation used a relative
path from the read-only repository and failed to locate the sandbox file; rerunning
from the sandbox succeeded. Server scompile.py compiled the sole delivered file
cleanly (3.6 seconds), with no warnings or errors.

## Worker report

Module `Sheaf.CategoryTheory.FiniteCohomologicalDimensionAcyclicComplex` states
`CategoryTheory.Functor.exists_rightDerived_computes_acyclic_of_finite_dimension`.
Its only theorem has proof `sorry`; it introduces no definitions or auxiliary axioms.
The node's statement and dependency lists are unchanged.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The two abelian categories are `{A : Type u₁} {B : Type u₂}` with independent
  category universes `v₁`, `v₂` and `[Abelian A] [Abelian B]`.
- Grothendieckness of the source is `[IsGrothendieckAbelian.{v₁} A]`, as specified
  by the dependency's Mathlib match. No Grothendieck hypothesis is placed on B.
  Enough injectives, hence injective resolutions for the ordinary right derived
  functors, is inferred from Grothendieckness, not assumed separately.
- The functor is `(F : A ⥤ B)`. Additivity is `[F.Additive]`; left exactness is
  `[PreservesFiniteLimits F]`, using def-sp-left-exact-additive's recorded interface.
- The nonnegative integer bound is `(d : ℕ)`. Its uniform vanishing condition is
  `hd : ∀ (M : A) (q : ℕ), d < q → IsZero ((F.rightDerived q).obj M)`.
  Naturals encode precisely the nonnegative integers; no bound on complex degrees
  is introduced.
- The cochain complexes are `CochainComplex A ℤ`. The chosen derived categories
  are parameterized by `[HasDerivedCategory.{w₁} A]` and
  `[HasDerivedCategory.{w₂} B]`, allowing independent morphism-size choices.
  These are the localization choices prescribed by def-weil-abstract-derived-category,
  not additional mathematical existence assumptions; standard localizations exist.
- The conclusion existentially supplies `RF : DerivedCategory A ⥤ DerivedCategory B`
  and the natural comparison `α` from termwise F followed by `DerivedCategory.Q`
  to `DerivedCategory.Q ⋙ RF`. Thus `α.app L` has exactly the node's direction
  `Q_B(F(L)) ⟶ RF(Q_A(L))`.
- The first conjunct states the universal property of the right derived functor:
  for every G, composition with α after whiskering by Q gives a bijection from
  natural transformations RF → G to transformations F(complexes) → Q ⋙ G.
  This is the same universal-property formulation used by the recorded
  K-injective-total-derived dependency, pulled back to complexes.
- The second conjunct quantifies over every unbounded L and assumes
  `∀ r : ℤ, F.rightAcyclic (L.X r)`; it concludes `IsIso (α.app L)`.
  The imported rightAcyclic means precisely vanishing of all positive ordinary
  derived functors. There is no bounded-below or bounded-above restriction.
- The last conjunct is the naturality square for each `f : L ⟶ M` between
  complexes with right acyclic terms. Its left side is `Q_B(F(f)) ≫ α_M` and
  its right side is `α_L ≫ RF(Q_A(f))`. In combination with the preceding
  comparison isomorphisms it is exactly the claimed identification of maps.
  No quasi-isomorphism hypothesis is imposed on f.

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`:
  `CategoryTheory.IsGrothendieckAbelian`, imported through EnoughInjectives.
- `Mathlib.CategoryTheory.Abelian.Basic`: `CategoryTheory.Abelian`.
- `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`:
  `CategoryTheory.Functor.Additive`.
- `Mathlib.CategoryTheory.Limits.Preserves.Finite`: `PreservesFiniteLimits`.
- `Mathlib.CategoryTheory.Abelian.RightDerived`:
  `CategoryTheory.Functor.rightDerived` and its injective-resolution computation;
  the proof plan also uses `isZero_rightDerived_obj_injective_succ`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q`.
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic`:
  `CategoryTheory.Functor.rightAcyclic`, used directly, never copied.
- Proof imports include
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective`
  (functorial K-injective replacements and their injective terms),
  `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`
  (`CochainComplex.mappingCone.quasiIso_iff_acyclic`),
  `Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence`
  (`CategoryTheory.ShortComplex.ShortExact.exists_rightDerived_full_long_exact`),
  and `Sheaf.CategoryTheory.KInjectiveTotalDerived`
  (`CategoryTheory.exists_rightDerived_of_enough_isKInjective`).
  The Grothendieck enough-injectives theorem is supplied by
  `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`.

Source checked: `literature/stacks-project/derived.tex`,
`lemma-unbounded-right-derived` (Tag 07K7), assertions (1)-(2).
Its bound n can be taken to be d+1. Enough acyclics follows from injectives.
The node's finite cycle-dimension-shifting proof, rather than an unbounded
spectral-sequence convergence claim, is reproduced in the declaration docstring.

Edge cases checked: d=0 says all positive derived functors vanish and permits
all complexes; zero categories, the zero functor and zero complexes are allowed;
all integer degrees, including negative degrees, occur in the acyclicity
hypothesis. Maps may be zero, identities, arbitrary maps, or quasi-isomorphisms.
Nothing requires nonzero objects or a bounded complex. Independent object,
category-morphism and derived-morphism universes are retained.
No statement fault or STATEMENT-DISPUTED issue was found.

Searches (2026-10-15):

- msearch.py / leanfinder: "Finite cohomological dimension unbounded right derived
  functor computed on complexes of acyclic objects". Eight hits, consisting of
  derived-category support bounds and injective-object vanishing. No exact match.
- msearch.py / loogle: "CategoryTheory.Functor.rightDerived,
  CategoryTheory.Functor.rightAcyclic". No hits; rightAcyclic is an upstream,
  rather than Mathlib, declaration, and was read directly in its recorded module.
- msearch.py / grep, Mathlib CategoryTheory:
  `finite.*cohomological|acyclic.*comput|comput.*acyclic`. Zero hits.
- rg of the upstream WeilConjectures tree and project lean/Sheaf for the same
  expression and the item id: contextual cohomological-dimension statements and
  specialized acyclic computations, no general finite-dimension unbounded theorem.
- rg of Mathlib, upstream, project Lean and dag/lean_names_upstream.json for the
  proposed declaration name and the node id: no existing declaration.
- Read the upstream Acyclic module: its `quasiIso_map_of_rightAcyclic` requires
  bounded-below complexes. It cannot replace this unbounded computation theorem.

Validation: scompile.py compiled the module cleanly. deliver2.py --no-push printed
OK: the module compiles and passes preflight except for the second reading, which
the second reader writes. Nothing was pushed. No second reading by this worker.

## Second reading by NE

Independent second reading, 2026-10-15. I opened the sandbox node and module,
the five statement-dependency nodes, and the actual declarations they record.
I read derived.tex, lemma-unbounded-right-derived (Tag 07K7), including its
hypotheses and proof. The source assumes abelian categories and a left exact
functor, enough right acyclic objects, and R^n F = 0 for one n ≥ 0. The node
specializes this to a Grothendieck source and the uniform bound d; injectives
supply enough acyclics and n = d + 1 supplies the source's vanishing. Assertions
(1)-(2), rather than its additional assertions (3)-(4), are this item's claim.

Object/hypothesis/conclusion checklist (all verdicts: exact):

1. A is Grothendieck abelian: `{A : Type u₁} [Category.{v₁} A] [Abelian A]
   [IsGrothendieckAbelian.{v₁} A]`. The dependency explicitly records the
   morphism-universe form of Mathlib's Grothendieck class. Its fields give
   exact small filtered colimits and a separator, and its hasColimits instance
   supplies small colimits. EnoughInjectives is inferred from the imported
   GrothendieckCategory.EnoughInjectives; no extra hypothesis is imposed.
2. B is abelian: `{B : Type u₂} [Category.{v₂} B] [Abelian B]`. There is no
   Grothendieck, injective-resolution, or colimit requirement on B.
3. F is the indicated additive left exact functor: `(F : A ⥤ B) [F.Additive]
   [PreservesFiniteLimits F]`. I read the recorded rightDerived definition
   and the preservesFiniteLimits_of_preservesKernels bridge: these are precisely
   the dependency's additive/kernel-preserving notion, not exactness of F.
4. A single nonnegative bound holds uniformly on objects: `(d : ℕ)` and
   `hd : ∀ (M : A) (q : ℕ), d < q → IsZero ((F.rightDerived q).obj M)`.
   The derived functor here is cohomology of F applied to an injective resolution,
   as required. Natural degrees express nonnegative derived-functor degrees.
5. Cochain complexes and their localizations are the recorded Mathlib notions:
   `CochainComplex A ℤ`, `DerivedCategory A`, `DerivedCategory B`, and
   `DerivedCategory.Q`. Independent `[HasDerivedCategory.{w₁} A]` and
   `[HasDerivedCategory.{w₂} B]` parameterize the chosen localizations;
   HasDerivedCategory.standard supplies them at max object/morphism universe.
6. Existence of the unbounded right derived functor and its comparison is
   `∃ (RF : DerivedCategory A ⥤ DerivedCategory B) (α :
   F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
   DerivedCategory.Q ⋙ RF), ...`. The first conjunct's bijection on natural
   transformations is exactly the right-derived universal property, also
   explicitly recorded in lem-weil-pbc-kinjective-total-derived. Its direction
   is Q_B(F(L)) → RF(Q_A(L)); RF and α are chosen once, before all complexes.
7. Every unbounded complex of F-acyclic objects computes RF: the second conjunct
   quantifies over every `L : CochainComplex A ℤ`, assumes
   `∀ r : ℤ, F.rightAcyclic (L.X r)`, and asserts `IsIso (α.app L)`.
   I read the upstream rightAcyclic definition: it is vanishing of
   `(F.rightDerived (q + 1)).obj X` for every q : ℕ, exactly all positive degrees.
8. Identification of maps is the final conjunct, for arbitrary `f : L ⟶ M`
   between two termwise acyclic complexes: `Q_B(F(f)) ≫ α.app M =
   α.app L ≫ RF.map (Q_A(f))`. Together with the preceding isomorphisms this
   is precisely the node's natural identification. This repeats naturality
   of the quantified natural transformation to expose the node's map clause;
   it adds no mathematical condition and does not restrict f to quasi-isomorphisms.

Edge cases: d = 0 includes exact functors and requires only positive-degree
vanishing; negative complex degrees remain unrestricted. The zero functor,
zero complexes, and the zero abelian category are included. An empty category
cannot be abelian, so there is no omitted empty-category case; no index family,
scheme, ring, or characteristic occurs in this abstract node. Identity, zero,
and arbitrary noninvertible chain maps are included. All six universe names
are explicitly bound; object and morphism universes of A and B, and the two
localization morphism universes, remain independent. No boundedness,
Noetherian, field, or finiteness hypothesis was added.

Independent searches, using different phrasing from the worker:

- msearch.py leanfinder: "An additive left exact functor with a uniform bound
  on derived functors admits total right derivation on unbounded acyclic-term
  complexes". Eight hits; ordinary rightDerived and exact-functor
  mapDerivedCategory/mapDerivedCategoryFactors are not this theorem.
- msearch.py loogle: `CategoryTheory.Functor.rightDerived`. Returned ordinary
  right-derived-functor infrastructure, not the unbounded computation result.
- Direct rg on Mathlib CategoryTheory and Algebra/Homology, upstream
  WeilConjectures, and project lean/Sheaf for finite dimension/derived,
  unbounded acyclic, and computes/rightDerived combinations. Results are
  unrelated dimension statements, specialized computations, and total-derived
  infrastructure; no exact existing theorem. Read upstream
  quasiIso_map_of_rightAcyclic itself: it requires IsStrictlyGE a for both
  complexes, so it does not replace this item.

I also opened the imported KInjectiveTotalDerived theorem, degreewise injective
K-injective resolution instance, full right-derived long exact sequence theorem,
and mappingCone.quasiIso_iff_acyclic. Their signatures supply the objects and
steps claimed in the proof plan. The module docstring cites Tag 07K7 and the
item blueprint; the theorem docstring carries all seven node proof steps,
including finite backwards dimension shifting and the d = 0 case. The only
new declaration is the named theorem with `sorry`; there is no definition,
hollow data, private notion, file-local instance, or proved auxiliary result.
There are no new nodes, dependency modules, or statement corrections to audit.

Mismatches found: none. Changes: appended this independent reading only; kept
the correct Lean statement, docstrings, imports and node unchanged. A direct
text comparison confirms lean.statement equals the file's signature verbatim.
All signature variables are bound. scompile.py compiled the delivered module
cleanly through its authorized local overlay (no errors or warnings).

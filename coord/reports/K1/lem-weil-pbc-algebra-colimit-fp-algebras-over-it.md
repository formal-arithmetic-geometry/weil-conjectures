## Worker report

The module `Sheaf.RingTheory.ColimitFinitelyPresentedAlgebras` states
`CommAlgCat.isFiltered_and_isColimit_finitelyPresentedAlgebras`, with its proof left
as `sorry`. No definition, additional node, dependency module, or statement correction
is needed.

Source read: Stacks Tag 0BUF, Lemma `lemma-ring-colimit-fp-category`, proof and
set-theoretic footnote, at https://stacks.math.columbia.edu/tag/0BUF. The local
literature/stacks-project/algebra.tex was absent, so the published source was opened.
The node uses any set of representatives rather than the footnote's particular set;
this is preserved in Lean.

Hypothesis and clause correspondence:

- The commutative ring R is `(R : Type u) [CommRing R]`.
- The commutative R-algebra Λ is `(Λ : CommAlgCat.{max u v} R)`; its ring and algebra
  structures are the existing instances on CommAlgCat.
- The set P is `(P : ObjectProperty (CommAlgCat.{max u v} R))`. An object property
  is a predicate on the set of bundled R-algebras, equivalently a subset. It does not
  impose closure under isomorphisms or exclude extra finitely presented algebras.
- Each member is finitely presented: `hfp : ∀ A, P A → Algebra.FinitePresentation R A`.
  Mathlib's `Algebra.FinitePresentation.iff` identifies this with the quotient by a
  finitely generated ideal described in the node, including zero variables/relations.
- Every finitely presented algebra has a representative: `hrep : ∀ A,
  Algebra.FinitePresentation R A → ∃ B : P.FullSubcategory, Nonempty (A ≅ B.obj)`.
  A CommAlgCat isomorphism is exactly an R-algebra isomorphism. Membership is the
  `property` field of B. No uniqueness of representatives is assumed.
- The index category is `CostructuredArrow P.ι Λ`. Its objects consist of
  `left : P.FullSubcategory` and `hom : P.ι.obj left ⟶ Λ`; these are the specified
  pairs (A, α). Its morphisms have an underlying algebra map and the equation
  `P.ι.map f.left ≫ Y.hom = X.hom`, exactly α' composed with φ equals α.
- Smallness is inherent in this construction: the object collection is a Type,
  and every hom collection is a Type, hence both are sets. No essential-smallness
  hypothesis on a large category or skeletal replacement is substituted.
- `IsFiltered (CostructuredArrow P.ι Λ)` asserts nonemptiness, common receiving
  objects, and equalization of parallel arrows, exactly the node's three conditions.
- `Cocone.fromCostructuredArrow P.ι (𝟭 (CostructuredArrow P.ι Λ))` is Mathlib's
  canonical cocone: its point is Λ and its component at (A, α) is α. Its diagram is
  the identity followed by `CostructuredArrow.proj P.ι Λ ⋙ P.ι`, so sends (A, α) to A
  and a triangle to its underlying algebra map.
- `Nonempty (IsColimit ...)` asserts the colimit universal property for precisely
  that cocone in commutative R-algebras. Nonempty packages the data-valued IsColimit
  as a proposition; it retains the existence and uniqueness of all factorizations.

Recorded dependency declarations used:

- def-weil-pbc-category-colimit: `CategoryTheory.Limits.IsColimit`, `Cocone`, and
  `CategoryTheory.IsFiltered`. Read the recorded module
  Mathlib.CategoryTheory.Limits.HasLimits (the generated colimit declaration and
  its docstring via the to_dual source), and the defining signatures/docstrings in
  Limits.IsLimit, Limits.Cones, and Filtered.Basic. This theorem needs the universal
  property, rather than a chosen colimit object.
- def-weil-pbc-finitely-presented-algebra: mathlib_match `Algebra.FinitePresentation`
  from Mathlib.RingTheory.FinitePresentation; read its class signature/docstring
  and `Algebra.FinitePresentation.iff` (finite polynomial quotient characterization).

All helper constructions are existing Mathlib notions: CommAlgCat, ObjectProperty's
full subcategory and inclusion, CostructuredArrow, and Cocone.fromCostructuredArrow.
The last declaration was read in Limits.ConeCategory. No copies are defined here.

Edge cases checked before writing: zero R and zero Λ are allowed (no Nontrivial
instance); zero generators and zero relations are allowed by FinitePresentation;
P may contain multiple isomorphic algebras and any extra finitely presented algebras;
P cannot be empty under hrep since R itself is finitely presented. Λ need not be
finitely presented. `u v` are explicitly bound and unrestricted; carriers use
`max u v` so the ambient category contains R and its finite polynomial algebras.
Every ordinary set of R-algebras fits by increasing v. The indexing category lives
in the larger object universe, which places no bound on the size of P. The colimit
is asserted in the algebra category, not merely for its underlying sets.

Searches actually run:

- msearch.py leanfinder, "Every commutative R algebra is the filtered colimit of the
  finitely presented R algebras mapping to it": eight hits, including
  RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit and
  CommRingCat.isFinitelyPresentable_hom. These concern maps out of finitely presented
  algebras into existing filtered colimits, not the present density statement.
- msearch.py loogle, "CommAlgCat, IsFiltered": zero hits; service reported unknown
  identifier IsFiltered. This query supplies no evidence of nonexistence.
- msearch.py grep, "CostructuredArrow|IsFinitelyAccessibleCategory|0BUF" in
  Algebra/Category: zero hits.
- msearch.py leansearch, "Every algebra is a filtered colimit of finitely presented
  algebras": unavailable, Internal Server Error (not a negative search).
- Direct rg of WeilConjectures and lean/Sheaf for the item id, accessibility,
  CostructuredArrow, and colimit/finite-presentation patterns: general uses of
  costructured arrows, no matching statement. The node's earlier Mathlib search
  candidates were also checked: Presentable.Dense supplies generic results under
  an accessibility hypothesis, which is not an instance for CommAlgCat here.
- Read CommAlgCat.Basic and CommAlgCat.FiniteType; no matching theorem.
- Searched the proposed declaration name in Mathlib, WeilConjectures, lean/Sheaf,
  and dag/lean_names_upstream.json: no collision.

Validation: scompile.py on the single module succeeded (exit code 0, 1.4 seconds),
with no errors or warnings. All universes and binders are explicit. The declaration
is the only theorem and its entire proof is sorry; the docstring records all seven
proof steps and their DAG dependencies. No statement dispute or node fault found.

## Second reading by K1

Independent reading of the sandbox node and module, both statement dependencies,
Mathlib's defining declarations, and Stacks Tag 0BUF. The local algebra.tex is
absent; I read the published lemma and fetched the upstream Stacks algebra.tex,
label `lemma-ring-colimit-fp-category`, including its proof and footnote. The
surrounding section introduces no additional hypotheses: the input is a map of
commutative rings. The footnote selects a set of polynomial quotients; the node
allows any set containing representatives, and its proof transports the tensor
products and quotients to those representatives. This changes neither conclusion.
The source's word "cofiltered" in its colimit paragraph is a typo: its statement,
the arrows in its proof, and the node all use filteredness.

Objects, hypotheses and conclusions, checked individually:

1. Arbitrary commutative ring R: `(R : Type u) [CommRing R]`. Exact; no field,
   Noetherian, characteristic, or Nontrivial assumption.
2. Commutative R-algebra Λ: `(Λ : CommAlgCat.{max u v} R)`. Exact: Basic.lean:30
   bundles a carrier, CommRing and Algebra R; its Hom is an R-algebra homomorphism
   and composition is algebra-map composition (Basic.lean:63-78).
3. Set P of R-algebras: `P : ObjectProperty (CommAlgCat.{max u v} R)`. Exact:
   ObjectProperty.Basic:35 is the predicate `C → Prop`, hence a subset of the
   bundled-object collection. It is not assumed skeletal or isomorphism-closed.
4. Every member of P is finitely presented: `hfp : ∀ A, P A →
   Algebra.FinitePresentation R A`. Exact. I opened the dependency
   def-weil-pbc-finitely-presented-algebra and FinitePresentation.lean:44,128:
   the class is existence of a finite-variable polynomial surjection with FG
   kernel, and `iff` is an algebra isomorphism from the quotient by an FG ideal.
   This is exactly the node's finite generators and finite relations.
5. Every finitely presented algebra has a representative in P: `hrep : ∀ A,
   Algebra.FinitePresentation R A → ∃ B : P.FullSubcategory,
   Nonempty (A ≅ B.obj)`. Exact: FullSubcategory has fields `obj` and `property`;
   the isomorphism is in CommAlgCat, hence preserves the R-algebra structure.
   No representative is required to be unique and no assumption is made on Λ's
   finite presentation. The universal/existential quantifier order agrees.
6. Index objects are all pairs (A, α), A in P, α : A → Λ:
   `CostructuredArrow P.ι Λ`. Exact: its `left` belongs to the full subcategory,
   whose inclusion has object B.obj; its `hom` is the map to Λ.
7. Index morphisms are precisely algebra maps φ with α'φ = α: morphisms in that
   costructured-arrow category. Exact: StructuredArrow.Basic:550 gives
   `S.map f.left ≫ Y.hom = X.hom`; FullSubcategory.ι maps a morphism to its
   underlying algebra map. `homMk` and `homMk_surjective` show no extra data or
   extra restriction on triangles.
8. Smallness: the above object's collection and every hom collection are Types,
   so are sets. Exact for the node's set-theoretic meaning. An explicit
   `SmallCategory` hypothesis is unnecessary; the hom universe can be smaller
   than the object universe. No chosen skeleton or essential-smallness substitute.
9. Nonemptiness, common receiving objects, equalization of parallel arrows:
   `IsFiltered (CostructuredArrow P.ι Λ)`. Exact: Filtered.Basic:82-98 defines
   these three conditions, including Nonempty (not just IsFilteredOrEmpty).
10. Diagram sends (A,α) to A and φ to φ: the diagram of
    `Cocone.fromCostructuredArrow P.ι (𝟭 (CostructuredArrow P.ι Λ))` is identity
    followed by `CostructuredArrow.proj P.ι Λ ⋙ P.ι`. Exact.
11. Specified cocone has vertex Λ and leg α: ConeCategory.lean:299 defines
    `pt := X` and `ι.app j := (G.obj j).hom`. Exact with X = Λ, G = identity.
12. That cocone is a colimit in commutative R-algebras:
    `Nonempty (IsColimit (...))`. Exact: IsLimit.lean:64-76 defines IsColimit
    by desc, factorization for every leg, and uniqueness for every cocone in the
    same category. Nonempty retains precisely existence of this universal
    property. I also read the category-colimit dependency's recorded HasLimits
    declaration (the to_dual-generated chosen colimit) and its listed Cocone,
    IsColimit and IsFiltered declarations. The statement correctly uses its
    universal-property interface; no HasColimit hypothesis is added.

Edge cases: R and Λ may be zero, and there is no restriction on characteristic.
FinitePresentation permits n = 0 and zero relations. P = empty cannot satisfy
hrep: R is finitely presented, including when R is zero; no separate nonempty
hypothesis hides this fact. Repeated isomorphism classes and extra finitely
presented objects are allowed. No schemes, n-dependent bounds, or empty-scheme
cases occur. Universes u and v are explicitly bound; max u v supplies an ambient
carrier universe containing R and polynomial presentations. Arbitrary sets of
algebras can be placed in a sufficiently large such universe (using universe
lifting when necessary); index objects need not lie in the carrier universe.
The universal property ranges over the ambient algebra category, with no bound
on a set P other than being a set in a universe.

Independent searches, using different wording from the author:

- LeanFinder through msearch.py: "The comma category of finite presentation
  algebras over a commutative algebra is filtered and the forgetful functor has
  that algebra as colimit". Eight hits: finite-presentation coyoneda preservation,
  finite presentability in Under R, and factorization through an already given
  filtered colimit. None states this density theorem.
- Loogle through msearch.py: `CategoryTheory.CostructuredArrow`. Twelve hits
  confirm the existing comma-category definition and its morphisms/projection;
  no algebra-density theorem.
- LeanSearch through msearch.py: "A commutative algebra is the colimit of the
  category of finite polynomial quotient algebras mapping to it". Internal Server
  Error; unavailable, not evidence of absence.
- Direct rg of Mathlib CommAlgCat, Ring/FinitePresentation, and Presentable/Dense
  for accessibility, 0BUF, finite-presentation/colimit patterns, and
  CostructuredArrow. Read Presentable/Dense:76-94: its generic results require
  IsFinitelyAccessibleCategory and the finitely presentable object property;
  they do not supply this theorem for arbitrary representative set P.
- Direct rg of WeilConjectures and lean/Sheaf for colimit/finitely-presented
  wording, accessibility, 0BUF and the proposed full declaration name, and of
  dag/lean_names_upstream.json for the name. Opened upstream
  Mathlib/Algebra/Category/Ring/FilteredColimits.lean:276-345: its
  `CommRingCat.isColimitFGSubalgebraCocone` assumes a field k and uses finitely
  generated subalgebras, with a colimit in CommRingCat, so is not this statement.
  The project's FinitePresentationColimit concerns descent of modules and
  projectivity, not the category of finite-presentation algebras over Λ.
  No exact existing statement or declaration-name collision found.

No mismatch found; no Lean or node change was needed. There are no new definition
nodes, dependency modules, or statement correction. The module's one theorem has
only `sorry` as proof and defines no data. Its docstring includes all seven node
proof steps with the dependencies they use. The imports supply exactly the
bundled algebra category, finite presentation, full subcategory, filteredness,
and canonical cocone. Header, namespace, declaration docs and line widths follow
the example. I checked the node's lean.statement is verbatim equal to the file's
signature, all binders/universes are explicit, and the only changed node field
against the read-only base is lean.

Validation: scompile.py on the absolute sandbox module path succeeded, exit code
0, 1.4 seconds, no errors or warnings. An initial invocation with a relative path
from the read-only repository failed to find the sandbox file; rerunning with its
absolute path fixed the invocation without changing code.

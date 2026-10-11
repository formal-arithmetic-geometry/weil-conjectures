## Worker report

The delivery adds filtered ind-diagram and cofiltered pro-diagram definitions and states
`CategoryTheory.preDerivedAdjunctionGeneral`.  The theorem uses abelian categories and
Mathlib derived categories, an adjunction `G ⊣ F`, objects `K`, `M`, represented values
`RF`, `LG`, essentially constant systems `I` and `H`, and isomorphisms identifying the
represented values with `F.obj K` and `G.obj M`.  Its conclusion is the canonical Hom-set
bijection, packaged as `Nonempty ((M ⟶ RF) ≃ (LG ⟶ K))`.

The ind definition binds a filtered category `J`, a diagram `F : J ⥤ C`, value `X`, a
natural family `p`, a splitting index and section, and the eventual factorization clause.
The pro definition binds a cofiltered category, diagram `G`, value `X`, a natural cone,
a splitting retraction, and the dual eventual factorization clause.  Each theorem
hypothesis and conclusion appears explicitly in the theorem signature.  The proof is
`sorry`, as required for stage 2.

Dependencies used are `CategoryTheory.Abelian` (Mathlib, for `def-sp-abelian`) and
`DerivedCategory` (Mathlib/Algebra/Homology/DerivedCategory/Basic, for
`def-weil-abstract-derived-category`).  The two project dependency nodes
`def-pc-essentially-constant-ind-diagram` and
`def-pc-essentially-constant-pro-diagram` are stated by the accompanying modules.

Edge cases checked: the filtered and cofiltered indexing categories may be empty only
when their typeclass permits it; no finiteness or nonzero assumptions are imposed on
categories or objects; all derived-category universes are explicit; the theorem allows
zero objects and empty Hom sets.

Searches: `rg -n "pre-derived|essentially constant|derived adjunction"` in the project
and source found no matching declaration.  LeanFinder query “general pre-derived
adjunction via localization and essentially constant ind/pro systems” returned only
Mathlib `CategoryTheory.Adjunction.derived` variants, which require absolute derived
functors.  Loogle query `CategoryTheory.Adjunction, Localization, IsLeftDerived,
IsRightDerived` returned no hits.  Grep of Mathlib `CategoryTheory` for
`lemma-pre-derived-adjoint-functors-general|essentially constant ind-object|localization
adjunction` returned no hits.  LeanSearch was unavailable (Internal Server Error).

## Statement corrected

The base leaves the componentwise action of underived functors on complexes implicit.
The final correction follows Stacks Derived Categories 0DVC (derived.tex,
lemma-pre-derived-adjoint-functors, lines 9569--9588), specialized from 0FND
(lines 9482--9566). It makes additivity, the induced homotopy-category functors,
the localization functors, the actual quasi-isomorphism diagrams, and the representing
cone/cocone explicit. It expands "canonical" into the fraction-representative formula
and "functorial" into an equation for both localized variables. It does not change
any unit statement or the six proof steps. The old statement is preserved verbatim
in statement_change.old_statement; old_stmt_deps records the two original dependencies.

The first worker's proposed correction was wrong: it assumed F and G were already
adjoint on derived categories, identified RF(K) with F(K) and LG(M) with G(M),
and used arbitrary unrelated diagrams. That circular correction has been replaced,
not endorsed. These additional hypotheses are absent from the final statement.

All citers were read:

- lem-pc-derived-adjoint-functors: holds true. Its first step uses the pointwise
  comparison and its second uses functoriality to assemble an adjunction when the
  functors are defined everywhere. Both are supplied, without assuming the derived
  adjunction. The Hom equivalence is inverted for the citer's orientation.
- lem-pc-rf-mv-triangle-naturality: holds true. Its adjoint-square argument needs
  the canonical comparison natural in both variables. The final equation supplies
  this for arbitrary localized morphisms. Compatibility with shift still comes from
  the triangulated derived functors, as in the citer; no citer was edited.

## Second reading by J1

Independent source-first reading: I opened the base and corrected item, both essential-
constancy nodes, the abelian and derived-category dependency nodes and their recorded
Mathlib declarations, both citers and their actual proof uses, all three final modules,
and Stacks derived.tex and categories.tex. The literature checkout was absent locally;
I fetched the official Stacks GitHub .tex sources into this item's scratchpad and
verified the labels and their recorded line locations. I did not write the first
worker's statement. The final delivery replaces its invalid correction.

The source introduces exact functors on unlocalized triangulated categories before
0FND; 0DVC specializes them to componentwise functors from an abelian adjunction.
The following is the source/object/hypothesis/conclusion list and its final Lean match:

- Abelian A, B: `{A : Type uA} [Category.{vA} A] [Abelian A]`, and the corresponding
  B binders. MATCH. I read CategoryTheory.Abelian in Mathlib's Abelian/Basic.lean;
  finite products in a preadditive category give the finite biproducts and zero object.
- D(A), D(B) and localization from homotopy categories: independent
  `[HasDerivedCategory.{wA} A]`, `[HasDerivedCategory.{wB} B]` and `QA`, `QB`, set to
  DerivedCategory.Qh. MATCH. Basic.lean defines the localization of integer-indexed
  cochain complexes, Q, Qh, and the factorization from the homotopy quotient.
- F:A->B, G:B->A, G left adjoint to F: `(F : A ⥤ B)`, `(G : B ⥤ A)`,
  `(adj : G ⊣ F)`. MATCH. `[F.Additive]`, `[G.Additive]` explicitly expose the
  componentwise structure. They exclude no abelian adjunction: the right adjoint
  preserves finite products and the left finite coproducts, hence both preserve
  biproducts and are additive. No preservation of quasi-isomorphisms is assumed.
- K, M complexes, considered up to homotopy: the HomotopyCategory A/B binders have
  shape `ComplexShape.up ℤ`. MATCH. Every homotopy-category object is represented
  by a complex. The Hom endpoints correctly use `QA.obj K`, `QB.obj M`.
- Indices s:K->I and t:P->M are quasi-isomorphisms with commuting triangles:
  `WA.Under ⊤ K` and `WB.Over ⊤ M`, where WA/WB are HomotopyCategory.quasiIso.
  MATCH. I read MorphismProperty.Comma: its object field `prop` restricts the
  structural arrow and ⊤ leaves the commuting-triangle morphisms unrestricted.
  The displayed filtered/cofiltered instances are the source's denominator-category
  structures, consequences of the quasi-isomorphism fraction calculus, not unrelated
  extra index categories. Fractions.lean gives both calculi for these WA/WB.
- Actual diagrams Q'F_h(I), QG_h(P), including transition maps: local `R`/`L` compose
  the respective forgetful functor with F/G.mapHomotopyCategory and Qh. MATCH.
  `Fh` and `Gh` are componentwise functors, not presumed derived functors.
  `ah := adj.mapHomotopyCategory ...` is the induced underived adjunction. I opened
  upstream HomotopyCategory/Adjunction.lean at this declaration: it descends the
  componentwise complex adjunction through homotopy-equivalence localization.
- Defined values RF(K), LG(M): `RF : DerivedCategory B`, `LG : DerivedCategory A`
  with `IsEssentiallyConstantIndDiagram (R K) RF` and its pro dual. MATCH.
- Their chosen representing cocone/cone: universally quantified natural transformations
  `p : R K ⟶ (Functor.const _).obj RF`, `u : (Functor.const _).obj LG ⟶ L M`,
  with `splitR K RF p`, `splitL M LG u`. MATCH. These local predicates spell out
  the witness clauses of the imported existential definitions for these particular
  natural transformations; they do not introduce another general definition. Every
  witness of the definition yields such p/u, and every such p/u yields a witness.
- Hom comparison with the source orientation: `∃! e : (QB.obj M ⟶ RF) ≃
  (LG ⟶ QA.obj K)`. MATCH. Equiv is the isomorphism of Hom sets.
- Canonicality: `canonical K M RF LG p u e` states its value on every pair of
  denominator indices and numerator f:P->F_h(I). `right t f` is Q'(t)^(-1)
  followed by Q'(f); `left s ((ah.homEquiv ...).symm f)` is the adjoint numerator
  followed by Q(s)^(-1). Multiplying by p and u gives exactly the six-colimit
  calculation. MATCH. Representatives exhaust the Hom set by essential constancy
  and fraction calculus, so uniqueness adds no strength beyond canonicality.
- Functoriality in both variables wherever the partial functors exist: the last
  universally quantified clause compares any canonical e' with e. `k` and `m` are
  arbitrary *derived-category morphisms*, not just images of homotopy maps.
  `r` and `l` are the induced maps of representing values, identified by the two
  displayed compatibility conditions on all left/right fraction representatives.
  The final equation is `e' (m ≫ h ≫ r) = l ≫ e h ≫ k`. MATCH, with the proper
  variance in M. The compatibility conditions express what "induced" means, not
  additional assumptions on the categories or underived functors. The quantification
  covers the source's triangulated subcategories without needing an extra closure
  assumption, since no triangle operation occurs in the Hom comparison itself.

Definition-module reading: both are existing DAG notions, not new nodes.
For the ind node I checked Stacks 05PU(1), categories.tex lines 2928--2947, and
05PY, lines 3134--3192. The module's J, Category J, IsFiltered J, C, Category C,
F and X give exactly the source objects. The natural p_j match the cocone;
j₀ and s with `s ≫ p j₀ = 𝟙 X` give its splitting; k, f₀:j₀->k, f:j->k and
`F.map f = p j ≫ s ≫ F.map f₀` give the eventual factorization. All MATCH.
For the pro node, 05PU(2) and 05PZ are dual: IsCofiltered J; natural u_j;
r with `u j₀ ≫ r = 𝟙 X`; arrows k->j₀ and k->j; and
`G.map f = G.map f₀ ≫ r ≫ u j`. All MATCH, including arrow directions.
The prior private copies were moved unchanged in substance to these dependency
modules, with source docstrings and their own blueprint ids. No new node was created.

Edge cases: the index categories are nonempty (identity quasi-isomorphisms), including
for zero complexes; the Stacks and Mathlib filtered/cofiltered conventions both require
nonemptiness. Zero objects and zero complexes, and cohomological degree n=0, are
allowed. No finiteness, boundedness, nonzero, Noetherian, scheme, ring, field, or
characteristic condition is introduced. Object/Hom/localization universes of A and B
remain independent. The canonical equivalence and both naturality variables retain
those universes; no ULift or universe equality silently restricts the Hom sets.

Independent searches, run via msearch.py and logged in searches.jsonl:
LeanFinder "pointwise derived adjunction essentially constant quasi-isomorphism diagrams"
returned homological-localization factorization declarations and exact-functor
mapDerivedCategoryFactors, not this pointwise theorem. "filtered diagram isomorphic to a
constant ind object splitting cocone eventual factorization" returned
IsEventuallyConstantFrom cocone constructions. I read EventuallyConstant.lean and
Indization/IndObject.lean: eventual transition isomorphisms are stronger than essential
constancy; IsIndObject only asserts an ind presentation, not constancy with specified
value. Loogle `CategoryTheory.Adjunction.mapHomotopyCategory` returned no hits in Mathlib;
direct rg found the upstream declaration subsequently read and imported. LeanSearch
for partially defined derived adjunction returned Internal Server Error, recorded as
unavailable. Grep `essentially.constant|preDerivedAdjunction` in Mathlib CategoryTheory
returned no hits. Grep `IsEventuallyConstant|IsIndObject|EssentiallyConstant` returned
the above different notions. Direct rg in WeilConjectures/ and lean/Sheaf/ found only
IsEssentiallyConstantWithValue for natural-number inverse systems of abelian groups,
a strict specialization. I read Mathlib Adjunction.derived: it assumes absolute
Kan-derived functors and composites; it does not give this pointwise criterion.
Neither definition nor the theorem has an exact existing declaration.

Mismatches repaired: the circular derived adjunction, arbitrary indexing diagrams,
extra RF=F(K)/LG=G(M) isomorphisms, existential unnamed bijection, missing naturality,
private dependency definitions, missing dependency records, insufficient theorem
proof docstring, and missing copyright header. The final node signature is copied
verbatim from the file, including its local let expressions. Every theorem proof
remains sorry; both definitions contain no sorry. All declaration docstrings cite
their source and node, and the theorem docstring gives all six proof steps with the
DAG lemmas used. I checked unbound variables/universes and line widths. Combined
server compilation of all three modules passes without warnings. The first combined
compile exposed reused universe names between sibling modules; independent names now
avoid that concatenation issue. The current delivery checker accepts the two dependency
modules under a correction; a suspected restriction from the initial local script
was disproved by the dry run and is not a blocker.

## Dependency modules

`def-pc-essentially-constant-ind-diagram`: no recorded Lean declaration or Mathlib
match exists. The private general definition belongs to this existing DAG node;
EssentiallyConstantIndDiagram.lean now supplies it, with an explanatory lean.note.

`def-pc-essentially-constant-pro-diagram`: the dual existing node likewise has no
Lean record or Mathlib match; EssentiallyConstantProDiagram.lean supplies precisely
its 05PU(2) definition, with its own signature and explanatory lean.note.

## Reviewer fix (R-pdg0952, stage 2)

E1 landed the two essential-constancy predicates (a7b6829e5) as
`Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantInd` / `...Pro`, declarations
`CategoryTheory.IsEssentiallyConstantIndDiagram` / `CategoryTheory.IsEssentiallyConstantProDiagram`
(value as argument, `IsFiltered J` / `IsCofiltered J` a conjunct). This delivery's two
dependency modules redefined the same names (H4/H12: second definition of a landed notion);
they are dropped and both dependency nodes reverted to their sheaf-dag records. The main
module now imports the landed modules, and the `[IsFiltered ...]`/`[IsCofiltered ...]`
instance binders are removed: filteredness of the denominator categories is a fact in the
node and is contained in the landed predicates. The statement is otherwise unchanged.
The "Dependency modules" and "Definition-module reading" sections above describe the
dropped modules.

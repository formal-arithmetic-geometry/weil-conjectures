## Worker report

The module states `AlgebraicGeometry.hom_etaleLocus_translation`. It uses the existing group
scheme encoding `CategoryTheory.GrpObj` through
`WeilConjectures.AlgebraicGeometry.GroupScheme.Basic`, the translation `GrpObj.mulLeft`, and
`GrpObj.onePoint`, together with `AlgebraicGeometry.IsAbelianVariety` from
`WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`.

The field `k` is bound with `[Field k]`; `A` and `H` are objects of
`Over (Spec (.of k))`, with `[GrpObj A]`, `[GrpObj H]`, and `[IsAbelianVariety A]`; `f` is a
homomorphism via `[IsMonHom f]`; `hA` renders the source's nonzero hypothesis as the absence of
an isomorphism from `A` to the terminal (zero) group scheme; and `a` is an arbitrary k-point.
The first conclusion is the set-image equality for the pointwise etale locus, expressed as
`∃ U, x ∈ U ∧ Etale (U.ι ≫ f.left)`. The second conclusion is that this set is empty or
`Set.univ`. The third is `Etale f.left` iff etaleness on an open neighbourhood of
`GrpObj.onePoint A`.

The dependency declarations used are `CategoryTheory.GrpObj` (Mathlib,
`Mathlib.CategoryTheory.Monoidal.Grp`), `AlgebraicGeometry.GrpObj.mulLeft` and
`AlgebraicGeometry.GrpObj.onePoint` (`WeilConjectures.AlgebraicGeometry.GroupScheme.Basic`),
and `AlgebraicGeometry.IsAbelianVariety`
(`WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`). The proof dependencies named by the
node are used in the docstring: `GrpObj.mulLeftIso` realizes translation automorphisms, and
`lem-sc-etale-base-change-geometric` supplies geometric base change.

Edge cases checked: the locus may be empty; the all-of-`A` case is represented by `Set.univ`;
no nonemptiness of the point set is assumed; arbitrary field characteristic is allowed; and
`a` ranges over all k-points, including the identity.

Searches: `msearch.py leanfinder "translation invariance etale locus homomorphism group scheme"`
returned no theorem; `msearch.py loogle "IsEtale translation homomorphism"` returned unknown
identifier; grep for `etale.*locus|IsEtaleAt` in Mathlib and WeilConjectures found no scheme-level
translation-locus declaration. Existing translation and abelian-variety declarations above were
therefore reused.

## Earlier second reading (a previous round; superseded)

Read the node and module independently. Every source hypothesis is represented: field, abelian
variety, group scheme target, homomorphism, nonzero condition, and arbitrary k-point. The three
clauses match translation invariance, empty-or-all consequence, and etale-at-identity
criterion. No proof is supplied beyond `sorry`.


## Second reading by H1

Independent source reading: the repository has no fetched Stacks tree. Read the local
Stacks copy `/home/ubuntu/c1-stacks-review/groupoids.tex`, lines 1825–1848,
`lemma-abelian-variety-multiplication-by-d-etale`, especially its translation argument.
It assumes an arbitrary field and a nonzero abelian variety; no algebraic closedness or
characteristic restriction. The node abstracts precisely that argument to a homomorphism
into a group scheme. Also read the preceding abelian-variety definition and smoothness
lemma, and all three statement-dependency node files and their defining Lean declarations.

Object/hypothesis/conclusion checklist (each verdict: matches):

- Field k: `{k : Type u} [Field k]`, with arbitrary bound universe u.
- Abelian variety A over k: `A : Over (Spec (.of k))`, `[GrpObj A]`,
  `[IsAbelianVariety A]`. Opened `AbelianVariety/Defs.lean`: the class extends
  `IsProper A.hom`, `Smooth A.hom`, `ConnectedSpace A.left`, exactly the recorded
  `def-sc-abelian-variety`. Stacks uses the equivalent proper geometrically integral
  group variety definition and proves smoothness. No extra structure hypothesis.
- Nonzero A: `hA : ¬ Nonempty (A ≅ 𝟙_ (Over (Spec (.of k))))` excludes the
  zero group scheme Spec k. An isomorphism to the terminal k-scheme is equivalent to
  being the trivial group scheme: its unique section is the identity, so the group
  structure is necessarily trivial. This is not an injectivity/nonemptiness condition.
- Group scheme H over the same k: `H : Over (Spec (.of k))`, `[GrpObj H]`.
  Opened Mathlib `Monoidal/Grp.lean`: multiplication/unit/associativity from MonObj,
  inverse and both inverse laws from GrpObj; no finiteness or separatedness of H.
- Homomorphism f: `(f : A ⟶ H) [IsMonHom f]`. Opened `Monoidal/Mon.lean`:
  the fields preserve the unit and multiplication. Between groups inversion then follows;
  this is a group homomorphism, not a monomorphism (IsMonHom does not assert injectivity).
- Every k-point a: `(a : 𝟙_ (Over (Spec (.of k))) ⟶ A)` is a section over k,
  universally bound after f, with no restriction to closed/geometric points.
- Translation: `GrpObj.mulLeft A a`. Opened `GroupScheme/Basic.lean`:
  its body is `lift (toUnit A ≫ a) (𝟙 A) ≫ μ[A]`, precisely the dependency
  node's left translation. The same file's `mulLeftIso` has this hom and inverse
  translation by a inverse, so translation is already an isomorphism.
- Étale locus: `{x : A.left | ∃ U : A.left.Opens, x ∈ U ∧ Etale (U.ι ≫ f.left)}`.
  Mathlib Etale is the actual étale ring-map property on affine charts; the displayed
  predicate is étaleness on a source neighbourhood, exactly the project convention
  for étale at a point. It uses all scheme points, not only rational points.
- Carries the locus isomorphically to itself: the first conjunct is `Set.image`
  equality under `(GrpObj.mulLeft A a).left.base`. Since the reused translation is
  an isomorphism, equality of this open locus gives its isomorphic restriction; no
  additional existence clause for the already known inverse is needed.
- Empty or all: the second conjunct is equality to `∅` or `Set.univ` for that same
  locus, not density or a statement just about rational points.
- Global criterion: the third conjunct is `Etale f.left ↔ ∃ U, onePoint A ∈ U ∧
  Etale (U.ι ≫ f.left)`. Opened `onePoint`: it evaluates the unit section at
  the unique prime of k. This is the identity point of the node.

Edge cases: the zero abelian variety is excluded exactly by hA; the empty scheme
cannot carry a group scheme over a field because its identity section would be missing.
Empty locus remains explicitly possible, and all-of-A is Set.univ. The identity k-point
is included among a; no assumption of other rational points is made. All characteristics,
including positive characteristic and imperfect fields, are allowed. There is no n or
index family in this item (so n = 0 and empty indexing do not apply). Scheme.{u} over
k : Type u is the project's recorded group-scheme encoding, and u is arbitrary; no
quantifier over test schemes in a smaller universe occurs. Every variable and universe
is explicitly bound.

Independent H4 searches: ran msearch LeanSearch for "A morphism of group schemes is
etale if and only if it is etale near the identity" (service unavailable: Internal
Server Error, no negative verdict inferred); LeanFinder for "The open subset where a
group scheme homomorphism is etale is invariant under left multiplication by rational
points" (eight results: composition lemmas and algebraic etaleLocus, no matching theorem);
Loogle `AlgebraicGeometry.Etale` (property and permanence lemmas, no matching theorem);
and msearch grep `etale.*(mulLeft|onePoint)|hom_etale|etaleLocus` in AlgebraicGeometry
(zero hits). Independently rg searched Mathlib, WeilConjectures and repository lean/Sheaf
for etale-locus, translations, and identity etaleness: ring algebra loci and specific
Artin–Schreier material are different statements. rg also checked the full proposed
name in the source, project, and upstream name index: absent. Reused the existing notions;
no definition, new node, or dependency module is necessary.

Mismatches and repair: no mathematical/signature mismatch. H8: the theorem's docstring
had no explicit source place; added the Stacks lemma label and expanded each of the
node's two proof steps, including both base-change reflections and source locality.
H9: added the repository-standard copyright/license/authors header. Kept all imports,
the declaration, signature and node's lean.statement unchanged; the three imports supply
translations, abelian varieties, and Etale respectively. No private/local notion, hollow
definition, theorem proof, or hidden binder was introduced. The sole proof remains sorry.
No statement correction was made; no statement_change or citer review is required.

Validation: scompile compiled the delivered module on the server in 1.9 seconds with
exit code 0 and no warnings. Verified the node lean.statement is verbatim equal to
the file signature and every Lean line is at most 100 characters.

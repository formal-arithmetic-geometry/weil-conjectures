## Worker report

Module: `Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry`.
Main declaration: `AlgebraicGeometry.affine_normal_quotient_geometry`.
There is one postponed theorem, with `sorry` as its entire proof. Its docstring gives
all eleven DAG proof steps, including their mathematical inputs. No theorem is proved.
The node copy changes only `lean`; the accepted stage-1 statement and split are preserved.

The helper `AlgebraicGeometry.IsFppfGroupQuotient` is the quotient-presentation
predicate belonging to this node, listed in `lean.declarations` and documented with
this node's source and blueprint id. It has real Prop-valued data: a kernel square,
local surjectivity, the sheaf condition, a normalized torsor isomorphism, and a
sheafification universal arrow. It contains no sorry, choice of a representing
object, or assumption of a quotient theorem. This is the helper authorization in
the human's new-targets isolation instructions; it introduces no independent
mathematical notion requiring a new DAG node. Finite type is written inline using
the recorded definitions rather than introducing another finite-type predicate.

Hypothesis and clause correspondence:

- The field is `{k : Type u} [Field k]`. Every scheme, group and test object uses
  the fixed universe u, as the existing group-scheme interface does. Extensions
  are arbitrary fields in this universe, not only finite or algebraic extensions.
- A group scheme is `Grp (Over (Spec (.of k)))`. This bundles exactly the recorded
  `GrpObj` data; arrows of `Grp` are scheme arrows with `IsMonHom`.
- Affineness of N and G is `[IsAffine N.X.left]`, `[IsAffine G.X.left]`.
  Finite type is the pair `LocallyOfFiniteType ...X.hom`, `QuasiCompact ...X.hom`,
  exactly the finite-type dependency record. No smoothness or reducedness is
  required of G or N.
- The given inclusion is `i : N ⟶ G`, with
  `[IsClosedSubgroupScheme i.hom.hom]` and
  `[IsNormalSubgroupScheme i.hom.hom]`. These are the recorded upstream notions,
  including injectivity and normality on every algebra of points.
- Representability and the quotient map are `∃ (Q : Grp ...) (q : G ⟶ Q)`.
  The first three conjuncts give Q affine and finite type over the SAME field.
- `IsFppfGroupQuotient i q` specifies exactly the quotient presentation.
  `IsPullback i.hom.hom (toUnit N.X) q.hom.hom η[Q.X]` identifies N with the
  scheme-theoretic fibre of the identity, with its specified inclusion.
- Its `Presheaf.IsLocallySurjective (Scheme.fppfTopology.over B)` is actual local
  surjectivity for jointly surjective flat locally finitely presented coverings.
  It does not demand surjectivity on the original algebra of sections.
- The helper's coequalizer has arrows `fst G.X N.X` and
  `lift (fst G.X N.X) (snd G.X N.X ≫ i.hom.hom) ≫ μ[G.X]`.
  On points these are `(g,n) ↦ g` and `(g,n) ↦ gn`; the pointwise coequalizer is
  exactly G(A)/N(A). The unit ηq is normalized by
  `coequalizer.π _ _ ≫ ηq = yoneda.map q.hom.hom`. Representable Q is required
  to be an fppf sheaf and composition by ηq is bijective for EVERY fppf sheaf
  of sets, the sheafification universal property. The big scheme site's affine
  basis induces precisely the algebra coverings in the node. A finite affine
  refinement is represented by the product algebra, also when the base algebra
  is zero; thus this is the same sheafification as the node's algebra description.
- Faithful flatness is explicitly `q.hom.hom.left.appTop.hom.FaithfullyFlat`,
  meaning the induced coordinate-algebra map is faithfully flat as specified.
  `Flat` and `Surjective` are also retained for the geometric interface; they
  are equivalent here by `Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine`.
- Finite presentation is `LocallyOfFinitePresentation q.hom.hom.left`.
  Since both ends are affine this morphism is affine, hence quasi-compact and
  quasi-separated; consequently this is full finite presentation, not merely
  a weaker local condition.
- The torsor conjunct is an actual `∃ e : G.X ⊗ N.X ≅ pullback q q` with its
  two projection equations. These force the morphism `(g,n) ↦ (g,gn)`; an
  unspecified isomorphism of those objects would not suffice.
- For every `(K : Type u) [Field K] [Algebra k K]`, the pullback functor's
  `.mapGrp.map i` and `.mapGrp.map q` again satisfy `IsFppfGroupQuotient`.
  This says Q_K with the ACTUAL base-changed q represents G_K/N_K, compatibly
  with the quotient maps. The unique compatible isomorphism with any other
  representative is exactly the uniqueness in the specified universal property.
- `Smooth G.X.hom → Smooth Q.X.hom` and
  `GeometricallyConnected G.X.hom → GeometricallyConnected Q.X.hom` give the two
  independent descent clauses. Mathlib's geometric connectedness is connectedness
  after field tests; over the field k this is equivalent to connectedness after
  an algebraic closure, the convention in the node. It includes nonemptiness.
- For every closed `j : S ⟶ Q`, the first universal clause constructs P, its
  inclusion p, projection h, and `a : N ⟶ P`. `IsPullback p h q j` is exactly
  P = G ×_Q S as a scheme over k. P is affine finite type and p is a closed
  subgroup. `a ≫ p = i` retains the specified original kernel, while
  `IsFppfGroupQuotient a h` gives the exact fppf sequence and P/N ≅ S.
- The same clause gives normality of p from normality of j, and the implication
  from `Smooth N`, `ConnectedSpace N`, `Smooth S`, `ConnectedSpace S` to BOTH
  `Smooth P` and `ConnectedSpace P`, with no assumption on smoothness of G.
- The next clause constructs S and a cartesian square for EVERY closed subgroup
  H of G containing N (`∃ a : N ⟶ H, a ≫ b = i`). This is surjectivity of inverse
  image on subgroups. The following equivalence states that S0 is contained in
  S1 exactly when its inverse image is contained in the other inverse image,
  by factorization of points on ALL test schemes. It proves order reflection
  as well as preservation. Combined with existence this is the claimed subgroup
  identification, up to the standard isomorphism of subgroup presentations.
  In particular mutual inclusions identify subgroup subobjects, so no injectivity
  or uniqueness part of the correspondence is lost.
- In the last clause the two cartesian squares and compatibility equations fix
  Pi as inverse images and t as the induced inclusion. Normality of s and t
  is equivalent, so normal inclusions are both preserved and reflected.
- When s is normal, there is an affine finite type group R with `r : S₀ ⟶ R`
  such that BOTH `IsFppfGroupQuotient s r` and
  `IsFppfGroupQuotient t (h₀ ≫ r)` hold. Thus S₀/S₁ and P₀/P₁ have the SAME
  representative, with the map induced by P₀ → S₀. This includes the normalized
  quotient comparison, rather than asserting an arbitrary unrelated isomorphism.

Dependency declarations read and used:

- `Field` from `Mathlib.Algebra.Field.Defs` (class extends CommRing and DivisionRing).
- `CategoryTheory.GrpObj`, `Grp`, their arrows, from
  `Mathlib.CategoryTheory.Monoidal.Grp`; `IsMonHom`, point groups and cartesian
  operations from `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`/`Mon`.
- `AlgebraicGeometry.IsSubgroupScheme`, `IsClosedSubgroupScheme`, and
  `IsNormalSubgroupScheme`, from
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`, lines 74--110 read in full,
  together with its kernel section and
  `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`.
- `LocallyOfFiniteType` from `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and
  `QuasiCompact` from `...Morphisms.QuasiCompact`.
- `Smooth` from `Mathlib.AlgebraicGeometry.Morphisms.Smooth`; `ConnectedSpace`
  from `Mathlib.Topology.Connected.Basic`; `GeometricallyConnected` from
  `Mathlib.AlgebraicGeometry.Geometrically.Connected` (the actual class inspected).
- The fppf topology and covering interpretation are from
  `Mathlib.AlgebraicGeometry.Sites.Fpqc`; local surjectivity from
  `Mathlib.CategoryTheory.Sites.LocallySurjective`; the over topology from
  `Mathlib.CategoryTheory.Sites.Over`; coequalizers from the Types/Colimits and
  FunctorCategory modules; canonical group base change from
  `Mathlib.CategoryTheory.Monoidal.Cartesian.Over` and `Functor.mapGrp`.
- All recorded available proof-dependency modules are plain imports, including
  AffineFiniteTypeAlgebra, finite type/finite presentation, faithful-flat base
  change, flat spectrum surjectivity, fpqc representable descent, smooth source
  descent, smooth base change/composition, the rational-point connectedness
  criterion, the closed-point residue-field criterion, and the connected-fibre
  quotient topology lemma. The representation-kernel, flat-image, general-linear
  definition and smooth affine torsor inputs currently have no recorded module;
  no fabricated import or second statement is added for these proof-only inputs.

Sources read: Milne PDF via pdftotext, especially printed pp.104--105 (5.24--5.29),
p.113 (5.55), and p.114 (5.59); the latest blueprint direct-images proof was also
read. The item is an auxiliary node and its source remains Milne's quotient theorem.
No statement correction or disputed statement was needed.

Edge cases checked before finalizing:

- N trivial and N=G give Q=G and Q=1, respectively, and the correct correspondence.
- Characteristic p and a nonsmooth infinitesimal kernel such as μ_p are allowed:
  smoothness of the quotient is conditional on G, not N; lifting is only fppf-local.
- Noncommutative groups are allowed: right cosets are a quotient presheaf, and
  normality is required exactly for group quotients. No commutativity is inserted.
- S trivial, S=Q, S1=S0, and S1 trivial yield the expected pullbacks and quotients.
- Empty affine TEST schemes (zero algebras) are allowed, and the sheaf/local
  surjectivity conditions impose their standard empty-cover behavior. The group
  scheme itself is never empty because it has an identity over the nonzero field.
- ConnectedSpace retains nonemptiness; neither geometric connectedness nor
  connectedness is weakened to preconnectedness. No perfection assumption on k.
- Identity and arbitrary transcendental field extensions are included. Base-change
  maps are the actual mapGrp images, so no arbitrary comparison map was chosen.

Searches performed (2026-10-23):

- msearch.py leanfinder: "An affine finite type group scheme over a field has an
  affine quotient by a normal closed subgroup; quotient map faithfully flat
  finitely presented and subgroup correspondence". Eight unrelated hits, including
  PreGaloisCategory.has_decomp_quotients and QuotientGroup.fg; no scheme quotient.
- msearch.py loogle: "AlgebraicGeometry.IsNormalSubgroupScheme,
  CategoryTheory.GrpObj.ker, AlgebraicGeometry.Flat". Unknown identifier for the
  project-specific first name; no exact match.
- msearch.py leansearch: "affine group scheme quotient by normal subgroup faithfully
  flat". Eight hits: Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine is the
  useful coordinate-ring criterion; remaining hits concern abstract quotient
  groups or ring quotients. None states the node.
- msearch.py grep on Mathlib AlgebraicGeometry:
  "fppf.*quotient|quotient.*fppf|IsNormalSubgroupScheme|faithfullyFlat.*quotient":
  zero matches.
- rg on lean/WeilConjectures and lean/Sheaf for the item id and normal quotient
  terminology: no existing affine group quotient theorem or helper predicate.
  Existing finite-flat relation quotients are restricted to finite relations.
  Their coequalizer/sheafification interface was read and reused as a pattern,
  without copying a finite-only hypothesis.
- Read DAG candidates for normal group quotients and quotient sheafification.
  The homomorphism-factorization node is unstated and a different result; other
  nodes concern special reductive groups or unrelated condensed quotients.
- `python3 tools/blueprint_refs.py search 'fppf quotient'`: zero blueprint matches.
- Exact-name rg across Mathlib, both project Lean roots and
  dag/lean_names_upstream.json found no IsFppfGroupQuotient or
  affine_normal_quotient_geometry declaration.

Validation: scompile.py compiles the actual module and its sandbox probe; the final
pass is required to have no warnings except the expected sorry warning. No global
build, direct repository write, or direct Git command was run.

## Second reading by NW

The dispatcher explicitly prohibits starting another agent. This is a second
clause-by-clause reading by the assigned worker, not a claim of independent
review; the maintainer supplies the independent review under the brief.

Read the node and final Lean again. The first draft had an extra finite-type
helper, removed in favor of the dependency's inline pair of properties. The
first import used the nonexistent Sites.Fppf path, corrected to Sites.Fpqc.
The successive quotient comparison was changed from a conditional comparison
with a supplied representative to an explicit existential common representative,
so it states existence of both quotients as well as their compatibility.
Faithful flatness of the actual coordinate-ring map is now explicit. The
cartesian kernel square and torsor projections were checked against the node's
(g,n) ↦ (g,gn), not just against the objects' names. Both directions of subgroup
inclusion and of normality are retained. Affineness supplies the compactness and
separatedness needed to read local finite presentation as finite presentation.
No mismatch in hypotheses or conclusion remains; no statement_change is needed.

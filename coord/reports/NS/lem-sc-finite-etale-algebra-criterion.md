## Worker report

Existing declarations suffice. No new Lean module, definition, theorem, or dependency
repair is delivered. Only the item's incomplete lean attachment is completed.
The source is WeilConjectures/AlgebraicGeometry/GroupScheme/Defs.lean on slopmaster2,
lines 148–175, read together with the blueprint node's complete statement and proof.

### Hypotheses and clauses

- The field k is `{K : Type u} [Field K]` in the surrounding source section.
- The finite k-algebra is `(A : Type u) [CommRing A] [Algebra K A]
  [Module.Finite K A]`. Finite here means finite-dimensional over the field.
- The structure morphism Spec A → Spec k is precisely
  `Spec.map (CommRingCat.ofHom (algebraMap K A))`.
- Its étaleness is the first member of the `List.TFAE`, using
  `AlgebraicGeometry.Etale`, the recorded scheme-convention predicate.
- Vanishing of Ω_{A/k} is its second member, `Subsingleton Ω[A⁄K]`.
  For a module this means the zero module, without choosing a model of zero.
- The third member quantifies over `(I : Type u) (_ : Finite I)` and fields
  `(L : I → Type u) (_ : ∀ i, Field (L i))`, with algebra structures
  `(_ : ∀ i, Algebra K (L i))` and the algebra isomorphism
  `(_ : A ≃ₐ[K] Π i, L i)`. Its final clause is exactly
  `∀ i, Module.Finite K (L i) ∧ Algebra.IsSeparable K (L i)`.
  Thus TFAE states the three equivalences, including the finite product description.
- For the final assertion, the second recorded declaration takes
  `{X : Scheme.{u}} (h : X ⟶ Spec (.of K)) [IsFinite h]` and concludes
  `Etale h ↔ letI := h.ΓAlgebra; Algebra.Etale K Γ(X, ⊤)`.
  Instantiate X with G.left and h with G.hom for
  `G : Over (Spec (.of K)) [CategoryTheory.GrpObj G]`.
  Group structure is unnecessary for this implication, so the already proved theorem
  applies directly to every finite group scheme without changing the node's statement.
  The existing signature's local algebra instance is the canonical one induced by h,
  not an arbitrary algebra structure. No new statement with a let binder is introduced.
  `Algebra.Etale.iff_exists_algEquiv_prod` identifies this last condition with the
  product of finite separable field extensions required by the node.

### Dependency declarations read and used

`def-weil-pbc-scheme-conventions` is explicitly a convention-only node, with null
module/declaration: it introduces no additional notion. Its relevant component
predicates are `AlgebraicGeometry.Etale` in Mathlib.AlgebraicGeometry.Morphisms.Etale
and `AlgebraicGeometry.IsFinite` in Mathlib.AlgebraicGeometry.Morphisms.Finite;
their full class signatures and docstrings were read.

`def-sc-group-scheme` records `CategoryTheory.GrpObj` in
Mathlib.CategoryTheory.Monoidal.Grp (full signature and inverse laws read), used
on Over (Spec (.of K)). Its record also lists the finite/étale predicates and
`Algebra.Etale.iff_exists_algEquiv_prod` in Mathlib.RingTheory.Etale.Field,
whose full signature and docstring were read. GroupScheme.Defs's module docstring
explicitly identifies all these specializations. Its finite-scheme theorem uses
`Scheme.Hom.etale_iff_etale_ΓAlgebra` in
WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree, whose signature and
canonical ΓAlgebra specialization were also read.

### Edge cases

The zero algebra is allowed: CommRing has no Nontrivial requirement, and I may be
empty, so the empty product and the empty affine scheme are included. There is
no Nonempty restriction on I. Single-field products and inseparable finite
extensions are covered by the separability condition. No characteristic
restriction is imposed, so positive characteristic and imperfect fields are
included. Finite group schemes require no commutativity or reducedness assumption.
All objects can be placed in a common universe u by universe lifting; the theorem
is universe polymorphic and imposes no bounded family of test algebras.
No statement fault or disputed statement was found.

### Searches

- msearch.py leanfinder: "A finite algebra over a field is etale iff its module
  of Kahler differentials is zero iff it is a product of finite separable field
  extensions" returned eight hits, notably Algebra.Etale.iff_exists_algEquiv_prod
  in Mathlib/RingTheory/Etale/Field, with the precise product signature.
- msearch.py loogle: "Algebra.Etale, KaehlerDifferential,
  Algebra.FormallyUnramified" returned zero hits.
- msearch.py grep: "iff_exists_algEquiv_prod|iff_subsingleton_kaehlerDifferential_of_field"
  in RingTheory/Etale returned five hits, including the product theorem.
- rg in WeilConjectures for the item id and both theorem names found the two
  exact declarations in GroupScheme/Defs.lean and the differential criterion
  in WeilConjectures/Mathlib/RingTheory/Etale/Field.lean. The source's proofs
  combine the affine étale comparison with the differential and product criteria.
- rg in lean/Sheaf for the item id and both theorem names found only a reference
  in RingTheory/WeaklyEtaleField.lean, no competing statement.
- Direct Mathlib rg and source reads confirmed GrpObj and the finite product
  criterion. The existing incomplete lean record and sorry audit independently
  name the same two GroupScheme.Defs declarations, both audited closed.

Validation: deliver2.py --no-push checks both existing declarations on the server
using scompile.py and runs server preflight. No local compilation is used.

## Second reading by NS

I independently opened the node, its blueprint source (order 423), both recorded
upstream theorems in GroupScheme/Defs.lean, the two statement-dependency nodes,
and the component declarations listed below. The actual source is the blueprint
Markdown, not a Stacks tag; its opening introduces precisely a field and a finite
commutative algebra, with no standing characteristic or reducedness assumption.

Object/hypothesis/conclusion checklist, in source order:

1. Field k: the enclosing `{K : Type u} [Field K]` supplies exactly this.
   Verdict: matches; it is not a separably closed or perfect field.
2. Finite k-algebra A: `(A : Type u) [CommRing A] [Algebra K A]
   [Module.Finite K A]`. Verdict: matches finite dimension over k, including
   the zero algebra. Commutativity is implicit in the source's Spec A.
3. Structure map: `Spec.map (CommRingCat.ofHom (algebraMap K A))`.
   Verdict: exactly Spec A to Spec k with its given k-algebra structure.
4. First condition: `Etale` of that structure map. Verdict: matches the
   scheme-conventions node. I read Mathlib Morphisms/Etale.lean's class:
   it requires the induced maps on affine opens to be étale ring maps.
5. Second condition: `Subsingleton Ω[A⁄K]`. Verdict: precisely vanishing
   of the Kahler differential module, since a module has a distinguished zero.
6. Third condition: the existential `I : Type u`, `Finite I`, family `L`,
   field and K-algebra instances, `A ≃ₐ[K] Π i, L i`, followed by
   `∀ i, Module.Finite K (L i) ∧ Algebra.IsSeparable K (L i)`.
   Verdict: exactly an algebra isomorphism to a finite product of finite
   separable extensions. The structures and isomorphism belong to the same
   existential scope; finiteness/separability apply to every factor.
7. Equivalence of all three: `List.TFAE` of these three propositions.
   Verdict: gives both directions of every required equivalence.
8. Finite group scheme G: the dependency represents this by
   `G : Over (Spec (.of K))`, `GrpObj G`, and `IsFinite G.hom`.
   I read `GrpObj` (MonObj plus inverse and its two laws), and `IsFinite`
   (affine morphism with finite ring maps on affine opens). Verdict: the
   correct group-object and finite-morphism notions, with no commutativity
   requirement. The second existing theorem applies with X = G.left and
   h = G.hom. Its availability for all finite schemes adds no hypothesis
   to this specialization and does not require a replacement statement.
9. Last equivalence: `Etale h ↔ letI := h.ΓAlgebra;
   Algebra.Etale K Γ(X, ⊤)`. Verdict: matches global sections with the
   canonical K-algebra structure. I opened ΓAlgebra: its real data is the
   ring map obtained from `(Scheme.ΓSpecIso R).inv ≫ h.appTop`.
   Mathlib's `Algebra.Etale.iff_exists_algEquiv_prod`, read in full signature,
   gives exactly the source's finite-separable-product meaning. Thus this
   assertion is covered together with, rather than omitted from, the attachment.

Edge cases: `Finite I` permits I empty, so the zero algebra and empty spectrum
are included. There is no `Nontrivial A` or `Nonempty I`. A finite group scheme
itself cannot be empty because its unit section exists; the finite-scheme
comparison nevertheless also covers empty X. No positive-characteristic,
inseparable, nilpotent, or imperfect-field case is excluded by a hypothesis.
Inseparable fields and nonreduced finite algebras are correctly tested, rather
than assumed away. There is no integer parameter n. Universe u is arbitrary;
objects in different universes can be viewed in their common maximum universe
without any small-test-object quantification becoming vacuous. The finite product
witness may always be chosen in A's universe. All signature variables, including
K, its field instance, and u, are bound in the source section.

Independent searches (different wording from the worker):

- leanfinder, "finite dimensional commutative algebra etale vanishing differentials
  separable field product": eight hits, including the formally étale product
  theorem and the étale predicate; no need for a new definition.
- loogle, `Algebra.Etale, _ ≃ₐ[_] _`: three hits, including the exact
  `Algebra.Etale.iff_exists_algEquiv_prod`.
- msearch grep, `etale_SpecMap|etale_iff_etale_Γ|finite.*separable.*product`:
  zero service hits; not treated as evidence of absence.
- Direct rg on all Mathlib, upstream WeilConjectures, and this project's
  lean/Sheaf with `etale.*tfae|etale_iff_etale_ΓAlgebra|
  iff_exists_algEquiv_prod|iff_subsingleton_kaehlerDifferential_of_field`
  found the two exact upstream declarations and their algebraic comparisons.
  The Sheaf hits use the product criterion for other results; they do not
  require a duplicate definition or statement here.

No mathematical mismatch, missing dependency interface, new node, or statement
correction was found. The recorded primary signature is verbatim the existing
source signature. Existing upstream proofs and docstrings are left unchanged:
this delivery creates no theorem, hollow definition, private notation or proof,
so the new-module proof/docstring requirements do not call for rewriting them.
The blueprint's longer proof is also retained verbatim in the node. Changes by
this second reader: this clause-by-clause report only; the Lean attachment is
unchanged. Server validation is performed by deliver2.py's scompile.py checks
of both existing declarations and server preflight; there is no delivered Lean
file to compile separately.

Validation result: dry run OK. Inspection revealed that the current scompile.py
wrapper now attempts a local overlay before its server fallback, so the first
dry run was repeated with NT_OVERLAY_SOURCE pointing to an absent item-local
overlay directory. This selects the existing OSError-to-server fallback without
editing any script. That server-only dry run also printed OK (c1b45ec6d5).
The final delivery uses the same server-only routing. Both recorded names are
checked by the generated existing-declaration probe; server preflight passes.

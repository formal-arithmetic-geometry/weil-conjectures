## Worker report

The module `Sheaf.RingTheory.IndPrincipalZariski` renders the complete collection of
conventions in this node through one new definition and four existing declarations.
No theorem is proved, no data is postponed, and no `sorry` occurs in the new module.
The source read was the complete blueprint definition at
`literature/blueprint/master/blueprint/sec-proper-base-change/sk-thm-properbasechange/def-weil-pbc-ind-etale-algebra.md`.
The node is unchanged outside its `lean` field.

Clause-by-clause correspondence:

- A commutative ring A and an A-algebra B: `(A B : Type u) [CommRing A]
  [CommRing B] [Algebra A B]`. Existing `Algebra.IndEtale` has these same binders;
  `Algebra.WeaklyEtale` also allows independent universes. A common universe does
  not impose a cardinal bound: both carriers may be placed in a common universe.
- Ind-etale: the existing `Algebra.IndEtale`, in
  `WeilConjectures.RingTheory.ProEtale.IndEtale`, has a field
  `exists_colimitPresentation` quantifying over `I : Type u`, `SmallCategory I`,
  `IsFiltered I`, and `P : ColimitPresentation I (CommAlgCat.of A B)`, with
  `∀ i, Algebra.Etale A (P.diag.obj i)`. Mathlib's `Algebra.Etale` includes
  `Algebra.FinitePresentation`; thus the finite-presentation clause is present.
- Ind-Zariski in the exact sense written here: `Algebra.IsIndPrincipalZariski`
  quantifies over that same kind of filtered algebra-colimit presentation. At
  each stage, `∃ (n : ℕ) (f : Fin n → A), Nonempty
  (P.diag.obj i ≃ₐ[A] ((j : Fin n) → Localization.Away (f j)))`
  says the stage is a finite product of A_f, as an A-algebra. Every finite family
  can be indexed by Fin n; the algebra equivalence allows any realization of its
  product or localizations. These terms are automatically finitely presented and
  etale, so they form the “such a presentation” of the preceding clause.
- Affine inverse limit: the existing
  `AlgebraicGeometry.proAffineEtale_Spec_iff` in
  `WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale` says
  `proAffineEtale (Spec.map f) ↔ f.hom.IndEtale`. The definition
  `proAffineEtale` is `MorphismProperty.pro.{u}
  (@Etale ⊓ .ofObjectProperty (IsAffine ·) ⊤)`: its stages are affine etale
  schemes and its limit is cofiltered. Transition maps between affine schemes
  are affine. No extra restriction on the transitions is needed. The existing
  ring-map `RingHom.IndEtale` uses the algebra structure induced by the map;
  for the algebraMap this is the supplied A-algebra structure.
- Weakly etale via spectra: the existing
  `AlgebraicGeometry.weaklyEtale_SpecMap_algebraMap_iff` in
  `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale` says
  `WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap A B))) ↔
  Algebra.WeaklyEtale A B`.
- Equivalent flatness conditions: `Algebra.WeaklyEtale` in
  `Mathlib.RingTheory.Etale.Weakly` has `flat : Module.Flat A B` and
  `flat_lmul' : (Algebra.TensorProduct.lmul' A (S := B)).Flat`.
  The latter is flatness along multiplication B tensor_A B → B. Its class
  docstring has a codomain typo (“→ R”); the actual field has codomain B,
  agreeing with the node. There is no extra faithful-flatness assumption.

Dependency `def-weil-pbc-scheme-conventions` was read in full. Its `lean` is a
convention record with null module and declaration, explicitly instructing citers
to use its named leaves; there is no declaration to import for the collection.
Its pertinent leaves use Mathlib `AlgebraicGeometry.Etale` and
`AlgebraicGeometry.WeaklyEtale`; their full class signatures/docstrings were read.
The latter is flatness of the morphism and of `pullback.diagonal f`, exactly as
used by the recorded affine equivalence. The module's public imports expose the
existing declarations listed above as well as the new definition.

Edge cases checked: `IsFiltered I` supplies nonemptiness (empty diagrams cannot
present a filtered colimit); I lies in the same universe as the algebras. `n = 0`
is allowed, giving the empty product/zero ring, and `f j = 0` is allowed, giving
zero principal localizations. No nontriviality, characteristic, injectivity,
faithful flatness or nonempty spectrum assumption is introduced. Arbitrary
commutative base rings and zero algebras remain admitted. Products have their
standard A-algebra structures; an abstract ring equivalence would have lost the
specified structure, so an algebra equivalence is used instead.

Searches made (also logged by msearch in the sandbox):

- LeanFinder: “ind-etale and ind-Zariski algebras as filtered colimits of etale
  algebras and finite products of principal localizations; weakly etale flat
  multiplication”: eight etale-related Mathlib results; no matching colimit
  definition.
- Loogle: “Algebra.IndEtale, Algebra.IndZariski, Algebra.WeaklyEtale”: no hits;
  the service does not know the project-specific IndEtale name.
- msearch grep: `IndEtale|IndZariski|WeaklyEtale` in RingTheory: five hits in
  Mathlib/RingTheory/Etale/Weakly.lean, including the reused class.
- LeanSearch: “filtered colimit of finite products of principal localizations
  of a commutative ring”: unavailable, HTTP 521 (no mathematical verdict).
- rg in upstream WeilConjectures and project lean/Sheaf for IndEtale,
  IndZariski, WeaklyEtale and their plain-language forms found the reused
  IndEtale class, the upstream IndZariski class, and the spectrum equivalences.
  `rg` for the exact item id in upstream WeilConjectures found no hits.
- rg for `IsIndPrincipalZariski|IndPrincipalZariski|finite products of.*localizations|
  finite products of.*localisations` in Mathlib, upstream and lean/Sheaf found
  no existing declaration of the principal-product presentation predicate.

Important distinction for the second reader: upstream `Algebra.IndZariski`,
whose complete signature and docstring were read in ProEtale/IndZariski.lean,
permits `Algebra.IsLocalIso` stages. Mathlib/RingTheory/LocalIso.lean defines this
as being source-locally a standard open immersion; it does not require a stage
itself to be a finite product of principal localizations. In particular, that
record cannot simply replace the explicit product condition in the node. The
new name `IsIndPrincipalZariski` preserves the blueprint's literal definition
without asserting it is equivalent to the upstream notion. This is a clause of
the item's existing definition, so no new definition node or dependency module
is needed. The other clauses are reused, not copied. No statement correction
or STATEMENT-DISPUTED flag is needed: the definition itself is well-typed and
has meaningful data, irrespective of how broad the upstream terminology is.

Validation: scompile.py compiled the module on the server, cleanly, in 1.3 s,
with nice 19, two threads, and the 60-second file limit. No local Lean or Lake
invocation was used. The delivery dry run is the final validation step.

## Second reading by NA

I independently read the item node, its complete blueprint source, the sandbox
module, the scheme-conventions dependency and its etale and weakly-etale leaves,
and the signatures and definitions of the reused declarations. The source is a
blueprint definition, with no additional ambient hypotheses. I also read Stacks
`proetale.tex`, definition-ind-zariski, definition-ind-etale and
remark-slightly-stronger (Tag 0A0D). The last explicitly distinguishes filtered
colimits of finite products of principal localizations from Stacks ind-Zariski.
This confirms that replacing the new predicate by upstream `Algebra.IndZariski`
would not render the blueprint's specified presentation condition.

Object, hypothesis and clause checklist, in source order:

1. A commutative ring A: `(A : Type u) [CommRing A]`. PASS: no field,
   Noetherian, characteristic or nontriviality hypothesis.
2. An A-algebra B: `(B : Type u) [CommRing B] [Algebra A B]`. PASS: the
   structure is the specified algebra structure, including in the stage
   equivalences; it is not replaced by an arbitrary ring map.
3. Ind-etale means a filtered colimit of finitely presented etale A-algebras:
   reused `Algebra.IndEtale.exists_colimitPresentation` quantifies over
   `I : Type u`, `SmallCategory I`, `IsFiltered I` and
   `P : ColimitPresentation I (CommAlgCat.of A B)`, with
   `Algebra.Etale A (P.diag.obj i)` at every i. PASS: the Mathlib class
   `Algebra.Etale` includes `FinitePresentation`; no hypothesis is lost.
4. Ind-Zariski means a presentation with finite products of principal
   localizations: `IsIndPrincipalZariski` has the same filtered colimit
   quantifiers, followed by `forall i, exists (n : Nat) (f : Fin n -> A)`
   and `Nonempty (P.diag.obj i ≃ₐ[A] ((j : Fin n) -> Localization.Away (f j)))`.
   PASS: stage sizes and elements may depend on i, every finite family can be
   indexed by Fin n, and the equivalence preserves the A-algebra structure.
   Principal localizations and their finite products are etale and finitely
   presented, so omitting a redundant etale conjunct does not weaken this clause.
5. The corresponding affine inverse limit: reused
   `AlgebraicGeometry.proAffineEtale_Spec_iff` has precisely
   `proAffineEtale (Spec.map f) ↔ f.hom.IndEtale` for `f : R ⟶ S` in
   `CommRingCat`. PASS: `proAffineEtale` is the cofiltered-limit property of
   etale maps with absolutely affine domains. Maps between those domains are
   affine. `RingHom.IndEtale` uses `f.toAlgebra`; its `algebraMap_iff` identifies
   this with the already specified A-algebra structure. This clause is read,
   as in the source, for an ind-etale algebra.
6. Weak etaleness is weak etaleness of Spec B -> Spec A: reused
   `weaklyEtale_SpecMap_algebraMap_iff` states exactly that equivalence, with
   no extra hypotheses. PASS: the dependency leaf's Mathlib `WeaklyEtale`
   has fields `Flat f` and `Flat (pullback.diagonal f)`.
7. Equivalent algebraic flatness conditions: reused `Algebra.WeaklyEtale A B`
   has `Module.Flat A B` and flatness of `Algebra.TensorProduct.lmul' A`.
   PASS: the latter map is B tensor_A B -> B, so this is flatness of B for
   its multiplication action, with no faithful-flatness requirement.

Edge cases: `IsFiltered` correctly excludes the empty indexing category but
imposes no inhabitance on the finite factors; `n = 0` gives the empty product,
a zero ring. The zero algebra, zero base ring when an algebra exists, empty
spectrum, and localization at zero are admitted. There is no characteristic
restriction. Universe u is explicitly bound and shared with the indexing
category, as required by the project convention for algebra colimits. Carriers
from different universes can be placed in a common larger universe; no fixed
small universe bound is imposed. The dependent product uses the standard
pointwise A-algebra structure. No variable or universe is left unbound.

Independent searches: LeanFinder query "filtered colimit of finite products of
principal localization algebras" returned eight results about products of prime
or maximal localizations, localization of products, and iterated localization;
none defines this predicate. Loogle `Localization.Away` returned the localization
construction and its maps and properties, not an ind presentation. LeanSearch
query "An algebra is a filtered colimit of finite products of principal
localizations of its base ring" failed with Internal Server Error; no verdict
is inferred from its unavailability. I searched Mathlib, upstream
WeilConjectures, project lean/Sheaf and DAG nodes independently with
`principal.*[Zz]ariski`, `[Zz]ariski.*principal`,
`finite products of.*locali`, and `IsIndPrincipalZariski`, and checked the
upstream-name table and exact blueprint id. No existing principal-product
predicate was found. Relevant DAG hits describe the same stronger convention
and already cite this item. I opened upstream `Algebra.IndZariski` and Mathlib
`Algebra.IsLocalIso`: their stages are source-locally standard open immersions,
not the finite products specified here. The remaining existing declarations
were opened and checked rather than recreated.

No mismatches were found, and I changed neither the Lean nor the node. There
are no new definition nodes, dependency modules, statement corrections or
citers to recheck under the statement-correction rule. The collection dependency
has no single declaration; its recorded convention directs users to the leaves,
which the reused modules use. The new definition contains real mathematical
data in its proposition and no sorry; the module proves no theorem. Its module
and declaration docstrings name the blueprint source and item. There are no
proof steps in this definition node to reproduce in a theorem docstring.

Validation: the unchanged module compiled cleanly using `scompile.py` on the
server in 1.3 seconds, nice 19, two threads, 60 seconds per file, with no
warnings. The node's `lean.statement` is verbatim the definition's signature.

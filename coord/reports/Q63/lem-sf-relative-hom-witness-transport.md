## Worker report

The module `Sheaf.CategoryTheory.RelativeHomWitnessTransport` states
`CategoryTheory.relative_hom_witness_transport`. Its sole proof is `sorry`.
No definitions, additional nodes, dependency repairs, or statement corrections are needed.
Only the item's `lean` field changes.

Sources read: the full node and its seven proof steps; both statement-dependency
nodes and their Mathlib matches; the full recorded Mathlib signatures and docstrings;
Stacks `categories.tex`, Tag 0037, definition-adjoint and the following unit/counit
paragraph (lines 3344–3390); the current blueprint
`main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-tower/lem-weil-finite-duality-site-comparison.proof.md`,
second paragraph. The blueprint motivates the locally closed comparison; the
explicit categorical argument is agent-formulated in the already reviewed node.

Hypothesis-by-hypothesis rendering:

- The categories A, P and Q have explicit independent object and morphism universes
  `uA vA uP vP uQ vQ` and `[Category.{vA} A]`, `[Category.{vP} P]`,
  `[Category.{vQ} Q]`. No smallness or universe equalities are imposed.
- `C : A ⥤ P` and `hC : ∀ L L', Function.Bijective (C.map : (L ⟶ L') → _)`
  express exactly the assumed Hom-set bijections.
- `D : ObjectProperty Q` and Mathlib's `D.FullSubcategory` give the full
  subcategory, whose ambient objects are `Y.obj` and ambient arrows `v.hom`.
- `F E : P ⥤ Q` and `J G : D.FullSubcategory ⥤ P` are precisely the four functors.
- `q : F ≅ E` is the specified natural isomorphism, with `q.inv.app K`
  the map E K → F K.
- `a` and `b` are the two supplied families of `Equiv`s with exactly the
  node's source and target Hom types; a ranges over all P, b only over A.
- `ha_left`, `ha_right`, `hb_left`, `hb_right` write both variable-naturality
  equations of both families, using the full subcategory's actual arrows.
- `θ : J ≅ G` and `hθ` give exactly
  `b L Y (q.inv.app (C.obj L) ≫ h) = a (C.obj L) Y h ≫ θ.hom.app Y`.
  Here `≫` is diagrammatic composition, reversing the node's written convention.

Clause-by-clause rendering, in conclusion order:

1. For every K, L, isomorphism α : C L ≅ K, and Y, the displayed lambda
   `fun z ↦ α.inv ≫ b L Y (E.map α.hom ≫ z)` is b^α. The first conjunct is
   `Function.Bijective` of this function. The next conjunct evaluates it at
   `q.inv.app K ≫ h`, giving exactly θ_Y a_K,Y(h).
2. For each pair α, β, `∃! t : L ≅ L', C.mapIso t = α ≪≫ β.symm`
   asserts both existence and uniqueness of the isomorphism over β⁻¹α;
   the following function equality says b^α = b^β for every Y.
3. `∃ bar : ∀ K : C.EssImageSubcategory, ∀ Y : D.FullSubcategory, ... ≃ ...`
   supplies the natural family on precisely the full essential image. Its first
   clause identifies it with b^α for every witness, and its second clause
   records the normalization on h q_K⁻¹.
4. The next two clauses give naturality for every morphism `f : K' ⟶ K`
   in the full essential-image subcategory and `v : Y ⟶ Y'` in D.
5. `(bar K Y).symm (g ≫ θ.hom.app Y) = q.inv.app K.obj ≫ (a K.obj Y).symm g`
   is exactly the stated inverse formula, for every g : K → J Y.
6. The `∀ d` clause quantifies over any already specified relative Hom bijection
   on the same domains, assumes its two naturality equations and its identity
   witness values `d (C.toEssImage.obj L) Y = b L Y`, and concludes `d = bar`.
   `C.toEssImage.obj L` is literally C L with its canonical essential-image proof.
7. The penultimate clause quantifies `hF : D (F.obj K.obj)` and evaluates
   `bar K ⟨F.obj K.obj, hF⟩` on `q.inv.app K.obj`; its right side transposes
   `𝟙 (F.obj K.obj)` with a and postcomposes with θ at the same D object.
8. The last clause quantifies `hJ : C.essImage (J.obj Y)` and evaluates bar at
   `⟨J.obj Y, hJ⟩`, on `q.inv.app (J.obj Y) ≫ (a (J.obj Y) Y).symm (𝟙 (J.obj Y))`.
   Its value is exactly `θ.hom.app Y`, as the counit identity requires.
   There is no assertion of an adjunction outside these domains.

Dependency declarations used:

- `def-nagata-category` is a Mathlib leaf matched to `CategoryTheory.Category`,
  in `Mathlib.CategoryTheory.Category.Basic` (available through the imports).
  Read its `CategoryStruct` data and all three category laws.
- `lem-weil-pbc-adjunction-of-natural-bijection` is a Mathlib leaf matched to
  `CategoryTheory.Adjunction.mkOfHomEquiv`, in
  `Mathlib.CategoryTheory.Adjunction.Basic`. Read `CoreHomEquiv`, its two
  naturality fields, the construction and `mkOfHomEquiv_homEquiv`.
  The import retains the node's identity-transpose convention and its proof route;
  the relative theorem uses explicit naturality equations because F does not
  necessarily land in D, so no global `CoreHomEquiv F J` can be assumed.
- The existing Mathlib notions `ObjectProperty.FullSubcategory`,
  `Functor.essImage`, `Functor.EssImageSubcategory`, and `Functor.toEssImage`
  are used directly; their source declarations were read. No copies are defined.

Edge cases checked before writing: empty A makes the essential-image conclusions
vacuous, without asserting global bijections from b; empty D makes all Hom-family
clauses vacuous. α an identity recovers b using the category/functor identity laws.
Different preimages L, L' are allowed even if C L = C L'; fully faithful Hom maps
supply the unique isomorphism rather than assuming equality of objects.
A non-surjective fully faithful C is allowed; bar's K is only in its essential image.
A full D need not be closed under isomorphisms: the unit uses actual membership
`D (F.obj K.obj)` and no repleteness assumption. A J Y outside the essential image
has no counit clause. As a scalar check in a one-object group category, step 2's
formula is θ a(z q), independent of α; inverse evaluation gives a⁻¹(g) q⁻¹
in the node's composition order. Arbitrary independent category universes remain
bound explicitly and compile without any equality constraints.

Searches made with the prescribed `msearch.py Q63 lem-sf-relative-hom-witness-transport`:

- `leanfinder "Natural relative Hom bijections extend along fully faithful isomorphism witnesses independently and identify units and counits"`:
  eight hits, including `Adjunction.restrictFullyFaithful_homEquiv_apply`,
  `Functor.FullyFaithful.homEquiv`, and `Functor.FullyFaithful.isoEquiv`.
- `loogle "CategoryTheory.Functor.FullyFaithful, CategoryTheory.Adjunction.homEquiv"`:
  one hit, `Adjunction.restrictFullyFaithful_homEquiv_apply`.
- `leansearch "relative hom bijection transport along isomorphism fully faithful functor"`:
  eight hits, including `Functor.FullyFaithful.ofIso`, `.map_bijective`, `.homEquiv`,
  `.isoEquiv`, and `Iso.homCongr`. None gives the complete relative-domain theorem.
- `grep "homEquiv.*(essImage|EssentialImage)|restrictFullyFaithful_homEquiv" CategoryTheory`:
  two hits, in `Adjunction/Restrict.lean` and its site-theory application.
  Read `restrictFullyFaithful` and its Hom formula: these assume an existing
  global adjunction and do not state this theorem.
- Project `rg` searches for `relativeHom|relative_hom|witness.transport|WitnessTransport`
  and `relative.*[Hh]om|[Hh]om.*witness|[Hh]om.*[Bb]ijection|[Bb]ijection.*essential`
  in `lean/WeilConjectures` and `lean/Sheaf` found related applications and
  `CoherentRightAdjointComparisons` / `ClosedAdjunctionComparison`.
  Their signatures were read: these concern global adjunctions and tensor-Hom,
  respectively, not fully faithful witnesses with relative domains.
- `grep -rn "lem-sf-relative-hom-witness-transport" lean/WeilConjectures`:
  no matches. A name search for `relativeHomWitnessTransport|relative_hom_witness_transport`
  in both project trees and Mathlib CategoryTheory found no collision.

No statement dispute or mathematical fault found. The one named theorem carries
all seven proof steps in its docstring. The server's prescribed scompile run
compiled both sandbox and library-path variants cleanly (19.4 s and 8.4 s).

## Second reading by Q63

This is a second pass by the sole dispatcher-started worker, following the
explicit instruction not to start other agents; independent maintainer review
still applies to the delivery. Reopened the node and the finished module and
checked the hypothesis and clause mapping above.

In particular, a is natural on all P, while b is natural only along C-images
of A morphisms. The formula uses `α.inv` on the left in Lean's diagrammatic
composition, and `E.map α.hom` before z; the comparison is q.inv, not q.hom.
The unique t maps to `α ≪≫ β.symm`, whose hom is α followed by β⁻¹,
with the correct endpoints C L → C L'. Both α and β are arbitrary witnesses.
The bar binder uses Mathlib's full essential image, so naturality includes all
ambient arrows between such objects, not just images of A arrows. The inverse
formula has g followed by θ, and q.inv followed by a.symm, with the expected types.
The comparison family's identity restriction is equality of Equiv objects,
equivalent to equality of the Hom functions since inverse data are unique.
The final two clauses retain each of their explicit membership hypotheses;
no arbitrary identity or global adjunction was substituted. Every category and
universe is explicitly bound under `set_option autoImplicit false`.
No mismatch found and no source-statement edits made during the second pass.

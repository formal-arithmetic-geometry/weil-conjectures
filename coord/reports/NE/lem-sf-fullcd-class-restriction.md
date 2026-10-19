## Worker report

The delivery contains one module, `Sheaf.Paper.FullCDClassRestriction`, and changes only
`lean` in the item's node. No statement correction or new/dependency node is needed.
The module defines `AlgebraicGeometry.ProEtale.etaleOriginRestrictionWitnessIso` using
actual existing maps and states
`AlgebraicGeometry.ProEtale.etaleOrigin_restriction_to_proetale_base_change`, with proof
`sorry`. The helper belongs to this item's witness construction, not a new class predicate.

Hypotheses and clauses are matched as follows.

- The global datum is `(D : WeilConjectures.FiniteFieldDatum.{u})`, including the chosen
  finite field and its algebraic closure `D.k`. `(l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)`
  records the coefficient prime. `(E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]` records its finite extension. `(n : ℕ) (_hn : 1 ≤ n)`
  gives the positive level. Every coefficient category uses exactly
  `ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)`.
- `(Xbar : Scheme.{u}) [Xbar.Over (Spec (CommRingCat.of D.k))]` gives the `k`-scheme.
  `LocallyOfFiniteType (Xbar ↘ Spec ...)` and `QuasiCompact (Xbar ↘ Spec ...)` together
  give finite type, using the two classes recorded by `def-weil-finite-type-morphism`.
- `(Y : Scheme.{u}) (f : Xbar ⟶ Y) (V : Y.ProEt)` supplies the arbitrary target, the
  missing structural map fixed in the current DAG statement, and the weakly étale
  pro-étale object `V.hom : V.left ⟶ Y`.
- The chosen scheme `W` is `pullback f V.hom`; its maps `q` and `r` are
  `pullback.fst f V.hom` and `pullback.snd f V.hom`. Thus schemehood is in the type of
  `W`. The first conjunct `IsPullback ... f V.hom` states the cartesian universal
  property, and the second `WeaklyEtale (pullback.fst f V.hom)` makes it an object of
  `Xbar.ProEt`. Site objects remain in universe `u+1`, with morphisms in universe `u`.
- `F : Sheaf (Scheme.ProEt.topology Xbar) (ModuleCat ...)` is the pro-étale coefficient
  sheaf. `_hF : (comparisonUpperStar ... Xbar).essImage F` uses exactly the dependency's
  Mathlib match `Functor.essImage`: existence of an étale `G` and
  `Nonempty (ν_Xbar^* G ≅ F)`. Membership contains no chosen pair and assumes no
  constructibility or finite presentation.
- For **any** `G` and `α : ν_X^* G ≅ F`, `etaleOriginRestrictionWitnessIso q G α`
  constructs `q_proet^-1 F ≅ ν_W^* (q_et^-1 G)`. Its data are
  `Q.mapIso α.symm ≪≫ ((comparisonCoefficientPullbackIso ... q).app G).symm`.
  The fourth main-theorem conjunct explicitly quantifies over every such `G` and `α`
  and asserts existence of the displayed isomorphism, with that precise étale witness.
  The construction also works for the particular fibre-product projection in the node.
- The third conjunct is `(comparisonUpperStar ... W).essImage (Q.obj F)`, the claimed
  étale-origin condition on the **arbitrary** scheme `W`. The preceding constructed
  inverse isomorphism supplies the witness `(q_et^-1 G, b.symm)`.
- The final conjunct quantifies over **every** étale `G`, `G'` and `a : G ⟶ G'` and
  gives `Q(ν_X^* a) ≫ b_G' = b_G ≫ ν_W^*(q_et^-1 a)`, with both `b` components
  explicitly `etaleOriginRestrictionWitnessIso q _ (Iso.refl _)`. This is naturality
  of the actual isomorphisms for `F = ν_X^* G`, `α = id`, not an unrelated family.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`, with its field,
  algebraic-closure and instance fields.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` imports the constructions
  `Padic.coefficientExtensionRing` and the chosen ring of integers/uniformizer from
  `Sheaf.NumberTheory.Padics.CoefficientExtension`. Positive-level finiteness is the
  recorded theorem `Padic.finite_coefficientExtensionRing`; no finiteness instance is
  added as an extra hypothesis here.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, together with
  `QuasiCompact`. `Mathlib.AlgebraicGeometry.Scheme`: `Scheme` and its morphisms.
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, its
  projections and universal property; scheme pullbacks are supplied by the imports.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: `comparisonUpperStar` through its
  existing comparison adjunction `proEtaleSiteComparisonModules`. The fixed-coefficient
  categories are `Sheaf` with values in `ModuleCat`, the encoding expressly permitted
  by `def-weil-pbc-etale-sheaves`. Its recorded upstream module
  `WeilConjectures.AlgebraicGeometry.EtaleSheaves` is imported.
- `Mathlib.CategoryTheory.EssentialImage`: `CategoryTheory.Functor.essImage`, the exact
  recorded mathlib_match for `def-sf-fullcd-used-class`. This generic match is usable
  without changing that dependency record or defining another class predicate.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.upperStar`.
  The pro-étale inverse image uses upstream `ProEtale.upperStar`: its body is the
  identical `Functor.sheafPullbackConstruction.sheafPullback` along
  `MorphismProperty.Over.pullback @WeaklyEtale ⊤ q` as the recorded
  `Scheme.proEtaleSheafInverseImage`. Directly importing `ProEtaleInverseImage` together
  with the currently compiled comparison closure caused a duplicate declaration from
  legacy versus `FiniteCoefficient.UpperLowerStar.Defs`. Following the launcher rule,
  this module imports the existing comparison closure and uses the upstream operation
  with identical construction; it creates no replacement functor or arbitrary map.
- Proof dependency `lem-weil-pbc-comparison-pullback` has the current recorded module
  `Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence`, read both locally and through
  `scompile.py --source`. Its `comparisonCoefficientPullbackIso` is used directly.
  It is the mate of the canonical right-image comparison and has the orientation
  `ν_W^* q_et^-1 ≅ q_proet^-1 ν_X^*`; the helper takes its inverse.
- The other geometric proof dependency is the Mathlib weakly-étale base-change instance
  (`MorphismProperty.pullback_fst` specialized to `WeaklyEtale`), already imported with
  the small pro-étale site. There is no unstated prerequisite in this delivery.

Edge cases: `n = 1` is allowed; the empty scheme and empty pro-étale objects are allowed;
`f` can be the identity or arbitrary; `G` can be zero; every witness is allowed; and the
naturality condition includes identity and arbitrary arrows between different witnesses.
No finite-type, quasi-compactness, separatedness, surjectivity or nonemptiness hypothesis
is imposed on `Y`, `V`, `f`, or `W`. The node's existential class condition makes sense
on `W` regardless of finite type. The coefficient ring is placed in `Type (u+1)` as
required by the recorded fixed-module interface, leaving the site's object/morphism
universes distinct. In particular this does not identify site universes to use a
specialized API.

Searches actually made (2026-10-16; wrapper log `searches.jsonl`):

- `msearch.py leanfinder`, query "The inverse image of an etale-origin module sheaf
  along a scheme morphism is again of etale origin and is naturally isomorphic to
  the comparison pullback of its etale inverse image": eight hits, chiefly étale
  morphism/category results and `Scheme.Modules.restrictFunctorIsoPullback`; no match
  for this node's full statement.
- `msearch.py loogle`, query `"essImage"`: twelve hits including `Functor.essImage`,
  `essImage.ofIso` and `essImage.getIso`. The generic predicate is used, but these
  results do not give the geometric square and comparison statement.
- `msearch.py leansearch`, query "Pullback of a sheaf of modules from the etale site
  to the proetale site commutes with scheme inverse image": service unavailable,
  returning Internal Server Error. No mathematical verdict is inferred from failure.
- `msearch.py grep`, query `comparisonUpperStar|proetale.*pullback|essImage.*ofIso`:
  five Mathlib hits, all generic essential-image uses. Direct `rg` in Mathlib,
  upstream `WeilConjectures` and shared `lean/Sheaf` for the proposed declaration
  names found none. Searches for comparison and étale-origin vocabulary found
  `comparisonUpperStarCompUpperStarIso`, the exact recorded
  `comparisonCoefficientPullbackIso`, and the upstream `etaleOrigin_upperStar_obj`.
  The latter gives closure alone and neither the cartesian/weakly-étale clauses nor
  the specified every-witness comparison and naturality; it is not an exact existing
  statement of this node. The node-ID search in the older upstream checkout found
  no occurrence. The newer shared framework contains its partial closure theorem.

The blueprint markdown source path named in the node is absent from this local checkout;
the current fully split DAG statement and proof were read in full. No change of statement
or source-based correction is proposed. No `STATEMENT-DISPUTED` issue remains after
matching the arbitrary-scheme essential-image condition and every-witness quantifiers.

Independent second reading is left to the dispatcher's second worker.

## Second reading by NE

I independently read the current node, its three proof steps, all eleven statement
dependencies and their recorded declarations or Mathlib matches, and the delivered Lean
module. The following is my object/hypothesis/conclusion checklist, made against the
node rather than inferred from the worker report. All items pass.

1. Global finite-field datum and `k = Fbar`: `(D : FiniteFieldDatum.{u})`, with `D.k`.
   I opened `Sheaf.Paper.FiniteFieldFiber` through `scompile.py --source`: its fields
   include the prime, positive exponent, cardinality, finite base field, and the chosen
   algebraic closure with its field/algebra instances. This is the node's datum.
2. Prime, extension, level and coefficient ring: `(l : ℕ) [Fact l.Prime]`,
   `_hl : l ≠ D.p`, `(E : Type (u + 1)) [Field E] [Algebra (Padic l) E]`,
   `[FiniteDimensional (Padic l) E]`, `(n : ℕ) (_hn : 1 ≤ n)`, and
   `Padic.coefficientExtensionRing l E n`. I read the coefficient construction: it
   is the quotient of the recorded integer ring by the nth power of the ideal of its
   chosen uniformizer. The finite-dimensional hypothesis means finite field extension,
   exactly as the dependency says. The finiteness theorem is a dependency, not an extra
   hypothesis. No topology or continuity assumption is added on individual sheaves.
3. Finite-type k-scheme: `(Xbar : Scheme.{u}) [Xbar.Over (Spec (.of D.k))]`, and
   `LocallyOfFiniteType` and `QuasiCompact` of this structure morphism. I read the two
   Mathlib class signatures and the dependency's note that finite type is their
   conjunction. No separatedness, properness or smoothness is assumed.
4. Arbitrary target, morphism and pro-etale object: `(Y : Scheme.{u})`,
   `(f : Xbar ⟶ Y)` and `(V : Y.ProEt)`. I read `Scheme.ProEt` in Mathlib: it is
   `MorphismProperty.Over @WeaklyEtale ⊤ Y`, and `V.hom` has its `WeaklyEtale`
   instance from `V.prop`. There is no assumption that Y is over k or finite type,
   and no finiteness or nonemptiness assumption on V or f.
5. W, q, r and geometry: `pullback f V.hom`, `pullback.fst f V.hom`, and
   `pullback.snd f V.hom` are the dependency's chosen fibre product and projections.
   Schemehood is in their types. The first conjunct is `IsPullback ... f V.hom`,
   retaining the universal property, and the second is `WeaklyEtale` of q. Together
   with `Scheme.ProEt.mk` this says that q is an object of `Xbar.ProEt`; no further
   existential datum is missing. The ordering of the square's four arrows is correct.
6. F and existential class membership: F is a sheaf on `Scheme.ProEt.topology Xbar`
   with values in `ModuleCat.{u+1} A`, and `_hF` is
   `(comparisonUpperStar (ModuleCat A) Xbar).essImage F`. I read Mathlib
   `EssentialImage.lean:45`: this is precisely `∃ G, Nonempty (ν*.obj G ≅ F)`.
   It is the recorded `mathlib_match` of `def-sf-fullcd-used-class`, even though that
   dependency has no `lean` record. There is no chosen pair, finite presentation,
   constructibility or finite-stalk hypothesis. The fixed-module category is the
   second encoding expressly allowed by `def-weil-pbc-etale-sheaves`.
7. Comparison and inverse images: I read both `upperStar` bodies, the current server
   source of `ProEtaleInverseImage`, and `ProEtaleSiteComparison`. Etale and pro-etale
   upper star are the stated left Kan extensions followed by sheafification along
   scheme base change. In particular `ProEtale.upperStar` is definitionally the same
   construction as recorded `Scheme.proEtaleSheafInverseImage`, using the same
   `MorphismProperty.Over.pullback @WeaklyEtale ⊤ q`. `comparisonUpperStar` is the
   existing comparison functor on modules. Thus the different API name in the item
   is not a different notion or a private replacement. The current inverse-image
   dependency source now imports the finite-coefficient API; the worker report's
   historical collision is not evidence of a remaining unusable mathematical interface.
8. Every witness and the specified isomorphism: the fourth conjunct quantifies over
   every etale `G` and every `α : ν*.obj G ≅ F`, and asserts `Nonempty` of exactly
   `Q.obj F ≅ ν_W*.obj (q_et*.obj G)`. The preceding definition actually constructs
   that isomorphism for this very G and α. Its data are `Q.mapIso α.symm` followed
   by the inverse component of `comparisonCoefficientPullbackIso`. I read that
   declaration, including its ambient instances: it is the canonical conjugate of
   the right-image comparison, for arbitrary q; it is not a chosen `Nonempty` map.
   This is exactly the node's orientation and witness `q_et^-1 G`.
9. Class on W: the third conjunct is `(comparisonUpperStar _ W).essImage (Q.obj F)`.
   This specializes the same existential predicate on the arbitrary scheme W. The
   constructed inverse isomorphism supplies the class witness. No finite-type
   condition on W is inserted, so the node's explicit arbitrary-scheme clause survives.
10. Naturality: the last conjunct quantifies over all G, G' and all `a : G ⟶ G'`.
    Its equality is `Q(ν_X*(a)) ≫ b_G' = b_G ≫ ν_W*(q_et*(a))`, with both b's
    explicitly the constructed witness isomorphisms at `Iso.refl _`. Each side has
    source `Q(ν_X* G)` and target `ν_W*(q_et* G')`. This is precisely the node's
    naturality for F equal to `ν_X* G`, α the identity; it does not assert unrelated
    naturality for arbitrary witness choices.

I read the source TeX directly from the Stacks Project repository because
`literature/stacks-project/` is absent here:
[more-morphisms.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/more-morphisms.tex),
`lemma-base-change-weakly-etale` (Tag 094U), and
[proetale.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/proetale.tex),
`section-morphism` (Tag 09A5) and `section-comparison` (Tag 099R).
Tag 094U assumes just scheme morphisms and weak etaleness before base change.
The commuting inverse-image square in Tag 09A5 precedes the separate pushforward
lemma: the quasi-compact/quasi-separated assumptions belong to that latter lemma,
not to the square used here. Tag 099R constructs the comparison for an arbitrary
scheme, with compatible site choices. Consequently none of these sources supplies
a missing finiteness hypothesis on W or q. The original blueprint markdown path is
absent locally; its complete current DAG statement and source-labelled proof steps
were read without changing them. No statement correction or citer audit is needed.

Edge cases checked independently: n = 0 is excluded by the node itself and by
`1 ≤ n`; n = 1 is included. Any prime distinct from D.p is allowed, including 2.
The empty source, empty target where a morphism exists, and empty pro-etale object
are not excluded. A zero sheaf and zero etale witness are allowed. Identity f and
arbitrary f, and identity/zero/arbitrary maps a, all remain quantified. There is no
index-set binder, hence no nonempty-index restriction. Universes are explicitly bound:
the site has scheme objects at u (site-object universe u+1, Hom universe u), and
modules/coefficients use the dependency's larger u+1 convention. No equality of site
object and Hom universes or artificial smallness instance has been assumed. All
variables and universe names are bound (`autoImplicit false`).

Independent searches on 2026-10-16, recorded by the prescribed msearch wrapper:

- LeanFinder, `inverse image preserves the essential image of etale to proetale
  comparison and gives a natural isomorphism`: eight generic essential-image and
  etale-category hits, no complete match for this statement.
- Loogle, `"essImage"`: twelve hits, including the exact membership predicate,
  its witness and isomorphism operations. These are already reused.
- Grep wrapper, `etaleOrigin_upperStar_obj|comparisonUpperStarCompUpperStarIso`:
  no indexed hit. Direct `rg` on Mathlib, the slopmaster2 source, the shared
  `lean/WeilConjectures` framework and `lean/Sheaf` did find the upstream comparison
  and `etaleOrigin_upperStar_obj`; I opened their declarations. The latter asserts
  closure of the essential image for arbitrary q, but omits the geometry,
  every-witness isomorphism and naturality clauses of this node. It is a partial
  match, so marking this whole node `existing: true` would lose clauses. The helper
  introduces no second class predicate or comparison construction: it composes the
  existing operations with a supplied α. Neither delivered full declaration name
  occurs in those existing sources.
- LeanSearch, `Pullback of a sheaf in an essential image along a commuting square
  of functors preserves membership`: unavailable (Internal Server Error). I make
  no absence claim from this failed service.

No new node or dependency module is in this delivery, so H12/H13 introduce no
additional unchecked statements. The helper definition contains real isomorphism
data and no sorry. The sole postponed theorem is this DAG node, with exactly `by
sorry`. Module and declaration docstrings cite the source and blueprint id; the
theorem docstring follows all three proof steps, including the witness inverse and
the naturality equation. I found no mismatch needing a Lean or node edit and have
preserved them verbatim. The only change of this reading is this audit section.

Validation: `scompile.py NE lem-sf-fullcd-class-restriction
lean/Sheaf/Paper/FullCDClassRestriction.lean`, run from the sandbox, passed both
sandbox and library checks (4.3 s and 4.7 s) with no diagnostics. A separate textual
check confirmed the node's `lean.statement` is verbatim the theorem signature,
all lines are at most 100 characters, and the file contains exactly one sorry.

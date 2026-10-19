## Worker report

The module `Sheaf.Paper.AmbientIndDerivedSums` states the three numbered assertions
of `det-ambient-ind-derived-sums`. It has two theorem declarations, each with `sorry`:
`AlgebraicGeometry.ProEtale.indConstructibleDerived_sums_and_truncations` and
`AlgebraicGeometry.ProEtale.indConstructibleDerived_sums_and_truncations_padicAlgCl`.
No definition, axiom, helper theorem, or proof is added. The source is the actual
main-20261015 blueprint statement and proof in
`sec-six-functors-basics/sk-cor-ambient-ind-derived/sk-cor-ambient-ind-derived-sums`.
The source standing hypotheses are restored by the recorded statement correction below.

Hypotheses and objects, clause by clause:

- The standing field is `(k : Type u) [Field k] (p : ℕ) [CharP k p]` with
  `(hp : 0 < p)` and `(hpl : p ≠ ℓ)`. The scheme is `(X : Scheme.{u})` with
  `[X.Over (Spec (.of k))]`, `[IsSeparated (X ↘ Spec (.of k))]`,
  `[LocallyOfFiniteType (X ↘ Spec (.of k))]` and
  `[QuasiCompact (X ↘ Spec (.of k))]`. Locally finite type plus quasi-compactness
  is finite type. These are precisely the source standing hypotheses restored
  in the natural statement, not extra Lean-only assumptions. No cohomological
  bound is imposed on a complex or a family.
- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`. The first theorem takes
  `E : PadicAlgCl.FiniteIntermediateField ℓ`, the existing finite intermediate
  subfield of the fixed algebraic closure of Q_ℓ, with its inherited topology.
  A fixed algebraic closure represents the arbitrary algebraic closure in the
  statement up to coefficient isomorphism. The second theorem does not need a
  redundant E parameter.
- The two choices of Λ are `Profinite.continuousMapRingObj E` and
  `Profinite.padicAlgClRingObj ℓ`. The latter means precisely sections valued in
  some finite subextension, not all continuous maps to the valued algebraic closure.
- Their actual pulled-back ring objects are `padicSubfieldRingObj X ℓ E` and
  `padicAlgClRingObj X ℓ`. These transparent upstream abbreviations use
  `condensedRingObj Λ X`, with the canonical transported ring structure.
- A is `Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})` over that ring object.
  The category D(A) is `DerivedCategory` of that exact internal-module category;
  its canonical published derived-category instances are inferred, rather than
  replaced by any new choice. There is no derived-completeness condition.
- Cons is the recorded `IsConstantModelConstructible Λ X`. IndCons is exactly
  Mathlib `ObjectProperty.ind.{u + 1}` of that predicate. Its definition quantifies
  over small filtered colimit presentations in the ambient module category.
  Dic is written inline as `∀ m : ℤ, ObjectProperty.ind ...
  ((DerivedCategory.homologyFunctor _ m).obj K)`. It is not defined a second time.
- Small families are `S : Type (u + 1)`, matching the fixed site/coefficient
  convention and the filtered index universe in `ObjectProperty.ind`.
- Clause 1, the canonical comparison: `c : Cofan K` with `IsColimit c` is any
  ambient derived coproduct of the given family. In each degree n, `d : Cocone
  (Discrete.functor K ⋙ DerivedCategory.homologyFunctor _ n)` with `hd : IsColimit d`
  is its cohomology coproduct. The conclusion is
  `IsIso (hd.desc ((DerivedCategory.homologyFunctor _ n).mapCocone c))`.
  By the defining desc equations its composite with the s-th injection is H^n
  applied to the s-th derived injection. Thus it is exactly the canonical arrow
  in the node. This describes all chosen coproducts, without imposing an extra
  existence assumption; ambient existence is supplied by the recorded dependency.
- Clause 1, consequence: the second conjunct universally quantifies over the same
  family and colimit cofan, assumes the inline Dic predicate for each K s, and
  concludes it for c.pt. This is closure under arbitrary small sums.
- Clause 2: the third conjunct quantifies over any K and `n : ℤ`, assumes the
  inline Dic predicate, and concludes it for both
  `(DerivedCategory.TStructure.t.truncLE n).obj K` and
  `(DerivedCategory.TStructure.t.truncGE n).obj K`. These are the standard
  cohomological truncations, agreeing up to canonical isomorphism with the node's
  kernel/cokernel representatives; they are not brutal truncations.
- Clause 3, first inclusion: `constantModelBoundedConstructible Λ X ≤ fun K ↦ ...`
  uses the already recorded constant-model bounded predicate. It is standard
  t-boundedness intersected with constructibility in every degree.
- Clause 3, second inclusion: `localizingClosure
  (constantModelBoundedConstructible Λ X) ≤ fun K ↦ ...` uses the existing
  intersection construction on Dbc itself, not the finite-Tor subcategory Dctf.
  The existing closure uses all ambient existing coproducts in the object universe;
  the recorded `det-def-localizing-closure-existence` explains its equivalence to
  closure under the fixed u+1-small sums here, since Hom types are u+1-small.

Dependency declarations read and reused:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`, and its
  reexported continuous-function ring constructions.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic` (the shared side
  framework): `Profinite.padicAlgClCondensedRing`, `Profinite.padicAlgClRingObj`,
  including their finite-subextension-valued definition and commutative structure.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic` (shared side framework):
  `AlgebraicGeometry.ProEtale.coefficientRing`, `condensedRingObj` and its
  transported commutative ring-object structure. The public import through
  `ModuleObject.Colimit.Compatibility` additionally supplies the two canonical
  padic coefficient abbreviations used in the signatures.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField` and its
  standing scheme binders, the recorded setting interface; imported publicly.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `ModObj`, and the
  canonical category of internal modules, not a private sectionwise replacement.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and Q; `DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor` and its factorization through Q.
- `Sheaf.Paper.CondensedConstantConstructibility`: `IsConstantModelConstructible`
  and `constantModelBoundedConstructible`, including the affine-local convention
  on arbitrary schemes. The generic `boundedConstructible` and weak-Serre theorem
  from `Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible` are imported as the
  recorded bounded-constructible dependency; the concrete constant-model Dbc
  used here is explicitly provided by the recorded constructibility node itself.
- `Sheaf.Paper.LocalizingClosureExistence`: `localizingClosure_exists`; its public
  dependency `Sheaf.Paper.LocalizingClosure` defines `CategoryTheory.localizingClosure`.
- `Mathlib.CategoryTheory.ObjectProperty.Ind`: `ObjectProperty.ind`.
- `Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT` and `TruncLTGE`:
  the truncLE and truncGE functors used with the standard derived t-structure.

Proof-only imports include all stated proof dependencies:
`Sheaf.Paper.AmbientIndDerivedTriangulated` (`indConstructibleDerived_isTriangulated`),
`Sheaf.Paper.IndConstructibleFilteredColimits` (both coefficient cases of
`indConstructible_filteredColimits_and_sums`),
`Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`
(`SheafOfModules.isGrothendieckAbelianOfUniverses`),
`Sheaf.CategoryTheory.SheafTensor` (`sfbSheafTensor_properties`), and
`Mathlib.Algebra.Homology.Embedding.CochainComplex`
(`CochainComplex.quasiIsoAt_ιTruncLE`). Remaining proof dependencies are already
public statement imports. Both theorem docstrings carry all six proof steps.

The proof-interface scope discrepancy is repaired by the source-based statement
correction below. The recorded ind-heart and ambient triangulatedness theorems
now apply with precisely their standing field and scheme hypotheses. The earlier
ind-heart statement correction explicitly listed this item as a breaking citer;
this delivery repairs that mismatch.

Edge cases checked before writing: S may be empty, including in the canonical-map
clause and the sum-closure clause. The zero module has a finite constant model and
its one-object filtered presentation makes it ind-constructible. All integer n and
all integer cohomology degrees m are allowed. Zero and arbitrarily unbounded
complexes and families with no common bounds are allowed. Both truncation boundary
degrees retain H^n, as required. The empty scheme is permitted in the standing setting. General non-qcqs schemes
are outside that setting; the constructibility predicate itself is still the
recorded one, with its affine-local definition on general schemes.
No independent diagram universe, new ring-object instance, or cohomological bound
was introduced. No known counterexample; no STATEMENT-DISPUTED flag is asserted.

Searches for an existing exact statement (all msearch.py, group Q28/item id):

- leanfinder: `Derived category ind-constructible cohomology closed under coproducts
  truncations and contains localizing closure of bounded constructible complexes`:
  eight hits, including `DerivedCategory.IsGE`, `.IsLE`, `.TStructure.t`, and
  representative-isomorphism results; no ind-constructible or three-clause match.
- loogle: `"homologyFunctor", "PreservesColimits"`: zero hits.
- grep: `ind.?constructible|indConstructible|homologyFunctor.*[Cc]oproduct` in
  Mathlib CategoryTheory: zero hits.
- leansearch: `Cohomology of arbitrary coproducts in unbounded derived category of
  sheaves of modules and stability under canonical truncations`: eight generic
  coproduct/morphism-property hits (including AB4), no exact item match.
- rg of the source WeilConjectures tree for the item id and ind-constructible
  names: no declaration match. The newer shared side framework was also read.
- rg of lean/Sheaf found the already recorded triangulatedness and ind-heart
  declarations and downstream proof docstrings referring to this node, but no
  theorem stating these three conclusions. Localizing closure and constant-model
  constructibility were reused from those searches. The proposed full names
  also have no collision in the upstream-name inventory or either source tree.

Validation: file-only compilation through scompile.py; final clean compile and
prescribed deliver2.py dry run are recorded by the delivery wrapper. No global
build, direct Git command, or write to a shared/source checkout was performed.

## Statement corrected

The old statement, verbatim:

Let $X$ be a scheme, $\ell$ a prime, $\Qlb$ an algebraic closure of $\mathbf Q_\ell$, and $E\subseteq\Qlb$ a finite extension of $\mathbf Q_\ell$. Let $\Lambda=E$ or $\Qlb$, with the condensed coefficient conventions of [sk-def-sfb-condensed-ring; sk-def-sfb-qlbar-condensed], and put $\Lambda_X=p_X^*\Lambda$ [sk-def-sfb-pulled-back-coefficients]. All sheaves below are $\Lambda_X$-module objects [sk-def-sfb-module-objects]. Write $\mathcal A=\Mod_{\Lambda_X}$ and $D(X_{\mathrm{proét}},\Lambda)=D(\mathcal A)$ for the ordinary unbounded derived category [def-weil-abstract-derived-category]. All families and filtered diagrams are small in the fixed universe of the site and coefficient sheaves.

Write $\Cons(X,\Lambda)$ for the constructible sheaves [sk-def-sfb-constructible] and $\IndCons(X,\Lambda)$ for the full subcategory of $\mathcal A$ consisting of filtered colimits of constructible sheaves, computed in $\mathcal A$. Set
$$\Dic(X,\Lambda)=\{K\in D(\mathcal A):H^n(K)\in\IndCons(X,\Lambda)\text{ for every }n\in\mathbf Z\}.$$
Write $\Dbc(X,\Lambda)$ for the bounded complexes with constructible cohomology [sk-def-sfb-bounded-constructible] and $\Loc(\mathcal S)$ for the smallest full triangulated subcategory containing $\mathcal S$ and closed under isomorphisms and arbitrary small direct sums [det-def-localizing-closure-existence]. For a representative complex $C$, the canonical truncation $\tau_{\le n}C$ has terms $C^i$ for $i<n$, $\ker d^n$ in degree $n$, and zero above $n$; $\tau_{\ge n}C$ has zero terms below $n$, $\operatorname{coker}d^{n-1}$ in degree $n$, and $C^i$ above $n$, with the induced differentials.

1. For any family $(K_s)$ in $D(X_{\mathrm{proét}},\Lambda)$ and every $n\in\mathbf Z$, the canonical map
$$\bigoplus_s H^n(K_s)\longrightarrow H^n\!\left(\bigoplus_sK_s\right)$$
is an isomorphism. Consequently $\Dic(X,\Lambda)$ is closed under direct sums.
2. For $K\in\Dic(X,\Lambda)$ and $n\in\mathbf Z$, both $\tau_{\le n}K$ and $\tau_{\ge n}K$ lie in $\Dic(X,\Lambda)$.
3. $\Dbc(X,\Lambda)\subseteq\Dic(X,\Lambda)$ and $\Loc(\Dbc(X,\Lambda))\subseteq\Dic(X,\Lambda)$.

The stage-1 expansion explicitly says X is an arbitrary scheme, but the source proof invokes the ind-heart proposition and coefficient-heart lemma for a standing scheme. The latter states the standing-scheme restriction, and sk-def-sfb-dc-setting specifies separated finite-type schemes over a field of positive characteristic different from ell. The now-recorded ind-heart and ambient-triangulated interfaces have exactly that scope, with the ind-heart correction explicitly flagging this item as a breaking citer. Restore those source hypotheses rather than silently add them only in Lean. The parent unit already has that implicit standing setting; its conclusions and proof route are unchanged. No counterexample to the scoped assertion is claimed.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-cor-ambient-ind-derived/sk-cor-ambient-ind-derived-sums.md; All three assertions and proof via sk-prop-ind-heart; sk-lem-coefficient-heart/_section.md standing-scheme hypothesis; sk-def-sfb-dc-setting/_section.md first paragraph.

Only `statement` and the forced `stmt_deps` addition of `sk-def-sfb-dc-setting`
change, besides `lean` and the required `statement_change`. The proof and
proof_deps are unchanged; their route now has its missing source hypotheses.
The item is a detail of `sk-cor-ambient-ind-derived`, not that unit itself.
Every current stmt/proof citer was read; no citer was edited:

- `sk-thm-constructible-compactness`: holds true — Its separated finite-type scheme over the algebraic closure of a finite field satisfies the standing field setting; sum, truncation and localizing-containment uses remain valid.
- `det-proper-unbounded-window-ii-general`: holds false — It explicitly allows arbitrary schemes X,Y; its sum and truncation uses need the standing separated finite-type positive-characteristic field hypotheses.
- `lem-sfb-adic-proper-truncation-bound`: holds true — Its rational coefficient cases and schemes explicitly satisfy the same standing field setting; localizing containment and truncation uses remain valid.
- `sk-lem-proper-unbounded-window`: holds true — Its statement explicitly supplies the standing field setting inherited from the proper-heart bound; both truncation uses remain valid.
- `det-proper-unbounded-window-ii-bounded`: holds false — It allows an arbitrary proper morphism of schemes without the standing field setting; its cohomology-sum and truncation uses cannot apply this scoped interface.
- `det-proper-image-localizing-proper`: holds true — The use occurs in its rational coefficient assertions, which explicitly assume the standing field setting, so Loc(Dbc) containment still applies.
- `sk-lem-proper-unbounded-window-ii`: holds true — It explicitly assumes the standing separated finite-type positive-characteristic field setting; every sum and truncation use is unchanged.
- `det-proper-unbounded-window-arbitrary`: holds false — Its referenced bounded-below detail does not state the standing field hypotheses; those hypotheses must be made explicit before its truncation uses apply.
- `det-finite-window-bounded`: holds false — It states X is a scheme and supplies a uniform Ext bound, but does not supply the standing field setting needed to invoke the scoped truncation assertion.
- `det-constructible-compactness-bounded`: holds true — It explicitly has exactly the standing field setting, so its truncation and sum uses remain valid.
- `det-brown-hypotheses-generation`: holds true — Its separated finite-type scheme over the algebraic closure of a finite field satisfies the standing field setting; localizing containment is unchanged.

Preflight repair: the first dry run found a signature-record extraction error.
The extractor had matched the word theorem inside the proof docstring. It now
extracts from the declaration line itself, preserving the signature verbatim.

## Second reading by Q28

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

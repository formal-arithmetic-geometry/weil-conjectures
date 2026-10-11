## Worker report

Module: `Sheaf.AlgebraicGeometry.TruncationDerivedLimit`.
Declaration: `AlgebraicGeometry.truncation_isDerivedLimitTriangle_of_local_bound`.
The single theorem has a sorry proof; no definitions or other theorems are added.
The node is unchanged outside `lean`.

Source checked: https://stacks.math.columbia.edu/tag/0D64, Lemma 20.37.9.
The repository's `literature/stacks-project/cohomology.tex` is absent on this machine,
so the source tag was read online. It assumes a ringed space and the displayed
uniform bound on a basis, and concludes reconstruction by lower truncations.
The node deliberately specializes this to schemes; the Lean does the same.

Hypothesis and clause correspondence:

- Scheme X: `(X : Scheme.{u})`, with arbitrary explicitly bound universe u.
- E in D(O_X): `(E : schemeDerivedCategory X)`. The explicit
  `HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))`
  supplies the shared derived-category construction, with arbitrary morphism universe w.
  No quasi-coherence or boundedness hypothesis is imposed.
- Existence of an integer d >= 0: `∃ (d : ℕ) ...`. Naturals encode exactly the
  nonnegative integers; no upper bound is imposed on d.
- Basis B for X: `B : Set (Opens X)` and
  `IsTopologicalBasis ((fun U : Opens X => (U : Set X)) '' B)`.
  Members are open subsets; the image forgets their open-set proofs.
- Every U in B: `∀ (U : Opens X), U ∈ B → ...`.
- Every p > d: `∀ (p : ℕ), d < p → ...`. Since d >= 0, every integer p > d
  is positive, so this indexing excludes no source case.
- Every q < 0: `∀ (q : ℤ), q < 0 → ...`; no bound on negative q.
- H^q(E): `(DerivedCategory.homologyFunctor
  (SheafOfModules.{u} (moduleRings X.toRingedSpace)) q).obj E`.
- H^p(U,H^q(E)) = 0: `IsZero ((RingedSpace.openModuleCohomology
  X.toRingedSpace p U).obj (...))`. This is the right derived functor of sections
  over U on O_X-module sheaves, valued in abelian groups, not the unrelated Ext
  definition of abelian-sheaf cohomology. IsZero refers to the categorical group
  object, not to its bare underlying type.
- E_n for n >= 0: `fun n : ℕ => ((DerivedCategory.TStructure.t
  (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).truncGE (-(n : ℤ))).obj E`.
- Canonical transition E_(n+1) -> E_n: `natTransTruncGEOfLE
  (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)`, evaluated at E.
  The inline arithmetic discharges only the inequality required to specify this
  existing map; no mathematical theorem of the delivery is proved.
- Product existence: the conclusion first existentially quantifies a `HasProduct`
  of this tower. It is a conclusion, not an extra assumption. Lean registers this
  class-valued existential binder for the dependent remainder of the conclusion.
- Morphism E -> product with canonical components: the first Roos arrow is
  `Pi.lift (fun n : ℕ => (...truncGEπ (-(n : ℤ))).app E)`. The universal property
  fixes all its components to be the stipulated canonical maps.
- E with that map is a derived limit: `∃ δ : (∏ᶜ ...) ⟶ E⟦(1 : ℤ)⟧,
  IsDerivedLimitTriangle ... E (Pi.lift ...) δ`. This uses precisely the shared
  distinguished Roos-triangle predicate. As explained by the node's proof and the
  theorem docstring, this is the node's primary conclusion, expressing reconstruction
  up to isomorphism with a derived limit; it does not choose a nonexistent canonical
  Rlim functor or assert uniqueness of a comparison. The node's “that is” sentence is
  the same reconstruction assertion, not an additional functorial choice.

Dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and its `Scheme.Hom` signature/docstrings were read.
  Scheme is available through the derived-category import.
- `def-pc-derived-category`: `Sheaf.AlgebraicGeometry.DerivedCategory`,
  `AlgebraicGeometry.schemeDerivedCategory`; its carrier is the established
  SheafOfModules/moduleRings construction, not a second category on X.Modules.
- `pqf-def-cohomology`: `Sheaf.Paper.PQFCohomology`,
  `AlgebraicGeometry.sheafCohomologyAndHigherDirectImages` was read in full. Its
  docstring/record identifies the already defined module cohomology as right derived
  global sections. For the open-set cohomology required here, the established
  `Sheaf.Topology.OpenModuleCohomology` declaration
  `AlgebraicGeometry.RingedSpace.openModuleCohomology` is used directly; its full
  definition and docstring and those of `RingedSpace.moduleCohomology` were read.
  The PQF theorem supplies long exact sequences and higher direct images, which this
  statement does not assert, so its module is not imported unnecessarily.
- `def-sbc-standard-tstructure-derived-category`: Mathlib leaf, using
  `DerivedCategory.TStructure.t` from
  `Mathlib.Algebra.Homology.DerivedCategory.TStructure` and its truncations and
  comparison maps from `Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE`.
  The definition of t, truncGE, truncGEπ and natTransTruncGEOfLE were inspected.
- `def-weil-derived-limit`: `Sheaf.CategoryTheory.Triangulated.DerivedLimit`,
  `CategoryTheory.IsDerivedLimitTriangle` and `CategoryTheory.IsDerivedLimit` were
  read in full. The stronger specified-triangle form is required because the node
  fixes the projection components; it is part of this dependency's recorded names.

Edge cases checked before writing:

- d = 0 requires vanishing only for positive p, as in the affine case.
- n = 0 is truncGE 0; n+1 has the right transition direction, since -(n+1) <= -n.
- q ranges over all negative integers, while no restriction is made on H^q for q >= 0.
- The empty scheme admits the empty basis; its cohomology and tower are zero,
  consistent with the conclusion. Nonempty X cannot have an empty topological basis.
- E = 0 gives the zero tower and a distinguished zero triangle.
- Arbitrary u and w are bound explicitly; the countable tower does not require an
  independent large indexing universe or a nonempty-basis assumption.
- Products and K-injective resolutions are not added as hypotheses. Product existence
  is asserted inside the conclusion, so the statement applies to every E in the node.

Searches for an existing statement:

- msearch.py leanfinder, query `derived limit truncation tower bounded local
  cohomological dimension`: eight hits on isGE/isLE and injective dimension,
  including DerivedCategory.isGE_iff; none states this reconstruction theorem.
- msearch.py loogle, query `DerivedCategory.TStructure.t`: twelve hits on the
  standard t-structure and bounded derived subcategories; no derived-limit theorem.
- msearch.py grep, query `derived.*limit|truncationTower` in Algebra/Homology:
  zero hits.
- msearch.py leansearch, query `derived inverse limit of lower truncations under
  bounded local sheaf cohomology`: service unavailable (Internal Server Error).
- rg on WeilConjectures and lean/Sheaf for
  `lem-pc-ringed-space-truncation-derived-limit|truncation.*[Ll]imit|truncationTower`:
  no source declaration for this node. Project sibling
  `qcoh_truncation_isDerivedLimitTriangle` assumes quasi-coherent cohomology and
  refers to this node in its proof: a specialization, not this statement.
- rg for `truncation_isDerivedLimitTriangle_of_local_bound|local.*bound.*trunc|
  trunc.*local.*bound` in the source names, WeilConjectures, lean/Sheaf and Mathlib:
  no collision or matching declaration.

Validation: scompile.py U1 lem-pc-ringed-space-truncation-derived-limit compiled the
single module in 2.7 seconds, exit code 0, without warnings. The delivery dry run is
run after this report and the node record are written.

No statement correction, missing notion, unusable dependency, or disputed assertion
was found. No new nodes or dependency modules are delivered.

## Second reading by U1

I independently read the node, delivered theorem, all five statement dependency
nodes, and their actual declarations. Object/hypothesis/conclusion checklist:

1. Arbitrary scheme X: `(X : Scheme.{u})`. Mathlib's Scheme extends
   LocallyRingedSpace with local affine neighbourhoods. PASS: the node explicitly
   specializes the ringed-space source to schemes.
2. Arbitrary E in D(O_X): `(E : schemeDerivedCategory X)`. I opened the
   abbreviation: it is DerivedCategory of the shared SheafOfModules/moduleRings
   carrier. Its `HasDerivedCategory.{w}` binder supplies this localization,
   without imposing boundedness, quasi-coherence, or a geometric condition. PASS.
3. One nonnegative d and one basis B exist: `∃ (d : ℕ) (B : Set (Opens X)),
   IsTopologicalBasis ((fun U : Opens X => (U : Set X)) '' B) ∧ ...`.
   Naturals encode all integers d >= 0, and the image is the underlying family
   of open sets, a basis rather than merely a cover or an affine basis. PASS.
4. All U in B, all p > d, all q < 0: `∀ (U : Opens X), U ∈ B →
   ∀ (p : ℕ), d < p → ∀ (q : ℤ), q < 0 → ...`.
   Every integer p > d >= 0 is positive, so indexing p by naturals loses no
   source case. The quantifier order and strict inequalities match. PASS.
5. H^q(E): `(DerivedCategory.homologyFunctor
   (SheafOfModules.{u} (moduleRings X.toRingedSpace)) q).obj E`.
   I read its definition in Mathlib's DerivedCategory/HomologySequence.lean:
   it descends cochain-complex homology through localization. PASS.
6. H^p(U,H^q(E)) = 0: `IsZero ((RingedSpace.openModuleCohomology
   X.toRingedSpace p U).obj (...))`. I read openModuleSections and
   openModuleCohomology: right-derived evaluation at U using injective
   O_X-module resolutions, valued in AddCommGrpCat. IsZero is applied to a
   group object, not a bare Type. I also read the PQFCohomology dependency
   and RingedSpace.moduleCohomology: the shared open-set cohomology is the
   required notion, without a private definition or an abelian-sheaf Ext
   substitution. PASS.
7. E_n = tau_GE(-n) E for n >= 0: `fun n : ℕ =>
   ((DerivedCategory.TStructure.t (C := SheafOfModules.{u}
   (moduleRings X.toRingedSpace))).truncGE (-(n : ℤ))).obj E`.
   I read the standard t-structure and truncGE: good lower truncation in
   the unbounded derived category, not brutal truncation. PASS.
8. Canonical E_(n+1) -> E_n: `natTransTruncGEOfLE
   (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)`, evaluated at E.
   Its signature is t.truncGE a -> t.truncGE b for a <= b, hence the
   direction is correct. Inline arithmetic only types the existing map. PASS.
9. Product existence: `∃ (_ : HasProduct (fun n : ℕ => ...)), ...`.
   This asserts existence in the conclusion, with the dependent remainder
   using that same product; it is not an additional hypothesis. PASS.
10. E -> product with canonical components: `Pi.lift (fun n : ℕ =>
    (...truncGEπ (-(n : ℤ))).app E)`. I read truncGEπ's signature
    𝟭 -> t.truncGE n. The product universal property fixes exactly the
    canonical truncation components, not arbitrary tower maps. PASS.
11. E with that map is a derived limit: `∃ δ : (∏ᶜ ...) ⟶ E⟦(1 : ℤ)⟧,
    IsDerivedLimitTriangle ... E (Pi.lift ...) δ`. I opened this shared
    predicate and towerTransitionEndomorphism: the middle arrow is 1 - s,
    with component pr_n - pr_(n+1) ≫ f_n, and the triangle is distinguished.
    This is exactly the node's primary conclusion. Its explanatory
    isomorphism wording does not add a chosen Rlim functor: the dependency
    defines Rlim as a triple/property, with no canonical choice. Transport
    along the isomorphism in the node's proof gives the specified triangle;
    conversely this triangle realizes the reconstruction. PASS.

Source: the local Stacks checkout is absent, so I opened Tag 0D64 and the
original cohomology.tex at
https://raw.githubusercontent.com/stacks/stacks-project/master/cohomology.tex.
I read section-derived-limits, lemma-is-limit-dimension, the preceding
lemma-is-limit-spaltenstein, and the definitions of module cohomology and
RΓ(U,-). The section assumes only a ringed space and notes existence of
products in D(O_X). The lemma has exactly the common bound and basis,
without Noetherian, separatedness, characteristic, or finiteness assumptions.
The preceding lemma uses p(x,m) = d + max(0,m), matching the docstring's
pointwise reduction. The remaining proof steps choose a derived limit and
transport its Roos triangle; each is present in the theorem docstring.

Edge cases: d = 0 imposes positive-degree vanishing only; q = 0 is excluded
as required. At n = 0 the truncation is tau_GE 0 and the first transition
is tau_GE (-1) -> tau_GE 0. Zero E and the empty scheme are included. An
empty scheme admits the empty basis; a nonempty space cannot have one.
The tower index is the fixed nonempty ℕ, so an empty tower is not a case
of this node. Universes u and w are explicitly bound, with no independent
index universe. There is no base field or characteristic restriction.

Independent searches, with wording different from the worker's:

- LeanFinder: `left completeness derived category sheaves local cohomology
  vanishing`; eight hits on support/injectives (isGE_iff, isLE_iff,
  exists_iso_Q_obj_of_isGE, etc.), no reconstruction theorem.
- Loogle: `CategoryTheory.IsDerivedLimitTriangle`; zero hits, unknown
  identifier because this declaration is project-local.
- LeanSearch: `A complex is the homotopy inverse limit of its connective
  truncations if negative cohomology sheaves have bounded cohomological
  dimension`; unavailable with Internal Server Error, recorded as
  unavailable rather than a negative verdict.
- rg over Mathlib/Algebra/Homology, upstream WeilConjectures, project
  lean/Sheaf, and dag/lean_names_upstream.json for left.?complete,
  homotopy.?limit, truncation/limit in both orders, local cohomological
  dimension, Tag 0D64, and the new declaration name. Upstream hits concern
  homotopy-limit infrastructure and derived completion. I opened the
  project's qcoh_truncation_isDerivedLimitTriangle: it assumes quasi-coherent
  cohomology and cites this node in its proof, so is a specialization, not
  a realization of the present statement. No name collision was found.

No new definition nodes, dependency modules, or statement correction are
delivered. All required notions have usable shared declarations. The only
theorem has proof sorry; there are no hollow definitions, private declarations,
local notation, or local instances. Module and theorem docstrings have the
source and blueprint marker, and the theorem carries the node's proof steps.
Namespace, imports, line lengths, and bound variables meet the conventions.
The node's lean.statement is verbatim the file's theorem signature.

Mismatches found: none. Changes: appended this second-reading report only;
the Lean module and node record are unchanged.
Validation: scompile.py compiled the single delivered module in 2.5 seconds,
exit code 0, without warnings. The prescribed delivery dry run and final
delivery also run server compilation and preflight.

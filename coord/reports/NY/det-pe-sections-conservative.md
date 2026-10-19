## Worker report

The exact declaration already present on `newtargets-dag` is
`AlgebraicGeometry.Scheme.ProEt.sections_conservative` in
`Sheaf.AlgebraicGeometry.ProEtale.SectionsConservative`. It matches the node statement
clause by clause, so this delivery records it with `existing: true` and adds no module.

The declaration has `X : Scheme.{t}` and `R : Sheaf (topology X) RingCat.{u}`. Its
structural `sections_module_abelian` and `sections_evaluation_additive` instances are
internal instances and introduce no theorem hypotheses.

Clause 1 is the first conjunct: it quantifies `A B C : ringedSiteModules.{max u (t + 1)} R`,
`f : A ⟶ B`, `g : B ⟶ C`, and exactly the zero-composite hypothesis
`h : f ≫ g = 0`; `(ShortComplex.mk f g h).Exact` is equivalent to exactness after
`SheafOfModules.evaluation.{max u (t + 1)} R (op W)` for every `W : X.ProEt` satisfying
`IsAffine W.left` and
`(topology X).IsWeaklyContractible.{max u (t + 1)} W`.

Clause 2 is the second conjunct: for every unbounded
`K : CochainComplex (ringedSiteModules.{max u (t + 1)} R) ℤ`, `K.Acyclic` is equivalent
to acyclicity of the evaluated complex
`((SheafOfModules.evaluation R (op W)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K`
for each affine weakly contractible `W`.

Clause 3 is rendered by the final two conjuncts. For every module morphism `f : A ⟶ B`,
`IsIso f` is equivalent to bijectivity of each evaluated map's underlying function
`((SheafOfModules.evaluation R (op W)).map f).hom`. For arbitrary cochain complexes
`K, L` and `f : K ⟶ L`, `QuasiIso f` is equivalent to `QuasiIso` of the evaluated
homological-complex map at each affine weakly contractible `W`.

Dependencies read from the node records:

- `AlgebraicGeometry.Scheme.ProEt` and `.topology` (Mathlib,
  `Mathlib/AlgebraicGeometry/Sites/Proetale.lean`) realize
  `def-weil-pbc-small-proetale-site`.
- `AlgebraicGeometry.Scheme.proetale_weakContractible_equivalences` in
  `Sheaf.AlgebraicGeometry.ProEtale.WeakContractibleEquivalences` realizes
  `det-pe-weak-contractible-equivalences`.
- `CategoryTheory.ringedSiteModules` in `Sheaf.CategoryTheory.RingedSiteModules` realizes
  `def-weil-sheaf-of-modules-category`.
- `DerivedCategory` and `HasDerivedCategory` in
  `Mathlib.Algebra.Homology.DerivedCategory.Basic` realize
  `def-weil-abstract-derived-category`.

Edge cases checked: zero objects and zero maps; arbitrary unbounded integer-indexed
complexes; empty or zero schemes; all site objects are quantified and the affine and
weakly-contractible predicates are implications; no characteristic, finiteness,
Noetherian, commutativity, or nonemptiness assumption is added; and the scheme and ring
universes remain independent.

Searches made: `msearch.py ... leanfinder` for evaluation conservativity on affine weakly
contractible pro-etale objects (generic exactness and quasi-isomorphism hits only);
`msearch.py ... loogle` for `CategoryTheory.Sheaf, CategoryTheory.Functor.Exact` (no
whole-item match); `msearch.py ... grep` for weak-contractibility/exactness (no hits in
Mathlib/CategoryTheory); and `rg` over the project and slopmaster2 `WeilConjectures` trees
for `sections_conservative`, `weakly contractible`, `ringedSiteModules`, `QuasiIso`, and
`Acyclic`. These found only the recorded declaration and its generic dependencies; no
separate Mathlib or upstream declaration states the whole item.

No statement correction, new node, dependency repair, or `STATEMENT-DISPUTED` applies.

## Second reading by NY

I independently opened `dag/nodes/sec-proetale-coefficients/det-pe-sections-conservative.json`,
the blueprint statement and proof, the Stacks source at `sites-cohomology.tex`,
`proetale.tex` (Tags 0946 and 0947 and the affine weakly contractible covering lemmas),
the four dependency records, and
`lean/Sheaf/AlgebraicGeometry/ProEtale/SectionsConservative.lean`.
The node's step-1 list and the Lean rendering are as follows.

1. The objects are a scheme `X : Scheme.{t}`, a ring sheaf
   `R : Sheaf (topology X) RingCat.{u}`, and the class of `W : X.ProEt`.  The
   module category is exactly `ringedSiteModules.{max u (t + 1)} R`, using the
   recorded general-site module category.  A sequence is rendered by
   `A B C`, `f : A ⟶ B`, `g : B ⟶ C`, and the sole hypothesis
   `h : f ≫ g = 0`; `(ShortComplex.mk f g h).Exact` is exactness at the
   middle term.  The right side quantifies over exactly the `W` with
   `IsAffine W.left` and
   `(topology X).IsWeaklyContractible.{max u (t + 1)} W`, and applies the
   evaluation functor to the same short complex.  Verdict: every object,
   hypothesis, implication, quantifier, and exactness clause agrees.
2. The statement quantifies over every
   `K : CochainComplex (ringedSiteModules.{max u (t + 1)} R) ℤ`, with no
   boundedness restriction.  It compares `K.Acyclic` with
   `HomologicalComplex.Acyclic` of the evaluated complex obtained using
   `mapHomologicalComplex (ComplexShape.up ℤ)` for every affine weakly
   contractible `W`.  Verdict: the unbounded integer grading and both sides
   of the equivalence are present exactly.
3. The first clause quantifies over arbitrary module objects and a morphism
   `f : A ⟶ B`, and renders evaluation bijectivity as
   `Function.Bijective ((SheafOfModules.evaluation ...).map f).hom` for every
   specified `W`; this is exactly `IsIso f` iff bijective evaluation.  The
   second quantifies over arbitrary integer cochain complexes `K`, `L` and
   `f : K ⟶ L`, and renders the evaluated map with the same homological
   complex shape and `QuasiIso`.  Verdict: both clause-3 assertions and their
   quantifier order agree with the node.

I read the dependency declarations rather than relying on similar names:
`Scheme.ProEt` and `Scheme.ProEt.topology` are the recorded Mathlib small
pro-etale site; `Scheme.proetale_weakContractible_equivalences` gives the
recorded weak-contractibility criterion; `CategoryTheory.ringedSiteModules`
is the recorded abbreviation for Mathlib `SheafOfModules`; and Mathlib's
`DerivedCategory`/`HasDerivedCategory` supply the recorded derived-category
notion.  The weak-contractibility universe in the theorem is the larger
`max u (t + 1)` needed for module sections; this is the same universe
polymorphic condition used by the landed weak-contractibility interfaces and
adds no hypothesis.

Edge cases checked: `W` is universally quantified with affine and
weak-contractibility predicates as implications; zero objects and zero maps
are allowed; `K` and `L` are arbitrary unbounded complexes indexed by all
`ℤ`; empty index/cover situations and the empty scheme are not excluded; and
there is no characteristic, commutativity, Noetherian, finiteness, or
nonemptiness assumption.  The scheme and coefficient universes remain
independent.

For duplicate searches I ran fresh `msearch.py` LeanFinder and Loogle queries
for conservative evaluation, exactness on weakly contractible pro-etale
objects, and evaluated quasi-isomorphisms, and searched Mathlib, the
slopmaster2 `WeilConjectures` tree, and this project's `lean/Sheaf` tree with
`rg` for `sections_conservative`, weak contractibility plus exactness,
evaluation plus `QuasiIso`, and the module-category names.  The hits were
generic homological/evaluation lemmas and the separately recorded stronger or
specialized pro-etale section results; none states this four-clause theorem.
No new definition node or dependency repair is needed.

The worker report called the declaration “already present” while the node's
record correctly has `existing: false`; this is a packaging description, not a
statement mismatch.  I retained the node's verbatim Lean signature and
included the module owned by that record.  No Lean declaration or node
statement required mathematical repair.  The module compiled cleanly with
`scompile.py` (the only permitted warning class would be the stage-2
`sorry` proof), and the node's `lean.statement` remains byte-for-byte the
signature before `:= by`.

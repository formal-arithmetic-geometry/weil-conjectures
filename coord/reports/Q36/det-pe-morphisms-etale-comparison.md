## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleComparison` states
`AlgebraicGeometry.etale_indEtale_weaklyEtale_comparison`. It contains one
postponed proof (`by sorry`) and no definitions. The source is the blueprint node
`literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-def-pe-morphisms/det-pe-morphisms-etale-comparison.md`.

The theorem binds `u : U ⟶ X` with `{U X : Scheme.{u}}` in clauses 1, 3 and 4.
Clause 1 is `Etale u → WeaklyEtale u`, with no additional hypothesis. Clause 2
binds commutative rings `R B : Type u`, instances `[CommRing R]`, `[CommRing B]`
and `[Algebra R B]`, assumes `Algebra.IndEtale R B`, and concludes weak
étaleness of the canonical `Spec.map (CommRingCat.ofHom (algebraMap R B))`.
Clause 3 has exactly `WeaklyEtale u → LocallyOfFinitePresentation u → Etale u`.
Clause 4 is an iff for every affine target open `T : X.Opens` and affine source
open `V : U.Opens`, with `e : V ≤ u ⁻¹ᵁ T`; it says that the induced map
`(u.appLE T V e).hom` is flat and that the tensor multiplication map
`Algebra.TensorProduct.lmul' Γ(X,T) (S := Γ(U,V))`, supplied the induced algebra,
is flat. Thus all four clauses and every hypothesis of the node are rendered.

The statement uses these recorded declarations: `AlgebraicGeometry.Scheme` and
`Scheme.Hom` from `Mathlib.AlgebraicGeometry.Scheme`; `AlgebraicGeometry.WeaklyEtale`
from `Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`; `Algebra.IndEtale` from
`Sheaf.RingTheory.IndPrincipalZariski` (upstream `WeilConjectures.RingTheory.ProEtale.IndEtale`);
`AlgebraicGeometry.Etale` and `LocallyOfFinitePresentation` from the corresponding
Mathlib morphism modules; `AlgebraicGeometry.Spec` and `Spec.map` from
`Mathlib.AlgebraicGeometry.Scheme`; and `RingHom.Flat` from
`Mathlib.RingTheory.RingHom.Flat`. The proof-plan imports also include the
recorded affine pullback, flatness, finite-presentation, flat-monomorphism, and
ind-étale stability modules.

I checked empty schemes and opens, zero rings, identity maps, arbitrary filtered
ind-étale presentations, and the zero-generator case in the finite-presentation
argument. No characteristic, finiteness, quasi-compactness, or nontriviality
hypothesis was added. `set_option autoImplicit false` binds all variables.

Searches run with `msearch.py` (2026-10-16 UTC) were: LeanFinder query “Etale
morphisms and spectra of ind etale algebras are weakly etale; weakly etale
morphisms locally of finite presentation are etale; affine criterion by flat
multiplication” (8 generic étale hits, no four-clause match); Loogle query
`AlgebraicGeometry.WeaklyEtale, AlgebraicGeometry.Etale` (2 clause-1 hits);
grep query `WeaklyEtale|weaklyEtale` in `AlgebraicGeometry/Morphisms` (5 hits,
only the definition and APIs); and LeanSearch query “A morphism of schemes is
weakly etale if and only if on all affine charts its ring map and tensor
multiplication map are flat” (8 hits, no exact statement). `rg` searches of
Mathlib, upstream `WeilConjectures`, and project `lean/Sheaf` found no existing
four-clause declaration; the only node-id hit is a downstream citation.

## Earlier second reading (a previous round; superseded)

I independently opened the node and the module and matched each clause. Clause 1
is exactly `Etale u → WeaklyEtale u` for an arbitrary scheme morphism. Clause 2
uses precisely the canonical spectrum map of an `R`-algebra and only the
ind-étale hypothesis. Clause 3 has exactly the two stated hypotheses and the
étale conclusion. Clause 4 quantifies over all compatible affine charts and
contains both the section ring flatness and tensor multiplication flatness
conditions. The imports reuse the dependency declarations, the theorem has only
its expected `sorry` proof, and no mismatch was found.

## Second reading by Q36

I independently read the sandbox node and Lean file against the blueprint source
`sec-proetale-coefficients/sk-def-pe-morphisms/det-pe-morphisms-etale-comparison.md`.
I also opened the Stacks sources: `more-morphisms.tex`, the introduction to the
weakly etale section, Definition 094P and Lemma 094X;
`proetale.tex`, the ind-etale section and Lemma 097N; `morphisms.tex`,
Lemmas 01U5 and 0818; and `etale.tex`, Theorem 025G. These passages concern
arbitrary schemes and commutative rings, with no standing Noetherian, field,
characteristic, separatedness or quasi-compactness assumption.

The object/hypothesis/conclusion checklist is as follows.

1. Arbitrary schemes U and X and their morphism u are
   `∀ {U X : Scheme.{u}} (u : U ⟶ X)` in clauses 1, 3 and 4. These are the
   recorded `AlgebraicGeometry.Scheme` and `Scheme.Hom`, not affine schemes
   substituted for the general schemes. Verdict: exact.
2. Clause 1 has the single hypothesis that u is etale, `Etale u`, and the
   conclusion `WeaklyEtale u`. Neither property is an extra ambient instance.
   Verdict: exact implication.
3. Clause 2 introduces arbitrary commutative rings R and B and their structural
   ring map through `(R B : Type u) [CommRing R] [CommRing B] [Algebra R B]`.
   Every commutative ring map supplies this algebra structure. The hypothesis
   `Algebra.IndEtale R B` is the dependency's filtered-colimit notion, without
   a finite or explicitly chosen presentation. Its conclusion is weak etaleness
   of exactly `Spec.map (CommRingCat.ofHom (algebraMap R B))`, from Spec B to
   Spec R. This is the affine pro-etale situation spelled out in the node;
   it asserts no converse. Verdict: exact.
4. Clause 3 assumes `WeaklyEtale u` and `LocallyOfFinitePresentation u`, in
   that order, and concludes `Etale u`. Local finite presentation is not
   replaced by global finite presentation or finite type. Verdict: exact.
5. Clause 4 introduces all affine target opens `T : X.Opens` with
   `_hT : IsAffineOpen T`, all affine source opens `V : U.Opens` with
   `_hV : IsAffineOpen V`, and exactly the compatibility
   `e : V ≤ u ⁻¹ᵁ T`. The chart rings are `Γ(X, T)` and `Γ(U, V)`, and the
   ring map is `(u.appLE T V e).hom`. The first conjunct is its `RingHom.Flat`.
   Verdict: exact objects and chart hypotheses.
6. The second chart conjunct is `RingHom.Flat` of
   `(Algebra.TensorProduct.lmul' Γ(X, T) (S := Γ(U, V))).toRingHom`.
   The lambda's algebra argument is supplied by the same chart map's
   `.toAlgebra`; it is not a universally quantified or arbitrary extra algebra
   structure. I opened `TensorProduct/Maps.lean`: `lmul'_apply_tmul` identifies
   its value on b tensor c as bc. Thus this is precisely the multiplication
   B tensor_R B to B for the induced R-algebra. Verdict: exact.
7. The whole final clause is `WeaklyEtale u ↔ ∀ T ... V ... e, ... ∧ ...`.
   The flatness conditions are imposed on every compatible affine chart,
   as the node's proof step 2 explicitly requires, not on one selected chart.
   Both directions and both flatness conditions are present. Verdict: exact.

Dependency interfaces were checked in their source files, not inferred from
names. `Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale` defines weak etaleness
by flatness of u and `pullback.diagonal u`; `Morphisms.Etale` defines the
etale property on all affine chart maps; `Morphisms.FinitePresentation`
defines local finite presentation on those same maps, agreeing with the
pointwise definition via the node's recorded `iff_exists_appLE` interface.
`Mathlib.RingTheory.RingHom.Flat` evaluates module flatness using the given
ring map. The spectrum and its contravariant map are those in
`Mathlib.AlgebraicGeometry.Scheme`. `Sheaf.RingTheory.IndPrincipalZariski`
publicly exposes upstream `Algebra.IndEtale`, whose class fields give a small
filtered colimit presentation with etale terms; etale algebras already include
finite presentation. No private replacement is introduced. I also opened the
proof dependency nodes and `Sheaf.RingTheory.IndEtaleStability`, whose clause
`f.IndEtale → f.WeaklyEtale` is the clause used here. The affine pullback,
open pullback, flat affine criterion, finite-presentation chart criterion and
flat locally finitely presented monomorphism records point to the imported
Mathlib interfaces. There are no new nodes or dependency modules in this delivery.
There is no statement correction and therefore no correction/citer audit.

Edge cases: empty schemes and empty affine opens are permitted (their section
rings can be zero); no `Nonempty` or `Nontrivial` instance occurs. Zero rings
are allowed in clause 2. No finite index set or list of generators is bound in
the statement, so no empty-index or n=0 case is excluded; the seven-step proof
docstring explicitly includes the zero-generator diagonal presentation. All
characteristics and non-Noetherian rings remain allowed. The declaration is
polymorphic in `universe u`, uses the common universe of `Scheme.{u}` and of
the dependency `Algebra.IndEtale`, and adds no equality of independent site or
coefficient universes. All variables, universes and instances are bound;
`autoImplicit false` is present.

Independent searches (2026-10-16 UTC):

- `msearch.py ... leanfinder` with "An absolutely flat scheme morphism of local
  finite presentation is etale; affine rings criterion for flat diagonal":
  eight generic etale/flatness results, no full four-clause statement.
- `msearch.py ... loogle` with
  `AlgebraicGeometry.WeaklyEtale, AlgebraicGeometry.LocallyOfFinitePresentation`:
  zero results.
- `msearch.py ... leansearch` with "The diagonal of an affine morphism is flat
  precisely when multiplication of its tensor square is flat": eight results,
  including `diagonal_SpecMap`, `Flat.flat_appLE` and generic affine-property
  infrastructure; no full comparison.
- Independent `rg` searches used `absolutely.flat`, flatness of diagonals,
  weak-etale/local-finite-presentation combinations, and the declaration name,
  in pinned Mathlib, upstream `WeilConjectures`, project `lean/Sheaf`, the
  side `lean/WeilConjectures`, and `dag/lean_names_upstream.json`.
  I opened the substantive candidates: Mathlib `etale_le_weaklyEtale`
  covers clause 1; upstream `proAffineEtale.weaklyEtale` covers clause 2;
  upstream `WeaklyEtale.etale` covers clause 3; and upstream
  `WeaklyEtale.hasRingHomProperty` plus the affine spectrum comparison provide
  the infrastructure for clause 4. None is the whole four-clause declaration.
  The existing notions are all reused; no duplicate definition was written.

H5/H6/H8/H9: the module introduces no definitions, has only the single named
postponed theorem with `by sorry`, and contains no proved helpers or hidden
axioms. Both docstrings cite the source and exact blueprint id. The theorem
proof docstring follows all seven node proof steps, including the neighbourhood
argument for the diagonal, the finite-generator kernel presentation and the
flat-monomorphism argument. The header, namespace and imports follow the
conventions; every Lean line is at most 100 characters. A literal comparison
confirms `lean.statement` equals the source signature verbatim.

No mathematical mismatch was found. I preserved the Lean declaration and node
record and added this detailed independent reading; the earlier second-reading
paragraph remains explicitly labelled superseded. The prescribed `scompile.py`
compiled the delivered module cleanly, with no errors or unexpected warnings.
